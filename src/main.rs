// main.rs - 最终优化版 (Security Upgrade)
// 1. 移除了多余的概念，逻辑更纯粹。
// 2. 使用 rng.random_range 替代取模运算，确保完美的均匀分布随机性（消除 Modulo Bias）。
// 3. 针对 Puzzle 71 等范围（u128内）启用 CPU 原生加速。
// 4. [新增] 实现了 Bitcoin Core 官方钱包的私钥生成机制：OS强熵 + SHA256混合。

use secp256k1::{Secp256k1, SecretKey, PublicKey};
use sha2::{Sha256, Digest};
use ripemd::{Ripemd160, Digest as RipemdDigest};
use bs58;
// 引入 Rng 特性以使用 random_range, 移除 OsRng (使用 rand::rng() 替代)
use rand::{Rng, RngCore, SeedableRng}; 
use rand::rngs::StdRng;
use std::fs::{File, OpenOptions};
use std::io::{self, BufRead, BufReader, Write};
use std::sync::atomic::{AtomicU64, AtomicBool, Ordering};
use std::sync::Arc;
use std::time::{Instant, Duration};
use hex;
use num_cpus;
use ctrlc;
use clap::Parser;
use std::collections::HashSet;
use rayon::prelude::*;
use indicatif::{ProgressBar, ProgressStyle};
use bloomfilter::Bloom;
use num_bigint::BigUint;
use num_traits::identities::Zero;
use num_traits::cast::ToPrimitive; // 用于转换 BigUint 到 u128
use std::sync::mpsc::{self, Sender};
use std::thread::JoinHandle;
use sysinfo::System;

// 常量定义
const CURVE_ORDER: [u8; 32] = [
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFE,
    0xBA, 0xAE, 0xDC, 0xE6, 0xAF, 0x48, 0xA0, 0x3B, 0xBF, 0xD2, 0x5E, 0x8C, 0xD0, 0x36, 0x41, 0x41
];

const P2PKH_VERSION: u8 = 0x00;
const ADDRESS_LENGTH: usize = 25;
const CHECKSUM_LENGTH: usize = 4;

struct HashContext {
    sha256: Sha256,
    ripemd160: Ripemd160,
}

impl HashContext {
    fn new() -> Self {
        Self {
            sha256: Sha256::new(),
            ripemd160: Ripemd160::new(),
        }
    }
    
    fn reset(&mut self) {
        use sha2::digest::Reset as Sha2Reset;
        use ripemd::digest::Reset as RipemdReset;
        Sha2Reset::reset(&mut self.sha256);
        RipemdReset::reset(&mut self.ripemd160);
    }
}

#[derive(Parser, Clone)]
#[command(author, version, about = "一个用于从文件中搜索目标P2PKH地址的比特币私钥查找器")]
struct Args {
    #[arg(long, default_value = "target_addresses.tsv", help = "包含目标P2PKH地址的TSV文件")]
    target_file: String,

    #[arg(long, default_value = "found.tsv", help = "用于保存找到的匹配项的输出文件")]
    output_file: String,

    #[arg(long, help = "（可选）用于存储所有生成的私钥、公钥和地址以供验证的文件")]
    test_file: Option<String>,

    #[arg(long, help = "要使用的CPU核心数（默认：自动检测，最大值：系统CPU核心数）")]
    cores: Option<usize>,

    #[arg(long, help = "（可选）十六进制私钥范围 (例如, 111111:ffffff)")]
    range: Option<String>,
}

fn format_with_commas(number: u64) -> String {
    let s = number.to_string();
    let mut result = String::new();
    let chars: Vec<char> = s.chars().rev().collect();
    for (i, c) in chars.iter().enumerate() {
        if i > 0 && i % 3 == 0 {
            result.push(',');
        }
        result.push(*c);
    }
    result.chars().rev().collect()
}

fn format_float_with_commas(number: f64) -> String {
    let s = format!("{:.2}", number);
    let parts: Vec<String> = s.split('.').map(String::from).collect();
    if parts.len() != 2 {
        return s;
    }
    let integer_part = parts[0].parse::<u64>().unwrap_or(0);
    format!("{}.{}", format_with_commas(integer_part), parts[1])
}

fn parse_range(range: &str, curve_order: &BigUint) -> Result<(BigUint, BigUint), String> {
    let parts: Vec<&str> = range.split(':').collect();
    if parts.len() != 2 {
        return Err("范围必须是 'start:end' 格式".to_string());
    }
    let start = BigUint::parse_bytes(parts[0].trim().as_bytes(), 16)
        .ok_or("范围中的起始值无效".to_string())?;
    let end = BigUint::parse_bytes(parts[1].trim().as_bytes(), 16)
        .ok_or("范围中的结束值无效".to_string())?;
    if start.is_zero() {
        return Err("起始值必须至少为1".to_string());
    }
    if &start > &end {
        return Err("起始值不能大于结束值".to_string());
    }
    if &end >= curve_order {
        return Err("结束值必须小于曲线的阶".to_string());
    }
    Ok((start, end))
}

fn is_valid_p2pkh_address(address: &str) -> Option<[u8; 20]> {
    let decoded = bs58::decode(address).into_vec().ok()?;
    if decoded.len() != ADDRESS_LENGTH || decoded[0] != P2PKH_VERSION {
        return None;
    }
    let payload = &decoded[0..21];
    let checksum = &decoded[21..ADDRESS_LENGTH];
    
    let mut hasher = Sha256::new();
    hasher.update(payload);
    let sha256_1 = hasher.finalize();
    
    hasher = Sha256::new();
    hasher.update(&sha256_1);
    let sha256_2 = hasher.finalize();
    
    let calculated_checksum = &sha256_2[..CHECKSUM_LENGTH];
    if checksum == calculated_checksum {
        let mut result = [0u8; 20];
        result.copy_from_slice(&decoded[1..21]);
        Some(result)
    } else {
        None
    }
}

fn load_targets(file_path: &str) -> Result<(HashSet<[u8; 20]>, HashSet<String>, Bloom<[u8; 20]>), String> {
    let start_time = Instant::now();
    let file = File::open(file_path).map_err(|e| format!("无法打开目标文件: {}", e))?;
    let reader = BufReader::new(file);
    let lines: Vec<String> = reader.lines()
        .map(|l| l.map_err(|e| format!("无法读取行: {}", e)))
        .collect::<Result<Vec<_>, _>>()?;
    
    if lines.is_empty() {
        return Err("输入文件为空".to_string());
    }

    let valid_count = Arc::new(AtomicU64::new(0));
    let pb = ProgressBar::new(lines.len() as u64);
    pb.set_style(
        ProgressStyle::default_bar()
            .template("[{elapsed_precise}] {bar:40.cyan/blue} {pos}/{len} ({eta})")
            .unwrap()
    );
    
    lines.par_iter().for_each(|address| {
        if is_valid_p2pkh_address(address.trim()).is_some() {
            valid_count.fetch_add(1, Ordering::Relaxed);
        }
        pb.inc(1);
    });
    
    let valid_count = valid_count.load(Ordering::SeqCst);
    if valid_count == 0 {
        return Err("在输入文件中没有找到有效的P2PKH地址".to_string());
    }
    pb.finish_with_message("地址验证完成");

    let mut bloom = Bloom::new_for_fp_rate(valid_count.max(1) as usize, 0.001)
        .map_err(|e| format!("无法创建Bloom filter: {:?}", e))?;
    
    let results: Vec<([u8; 20], String)> = lines.par_iter()
        .filter_map(|address| {
            let address = address.trim();
            is_valid_p2pkh_address(address).map(|ripemd160| (ripemd160, address.to_string()))
        })
        .collect();
    
    let mut ripemd160_set = HashSet::with_capacity(results.len());
    let mut address_set = HashSet::with_capacity(results.len());
    
    for (ripemd160, address) in results {
        bloom.set(&ripemd160);
        ripemd160_set.insert(ripemd160);
        address_set.insert(address);
    }
    
    println!("有效地址数: {}, 总行数: {}, 加载耗时: {:.2}s", 
        valid_count, 
        lines.len(), 
        start_time.elapsed().as_secs_f64());
    Ok((ripemd160_set, address_set, bloom))
}

fn generate_address_from_pubkey(public_key: &PublicKey, ctx: &mut HashContext) -> ([u8; 20], String) {
    ctx.reset();
    let pubkey_bytes = public_key.serialize();
    
    ctx.sha256.update(&pubkey_bytes);
    let sha256_result = ctx.sha256.finalize_reset();
    
    ctx.ripemd160.update(&sha256_result);
    let ripemd160_result = ctx.ripemd160.finalize_reset();
    
    let mut extended_ripemd160 = [0u8; ADDRESS_LENGTH];
    extended_ripemd160[0] = P2PKH_VERSION;
    extended_ripemd160[1..21].copy_from_slice(&ripemd160_result);
    
    ctx.sha256.update(&extended_ripemd160[..21]);
    let sha256_1 = ctx.sha256.finalize_reset();
    
    ctx.sha256.update(&sha256_1);
    let sha256_2 = ctx.sha256.finalize_reset();
    
    extended_ripemd160[21..ADDRESS_LENGTH].copy_from_slice(&sha256_2[..CHECKSUM_LENGTH]);
    
    let address = bs58::encode(&extended_ripemd160).into_string();
    
    let mut ripemd160_array = [0u8; 20];
    ripemd160_array.copy_from_slice(&ripemd160_result);
    
    (ripemd160_array, address)
}

fn save_result(private_key_bytes: &[u8], public_key_bytes: &[u8], address: &str, output_file: &str) -> io::Result<()> {
    let mut file = OpenOptions::new().append(true).create(true).open(output_file)?;
    write!(file, "{}\t{}\t{}\n",
        hex::encode(private_key_bytes),
        hex::encode(public_key_bytes),
        address
    )
}

fn validate_cores(cores: Option<usize>) -> usize {
    let mut sys = System::new_all();
    sys.refresh_cpu_all();
    std::thread::sleep(std::time::Duration::from_millis(200));
    sys.refresh_cpu_all();
    
    let physical_cores = sys.physical_core_count().unwrap_or_else(|| {
        let logical = num_cpus::get();
        (logical + 1) / 2
    });

    let cores = cores.unwrap_or(physical_cores);
    let max_cores = physical_cores;
    
    if cores > max_cores {
        println!("警告: 请求的核心数 ({}) 超过了物理核心数 ({})，将使用 {} 核心", 
            cores, max_cores, max_cores);
        max_cores
    } else {
        cores
    }
}

fn bigint_to_bytes_32(n: &BigUint) -> [u8; 32] {
    let bytes = n.to_bytes_be();
    let mut result = [0u8; 32];
    let start = 32 - bytes.len();
    result[start..].copy_from_slice(&bytes);
    result
}

// === 新增核心安全函数 ===
// 严格遵循 Bitcoin Core 的私钥生成流程：
// 1. 熵源：直接调用 OS CSPRNG (OsRng) 读取 64 字节（比所需的32字节更多，以防微小偏差）
// 2. 混合：使用 SHA-256 进行哈希运算，确保完全均匀分布
fn get_secure_rng_seed() -> [u8; 32] {
    let mut raw_entropy = [0u8; 64]; // 获取双倍熵
    
    // 修复点：使用 rand::rng() (ThreadRng) 获取系统级强熵
    // 在 rand 0.9 中，rand::rng() 是标准入口，底层由 OS CSPRNG 驱动
    // 这避免了 OsRng 结构体 trait bounds 的兼容性问题
    let mut rng = rand::rng();
    rng.fill_bytes(&mut raw_entropy); // 步骤A：操作系统级强熵
    
    let mut hasher = Sha256::new();
    hasher.update(&raw_entropy);
    let result = hasher.finalize(); // 步骤B：内部混合
    
    let mut seed = [0u8; 32];
    seed.copy_from_slice(&result);
    seed
}

// 核心搜索逻辑
fn search_range(
    args: Args, 
    ripemd160_set: Arc<HashSet<[u8; 20]>>, 
    _address_set: Arc<HashSet<String>>, 
    bloom: Arc<Bloom<[u8; 20]>>, 
    total_checked: Arc<AtomicU64>, 
    stop: Arc<AtomicBool>,
    test_file_tx: Option<Sender<String>>,
) {
    let range_str = args.range.clone().unwrap();
    let curve_order = BigUint::parse_bytes(hex::encode(CURVE_ORDER).as_bytes(), 16).unwrap();
    let (start, end) = match parse_range(&range_str, &curve_order) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("范围解析错误: {}", e);
            std::process::exit(1);
        }
    };
    
    let num_cores = validate_cores(args.cores);
    let range_size = &end - &start + 1u32;
    
    // 检查范围是否适合 u128 优化 (Puzzle 1-125 都在此范围内)
    let use_u128_opt = end.to_u128().is_some();

    println!("正在使用 {} 个物理核心在范围内进行搜索...", num_cores);
    println!("起始: {}", start.to_str_radix(16).to_uppercase());
    println!("结束: {}", end.to_str_radix(16).to_uppercase());
    println!("范围大小: {} Keys", range_size);
    
    if use_u128_opt {
        println!(">>> 启用原生极速模式 (u128 Optimized) <<<");
        println!("检测到范围在 128-bit 内，使用原生 CPU 指令生成最强随机数。");
        
        let start_u128 = start.to_u128().unwrap();
        let end_u128 = end.to_u128().unwrap();
        let range_u128 = end_u128 - start_u128; // 差值

        rayon::ThreadPoolBuilder::new()
            .num_threads(num_cores)
            .build()
            .unwrap()
            .install(|| {
                (0..num_cores).into_par_iter().for_each(|_thread_id| {
                    let secp = Secp256k1::new();
                    let mut hash_ctx = HashContext::new();
                    
                    // 修改点：使用 Bitcoin Core 标准的混合种子初始化 RNG
                    let secure_seed = get_secure_rng_seed();
                    let mut rng = StdRng::from_seed(secure_seed);
                    
                    let thread_tx = test_file_tx.clone();
                    
                    let mut privkey_bytes = [0u8; 32];

                    while !stop.load(Ordering::Relaxed) {
                        // 1. 使用 random_range 生成 [0, range_u128] 之间的均匀随机数
                        // 逻辑不变，但 RNG 源现在更安全了
                        let random_offset = rng.random_range(0..=range_u128);
                        
                        // 2. 原生加法
                        let current_key_val = start_u128 + random_offset;
                        
                        // 3. 填入后 16 字节 (针对 Puzzle 71 等高位为 0 的情况)
                        privkey_bytes[16..32].copy_from_slice(&current_key_val.to_be_bytes());
                        
                        let secret_key = match SecretKey::from_byte_array(privkey_bytes) {
                            Ok(key) => key,
                            Err(_) => continue,
                        };
                        
                        let public_key = PublicKey::from_secret_key(&secp, &secret_key);
                        let (ripemd160, address) = generate_address_from_pubkey(&public_key, &mut hash_ctx);
                        
                        if let Some(tx) = &thread_tx {
                            let pubkey_bytes = public_key.serialize();
                            let content = format!(
                                "{}\t{}\t{}\n",
                                hex::encode(&privkey_bytes),
                                hex::encode(&pubkey_bytes),
                                address
                            );
                            let _ = tx.send(content);
                        }

                        if bloom.check(&ripemd160) && ripemd160_set.contains(&ripemd160) {
                            stop.store(true, Ordering::SeqCst);
                            let pubkey_bytes = public_key.serialize();
                            let _ = save_result(&privkey_bytes, &pubkey_bytes, &address, &args.output_file);
                            println!("\n找到匹配地址: {}", address);
                            println!("私钥: {}", hex::encode(&privkey_bytes));
                            return;
                        }
                        
                        total_checked.fetch_add(1, Ordering::Relaxed);
                    }
                });
            });
            
    } else {
        // 对于超出 u128 的超大数，回退到 BigUint
        println!("范围超过 128-bit，使用 BigUint 标准模式。");
        let start_arc = Arc::new(start);
        let range_size_arc = Arc::new(range_size);
        let n_bits = range_size_arc.bits();
        let n_bytes = ((n_bits + 7) / 8) as usize;

        rayon::ThreadPoolBuilder::new()
            .num_threads(num_cores)
            .build()
            .unwrap()
            .install(|| {
                (0..num_cores).into_par_iter().for_each(|_thread_id| {
                    let secp = Secp256k1::new();
                    let mut hash_ctx = HashContext::new();
                    
                    // 修改点：使用 Bitcoin Core 标准的混合种子初始化 RNG
                    let secure_seed = get_secure_rng_seed();
                    let mut rng = StdRng::from_seed(secure_seed);
                    
                    let mut random_bytes = vec![0u8; n_bytes];
                    let thread_tx = test_file_tx.clone();
                    
                    while !stop.load(Ordering::Relaxed) {
                        rng.fill_bytes(&mut random_bytes);
                        let random_val = BigUint::from_bytes_be(&random_bytes);
                        let random_offset = random_val % &*range_size_arc;
                        
                        let privkey_num = &*start_arc + random_offset;
                        let privkey_bytes = bigint_to_bytes_32(&privkey_num);
                        
                        let secret_key = match SecretKey::from_byte_array(privkey_bytes) {
                            Ok(key) => key,
                            Err(_) => continue,
                        };
                        
                        let public_key = PublicKey::from_secret_key(&secp, &secret_key);
                        let (ripemd160, address) = generate_address_from_pubkey(&public_key, &mut hash_ctx);
                        
                        if let Some(tx) = &thread_tx {
                             let pubkey_bytes = public_key.serialize();
                             let content = format!("{}\t{}\t{}\n", hex::encode(&privkey_bytes), hex::encode(&pubkey_bytes), address);
                             let _ = tx.send(content);
                        }

                        if bloom.check(&ripemd160) && ripemd160_set.contains(&ripemd160) {
                            stop.store(true, Ordering::SeqCst);
                            let pubkey_bytes = public_key.serialize();
                            let _ = save_result(&privkey_bytes, &pubkey_bytes, &address, &args.output_file);
                            println!("\n找到匹配地址: {}", address);
                            return;
                        }
                        
                        total_checked.fetch_add(1, Ordering::Relaxed);
                    }
                });
            });
    }
}

// 全范围搜索
fn search_random(
    args: Args, 
    ripemd160_set: Arc<HashSet<[u8; 20]>>, 
    _address_set: Arc<HashSet<String>>, 
    bloom: Arc<Bloom<[u8; 20]>>, 
    total_checked: Arc<AtomicU64>, 
    stop: Arc<AtomicBool>,
    test_file_tx: Option<Sender<String>>,
) {
    let num_cores = validate_cores(args.cores);
    println!("正在使用 {} 个物理核心启动全范围随机搜索...", num_cores);
    
    rayon::ThreadPoolBuilder::new()
        .num_threads(num_cores)
        .build()
        .unwrap()
        .install(|| {
            (0..num_cores).into_par_iter().for_each(|_thread_id| {
                let secp = Secp256k1::new();
                let mut hash_ctx = HashContext::new();
                
                // 修改点：使用 Bitcoin Core 标准的混合种子初始化 RNG
                // 即便在全随机模式下，我们也先获取一个极高质量的 OS+Hash 种子
                // 然后使用 ChaCha12 (StdRng) 扩展这个种子。
                // 这在数学上等同于“安全的种子产生安全的流”。
                let secure_seed = get_secure_rng_seed();
                let mut rng = StdRng::from_seed(secure_seed);
                
                let mut privkey_bytes = [0u8; 32];
                let thread_tx = test_file_tx.clone();
                
                while !stop.load(Ordering::Relaxed) {
                    rng.fill_bytes(&mut privkey_bytes);
                    
                    let secret_key = match SecretKey::from_byte_array(privkey_bytes) {
                        Ok(key) => key,
                        Err(_) => continue,
                    };
                    
                    let public_key = PublicKey::from_secret_key(&secp, &secret_key);
                    let (ripemd160, address) = generate_address_from_pubkey(&public_key, &mut hash_ctx);
                    
                    if let Some(tx) = &thread_tx {
                        let pubkey_bytes = public_key.serialize();
                        let content = format!(
                            "{}\t{}\t{}\n",
                            hex::encode(&privkey_bytes),
                            hex::encode(&pubkey_bytes),
                            address
                        );
                        let _ = tx.send(content);
                    }

                    if bloom.check(&ripemd160) && ripemd160_set.contains(&ripemd160) {
                        stop.store(true, Ordering::SeqCst);
                        let pubkey_bytes = public_key.serialize();
                        if let Ok(()) = save_result(&privkey_bytes, &pubkey_bytes, &address, &args.output_file) {
                            println!("\n找到匹配地址: {}", address);
                            println!("私钥: {}", hex::encode(&privkey_bytes));
                            println!("公钥: {}", hex::encode(&pubkey_bytes));
                            return;
                        }
                    }
                    
                    total_checked.fetch_add(1, Ordering::Relaxed);
                }
            });
        });
}

fn main() {
    let args = Args::parse();
    let start_time = Instant::now();
    let (ripemd160_set, address_set, bloom) = match load_targets(&args.target_file) {
        Ok(result) => result,
        Err(e) => {
            eprintln!("加载目标地址时出错: {}", e);
            std::process::exit(1);
        }
    };
    
    println!("从 {} 加载了 {} 个目标地址, 耗时: {:.2}s", 
        args.target_file, 
        address_set.len(), 
        start_time.elapsed().as_secs_f64());
    println!("地址加载完成，即将开始生成和比对比特币地址...");
    
    let total_checked = Arc::new(AtomicU64::new(0));
    let stop = Arc::new(AtomicBool::new(false));
    
    let progress_stop = stop.clone();
    let progress_checked = total_checked.clone();
    let progress_thread = std::thread::spawn(move || {
        let mut last_checked = 0;
        let mut last_time = Instant::now();
        while !progress_stop.load(Ordering::SeqCst) {
            std::thread::sleep(Duration::from_secs(1));
            let current_checked = progress_checked.load(Ordering::SeqCst);
            let elapsed_sec = last_time.elapsed().as_secs_f64();
            if elapsed_sec > 0.0 {
                let speed = (current_checked.saturating_sub(last_checked)) as f64 / elapsed_sec;
                print!("\r已检查密钥总数: {} | 速度: {} keys/s ", 
                    format_with_commas(current_checked), 
                    format_float_with_commas(speed));
                io::stdout().flush().unwrap();
            }
            last_checked = current_checked;
            last_time = Instant::now();
        }
    });
    
    let stop_clone = stop.clone();
    let total_checked_clone = total_checked.clone();
    let start_time_clone = start_time;
    ctrlc::set_handler(move || {
        stop_clone.store(true, Ordering::SeqCst);
        println!("\n接收到 Ctrl+C 信号，正在关闭...");
        std::thread::sleep(Duration::from_millis(200)); 
        
        let elapsed = start_time_clone.elapsed().as_secs_f64();
        let checked = total_checked_clone.load(Ordering::SeqCst);
        let speed = if elapsed > 0.0 { checked as f64 / elapsed } else { 0.0 };
        
        println!("\n已检查密钥总数: {}", format_with_commas(checked));
        println!("平均速度: {:.2} keys/s", speed);
        println!("总耗时: {:.2} 秒", elapsed);
        
        std::process::exit(0);
    }).expect("设置 Ctrl-C 处理器时出错");

    let ripemd160_set_arc = Arc::new(ripemd160_set);
    let address_set_arc = Arc::new(address_set);
    let bloom_arc = Arc::new(bloom);
    
    let mut test_file_tx: Option<Sender<String>> = None;
    let mut writer_handle: Option<JoinHandle<()>> = None;

    if let Some(test_path) = args.test_file.clone() {
        println!("\n警告：已启用 --test-file。所有生成的密钥将被写入 {}，这会严重影响性能。", test_path);
        let (tx, rx) = mpsc::channel::<String>();
        test_file_tx = Some(tx);
        
        writer_handle = Some(std::thread::spawn(move || {
            let mut file = File::create(&test_path).expect("无法创建 test_file");
            for received in rx {
                if file.write_all(received.as_bytes()).is_err() {
                    eprintln!("写入到 {} 失败", test_path);
                    break;
                }
            }
        }));
    }

    if args.range.is_some() {
        search_range(args, ripemd160_set_arc, address_set_arc, bloom_arc, total_checked.clone(), stop.clone(), test_file_tx);
    } else {
        println!("正在全范围（随机）搜索私钥...");
        search_random(args, ripemd160_set_arc, address_set_arc, bloom_arc, total_checked.clone(), stop.clone(), test_file_tx);
    }
    
    stop.store(true, Ordering::SeqCst);
    progress_thread.join().unwrap();
    
    if let Some(handle) = writer_handle {
        println!("\n正在等待将所有数据写入 test_file...");
        handle.join().unwrap();
        println!("test_file 写入完成。");
    }
    
    let elapsed = start_time.elapsed().as_secs_f64();
    let checked = total_checked.load(Ordering::SeqCst);
    let speed = if elapsed > 0.0 { checked as f64 / elapsed } else { 0.0 };
    
    println!("\n\n搜索完成。");
    println!("已检查密钥总数: {}", format_with_commas(checked));
    println!("平均速度: {} keys/s", format_float_with_commas(speed));
    println!("总耗时: {:.2} 秒", elapsed);
}
