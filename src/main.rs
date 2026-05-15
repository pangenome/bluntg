//! bluntg CLI: reads GFA1 on stdin, writes bluntified GFA1 on stdout.
//! `k` is inferred from the first link's overlap if not given.

use bluntg::{bluntify, bluntify_var, infer_k, is_uniform_overlap, parse_gfa, write_gfa};
use flate2::read::MultiGzDecoder;
use std::io::{self, Read};
use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    let k_arg: Option<usize> = args.get(1).and_then(|s| s.parse().ok());

    let mut raw: Vec<u8> = Vec::new();
    if let Err(e) = io::stdin().lock().read_to_end(&mut raw) {
        eprintln!("bluntg: read error: {e}");
        return ExitCode::from(1);
    }

    let input: Vec<u8> = if raw.starts_with(&[0x1f, 0x8b]) {
        let mut decoded = Vec::new();
        match MultiGzDecoder::new(raw.as_slice()).read_to_end(&mut decoded) {
            Ok(_) => decoded,
            Err(e) => {
                eprintln!("bluntg: gzip error: {e}");
                return ExitCode::from(1);
            }
        }
    } else {
        raw
    };

    let gfa = parse_gfa(&input);
    let uniform = is_uniform_overlap(&gfa);
    let k = k_arg.unwrap_or_else(|| infer_k(&gfa));

    if uniform && k < 2 {
        eprintln!("bluntg: refusing to run with k = {k} (need k ≥ 2)");
        return ExitCode::from(2);
    }

    let blunted = if uniform {
        bluntify(gfa, k)
    } else {
        bluntify_var(gfa)
    };

    let stdout = io::stdout();
    let mut out = io::BufWriter::new(stdout.lock());
    if let Err(e) = write_gfa(&mut out, &blunted) {
        eprintln!("bluntg: write error: {e}");
        return ExitCode::from(1);
    }

    ExitCode::SUCCESS
}
