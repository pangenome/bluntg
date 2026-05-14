//! gen-gfa: trivial De Bruijn graph builder for bluntify test input.
//!
//! Reads one FASTA file (optionally gzip-compressed) and a `k` value,
//! emits a GFA1 stream on stdout with:
//!   • one `S` segment per distinct k-mer (numbered 1..);
//!   • one `L` link per distinct (k-1)-overlap adjacency;
//!   • one `P` path per input record, listing the k-mer walk through the graph.
//!
//! This is *not* a unitig builder — every k-mer is its own node, which keeps
//! the input shape simple and exercises bluntify on a graph with abundant
//! length-`k` segments and (k-1)-overlap edges.
//!
//! Usage:  gen-gfa <k> <fasta[.gz]>   > output.gfa

use flate2::read::MultiGzDecoder;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::fs::File;
use std::io::{self, BufRead, BufReader, Read, Write};
use std::path::Path;
use std::process::ExitCode;

struct FastaRecord {
    name: String,
    seq: Vec<u8>,
}

fn open_reader(path: &Path) -> io::Result<Box<dyn Read>> {
    let f = File::open(path)?;
    let is_gz = path
        .extension()
        .map(|e| e == "gz" || e == "bgz")
        .unwrap_or(false);
    if is_gz {
        Ok(Box::new(MultiGzDecoder::new(f)))
    } else {
        Ok(Box::new(f))
    }
}

fn read_fasta(path: &Path) -> io::Result<Vec<FastaRecord>> {
    let r = open_reader(path)?;
    let mut br = BufReader::new(r);
    let mut records: Vec<FastaRecord> = Vec::new();
    let mut cur: Option<FastaRecord> = None;
    let mut line = String::new();
    loop {
        line.clear();
        let n = br.read_line(&mut line)?;
        if n == 0 {
            break;
        }
        let s = line.trim_end_matches(['\r', '\n']);
        if s.is_empty() {
            continue;
        }
        if let Some(rest) = s.strip_prefix('>') {
            if let Some(rec) = cur.take() {
                records.push(rec);
            }
            let name = rest.split_whitespace().next().unwrap_or("").to_string();
            cur = Some(FastaRecord {
                name,
                seq: Vec::new(),
            });
        } else if let Some(rec) = cur.as_mut() {
            rec.seq.extend(s.bytes().map(|b| b.to_ascii_uppercase()));
        }
    }
    if let Some(rec) = cur.take() {
        records.push(rec);
    }
    Ok(records)
}

fn write_gfa<W: Write>(
    out: &mut W,
    records: &[FastaRecord],
    k: usize,
) -> io::Result<()> {
    // Assign IDs to k-mers in first-seen order so output is deterministic
    // and walk reconstruction is straightforward.
    let mut id_of: BTreeMap<Vec<u8>, u64> = BTreeMap::new();
    let mut id_order: Vec<Vec<u8>> = Vec::new();
    let intern = |kmer: &[u8], id_of: &mut BTreeMap<Vec<u8>, u64>,
                  id_order: &mut Vec<Vec<u8>>| -> u64 {
        if let Some(&id) = id_of.get(kmer) {
            id
        } else {
            let id = (id_order.len() as u64) + 1;
            id_order.push(kmer.to_vec());
            id_of.insert(kmer.to_vec(), id);
            id
        }
    };
    // First pass: intern every k-mer that appears, collect edges and paths.
    let mut edges: BTreeSet<(u64, u64)> = BTreeSet::new();
    let mut paths: Vec<(String, Vec<u64>)> = Vec::new();
    for rec in records {
        if rec.seq.len() < k {
            continue;
        }
        let mut path_ids: Vec<u64> = Vec::with_capacity(rec.seq.len() + 1 - k);
        let mut prev: Option<u64> = None;
        for i in 0..=(rec.seq.len() - k) {
            let kmer = &rec.seq[i..i + k];
            let id = intern(kmer, &mut id_of, &mut id_order);
            if let Some(p) = prev {
                if p != id {
                    edges.insert((p, id));
                }
            }
            path_ids.push(id);
            prev = Some(id);
        }
        paths.push((rec.name.clone(), path_ids));
    }
    writeln!(out, "H\tVN:Z:1.0")?;
    // Segments
    for (idx, kmer) in id_order.iter().enumerate() {
        let id = (idx as u64) + 1;
        out.write_all(b"S\t")?;
        write!(out, "{id}\t")?;
        out.write_all(kmer)?;
        writeln!(out)?;
    }
    // Links
    let overlap = k.saturating_sub(1);
    for (a, b) in &edges {
        writeln!(out, "L\t{a}\t+\t{b}\t+\t{overlap}M")?;
    }
    // Paths
    for (name, ids) in &paths {
        let segs: Vec<String> = ids.iter().map(|i| format!("{i}+")).collect();
        let overlaps: Vec<String> = (0..ids.len().saturating_sub(1))
            .map(|_| format!("{overlap}M"))
            .collect();
        let overlaps_str = if overlaps.is_empty() {
            "*".to_string()
        } else {
            overlaps.join(",")
        };
        writeln!(out, "P\t{name}\t{}\t{overlaps_str}", segs.join(","))?;
    }
    Ok(())
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 3 {
        eprintln!("usage: gen-gfa <k> <fasta[.gz]>");
        return ExitCode::from(2);
    }
    let k: usize = match args[1].parse() {
        Ok(k) if k >= 2 => k,
        _ => {
            eprintln!("error: k must be an integer ≥ 2");
            return ExitCode::from(2);
        }
    };
    let path = Path::new(&args[2]);
    let records = match read_fasta(path) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("error reading {}: {e}", path.display());
            return ExitCode::from(1);
        }
    };
    let stdout = io::stdout();
    let mut lock = stdout.lock();
    if let Err(e) = write_gfa(&mut lock, &records, k) {
        eprintln!("error writing GFA: {e}");
        return ExitCode::from(1);
    }
    ExitCode::SUCCESS
}
