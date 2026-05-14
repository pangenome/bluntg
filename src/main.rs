//! bluntg: native-Rust bluntifier, mirrors lean/Bluntg/GFA.lean exactly.
//!
//! Usage:
//!   bluntg [k]   # reads GFA1 on stdin, writes bluntified GFA1 on stdout
//!                # k is inferred from the first link's overlap if not given

use flate2::read::MultiGzDecoder;
use std::collections::HashMap;
use std::io::{self, Read, BufRead, BufReader, Write};
use std::process::ExitCode;

// ── Data types (mirror Lean GFA.lean) ────────────────────────────────────────

struct Segment {
    id: String,
    seq: Vec<u8>,
}

struct Link {
    from_id: String,
    from_plus: bool,
    to_id: String,
    to_plus: bool,
    overlap: usize,
}

struct PathStep {
    seg_id: String,
    is_plus: bool,
}

struct GfaPath {
    name: String,
    steps: Vec<PathStep>,
    overlaps: Vec<usize>, // empty when original CIGAR was "*"
}

struct Gfa {
    segments: Vec<Segment>,
    links: Vec<Link>,
    paths: Vec<GfaPath>,
}

// ── Parsing ───────────────────────────────────────────────────────────────────

fn parse_orient(s: &str) -> Option<bool> {
    match s {
        "+" => Some(true),
        "-" => Some(false),
        _ => None,
    }
}

// Parses "NM" -> N and "*" -> 0, matching Lean's parseOverlap.
fn parse_overlap_cigar(s: &str) -> Option<usize> {
    if s == "*" {
        Some(0)
    } else {
        s.strip_suffix('M')?.parse().ok()
    }
}

enum LineKind {
    Segment(Segment),
    Link(Link),
    Path(GfaPath),
    Other,
}

fn parse_line(line: &str) -> LineKind {
    let parts: Vec<&str> = line.split('\t').collect();
    match parts.as_slice() {
        ["S", id, seq, ..] => LineKind::Segment(Segment {
            id: id.to_string(),
            seq: seq.as_bytes().to_vec(),
        }),
        ["L", frm, fo, to, too, ov, ..] => {
            let fp = match parse_orient(fo) { Some(v) => v, None => return LineKind::Other };
            let tp = match parse_orient(too) { Some(v) => v, None => return LineKind::Other };
            let w = match parse_overlap_cigar(ov) { Some(v) => v, None => return LineKind::Other };
            LineKind::Link(Link {
                from_id: frm.to_string(),
                from_plus: fp,
                to_id: to.to_string(),
                to_plus: tp,
                overlap: w,
            })
        }
        ["P", name, segs, ovs, ..] => {
            let steps: Vec<PathStep> = segs.split(',').filter_map(|s| {
                if s.len() < 2 { return None; }
                // last byte is '+' or '-' (ASCII), safe to split at byte boundary
                let (head, last) = s.split_at(s.len() - 1);
                let is_plus = parse_orient(last)?;
                Some(PathStep { seg_id: head.to_string(), is_plus })
            }).collect();
            let overlaps: Vec<usize> = if *ovs == "*" {
                vec![]
            } else {
                ovs.split(',').filter_map(|s| parse_overlap_cigar(s)).collect()
            };
            LineKind::Path(GfaPath { name: name.to_string(), steps, overlaps })
        }
        _ => LineKind::Other,
    }
}

fn parse_gfa(input: &[u8]) -> Gfa {
    let mut gfa = Gfa { segments: Vec::new(), links: Vec::new(), paths: Vec::new() };
    for line in BufReader::new(input).lines().flatten() {
        match parse_line(&line) {
            LineKind::Segment(s) => gfa.segments.push(s),
            LineKind::Link(l) => gfa.links.push(l),
            LineKind::Path(p) => gfa.paths.push(p),
            LineKind::Other => {}
        }
    }
    gfa
}

// ── Bluntify (mirrors Lean GFA.bluntify / GFA.bluntifyVar) ───────────────────

// Mirrors Lean's trimSeq: drop lt from left, then take (len - lt - rt) chars.
// Nat subtraction saturates at 0, so over-trimming yields empty.
fn trim_seq(seq: &[u8], lt: usize, rt: usize) -> Vec<u8> {
    let len = seq.len();
    if lt >= len { return vec![]; }
    let take = (len - lt).saturating_sub(rt);
    seq[lt..lt + take].to_vec()
}

fn infer_k(gfa: &Gfa) -> usize {
    gfa.links.first().map(|l| l.overlap + 1).unwrap_or(1)
}

fn is_uniform_overlap(gfa: &Gfa) -> bool {
    match gfa.links.first() {
        None => true,
        Some(first) => gfa.links.iter().all(|l| l.overlap == first.overlap),
    }
}

// Per-segment right-side trim: max over incident edges of (o+1)/2.
// Mirrors Lean GFA.rightOverlap.
fn right_overlap_map(gfa: &Gfa) -> HashMap<String, usize> {
    let mut map: HashMap<String, usize> = HashMap::new();
    for l in &gfa.links {
        let amt = (l.overlap + 1) / 2;
        if l.from_plus {
            let e = map.entry(l.from_id.clone()).or_insert(0);
            *e = (*e).max(amt);
        }
        if !l.to_plus {
            let e = map.entry(l.to_id.clone()).or_insert(0);
            *e = (*e).max(amt);
        }
    }
    map
}

// Per-segment left-side trim: max over incident edges of o/2.
// Mirrors Lean GFA.leftOverlap.
fn left_overlap_map(gfa: &Gfa) -> HashMap<String, usize> {
    let mut map: HashMap<String, usize> = HashMap::new();
    for l in &gfa.links {
        let amt = l.overlap / 2;
        if !l.from_plus {
            let e = map.entry(l.from_id.clone()).or_insert(0);
            *e = (*e).max(amt);
        }
        if l.to_plus {
            let e = map.entry(l.to_id.clone()).or_insert(0);
            *e = (*e).max(amt);
        }
    }
    map
}

// Variable per-edge overlap bluntify. Mirrors Lean GFA.bluntifyVar.
// For uniform-k inputs this reduces to the fixed-k result: every right side
// gets k/2 and every left side gets (k-1)/2.
fn bluntify_var(gfa: Gfa) -> Gfa {
    let rights = right_overlap_map(&gfa);
    let lefts  = left_overlap_map(&gfa);

    let segments = gfa.segments.into_iter().map(|s| {
        let l = lefts.get(&s.id).copied().unwrap_or(0);
        let r = rights.get(&s.id).copied().unwrap_or(0);
        Segment { id: s.id, seq: trim_seq(&s.seq, l, r) }
    }).collect();

    let links = gfa.links.into_iter().map(|l| Link {
        from_id: l.from_id,
        from_plus: l.from_plus,
        to_id: l.to_id,
        to_plus: l.to_plus,
        overlap: 0,
    }).collect();

    let paths = gfa.paths.into_iter().map(|p| GfaPath {
        name: p.name,
        steps: p.steps,
        overlaps: p.overlaps.iter().map(|_| 0).collect(),
    }).collect();

    Gfa { segments, links, paths }
}

// Fixed-k bluntify. Kept for the uniform-k path (byte-identical with Lean's
// bluntifyGfa for inputs that have no same-side + - edges).
fn bluntify(gfa: Gfa, k: usize) -> Gfa {
    let right_amt = k / 2;
    let left_amt  = (k - 1) / 2;

    // Collect the segment IDs that have at least one right-side / left-side
    // edge, so we know when to apply the trim.
    let mut right_ids: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut left_ids:  std::collections::HashSet<String> = std::collections::HashSet::new();
    for l in &gfa.links {
        if  l.from_plus { right_ids.insert(l.from_id.clone()); }
        if !l.to_plus   { right_ids.insert(l.to_id.clone()); }
        if !l.from_plus { left_ids.insert(l.from_id.clone()); }
        if  l.to_plus   { left_ids.insert(l.to_id.clone()); }
    }

    let segments = gfa.segments.into_iter().map(|s| {
        let l = if left_ids.contains(&s.id)  { left_amt }  else { 0 };
        let r = if right_ids.contains(&s.id) { right_amt } else { 0 };
        Segment { id: s.id, seq: trim_seq(&s.seq, l, r) }
    }).collect();

    let links = gfa.links.into_iter().map(|l| Link {
        from_id: l.from_id,
        from_plus: l.from_plus,
        to_id: l.to_id,
        to_plus: l.to_plus,
        overlap: 0,
    }).collect();

    let paths = gfa.paths.into_iter().map(|p| GfaPath {
        name: p.name,
        steps: p.steps,
        overlaps: p.overlaps.iter().map(|_| 0).collect(),
    }).collect();

    Gfa { segments, links, paths }
}

// ── Output (mirrors Lean GFA.write) ──────────────────────────────────────────

// Lean's write uses String.intercalate "\n" lines ++ "\n":
// H\tVN:Z:1.0\n<seg>\n...\n<link>\n...\n<path>\n...\n
fn write_gfa<W: Write>(out: &mut W, gfa: &Gfa) -> io::Result<()> {
    out.write_all(b"H\tVN:Z:1.0")?;
    for s in &gfa.segments {
        out.write_all(b"\nS\t")?;
        out.write_all(s.id.as_bytes())?;
        out.write_all(b"\t")?;
        out.write_all(&s.seq)?;
    }
    for l in &gfa.links {
        out.write_all(b"\nL\t")?;
        out.write_all(l.from_id.as_bytes())?;
        out.write_all(if l.from_plus { b"\t+" } else { b"\t-" })?;
        out.write_all(b"\t")?;
        out.write_all(l.to_id.as_bytes())?;
        out.write_all(if l.to_plus { b"\t+" } else { b"\t-" })?;
        write!(out, "\t{}M", l.overlap)?;
    }
    for p in &gfa.paths {
        out.write_all(b"\nP\t")?;
        out.write_all(p.name.as_bytes())?;
        out.write_all(b"\t")?;
        let mut first = true;
        for s in &p.steps {
            if !first { out.write_all(b",")?; }
            out.write_all(s.seg_id.as_bytes())?;
            out.write_all(if s.is_plus { b"+" } else { b"-" })?;
            first = false;
        }
        out.write_all(b"\t")?;
        if p.overlaps.is_empty() {
            out.write_all(b"*")?;
        } else {
            let mut first = true;
            for &w in &p.overlaps {
                if !first { out.write_all(b",")?; }
                write!(out, "{}M", w)?;
                first = false;
            }
        }
    }
    out.write_all(b"\n")?;
    Ok(())
}

// ── Entry point ───────────────────────────────────────────────────────────────

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

    // Guard only applies to the uniform-k path; variable-overlap mode derives
    // all trims from per-link CIGARs and doesn't use a global k.
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
