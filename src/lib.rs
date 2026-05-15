//! bluntg library: native-Rust bluntifier, mirrors lean/Bluntg/GFA.lean exactly.
//!
//! Public surface: [`Gfa`] + [`parse_gfa`] / [`write_gfa`] for I/O,
//! [`bluntify`] (fixed-k), [`bluntify_var`] (per-edge overlap), and
//! [`bluntify_auto`] which dispatches between them.

use std::collections::{HashMap, HashSet};
use std::io::{self, BufRead, BufReader, Write};

// ── Data types (mirror Lean GFA.lean) ────────────────────────────────────────

pub struct Segment {
    pub id: String,
    pub seq: Vec<u8>,
}

pub struct Link {
    pub from_id: String,
    pub from_plus: bool,
    pub to_id: String,
    pub to_plus: bool,
    pub overlap: usize,
}

pub struct PathStep {
    pub seg_id: String,
    pub is_plus: bool,
}

pub struct GfaPath {
    pub name: String,
    pub steps: Vec<PathStep>,
    /// Empty when the original CIGAR field was `*`.
    pub overlaps: Vec<usize>,
}

pub struct Gfa {
    pub segments: Vec<Segment>,
    pub links: Vec<Link>,
    pub paths: Vec<GfaPath>,
}

// ── Parsing ───────────────────────────────────────────────────────────────────

fn parse_orient(s: &str) -> Option<bool> {
    match s {
        "+" => Some(true),
        "-" => Some(false),
        _ => None,
    }
}

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
                let (head, last) = s.split_at(s.len() - 1);
                let is_plus = parse_orient(last)?;
                Some(PathStep { seg_id: head.to_string(), is_plus })
            }).collect();
            let overlaps: Vec<usize> = if *ovs == "*" {
                vec![]
            } else {
                ovs.split(',').filter_map(parse_overlap_cigar).collect()
            };
            LineKind::Path(GfaPath { name: name.to_string(), steps, overlaps })
        }
        _ => LineKind::Other,
    }
}

pub fn parse_gfa(input: &[u8]) -> Gfa {
    let mut gfa = Gfa { segments: Vec::new(), links: Vec::new(), paths: Vec::new() };
    for line in BufReader::new(input).lines().map_while(Result::ok) {
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

fn trim_seq(seq: &[u8], lt: usize, rt: usize) -> Vec<u8> {
    let len = seq.len();
    if lt >= len { return vec![]; }
    let take = (len - lt).saturating_sub(rt);
    seq[lt..lt + take].to_vec()
}

pub fn infer_k(gfa: &Gfa) -> usize {
    gfa.links.first().map(|l| l.overlap + 1).unwrap_or(1)
}

pub fn is_uniform_overlap(gfa: &Gfa) -> bool {
    match gfa.links.first() {
        None => true,
        Some(first) => gfa.links.iter().all(|l| l.overlap == first.overlap),
    }
}

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

pub fn bluntify_var(gfa: Gfa) -> Gfa {
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

pub fn bluntify(gfa: Gfa, k: usize) -> Gfa {
    let right_amt = k / 2;
    let left_amt  = (k - 1) / 2;

    let mut right_ids: HashSet<String> = HashSet::new();
    let mut left_ids:  HashSet<String> = HashSet::new();
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

/// Dispatch: uniform-overlap inputs go through fixed-k [`bluntify`],
/// otherwise [`bluntify_var`]. A uniform graph with `k < 2` is returned
/// unchanged (already blunt or empty).
pub fn bluntify_auto(gfa: Gfa) -> Gfa {
    if is_uniform_overlap(&gfa) {
        let k = infer_k(&gfa);
        if k < 2 { gfa } else { bluntify(gfa, k) }
    } else {
        bluntify_var(gfa)
    }
}

// ── Output (mirrors Lean GFA.write) ──────────────────────────────────────────

pub fn write_gfa<W: Write>(out: &mut W, gfa: &Gfa) -> io::Result<()> {
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
