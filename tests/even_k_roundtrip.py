#!/usr/bin/env python3
"""Even-`k` round-trip test for `bluntg`.

For every P line in a GFA, compute the spelled string with the original
(k-1)-overlaps, run `bluntg` to produce the bluntified GFA, then compute
the spelled string of the bluntified P line (which has 0-overlaps and
may now traverse one or more connector nodes inserted at same-side
bidirected edges). Compare the bluntified spelling against the
appropriately-trimmed middle of the original spelling.

Run two scenarios:
  1. synthetic GFA exercising a single `L + -` (same-side) edge;
  2. yeast chrV at k=30 (all `+ +` edges, no connectors).
"""
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Tuple

COMP = {"A": "T", "T": "A", "C": "G", "G": "C", "N": "N",
        "a": "t", "t": "a", "c": "g", "g": "c", "n": "n"}


def revcomp(s: str) -> str:
    return "".join(COMP.get(c, c) for c in reversed(s))


@dataclass
class Gfa:
    segments: Dict[str, str]           # id -> seq
    links: List[Tuple[str, bool, str, bool, int]]  # (from, from+, to, to+, overlap)
    paths: List[Tuple[str, List[Tuple[str, bool]], List[int]]]  # (name, steps, overlaps)


def parse_gfa(text: str) -> Gfa:
    g = Gfa(segments={}, links=[], paths=[])
    for line in text.splitlines():
        parts = line.split("\t")
        if not parts:
            continue
        if parts[0] == "S" and len(parts) >= 3:
            g.segments[parts[1]] = parts[2]
        elif parts[0] == "L" and len(parts) >= 6:
            fp = parts[2] == "+"
            tp = parts[4] == "+"
            ov = int(parts[5].rstrip("M")) if parts[5] != "*" else 0
            g.links.append((parts[1], fp, parts[3], tp, ov))
        elif parts[0] == "P" and len(parts) >= 4:
            seg_strs = parts[2].split(",")
            steps = []
            for s in seg_strs:
                orient = s[-1] == "+"
                seg = s[:-1]
                steps.append((seg, orient))
            if parts[3] == "*":
                overlaps = []
            else:
                overlaps = [int(o.rstrip("M")) for o in parts[3].split(",")]
            g.paths.append((parts[1], steps, overlaps))
    return g


def read_seq(g: Gfa, seg: str, plus: bool) -> str:
    s = g.segments[seg]
    return s if plus else revcomp(s)


def spell_walk(g: Gfa, steps: List[Tuple[str, bool]], overlaps: List[int]) -> str:
    """Spell a walk: emit the first node's read, then for each subsequent
    step append the read with `overlaps[i-1]` chars dropped from the
    front."""
    if not steps:
        return ""
    out = [read_seq(g, *steps[0])]
    for i in range(1, len(steps)):
        s = read_seq(g, steps[i][0], steps[i][1])
        ov = overlaps[i - 1] if i - 1 < len(overlaps) else 0
        out.append(s[ov:])
    return "".join(out)


def side_sets(g: Gfa) -> Tuple[set, set]:
    """Return (lefts, rights): segment ids whose left/right side is touched."""
    lefts = set()
    rights = set()
    for fid, fp, tid, tp, _ in g.links:
        if fp:
            rights.add(fid)
        else:
            lefts.add(fid)
        if tp:
            lefts.add(tid)
        else:
            rights.add(tid)
    return lefts, rights


def head_left_trim(g: Gfa, steps: List[Tuple[str, bool]], k: int) -> int:
    """Trim amount on the entry side of the walk's first node."""
    lefts, rights = side_sets(g)
    seg, plus = steps[0]
    # Entry side: + → left; - → right
    if plus:
        return (k - 1) // 2 if seg in lefts else 0
    else:
        return k // 2 if seg in rights else 0


def tail_right_trim(g: Gfa, steps: List[Tuple[str, bool]], k: int) -> int:
    """Trim amount on the exit side of the walk's last node."""
    lefts, rights = side_sets(g)
    seg, plus = steps[-1]
    # Exit side: + → right; - → left
    if plus:
        return k // 2 if seg in rights else 0
    else:
        return (k - 1) // 2 if seg in lefts else 0


def run_roundtrip(original_text: str, k: int, label: str, bluntg_bin: Path) -> bool:
    """Bluntify `original_text` with `k`, then check that every P line's
    bluntified spelling equals the appropriately-trimmed original spelling."""
    proc = subprocess.run(
        [str(bluntg_bin), str(k)],
        input=original_text, capture_output=True, text=True, check=True,
    )
    blunt_text = proc.stdout
    orig = parse_gfa(original_text)
    blunt = parse_gfa(blunt_text)

    if len(orig.paths) != len(blunt.paths):
        print(f"[{label}] FAIL: path count differs "
              f"({len(orig.paths)} -> {len(blunt.paths)})")
        return False

    ok = True
    checks = 0
    for (oname, osteps, oov), (bname, bsteps, bov) in zip(orig.paths, blunt.paths):
        if oname != bname:
            print(f"[{label}] FAIL: path name {oname} -> {bname}")
            ok = False
            continue
        orig_spell = spell_walk(orig, osteps, oov)
        blunt_spell = spell_walk(blunt, bsteps, bov)
        # Compute expected trim from the *original* graph's side-sets,
        # since trim amounts are defined relative to the original
        # bidirected graph structure (the bluntified graph has its own
        # connectors which would otherwise be counted).
        l = head_left_trim(orig, osteps, k)
        r = tail_right_trim(orig, osteps, k)
        expected = orig_spell[l : len(orig_spell) - r] if r > 0 else orig_spell[l:]
        if blunt_spell != expected:
            print(f"[{label}] FAIL on path '{oname}':")
            print(f"  original ({len(orig_spell)}): {orig_spell[:80]}...")
            print(f"  bluntified ({len(blunt_spell)}): {blunt_spell[:80]}...")
            print(f"  expected   ({len(expected)}): {expected[:80]}...")
            print(f"  trim: left={l}, right={r}")
            ok = False
        checks += 1
    if ok:
        print(f"[{label}] OK: {checks} P-line(s) round-tripped at k={k}")
    return ok


def main() -> int:
    repo = Path(__file__).resolve().parent.parent
    bluntg = repo / "lean" / ".lake" / "build" / "bin" / "bluntg"
    if not bluntg.exists():
        print(f"bluntg not built at {bluntg}; run `(cd lean && lake build)`",
              file=sys.stderr)
        return 2

    # 1. Synthetic GFA with a same-side `+ -` edge that requires a connector,
    # exercised in BOTH walk directions (forward `1+,2-` and reverse `2+,1-`).
    synth = (
        "H\tVN:Z:1.0\n"
        "S\t1\tGATC\n"
        "S\t2\tCGAT\n"
        "L\t1\t+\t2\t-\t3M\n"
        "P\ttest_fwd\t1+,2-\t3M\n"
        "P\ttest_rev\t2+,1-\t3M\n"
    )
    ok1 = run_roundtrip(synth, 4, "synth-plus-minus", bluntg)

    # 2. Larger synthetic with k=6 and a same-side `+ -` edge.
    # A = "AGATCC" (len 6); for `+ -` walk A+, B- has overlap A's last 5
    # = first 5 of rc(B); pick rc(B) starting with "GATCC" so B's last 5
    # = rc("GATCC") = "GGATC". B = "?GGATC" → choose first char so the
    # round-trip remains stable. Pick B = "TGGATC" (len 6).
    synth2_a = "AGATCC"
    synth2_b = "TGGATC"
    # Sanity: A[-5:] = "GATCC"; rc(B)[:5] = "GATCC". ✓
    assert synth2_a[-5:] == revcomp(synth2_b)[:5], "synth2 overlap mismatch"
    synth2 = (
        "H\tVN:Z:1.0\n"
        f"S\tA\t{synth2_a}\n"
        f"S\tB\t{synth2_b}\n"
        "L\tA\t+\tB\t-\t5M\n"
        "P\twalk2\tA+,B-\t5M\n"
    )
    ok2 = run_roundtrip(synth2, 6, "synth-plus-minus-k6", bluntg)

    # 3. Yeast chrV at k=30 (all `+ +` edges from gen-gfa).
    yeast_fa = repo / "data" / "yeast.chrV.fa.gz"
    gen_gfa = repo / "target" / "release" / "gen-gfa"
    if not yeast_fa.exists():
        print(f"yeast fasta missing at {yeast_fa}; skipping", file=sys.stderr)
        return 0 if (ok1 and ok2) else 1
    if not gen_gfa.exists():
        print(f"gen-gfa missing at {gen_gfa}; run `cargo build --release`",
              file=sys.stderr)
        return 0 if (ok1 and ok2) else 1

    yeast_gfa = subprocess.run(
        [str(gen_gfa), "30", str(yeast_fa)],
        capture_output=True, text=True, check=True,
    ).stdout
    ok3 = run_roundtrip(yeast_gfa, 30, "yeast-k30", bluntg)

    return 0 if (ok1 and ok2 and ok3) else 1


if __name__ == "__main__":
    sys.exit(main())
