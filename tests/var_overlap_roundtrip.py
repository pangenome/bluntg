#!/usr/bin/env python3
"""Variable per-edge overlap round-trip test for `bluntg`.

Builds a synthetic GFA with **three different overlap lengths** on three
different L lines (CIGARs 17M, 9M, 13M), exercising the per-edge
variable-overlap path in `GFA.bluntifyVar` / `Bluntg.VarOverlap`.

For every P line in the input, the test:
  1. Computes the spelled string under the original variable overlaps.
  2. Runs `bluntg` (which detects variable overlap and dispatches to
     `bluntifyVar`).
  3. Spells the bluntified P line (now with 0M overlaps).
  4. Verifies the bluntified spelling equals the appropriately-trimmed
     middle of the original spelling.

This is the validation referenced in the `overlaps-lean` task
description (DESIGN-overlaps.md §6.2 T3).
"""
import subprocess
import sys
from pathlib import Path

COMP = {"A": "T", "T": "A", "C": "G", "G": "C", "N": "N"}


def revcomp(s: str) -> str:
    return "".join(COMP.get(c, c) for c in reversed(s))


def parse_gfa(text: str):
    segs = {}
    links = []
    paths = []
    for line in text.splitlines():
        parts = line.split("\t")
        if not parts:
            continue
        if parts[0] == "S" and len(parts) >= 3:
            segs[parts[1]] = parts[2]
        elif parts[0] == "L" and len(parts) >= 6:
            fp = parts[2] == "+"
            tp = parts[4] == "+"
            ov = int(parts[5].rstrip("M")) if parts[5] != "*" else 0
            links.append((parts[1], fp, parts[3], tp, ov))
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
            paths.append((parts[1], steps, overlaps))
    return segs, links, paths


def read_seq(segs, seg, plus):
    s = segs[seg]
    return s if plus else revcomp(s)


def spell_walk(segs, steps, overlaps):
    """Spell a walk under the given per-edge overlaps."""
    if not steps:
        return ""
    out = [read_seq(segs, *steps[0])]
    for i in range(1, len(steps)):
        s = read_seq(segs, steps[i][0], steps[i][1])
        ov = overlaps[i - 1] if i - 1 < len(overlaps) else 0
        out.append(s[ov:])
    return "".join(out)


def left_overlap_map(links):
    """Per-segment left-side max-aggregated trim = max over left-incident
    edges of (o // 2)."""
    m = {}
    for fid, fp, tid, tp, ov in links:
        amt = ov // 2
        if not fp:
            m[fid] = max(m.get(fid, 0), amt)
        if tp:
            m[tid] = max(m.get(tid, 0), amt)
    return m


def right_overlap_map(links):
    """Per-segment right-side max-aggregated trim = max over right-incident
    edges of ((o + 1) // 2)."""
    m = {}
    for fid, fp, tid, tp, ov in links:
        amt = (ov + 1) // 2
        if fp:
            m[fid] = max(m.get(fid, 0), amt)
        if not tp:
            m[tid] = max(m.get(tid, 0), amt)
    return m


def head_left_trim(left_map, right_map, steps):
    """Trim on entry side of head: + → left, - → right."""
    seg, plus = steps[0]
    return left_map.get(seg, 0) if plus else right_map.get(seg, 0)


def tail_right_trim(left_map, right_map, steps):
    """Trim on exit side of tail: + → right, - → left."""
    seg, plus = steps[-1]
    return right_map.get(seg, 0) if plus else left_map.get(seg, 0)


def run_roundtrip(text, label, bluntg_bin):
    """Bluntify `text` and verify P-line spelling preservation."""
    proc = subprocess.run(
        [str(bluntg_bin), "1"],  # k=1 is innocuous; CLI uses bluntifyVar
                                 # automatically for variable-overlap input.
        input=text, capture_output=True, text=True, check=True,
    )
    blunt_text = proc.stdout
    osegs, olinks, opaths = parse_gfa(text)
    bsegs, blinks, bpaths = parse_gfa(blunt_text)

    if len(opaths) != len(bpaths):
        print(f"[{label}] FAIL: path count differs "
              f"({len(opaths)} -> {len(bpaths)})")
        return False

    olm = left_overlap_map(olinks)
    orm = right_overlap_map(olinks)

    ok = True
    checks = 0
    for (oname, osteps, oov), (bname, bsteps, bov) in zip(opaths, bpaths):
        if oname != bname:
            print(f"[{label}] FAIL: path name {oname} -> {bname}")
            ok = False
            continue
        orig_spell = spell_walk(osegs, osteps, oov)
        blunt_spell = spell_walk(bsegs, bsteps, bov)
        l = head_left_trim(olm, orm, osteps)
        r = tail_right_trim(olm, orm, osteps)
        expected = orig_spell[l : len(orig_spell) - r] if r > 0 else orig_spell[l:]
        if blunt_spell != expected:
            print(f"[{label}] FAIL on path '{oname}':")
            print(f"  original   ({len(orig_spell)}): {orig_spell}")
            print(f"  bluntified ({len(blunt_spell)}): {blunt_spell}")
            print(f"  expected   ({len(expected)}): {expected}")
            print(f"  trim: left={l}, right={r}")
            ok = False
        checks += 1
    if ok:
        print(f"[{label}] OK: {checks} P-line(s) round-tripped with "
              f"variable overlap")
    return ok


def main():
    repo = Path(__file__).resolve().parent.parent
    bluntg = repo / "lean" / ".lake" / "build" / "bin" / "bluntg"
    if not bluntg.exists():
        print(f"bluntg not built at {bluntg}; run `(cd lean && lake build)`",
              file=sys.stderr)
        return 2

    # Construct a 4-segment chain with THREE different overlap lengths.
    # The overlap regions are chosen so that each edge's overlap invariant
    # `Suffix(seq u, o) = Prefix(seq v, o)` holds exactly.

    ab_overlap = "ATCGATCGATCGATCGA"  # 17 chars
    bc_overlap = "GCATGCATG"           # 9 chars
    cd_overlap = "TGCATGCATGCAT"       # 13 chars

    # A: arbitrary prefix + ab_overlap as its suffix.
    seg_a = "AAA" + ab_overlap                       # length 20
    # B: ab_overlap as its prefix + bc_overlap as its suffix.
    seg_b = ab_overlap + bc_overlap                  # length 26
    # C: bc_overlap as its prefix + cd_overlap as its suffix.
    seg_c = bc_overlap + cd_overlap                  # length 22
    # D: cd_overlap as its prefix + arbitrary suffix.
    seg_d = cd_overlap + "GGG"                       # length 16

    # Sanity check overlap invariants.
    assert seg_a[-17:] == seg_b[:17] == ab_overlap
    assert seg_b[-9:]  == seg_c[:9]  == bc_overlap
    assert seg_c[-13:] == seg_d[:13] == cd_overlap

    gfa = (
        "H\tVN:Z:1.0\n"
        f"S\tA\t{seg_a}\n"
        f"S\tB\t{seg_b}\n"
        f"S\tC\t{seg_c}\n"
        f"S\tD\t{seg_d}\n"
        "L\tA\t+\tB\t+\t17M\n"
        "L\tB\t+\tC\t+\t9M\n"
        "L\tC\t+\tD\t+\t13M\n"
        "P\tchain\tA+,B+,C+,D+\t17M,9M,13M\n"
    )

    ok = run_roundtrip(gfa, "var-three-overlaps", bluntg)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
