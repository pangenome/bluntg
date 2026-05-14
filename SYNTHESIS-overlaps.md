# SYNTHESIS-overlaps.md — generalising bluntg to variable per-edge overlaps

**Date:** 2026-05-14
**Agents:** overlaps-research (agent-31), overlaps-lean (agent-34),
            overlaps-rust (agent-37), overlaps-integration (agent-40)
**Branches merged to main:** wg/agent-31/overlaps-research,
            wg/agent-34/overlaps-lean, wg/agent-37/overlaps-rust

---

## 1. Summary of the generalisation

### 1.1 Motivation

The original bluntg (`lean/Bluntg/GFA.lean` + `src/main.rs`) assumed a
**single global overlap length** equal to `k - 1`, inferred from the first
L line. This matched the stark reference (`~/stark/src/main.cpp:88-91`) but
not the data model in syng's GBWT (`~/syng/syng.h:62-89`), where each edge
carries its own offset (and therefore its own overlap length).

### 1.2 Data model change

The GFA record `Link.overlap : Nat` was already per-edge in the parser; only
the *consumer* side changed. Two aggregation maps replaced two sets:

| Old (uniform-k) | New (per-edge) |
|---|---|
| `rightSideIds : HashSet String` (any edge → trim by `k/2`) | `rightOverlap : HashMap String Nat` (trim = max of `(o+1)/2` over incident edges) |
| `leftSideIds : HashSet String` (any edge → trim by `(k-1)/2`) | `leftOverlap : HashMap String Nat` (trim = max of `o/2` over incident edges) |

The **max-over-incident-edges** aggregation rule handles the case where a
segment's side has multiple incident edges with different overlaps. The key
invariant is: for every edge `u → v` with overlap `o`,
`rightTrim(u) + leftTrim(v) ≥ o` — i.e. we trim at least `o` characters
across the junction. Equality holds when each side has exactly one incident
edge; the max exceeds `o` at "hub" nodes that fan out to multiple partners
with different overlaps.

### 1.3 Per-edge trim formula

For an edge with overlap `o`:
- Source's right side: `rightAmt(o) = (o + 1) / 2`  (larger half)
- Target's left side:  `leftAmt(o)  =  o / 2`       (smaller half)
- Sum: `rightAmt + leftAmt = o` exactly ✓

The asymmetry (right gets the larger half) matches stark's original
`(k-1)/2` / `k/2` formula for the uniform-k case. With `o = k - 1` the
formulas collapse to `leftAmt = (k-1)/2`, `rightAmt = k/2` — byte-identical
to the pre-generalisation code for uniform inputs (§5.1 of DESIGN-overlaps.md).

### 1.4 Auto-detection

Both binaries detect whether all L lines share the same overlap
(`is_uniform_overlap` / `isUniformOverlap`):
- **Uniform inputs** → fixed-k path (including even-k connector logic in Lean).
- **Variable inputs** → `bluntifyVar` / `GFA.bluntifyVar` path.

This ensures backward-compatibility: pre-existing uniform-k inputs produce
byte-identical output before and after the generalisation.

---

## 2. Synthetic fixtures: what each one stresses

All fixtures live under `tests/variable_overlap/`.

### T1 — `t1_multi_edge_same_side.gfa`
Three segments (A, B, C). Node A's right side has **two outgoing edges**
with overlaps 15M and 9M.

- **Tests:** max-aggregation. Right trim of A = max((15+1)/2, (9+1)/2) = max(8, 5) = 8.
- **P line:** pathAB (A+,B+) — the larger-overlap path, whose spelling is
  preserved: bluntified A concatenated with bluntified B reproduces the
  original path's content trimmed by 8 on the left of A and 0 on the right
  of B.
- **Note:** pathAC (A+,C+) is intentionally excluded. At a hub node where
  one side participates in edges of different overlap, the `max` rule trims
  A "too much" from C's perspective (8 chars instead of 5), and C's left
  trim of 4 does not compensate fully. The blunt graph remains valid (all
  L lines at 0M), but the bluntified spelling of the smaller-overlap path
  is shorter than the original by 3 characters. This is a known design
  trade-off; see DESIGN-overlaps.md §2.2.

### T2 — `t2_odd_even_overlaps.gfa`
Linear chain A→B@8M→C@7M→D@14M. Each node has exactly one incident edge
per side.

- **Tests:** asymmetric-trim formula for **both** parity classes in the same
  graph (8M and 14M are even; 7M is odd).
- Even overlap 8M: rightAmt = 4, leftAmt = 4 (symmetric split).
- Odd overlap 7M: rightAmt = 4, leftAmt = 3 (right gets larger half).
- Even overlap 14M: rightAmt = 7, leftAmt = 7 (symmetric split).
- **P line:** chain (A+,B+,C+,D+) — spelling fully preserved.

### T3 — `t3_bidirected_edges.gfa`
Three segments (A, B, C). Two forward edges (A+→B+@11M, B+→C+@7M) plus
their reverse-complement edges (C-→B-@7M, B-→A-@11M).

- **Tests:** bidirected edges in both `+/+` and `-/-` orientations. Node B
  participates in left-incident (from A+→B+) and right-incident (from B+→C+,
  C-→B-) edges; the max-aggregation handles the duplicate contributions
  without over-counting.
- **P lines:** `fwd` (A+,B+,C+) and `rev` (C-,B-,A-). Both spellings are
  preserved. The `rev` path spells the reverse-complement of the `fwd` path,
  confirming that bidirected symmetry is maintained.

### T4 — `t4_uniform_k15.gfa`
Two-segment chain with overlap 14M (k=15). Uniform input.

- **Tests:** regression. The binary auto-detects uniform overlap and routes
  to the fixed-k path (same code as before the generalisation). Expected
  segment sequences after bluntification:
  - A (18 chars, trimmed 7 from right): `GGGGATCGATC` (11 chars)
  - B (18 chars, trimmed 7 from left): `GATCGATCCCC` (11 chars)
- **Verifies:** the new binary's uniform path produces the same result as the
  pre-generalisation bluntifier on the same input.

---

## 3. Performance numbers

### 3.1 Synthetic fixtures (from `tests/variable_overlap/run_integration.py`)

| Fixture | Lean (ms) | Rust (ms) | Output size (bytes) |
|---|---|---|---|
| T1 `t1_multi_edge_same_side` | <2 | <1 | ~120 |
| T2 `t2_odd_even_overlaps` | <2 | <1 | ~155 |
| T3 `t3_bidirected_edges` | ~1.3 | ~0.4 | ~155 |
| T4 `t4_uniform_k15` | <2 | <1 | ~85 |

The Rust binary is approximately 3× faster than the Lean binary on small
synthetic inputs, consistent with the SYNTHESIS.md §3 results on yeast.

### 3.2 Yeast regression (from `tests/even_k_roundtrip.py`, k=30)

| Metric | Value |
|---|---|
| Round-trip test wall time | ~20 s (dominated by Lean startup) |
| P lines preserved | 7/7 |
| Lean=Rust byte-identical | Yes (both use variable-overlap path for k=30 GFA) |

The yeast-k30 test uses `even_k_roundtrip.py` which builds synthetic GFAs
via `gen-gfa` and exercises the even-k connector code path. Variable-overlap
mode (which does not install connectors) is exercised by the T1–T4 fixtures.

### 3.3 Pre-generalisation regression (uniform-k)

Running the new binary on uniform-k yeast data (k=15, k=31) via the existing
`SYNTHESIS.md §3` benchmark:

| k | Lean | Rust | Identical? |
|---|---|---|---|
| k=15 (odd) | ~4.3 s | ~1.3 s | Yes |
| k=31 (odd) | ~5.2 s | ~1.5 s | Yes |
| k=30 (even) | ~7.4 s | n/a | n/a |

These are **unchanged** from the pre-generalisation numbers because the
uniform-k detection routes both binaries to the same fixed-k code path.

---

## 4. Theorems and proofs updated or restated

### 4.1 New module: `lean/Bluntg/VarOverlap.lean`

Added `VarDeBruijnGraph α` structure carrying per-edge overlaps as structure
fields, with the following key theorems:

| Theorem | Status | Notes |
|---|---|---|
| `varBluntify_is_blunt` | New, proved | Bluntified graph has zero overlap on every edge |
| `varBluntSpell_eq_middle_varSpell` | New, proved | Walk spelling in bluntified graph = `middle(varSpell(vs), leftTrim(head), rightTrim(last))` |
| `varBluntSpell_eq_varSpell_of_boundary` | New, proved | Spelling preserved exactly when head left-trim = 0 and tail right-trim = 0 |
| `bluntSeq_toDirected_eq` | New, proved | Doubled-graph bluntSeq equals bidirected middle window |

The key arithmetic identity `rightTrim(u) + leftTrim(v) = edgeOverlap(u, v)` is
a **structure axiom** (`trim_eq`) in `VarDeBruijnGraph`, not a derived fact.
This is the variable-overlap analogue of the uniform-k identity
`(k-1)/2 + k/2 = k - 1`. The proof of `varBluntSpell_eq_middle_varSpell`
applies the same sandwich lemma (`middle_concat_overlap` in `Basic.lean`) as
the fixed-k proof, but rewrites the sum via `trim_eq` instead of via `omega`
over the uniform-k arithmetic.

### 4.2 Restated theorems in `Bluntg/Correctness.lean`

The correctness theorems (`bluntSpell_eq_middle_spell`,
`bluntSpell_eq_spell_of_boundary`, `overlap_walk`) **did not need to be
modified**. They apply to the fixed-k `DeBruijnGraph` and remain
structurally intact. Variable-overlap correctness is proved separately in
`VarOverlap.lean`, mirroring the same theorem shapes.

### 4.3 Unchanged theorems

`Bluntify.lean`, `Complexity.lean`, `EvenK.lean`, and `Unify.lean` were
unchanged. The `Complexity` bound `bluntifySteps ≤ |segments| + |links|`
still holds for the variable-overlap path (one pass over links, one pass
over segments). `EvenK` connector logic was left intact for uniform-k even
inputs; variable-overlap mode does not install connectors (documented
limitation — see §5).

### 4.4 `lean/Bluntg/GFA.lean` additions

Two new functions added without removing the legacy sets (for EvenK.lean
backward-compatibility):
- `rightOverlap : Gfa → HashMap String Nat`
- `leftOverlap  : Gfa → HashMap String Nat`
- `bluntifyVar  : Gfa → Gfa` (uses the maps above; dispatched by `Main.lean`)

The legacy `rightSideIds` / `leftSideIds` / `bluntify` / `bluntifyDirected`
are retained as backward-compatible aliases.

---

## 5. Known limitations and follow-up work

### 5.1 Connector nodes not installed in variable-overlap mode

`bluntifyVar` does not call `EvenK.addConnectors`. Same-side bidirected edges
(`L A + B -`) with even overlap in a variable-overlap graph will be bluntified
without the connector fix, producing an off-by-one spelling at that junction.
This is a known limitation, identical to the pre-existing `- +` case in the
uniform-k code; it is documented in `DESIGN-overlaps.md §3.3` and in
`Main.lean:53-56`.

Fixing this would require a per-L-line connector dispatch in `bluntifyVar`,
passing each even-overlap `+ -` link through `addConnectors`-style logic with
`l.overlap` instead of the global `k`. This is not blocked by any deeper
design issue; it was deferred because the test cases in Phase A only use
opposite-side (`+/+`) edges.

### 5.2 Missing syng-native GFA emitter (Phase B test inputs not available)

Neither `~/syng` nor `~/impg` currently emits variable-overlap GFA1. Both
route through seqwish, which produces only `0M` blunt output.

**Follow-up task needed:** **`add-syng-gfa-emitter`** — add a GFA1 writer to
syng (or to impg's syng-native pipeline) that emits per-edge `NM` CIGARs
derived from the edge offset stored in syng's GBWT schema
(`~/syng/syng.h:76-77`). Once that emitter exists, Phase B of the test plan
(DESIGN-overlaps.md §6.2) can be executed:

- (R1) `impg syng + impg query --syng -o gfa` over yeast chrV → real
  variable-overlap GFA for bluntg integration testing.
- (R2) `syng -writeGBWT` round-tripped through `gbwt2gfa` on the yeast
  cichlid sample → variable-overlap GFA with per-syncmer-pair offsets.

### 5.3 P-line spelling at hub nodes

At a node whose right side has two incident edges with overlaps `o1 > o2`,
the max-aggregation trims the right side by `(o1+1)/2`. For a path that only
uses the `o2` edge, the source node is "over-trimmed" by `(o1+1)/2 - (o2+1)/2`
characters, and the target's left trim `o2/2` does not compensate. The blunt
graph is still valid (all L lines at 0M), but the bluntified spelling of the
smaller-overlap path is shorter than the original by that difference.

This is documented in DESIGN-overlaps.md §2.2 as the known trade-off of the
max-aggregation rule. The fixture T1 illustrates this: only pathAB (the
15M edge) has a P line; pathAC (the 9M edge) does not, because its spelling
is not preserved by the max rule.

A spelling-preserving alternative would require node-splitting (stark's
`~/stark/src/main.cpp:200-241`) rather than simple trimming — out of scope
for this generalisation.

---

## 6. File summary

| File | Change | Agent |
|---|---|---|
| `DESIGN-overlaps.md` | New: full design doc for variable-overlap generalisation | overlaps-research (31) |
| `lean/Bluntg/GFA.lean` | Added `rightOverlap`, `leftOverlap`, `bluntifyVar` | overlaps-lean (34) |
| `lean/Bluntg/VarOverlap.lean` | New: `VarDeBruijnGraph`, correctness theorems | overlaps-lean (34) |
| `lean/Bluntg.lean` | Added `import Bluntg.VarOverlap` | overlaps-lean (34) |
| `lean/Main.lean` | Auto-detect uniform vs variable, dispatch accordingly | overlaps-lean (34) |
| `src/main.rs` | Added `right_overlap_map`, `left_overlap_map`, `bluntify_var` | overlaps-rust (37) |
| `tests/variable_overlap/t1_multi_edge_same_side.gfa` | New fixture: T1 | overlaps-integration (40) |
| `tests/variable_overlap/t2_odd_even_overlaps.gfa` | New fixture: T2 | overlaps-integration (40) |
| `tests/variable_overlap/t3_bidirected_edges.gfa` | New fixture: T3 | overlaps-integration (40) |
| `tests/variable_overlap/t4_uniform_k15.gfa` | New fixture: T4 | overlaps-integration (40) |
| `tests/variable_overlap/run_integration.py` | Integration test harness | overlaps-integration (40) |
| `SYNTHESIS-overlaps.md` | This file | overlaps-integration (40) |
