# Synthesis Report — bluntg parallel tracks

**Date:** 2026-05-14  
**Branch:** wg/agent-25/synthesize-tracks (merged onto main)

---

## 1. Track merge status

| Track | Branch | Merged cleanly? | Notes |
|---|---|---|---|
| A — Rust port | `wg/agent-15/track-a-rust` | Yes | Squash-merged to main as `9d7a4fc` |
| B — Even-k connectors | `wg/agent-13/track-b-even` | Yes | Squash-merged to main as `90895a3`; includes own merge of A+C |
| C — Complexity bound | `wg/agent-14/track-c-complexity` | Yes | Squash-merged to main as `9b0bf19` |
| D — Unify | `wg/agent-12/track-d-unify` | Manual resolution | See below |

### Track D resolution notes

Track D was branched from the initial commit (not from main), so it diverged from
tracks A/B/C. Three of its GFA.lean changes conflicted with the EvenK additions:

1. **`rightSideIds` / `leftSideIds` → `private`** — reverted; EvenK.lean reads these directly.
2. **`bluntifyDirected` alias removed** — reverted; EvenK.lean calls `GFA.bluntifyDirected`.
3. **`Main.lean` reverted to `GFA.bluntify`** — reverted; kept `bluntifyGfa` (even-k-aware).

New files (`Bluntg/Unify.lean`, `MainUnify.lean`) were copied verbatim. The
`lean/Bluntg.lean`, `lean/lakefile.toml`, and `README.md` were merged by hand.

---

## 2. Final theorem inventory

| Theorem | Module | Statement |
|---|---|---|
| `bluntify_is_blunt` | `Correctness` | Bluntified graph has zero overlap on every edge |
| `bluntSpell_eq_middle_spell` | `Correctness` | Walk spelling in bluntified graph = `middle(spell(vs), leftTrim, rightTrim)` |
| `bluntSpell_eq_spell_of_boundary` | `Correctness` | Spelling preserved exactly at boundary walks |
| `middle_concat_overlap` | `Basic` | Key list-arithmetic identity for sandwich+overlap composition |
| `bluntifySteps_le` | `Complexity` | `bluntifySteps g ≤ g.segments.length + g.links.length` (O(V+E) bound) |
| `augmentedSpell_length` | `EvenK` | Path length invariant preserved after connector-node insertion |
| `rewriteAligned_spell_preserved` | `Unify` | Single `unify` merge of `u + v +` chain preserves spelling of every safe path |
| `Path.unifyRewrite_spell` | `Unify` | Preservation lifted to `Path` / `Gfa.pathSpell` |

Zero `sorry`s in the merged codebase (verified: `grep -r sorry lean/Bluntg/ lean/Main*.lean`).

---

## 3. Benchmark numbers (yeast chrV, single run)

All timings on the synthesis branch after merging all tracks.

### Bluntify runtime (Lean vs Rust)

| k | Lean `bluntg` | Rust `bluntg` | Identical? |
|---|---|---|---|
| k=15 (odd) | 4.3 s | 1.3 s | Yes (byte-identical) |
| k=31 (odd) | 5.2 s | 1.5 s | Yes (byte-identical) |
| k=30 (even) | 7.4 s | — | n/a (Rust port covers odd-k only) |

### Unify reduction (Lean `unify`, k=31)

| Stage | Segments | P-lines |
|---|---|---|
| Input (raw de Bruijn, k=31) | 889,945 | 7 |
| After `bluntg` | 889,945 | 7 |
| After `unify` | 24,473 | 7 |

**Reduction factor: ~36×.** All 7 P-line spellings preserved (verified empirically by spelling comparison).

### Unify runtime

| Input | `unify` wall time |
|---|---|
| k=30 blunted (881k segs) | 8.3 s |
| k=31 blunted (890k segs) | 8.1 s |

The reference implementation is O(N²) per call; a future optimisation pass (`@[implemented_by]` single-pass) is already sketched in `Unify.lean`.

---

## 4. Follow-up work

| Item | Priority | Notes |
|---|---|---|
| `merge_nodes` (partial node merges) | Medium | Not ported; stark's `src/main.cpp:245-285` reference |
| Rust port for even-k | Low | Lean handles it; Rust parity not required for correctness |
| `unify` O(N) single-pass `@[implemented_by]` | Medium | Current fuel-bounded loop is O(N²); sketched in `Unify.lean` |
| Worst-case complexity for `unify` | Low | `bluntifySteps_le` covers bluntify; `unify` lacks a formal bound |
| Bidirected GFA `-` orientation treatment | Low | Passed through but not treated at graph level |
| Connect `BidirectedDeBruijnGraph.bluntify` to GFA I/O | Low | Lean proof exists; GFA wrapper not yet wired |
