# bluntg — handoff & next steps

This document is the entry point for anyone (subagent or human) picking
up `bluntg` from the initial commit. It describes the current state,
the four next tracks, and the conventions to follow so the tracks merge
back cleanly.

## Current state (commit `main`)

**Working end-to-end:**

- `cargo build --release` produces `target/release/gen-gfa` — k-mer DBG
  builder. Reads FASTA (plain / gzip / bgzip), emits GFA1.
- `(cd lean && lake build)` produces `lean/.lake/build/bin/bluntg` —
  Lean executable. Parses GFA1, bluntifies, writes GFA1.
- Round-trip: `gen-gfa 31 data/yeast.chrV.fa.gz | bluntg` — runs in
  ~7s on 7 yeast haplotypes, ~900k segments.

**Lean library (`lean/Bluntg/`)** has **zero `sorry`s**. Headline theorems:

| Theorem | Where |
|---|---|
| `bluntify_is_blunt` | `Bluntg/Correctness.lean` |
| `bluntSpell_eq_middle_spell` | `Bluntg/Correctness.lean` |
| `bluntSpell_eq_spell_of_boundary` | `Bluntg/Correctness.lean` |
| `middle_concat_overlap` | `Bluntg/Correctness.lean` (the list-arith key step) |
| bidirected `toDirected` doubling | `Bluntg/Bidirected.lean` |

**Edge-side accounting in `GFA.bluntify`** is bidirected: every `L` line
is mapped to one side of `from` (right if `+`, left if `-`) and one side
of `to` (left if `+`, right if `-`), and a segment's end is trimmed iff
**any** edge touches that side. For odd `k` the left and right trim
amounts coincide; for even `k` they differ and the connector-node fix
is missing — see track B.

**Conventions worth knowing:**

- The Lean root namespace is `Bluntg`. The library module is `Bluntg`,
  the executable module is `Main` (declared in `lean/lakefile.toml`).
- `Suffix s n = s.drop (s.length - n)` and `Prefix s n = s.take n` are
  in `Bluntg/Basic.lean`; `middle s l r = (s.drop l).take (s.length - l - r)`.
- `DeBruijnGraph α k` (`Bluntg/Graph.lean`) is the *directed* model;
  `BidirectedDeBruijnGraph α k` (`Bluntg/Bidirected.lean`) is the
  bidirected one. The doubling lowers bidirected to directed.
- Block comments **nest** in Lean 4 — be careful with `+/-` inside
  multi-line comments (they open a comment). Use `±` or split.
- `String.dropRight`/`takeRight` are deprecated; use
  `String.dropEnd`/`takeEnd` and convert the resulting `String.Slice`
  with `.toString`.

## Four parallel tracks

The tracks are independent except for `Bluntg.lean` (root import list)
and `README.md`. Both merge cleanly.

### Track A — Rust port (primary author, on `main`)

**Goal:** native-Rust `bluntg` binary that matches the Lean binary's
output byte-for-byte on at least the yeast test set.

**Scope:**
- New file: `src/bin/bluntg.rs` (or replace `src/main.rs` and rename the
  package binary).
- Mirror the algorithm in `lean/Bluntg/GFA.lean` exactly:
  parse GFA1 → compute `rightSideIds` / `leftSideIds` → trim → write.
- Bidirected accounting: a `L A from_o B to_o` line contributes to
  - A's *right* side iff `from_o = '+'`, else A's *left* side;
  - B's *left*  side iff `to_o   = '+'`, else B's *right* side.
- Trim amounts: `(k - 1) / 2` from the left if `leftSideIds.contains s.id`,
  `k / 2` from the right if `rightSideIds.contains s.id`.
- All link/path overlap CIGARs become `0M`.

**Definition of done:**
- `diff <(target/release/bluntg < input.gfa) <(lean/.lake/build/bin/bluntg < input.gfa)`
  is empty on the yeast pipeline and on a handful of synthetic
  bidirected inputs.
- `cargo build --release` clean (no warnings).

**Hints:**
- For large GFAs, prefer `BufWriter<Stdout>` and `Vec<u8>` over `String`
  in the hot path — yeast at k=31 is ~150 MB of output text.
- Use `BTreeMap<&str, u64>` (or `FxHashMap`) for ID interning if you
  want to be fast; the current Lean side uses Lean's `HashMap` so the
  Rust side has no reason to be slower.
- Reuse `flate2::MultiGzDecoder` if input may be gzipped/bgzipped.

### Track B — Even-`k` connector nodes (worktree `even-k`)

**Goal:** handle the asymmetric trim case correctly.

**Scope:**
- For even `k`, `(k-1)/2 ≠ k/2`. In a bidirected graph the same node
  can be entered through either side, so the per-side trim becomes
  ill-defined. Stark inserts a 1-character "connector" node between
  every bidirected edge and runs odd-`k` bluntify afterwards.
- New module: `lean/Bluntg/EvenK.lean`.
  - Define `addConnectors : Gfa → Gfa` (operating on the loose GFA
    record types in `Bluntg/GFA.lean`) that, for each `L` line at
    even `k`, inserts a fresh segment containing the middle character
    of the original `(k-1)`-overlap.
  - Prove (at the `BidirectedDeBruijnGraph` level) a path bijection:
    walks in `G` correspond one-to-one with walks in `addConnectors G`
    that spell the same string.
- Thread through `GFA.bluntify`: if `k % 2 = 0`, run `addConnectors`
  first.

**Definition of done:**
- Module compiles with no `sorry`.
- New executable test: even-`k` round-trip preserves every P line's
  spelling.

**Hints:**
- Stark's even-`k` handling is in `bluntify()` after the `if (k % 2 == 0)`
  branch in `/home/erik/stark/src/main.cpp:186-242`. Re-read it
  carefully — the connector node carries a single character that's the
  "middle" of the overlap, and edges from the original two endpoints
  both point to it.
- The path bijection is the right correctness lemma — once you have it
  spelling preservation is `spellTail.cons` plus the directed
  `bluntSpell_eq_middle_spell`.

### Track C — Linear-time complexity bound (worktree `complexity`)

**Goal:** formal proof that `bluntify` (the algorithm itself, not just
the function) runs in `O(|V| + |E|)`.

**Scope:**
- New module: `lean/Bluntg/Complexity.lean`.
- Define an explicit step-count function `bluntifySteps : Gfa → ℕ`
  matching a deterministic execution model (one fold over links to
  compute side sets, one map over segments to apply the trim). The
  natural choice is `bluntifySteps g = g.links.size + g.segments.size`.
- State and prove `bluntifySteps g ≤ C * (|V| + |E|)` for some explicit
  constant `C`.
- Optionally also define a `bluntifySteps` for the `DeBruijnGraph`
  version and prove the same.

**Definition of done:**
- Theorem stated and proved with no `sorry`.
- The chosen step-count function corresponds 1:1 with a loop bound in
  the Lean implementation — i.e., the proof bounds *real* work, not a
  trivial constant.

**Hints:**
- `Array.foldl` and `Array.map` each touch each element once, so the
  step counts collapse to `|links| + |segments|` directly.
- The `HashSet.contains` lookups inside the segment loop are O(1) on
  average — but if you want a worst-case bound, switch to a sorted
  `Array` of ids and binary search, or use `Std.HashMap.find?` and
  document the average-case caveat.

### Track D — `unify` / `merge_nodes` (worktree `unify`)

**Goal:** port stark's unitig-compaction passes.

**Scope:**
- `unify` collapses simple chains of nodes (`u → v` with `u` having one
  out-edge to `v` and `v` having one in-edge from `u`) into a single
  segment with the concatenated sequence.
- `merge_nodes` does partial merges when two nodes share a prefix or
  suffix — see `partial_left_merge_to` / `partial_right_merge_to` in
  `/home/erik/stark/src/node.cpp`.
- New module: `lean/Bluntg/Unify.lean`.
- Define `unify : Gfa → Gfa` and prove path-spelling is preserved.
- `merge_nodes` is more involved and can be a follow-up — the unify
  pass alone gives most of stark's output compaction.

**Definition of done:**
- `unify` defined, path-preservation theorem proved with no `sorry`.
- An end-to-end test confirms that `bluntg | unify` on the yeast input
  produces fewer segments than `bluntg` alone, and every P line's
  spelling is unchanged.

**Hints:**
- Reference: `unify` in `/home/erik/stark/src/main.cpp:245-285`.
- The "no other in/out edges" predicate is straightforward: iterate
  the link set once to compute per-segment in/out degree, then in a
  second pass identify mergeable pairs.

## Workflow for parallel tracks

For each Lean track (B/C/D), create a worktree:

```bash
git worktree add ../bluntg-even-k     -b even-k
git worktree add ../bluntg-complexity -b complexity
git worktree add ../bluntg-unify      -b unify
```

Inside each worktree, build is independent:

```bash
cd ../bluntg-even-k
(cd lean && lake build)
```

When a track is done, open a PR against `main`. The only "shared" file
each track touches is `lean/Bluntg.lean` (the import list) — adding
one new `import Bluntg.<Module>` line. Merges are trivial.

For the Rust track, work directly on `main` (or a short-lived branch).
The Rust port doesn't touch the Lean modules at all, so it composes
freely with the Lean tracks.

## Things to test before pushing any branch

1. `(cd lean && lake build)` — zero errors, zero new `sorry`s.
   (Unused-variable lint warnings are OK; they exist in `main` already.)
2. `cargo build --release` — clean.
3. Yeast round-trip still works:
   ```bash
   ./target/release/gen-gfa 15 data/yeast.chrV.fa.gz \
     | ./lean/.lake/build/bin/bluntg \
     | head -5
   ```

## Pointers to reference material

- Stark source: `~/stark/src/main.cpp`, `~/stark/src/node.cpp`,
  `~/stark/src/node.h`. The `bluntify()`, `unify()`, and
  `merge_nodes()` functions are the load-bearing ones.
- Yeast chrV test data: `data/yeast.chrV.fa.gz` (7 haplotypes, ~4 MB
  uncompressed). Originally copied from
  `~/impg/tests/test_data/yeast.chrV.fa.gz`.
- The GFA1 spec, especially section "Optional fields" for the `L` and
  `P` line semantics:
  <https://github.com/GFA-spec/GFA-spec/blob/master/GFA1.md>.
