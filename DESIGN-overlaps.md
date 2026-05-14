# DESIGN-overlaps.md — generalising bluntg to variable-length per-edge overlaps

**Status:** research / design only — no implementation in this PR.
**Date:** 2026-05-14
**Branch:** `wg/agent-31/overlaps-research`

---

## 0. Motivation in one paragraph

`bluntg` (Lean and Rust ports) currently assumes every L line in the input
GFA carries the **same** overlap length, equal to `k-1` for a single
graph-wide `k`. The whole pipeline is parametrised by that one `k`:
`k` is inferred from the first link (`lean/Bluntg/GFA.lean:218-221`,
`src/main.rs:152-154`), the trim amounts are global (`(k-1)/2` left,
`k/2` right — `lean/Bluntg/GFA.lean:200-212`, `src/main.rs:156-183`,
mirroring stark's `bluntify()` at `~/stark/src/main.cpp:169-243`), and
the connector-node fix-up for even `k` uses the same global value
(`lean/Bluntg/EvenK.lean:131-141, 215-224`).

Real graphs from **syng** and from **impg's syng-native pipeline** carry
*per-edge* overlap lengths because syncmer paths advance by an offset
that varies along the path. The CIGAR `<N>M` on each L line is a per-edge
quantity, not a single global constant. We need a generalisation that
keeps the existing odd-`k`/even-`k` correctness story while accepting
heterogeneous overlaps.

---

## 1. Background — current overlap conventions in the wild

### 1.1 What bluntg currently expects

Today bluntg's parser (`lean/Bluntg/GFA.lean:75-82`) accepts any `<N>M`
CIGAR (or `*`, treated as 0) but the bluntify pass throws the value
away — it only consults `k = 1 + g.links[0].overlap`. The proof side
matches the implementation: `DeBruijnGraph` carries a *single* `k`
(`lean/Bluntg/Graph.lean:22-28`) and the overlap invariant
`Suffix (seq u) (k-1) = Prefix (seq v) (k-1)`
(`Bluntg/Graph.lean:27-28`) is uniform across edges. `BidirectedDeBruijnGraph`
is the same — one `k`, one universal `(k-1)`-overlap (`Bluntg/Bidirected.lean:64-89`).

### 1.2 What seqwish-derived GFAs emit (impg today)

Both impg paths that emit GFA today produce *fully blunt* graphs
(`0M` on every L line) because they go through `seqwish::gfa::emit_gfa`
(seqwish vendored at
`~/.cargo/git/checkouts/seqwish-be7416204a0fe48d/15aee55/src/gfa.rs:89`).
Concrete sites in impg:

* `~/impg/src/commands/lace.rs:1075, 1324, 1331, 2098, 2365–2624` — all
  emit `L … 0M`, both in the production lacing code and in the unit-test
  fixtures.
* `~/impg/src/commands/graph.rs:329-367` — calls `seqwish::gfa::emit_gfa`,
  which writes `0M` (seqwish does the bluntification at the C++ layer
  before emit).
* `~/impg/o.gfa` (sample output from the repo, 36 307 L lines) — every
  line is `L … 0M`.

So the *current* impg GFA output is no harder than a stark-style blunted
graph: `k=1` and bluntg is a no-op.

### 1.3 What syng natively encodes (the future case)

syng's GBWT does not currently emit GFA1 directly (only ONElib `gbwt`
files). But the on-disk schema in `~/syng/syng.h:62-89` makes the
overlap structure explicit:

```
"O V 1 3 INT               graph node (vertex): length\n"
"D E 3 3 INT 3 INT 3 INT   edge +: adjacent node (- if reversed), offset, count\n"
"D e 3 3 INT 3 INT 3 INT   edge -: adjacent node (- if reversed), offset, count\n"
"D Z 4 3 INT 3 INT 3 INT 3 INT   GBWT path: starting node, pos, count, then length in nodes\n"
"D o 1 8 INT_LIST          if z, then offsets of the nodes from start of sequence, 1:1 with z\n"
```

Two key facts:

* Each **edge** stores an `offset` (the displacement of the next node
  from the start of this node along the path). The overlap on that edge
  is `parent_node_length - offset`.
* Nodes can have **non-uniform length** — `SyngBWT.fixedLen == 0` mode
  stores per-node lengths in `Array length` (`~/syng/syng.h:28-37`).
  The default fixed-length mode gives every syncmer length `w + k`
  (default 63 bp from `~/impg/notes/SYNG_INTEGRATION.md:47-49,396-405`),
  but variable-length nodes are a first-class concept.

In syng's GBWT, when path P traverses `(node A, offset_A) → (node B, …)`,
the edge `A → B` carries an offset along P, and the *overlap on that L
line* is `len(A) − offset_AB`. Different paths through the same node A
can take different next nodes with different offsets, so the *same node*
can have several outgoing edges with **different per-edge overlaps**.
This is what variable-overlap GFA emission from syng will look like.

### 1.4 Per-segment-side asymmetry

There is a second, subtler asymmetry to plan for. In syng's data model
the offset attaches to the *edge*, not to the segment side. So node A's
right side may participate in edges `A → B` (overlap 30), `A → C`
(overlap 25), `A → D` (overlap 17) all at once. The trim amount we
apply at A's right side has to be a single value (you cannot trim a
suffix to two different lengths simultaneously) yet must respect every
edge's overlap budget. This is the central design choice of §2 below.

### 1.5 stark and the original bluntifier reference

stark's `bluntify()` at `~/stark/src/main.cpp:169-243` is the algorithm
bluntg-Lean and bluntg-Rust both mirror. It also inherits the
single-`k` assumption (`~/stark/src/main.cpp:88-91` reads `match` from
the first L line and asserts every later L line has the same value:
`if (k != match + 1) logger->error("Error! different k's: %d - %d", k, match + 1);`).
**This is the exact assertion we are removing.**

---

## 2. Data model change

### 2.1 The shape of the change

The current `Bluntg.GFA.Link` already carries a per-link `overlap : Nat`
(`lean/Bluntg/GFA.lean:34-40`); the parse side already populates it
correctly per link. **No GFA-record change is needed.** What changes is
the *consumer* side — `bluntify` and the side-edged sets.

Currently bluntify computes two `HashSet String`s
(`lean/Bluntg/GFA.lean:171-183`):

```lean
def rightSideIds (g : Gfa) : HashSet String := …  -- “does any L touch A's right end?”
def leftSideIds  (g : Gfa) : HashSet String := …  -- “does any L touch A's left  end?”
```

These reduce a per-edge fact to a per-side bit (any incident edge ⇒
trim by the global amount). We replace each with a per-side **map**:

```lean
def rightOverlap (g : Gfa) : HashMap String Nat   -- right-side trim amount per segment
def leftOverlap  (g : Gfa) : HashMap String Nat   -- left-side  trim amount per segment
```

The contains-key relation replaces the existing `contains` test (a
segment's right side is *edged* iff its right-overlap entry is present);
the value is the trim amount used at that side.

The Rust port mirrors the same change: replace the two `HashSet<String>`s
in `src/main.rs:124-141` with two `HashMap<String, usize>`s and read the
amount from the map in `bluntify()` (`src/main.rs:156-183`).

### 2.2 Aggregation: max-over-incident-edges, with a side-condition

The fundamental question is: *if two edges incident at A's right end
have different overlaps `o₁ ≠ o₂`, what do we trim?*

We adopt **max-over-incident-edges** for the right-trim half and
**max-over-incident-edges** for the left-trim half, each subject to
preserving the existing `(k-1)/2 / k/2` asymmetry **per edge**:

* For each incident edge `e` with overlap `oᵉ`, define
  `leftAmtᵉ = (oᵉ) / 2`  and  `rightAmtᵉ = (oᵉ + 1) / 2`
  (the same `(o-1)/2`/`o/2` formula generalised: the smaller half
  goes to the left side and the larger half to the right side; `oᵉ-1`
  becomes `oᵉ` for the divided amounts because we are now talking about
  the per-edge overlap *length*, not `k-1` for a uniform-`k` graph).
  See §3 for the arithmetic that justifies this.
* Aggregate by `max` per side:
  `leftOverlap[A] = max { leftAmtᵉ | e left-incident to A }`,
  `rightOverlap[A] = max { rightAmtᵉ | e right-incident to A }`.

**Why max, not sum.** Trim is a single suffix-/prefix-deletion on the
node sequence; you cannot delete two suffixes of different lengths.
You must delete enough to satisfy *every* edge's overlap budget, which
means deleting `max`. Trimming more than the max of any single edge's
half would erase characters that belong to the shared region of *some*
edge but not another — i.e. you would delete distinct content, not
shared content, breaking spelling preservation.

**Why not sum.** Sum trims for overlaps from *different* edges that
share the same side — but that is wrong: each individual edge's overlap
is the entire shared region between *two specific* node sequences. There
is no compositional sense in which "two edges of length 17 and 25 share
17+25 characters at A's right." The overlap of edge `A → B` is just
`min(suffix-of-A, prefix-of-B)`.

**Edge case the max rule produces.** If A has two right-incident edges
with overlaps 30 and 17, `rightOverlap[A] = max(15, 9) = 15`. Edge
`A → B@30M` is *over-trimmed* on A's side relative to its own
budget — which corresponds at the GFA level to the bluntified L-line
having a **non-zero leftover overlap on the B side**: B contributes
`30 − 15 = 15` characters of its prefix that A no longer has. That is
fine: bluntg's job is to set the L-line CIGAR to `0M`, but to do so
honestly we must also trim B's left side by *at least 15*. The
aggregation on B's side picks that up by the same `max` rule, because
its `leftAmtᵉ` for edge `A → B@30M` is `30/2 = 15`.

This is the central invariant. *Every individual edge's per-side trim
budgets get aggregated by max. The maxes are consistent precisely when
both endpoints of each edge see the same per-edge contribution.* We
prove this preserves spelling (§4); the key fact is `leftAmtᵉ +
rightAmtᵉ = oᵉ` exactly, so the per-edge total trim across the junction
still equals the per-edge overlap.

### 2.3 What about same-side bidirected edges (the `+ -` and `- +` cases)?

Same-side bidirected edges `L A + B -` and `L A - B +` already need the
even-`k` connector-node trick under the *uniform* model
(`lean/Bluntg/EvenK.lean:62-77`). With variable overlap they need the
trick whenever the per-edge overlap `oᵉ` is **even** (then the asymmetric
`oᵉ/2` left + `oᵉ/2` right miss the middle character on `+ -`, or
double-count it on `- +`). For odd `oᵉ` the directed asymmetric trim
sums to exactly `oᵉ`, and no connector is needed.

Concretely the dispatch is no longer "if `k % 2 == 0`" but
"per same-side L line, if `oᵉ % 2 == 0`":

```
for each L line:
  if isPlusMinusSameSide L and L.overlap % 2 == 0:
     install connector for L using middleCharRightOverlap A L.overlap
  else if isMinusPlusSameSide L:    -- still unhandled (cf. §4.4)
     warn / fail
```

The connector character is sourced from
`middleCharRightOverlap aSeq L.overlap` (i.e. the position formula in
`lean/Bluntg/EvenK.lean:51-60` parameterised on the per-edge overlap
instead of the global `k`). Connector segments and link splits
(`Bluntg/EvenK.lean:116-158`) carry over verbatim.

---

## 3. Generalising the asymmetric `(N-1)/2` / `N/2` trim per edge

### 3.1 The arithmetic, restated

For a single edge with overlap `o`, the directed bluntify must split
`o` characters between A's right side and B's left side. The current
`Bluntg.DeBruijnGraph.bluntify` uses
`leftTrim = (k-1)/2`, `rightTrim = k/2`, and proves
`leftTrim + rightTrim ≤ k - 1` (`lean/Bluntg/Bluntify.lean:47-54`).
With `o` standing in for the per-edge overlap, the analogous formulas
are:

* `leftAmt(o)  = o / 2`           — small half, goes to the *target's left side*
* `rightAmt(o) = (o + 1) / 2`      — large half, goes to the *source's right side*

Sum: `leftAmt(o) + rightAmt(o) = o`. (Note: in the uniform-`k` setting
with `o = k - 1`, this collapses to `(k-1)/2 + k/2 = k - 1`. ✓)

The *asymmetry* — that the right side gets the larger half — is what
makes the directed bluntify work for any `o` (odd or even). The
even-`k` connector trick is needed only on bidirected same-side edges
where both endpoints land on the *same* end; for opposite-side edges
the asymmetry sums correctly across the junction (see §3.2).

### 3.2 Per-side aggregation across the graph

After computing `leftAmt(oᵉ)` / `rightAmt(oᵉ)` per edge, aggregate per
segment side by `max`:

```
rightOverlap[A] = max { rightAmt(oᵉ) | e right-incident to A } ∪ {0}
leftOverlap [A] = max { leftAmt (oᵉ) | e left-incident  to A } ∪ {0}
```

Each segment is then trimmed by its `leftOverlap` chars on the left
and `rightOverlap` chars on the right (skipping if the side has no
incident edge — i.e. the entry is missing from the map).

### 3.3 Does the connector-node trick from Track B subsume the variable-overlap case?

**Partially — but only for the bidirected same-side edges, not the
mainline opposite-side ones.** The connector trick (Track B,
`lean/Bluntg/EvenK.lean`) addresses the geometric problem that on a
bidirected same-side edge `+ -` with even overlap the asymmetric trim
loses the middle character. Track B inserts a length-1 connector
segment carrying that middle character.

Under variable overlap, every same-side `+ -` edge whose `oᵉ` is even
needs its own connector — the connector character is still the *middle*
of *that edge's* overlap, sourced via
`middleCharRightOverlap aSeq oᵉ`. The connector mechanism is exactly
the same; only the global-`k` parametrisation goes away.

So Track B subsumes variable-overlap *for bidirected same-side edges*.
It does **not** generalise the per-side trim aggregation: nothing in
Track B replaces the `leftOverlap` / `rightOverlap` `HashMap` design of
§2 — it sits *on top* of that aggregation, replacing the
`if k % 2 == 0` test with `if oᵉ % 2 == 0` per L line.

### 3.4 Interaction with Track D (`unify` pass)

Track D's `unify` (`lean/Bluntg/Unify.lean`) operates on the *output of
bluntg* — i.e. on graphs with all L overlaps at `0M`. Its merge rule
fires on safe `+/+` chains where adjacent segments have the same
single-incident-edge structure. The pass is **agnostic to the original
overlap**: it only inspects the post-bluntg structure. So `unify`
needs no changes for variable overlap; it continues to reduce 36×
(SYNTHESIS.md §3) on the post-bluntg graph regardless of whether the
input graph had uniform or variable overlaps.

There is one *positive* interaction: variable-overlap graphs can leave
behind L lines whose per-edge `max` aggregation already exceeds the
edge's own budget. After bluntg, those edges are still `0M` and the
unify pass collapses any `+/+` chains as before — the over-trimming
on one side is simply not visible in the unitig structure.

---

## 4. Lean theorems: which restate, which still hold

### 4.1 `Bluntify`-level theorems (`lean/Bluntg/Bluntify.lean`)

* `leftTrim_le`, `rightTrim_le` (l.37-45) — restate as
  `leftTrim G v ≤ rightOverlapBound G v` where the bound is the
  max of `leftAmt(oᵉ)` over edges incident at v's left side.
  Proof structure (single `if`-split + `omega`) is unchanged.
* `trim_sum_le` (l.49-54) — **restate**, but the new statement is
  *per edge*, not per node:
  for any edge `e : u → v` with overlap `oᵉ`,
  `rightTrim G u + leftTrim G v ≥ oᵉ` (we trim *at least* `oᵉ` across
  the junction). The original theorem says `leftTrim + rightTrim ≤ k-1`
  *per node*, which is the wrong shape for variable overlap; the new
  shape is *per edge across the junction*. The new proof: each side's
  `max` aggregation includes the `(o-1)/2` / `o/2` halves of *this
  edge's* overlap, so the sum is at least `oᵉ`.
* `bluntSeq_length_pos` (l.60-71) — **likely still holds** but proof
  needs adjustment. The bound `leftTrim + rightTrim ≤ k - 1` was used to
  show the trimmed sequence is non-empty under `seq_len v ≥ k`. With
  variable overlap, the bound becomes `leftOverlap + rightOverlap ≤
  seq_len v - 1` (we never trim everything). Proof: each per-edge
  bound `leftAmtᵉ + rightAmtᵉ = oᵉ ≤ seq_len v - 1` (because edges
  exist only if `oᵉ` characters of v match the partner — and node
  sequences are at least `oᵉ + 1` long for any incident edge). This
  argument requires a new structural invariant on the graph: every
  segment is at least `1 + max_edge_o` long.
* `bluntify` (l.73-94) — definition body is per-edge under the new
  scheme; the *type* still holds (we still produce a graph with
  `k = 1`, i.e. zero overlap, in the codomain). All `@[simp]`
  helpers about `numNodes`, `hasEdge`, `seq` carry over.

### 4.2 `Correctness`-level theorems (`lean/Bluntg/Correctness.lean`)

* `bluntify_is_blunt` (l.32-37) — **unchanged**. It just witnesses
  zero overlap in the output graph regardless of source overlap shape.
* `spell_cons_cons`, `spell_length_ge`, `overlap_walk` (l.43-69) —
  these mention `(k-1)` directly. **Restate**: replace `k-1` with the
  per-edge overlap `oᵉ` from the just-traversed edge. Proof structure
  carries (each is one `omega` after the rewrite); the type system
  forces us to thread `oᵉ` through `spell` / `spellTail` so they take
  a *list of overlaps* alongside the list of nodes.
* `bluntSpell_eq_middle_spell` — **needs restating**. The current
  statement says
  `bluntSpell vs = middle (spell vs) (leftTrim head) (rightTrim last)`.
  In the variable-overlap setting, `spell` itself loses overlap-many
  characters at each junction — but those overlaps are now per-edge.
  The new statement is the same shape but `spell` is the
  `o`-aware variant. The proof relies on the `middle_concat_overlap`
  identity in `Bluntg/Basic.lean`, which is **list-arithmetic only**
  and works for any `wL`, `wR` — so the lemma is reused as-is.
* `bluntSpell_eq_spell_of_boundary` — **unchanged once `spell` is
  parameterised over per-edge overlaps**.
* `middle_concat_overlap` (`Bluntg/Basic.lean`) — **unchanged**.
  Pure list arithmetic, no `k`.

### 4.3 Bidirected-level theorems (`lean/Bluntg/Bidirected.lean`)

The `BidirectedDeBruijnGraph` structure currently bundles a single `k`
into the type. Two options:

* **(a)** Keep the structure as-is and have the *consumer* (`bluntify`)
  take a per-edge `overlap : … → Nat` function alongside `hasEdge`.
  The structure-level `overlap` invariant
  (`Bluntg/Bidirected.lean:80-89`) becomes
  `Suffix (readSeq u su) (overlap u su v sv) =
   Prefix (readSeq v sv.flip) (overlap u su v sv)`.
* **(b)** Drop `k` from the type entirely and store per-edge overlaps
  on the structure. This is more invasive but cleaner.

**Recommendation: (a).** It minimises proof churn and keeps the
existing `doubledNumNodes` / `encode` machinery (`Bluntg/Bidirected.lean:113-…`)
untouched. The `seq_len` invariant becomes
`∀ v, max_incident_overlap v + 1 ≤ (seq v).length`.

### 4.4 Even-`k` / connector theorems (`lean/Bluntg/EvenK.lean`)

* `augmentedSpell_length` (l.342-393) — **unchanged**. It's a length
  identity over arbitrary `mid : ConnectorSpec G` and arbitrary `k`;
  the proof is structural induction with `omega`, no `k`-specific
  arithmetic beyond `k - 1 ≤ readSeq.length` which carries over to
  `oᵉ - 1 ≤ readSeq.length` (the new per-edge invariant).
* `addConnectors` (l.215-224) — **restate**: dispatch
  per-L-line on `oᵉ % 2 == 0` instead of globally on `k % 2 == 0`. The
  loop body is unchanged.
* `isPlusMinusSameSide` and the `- +` limitation (l.78-79) — still
  applies. The known limitation that `- +` same-side bidirected edges
  produce off-by-one spelling carries verbatim into the variable case;
  it is *no worse* than today, and addressing it remains future work
  (it would require stark's full node-split mechanism, currently
  unported per SYNTHESIS.md §4).

### 4.5 Unify theorems (`lean/Bluntg/Unify.lean`)

* `rewriteAligned_spell_preserved`, `Path.unifyRewrite_spell` — **unchanged**.
  Unify operates on bluntified graphs (all 0M overlaps) and the
  arithmetic is entirely about contiguous strings, not overlaps.

### 4.6 Complexity bound (`lean/Bluntg/Complexity.lean`)

* `bluntifySteps_le` — **unchanged statement**, possibly
  unchanged proof. The bound `g.segments.length + g.links.length`
  still holds; max-aggregation is one pass over `g.links`, so the
  step count is the same.

---

## 5. Rust port mirror

The Rust port (`src/main.rs`) is a literal translation of
`lean/Bluntg/GFA.lean`. The variable-overlap port is also literal:

* `right_side_ids` / `left_side_ids` (lines 124-141) → **rename and
  retype**: `right_overlap` / `left_overlap`, returning
  `HashMap<String, usize>` instead of `HashSet<String>`. Build by
  iterating links, computing per-edge `(o+1)/2` / `o/2`, and inserting
  with `entry().and_modify(max).or_insert(amt)`.
* `bluntify` (lines 156-183) — replace the lookups
  `if lefts.contains(&s.id) { left_amt } else { 0 }`
  with
  `*lefts.get(&s.id).unwrap_or(&0)` etc., reading the per-side amount
  from the map.
* `infer_k` (lines 152-154) — **delete**. With per-edge overlaps there
  is no global `k`. The CLI's `k` argument also goes away
  (`fn main`, line 235); the `k < 2` guard at line 261-264 is replaced
  by a per-link `o ≥ 1` validation during parse.
* `parse_overlap_cigar` (lines 55-61) — **unchanged**.
* The trim helper `trim_seq` (lines 144-150) — **unchanged**.
* Even-`k` / bidirected support: the Rust port currently does **not**
  implement the connector-node fix-up (Lean handles even-`k` via
  `EvenK.lean` only). The variable-overlap port should preserve this
  status quo — Rust handles only opposite-side edges, with same-side
  even-overlap edges producing a warning and an off-by-one spelling
  (matching the limitation in `EvenK.lean:62-77`).

The Rust output writer (`write_gfa`, lines 189-231) is **unchanged**:
it already writes per-link `<N>M` (line 204 `write!(out, "\t{}M", l.overlap)?;`)
and the post-bluntg `overlap` field is always 0, just as before.

### 5.1 Backward-compatibility for uniform-`k` inputs

A uniform-`k` GFA has every L line at `<k-1>M`. Under the new
aggregation, every right side is trimmed by `max((k-1+1)/2) = k/2` and
every left side by `max((k-1)/2)` — **byte-identical** to the current
uniform-`k` bluntg output. So no regression for stark/de-Bruijn-style
inputs; the Lean=Rust byte-identity result for k=15, 31 (SYNTHESIS.md §3)
should continue to hold.

---

## 6. Test plan

### 6.1 Existing tests that must still pass

* **k=15, 31 yeast chrV bluntify** — Lean=Rust byte-identical from
  SYNTHESIS.md §3. The data lives at `data/yeast.chrV.fa.gz` (in this
  repo) and at `~/impg/tests/test_data/yeast.chrV.fa.gz`. Run the
  existing CLIs after the port; output should be **byte-identical** to
  the pre-change baseline because uniform-`k` collapses to the new
  aggregation trivially (§5.1).
* **k=30 even-k 7/7 P-spelling preservation** — synthesize-tracks
  evaluator's pass criterion. Same uniform-`k` input, must remain
  preserved with the per-edge dispatch in §3.3.
* **`unify` 881k → 24k** — variable-overlap is invisible to unify (§3.4),
  so this benchmark is unaffected.

### 6.2 New integration tests (variable-overlap)

The natural test inputs are graphs that *will* be emitted by syng /
impg-syng-native once those paths gain a non-`0M` GFA emitter. As of
2026-05-14 such an emitter does not yet exist, so the test plan has
two phases.

**Phase A — synthetic variable-overlap fixtures (immediately).**

Construct hand-built GFAs in `tests/variable_overlap/` exercising:

* (T1) Two L lines incident at the same right side with overlaps
  `15M` and `9M`. Expected: that right side trims by `(15+1)/2 = 8`,
  not `8` and `5` independently. The downstream segments must be
  trimmed to compensate so the bluntified spelling matches the
  original.
* (T2) A `+ -` same-side bidirected edge with overlap `8M` (even) —
  expects a connector inserted carrying the middle char of the
  8-overlap; sibling edge with overlap `7M` (odd) on the same side
  must *not* trigger a connector.
* (T3) Mixed-overlap path `[L A+B+ 17M, L B+C+ 9M, L C+D+ 13M]` with
  a P line `A+,B+,C+,D+` and CIGAR `17M,9M,13M`. Expected: post-blunt
  spelling equals `seq(A) ++ drop(17, seq(B)) ++ drop(9, seq(C)) ++
  drop(13, seq(D))`.
* (T4) Regression for stark uniform-`k` (k=15, 31) inputs: confirm
  byte-identity vs the current bluntg output.

These can be generated by a small Python helper following the pattern
of `tests/even_k_roundtrip.py`.

**Phase B — real syng/impg outputs (when available).**

Two concrete pipelines that should produce variable-overlap GFAs and
become integration test sources:

* (R1) **`impg syng + impg query --syng -o gfa` over yeast chrV** —
  see `~/impg/notes/SYNG_INTEGRATION.md:355-394`. Run on
  `~/impg/tests/test_data/yeast.chrV.fa.gz` once the GFA emitter for
  syng-native graphs supports per-edge overlap. The current
  `impg graph` output (`~/impg/o.gfa`) is fully blunt and not useful
  as a variable-overlap fixture.
* (R2) **syng's `-writeGBWT` round-tripped through a future
  `gbwt2gfa` tool** on the yeast cichlid sample
  (`~/syng/README.md` example) or the `~/syng/TEST/test.fa` file.
  Will produce a graph whose L lines carry per-syncmer-pair overlaps
  derived from the edge offsets in the schema entry
  `~/syng/syng.h:76-77`.

The output of R1/R2 should pass the test asserting "for every original
input sequence, its P-line spelling under bluntg equals the original
sequence" (the universal bluntg correctness criterion).

### 6.3 Lean proof tests

Add a Lean test (in `lean/`) for each restated theorem in §4 — at
minimum a witness construction: a small concrete `DeBruijnGraph` /
`Gfa` value with two edges of different overlap, paired with the
expected `bluntSpell`. These act as compile-time sanity checks on the
restated definitions.

### 6.4 Smoke test for the manifest

After the implementation phases land, add a scenario at
`tests/smoke/scenarios/bluntg_variable_overlap.sh` that runs (T3)
end-to-end (parse → bluntify → reparse → compare spellings). List
`bluntg-variable-overlap` (or whatever the implementing task is named)
in `owners` of `tests/smoke/manifest.toml` so future regressions block
the smoke gate.

---

## 7. Sketch — file-by-file changes

These are change *signatures*, not implementations. Each is the
smallest delta consistent with §2-§6. **No code is changed in this PR.**

### 7.1 `lean/Bluntg/GFA.lean`

```lean
-- Replace rightSideIds / leftSideIds (lines 173-183):

/-- Per-segment **right-side trim amount**: the largest `(o+1)/2` over
    all L lines incident at that segment's right end. Absent ⇒ no
    edge ⇒ no trim. -/
def rightOverlap (g : Gfa) : HashMap String Nat :=
  g.links.foldl (fun acc l =>
    let amt := (l.overlap + 1) / 2
    let acc := if l.fromPlus then mapMaxInsert acc l.fromId amt else acc
    if !l.toPlus            then mapMaxInsert acc l.toId   amt else acc) ∅

def leftOverlap (g : Gfa) : HashMap String Nat :=
  g.links.foldl (fun acc l =>
    let amt := l.overlap / 2
    let acc := if !l.fromPlus then mapMaxInsert acc l.fromId amt else acc
    if l.toPlus              then mapMaxInsert acc l.toId   amt else acc) ∅

-- Replace bluntify (lines 200-212):

def bluntify (g : Gfa) : Gfa :=    -- no `k` parameter any more
  let rights := rightOverlap g
  let lefts  := leftOverlap  g
  let newSegments := g.segments.map fun s =>
    let l := lefts.findD  s.id 0
    let r := rights.findD s.id 0
    { s with seq := trimSeq s.seq l r }
  let newLinks := g.links.map fun l => { l with overlap := 0 }
  let newPaths := g.paths.map fun p =>
    { p with overlaps := p.overlaps.map (fun _ => 0) }
  { segments := newSegments, links := newLinks, paths := newPaths }

-- Delete inferK (lines 218-221) — no global k.
```

`bluntifyDirected` becomes a no-op alias, kept only for `EvenK.lean`'s
`bluntifyGfa` dispatch (which itself simplifies — see below).

### 7.2 `lean/Bluntg/EvenK.lean`

```lean
-- Per-L-line dispatch instead of global k % 2 == 0 (lines 215-224):

def addConnectors (g : Gfa) : Gfa :=
  -- For every same-side `+ -` link with even per-edge overlap, install
  -- a connector node carrying the middle character of that overlap.
  let trimmedOriginals := trimOriginalSegments g           -- see below
  let connectors       := buildConnectorSegments g          -- per-L-line oᵉ
  let newSegments      := trimmedOriginals ++ connectors
  let newLinks         := rewriteLinks g                    -- per-L-line oᵉ
  let linkIdx          := buildLinkIndex g
  let newPaths         := g.paths.map (rewritePath linkIdx g.links)
  { segments := newSegments, links := newLinks, paths := newPaths }

-- buildConnectorSegments (lines 116-127):
--   * change `middleCharRightOverlap aSeq k` to use `l.overlap` for `k`
--   * gate insertion on `isPlusMinusSameSide l && l.overlap % 2 == 0`
-- trimOriginalSegments (lines 132-141):
--   * source `leftAmt` / `rightAmt` from leftOverlap/rightOverlap maps
-- rewriteLinks (lines 146-158):
--   * gate the connector-rewrite arm on the same per-L-line predicate

-- bluntifyGfa (lines 232-234):

def bluntifyGfa (g : Gfa) : Gfa :=
  EvenK.addConnectors g    -- always — the per-L-line dispatch is inside
```

### 7.3 `lean/Bluntg/Bidirected.lean` and `lean/Bluntg/Bluntify.lean`

Per §4.3 (option a), thread an `overlap` function alongside `hasEdge`
in `BidirectedDeBruijnGraph` and `DeBruijnGraph`. Change the structure
field
```
overlap : ∀ u v, hasEdge u v = true →
           Suffix (seq u) (k - 1) = Prefix (seq v) (k - 1)
```
to
```
edgeOverlap : ∀ u v, hasEdge u v = true → Nat
overlap     : ∀ u v (h : hasEdge u v = true) →
               Suffix (seq u) (edgeOverlap u v h) =
                 Prefix (seq v) (edgeOverlap u v h)
seq_len     : ∀ v, 1 + maxIncidentOverlap v ≤ (seq v).length
```

Restate `leftTrim`, `rightTrim`, `trim_sum_le` (now per-edge), and
`bluntSeq_length_pos` per §4.1.

### 7.4 `src/bin/bluntg.rs` (today `src/main.rs`)

```rust
// Replace right_side_ids / left_side_ids (lines 124-141):

fn right_overlap(gfa: &Gfa) -> HashMap<String, usize> {
    let mut m: HashMap<String, usize> = HashMap::new();
    for l in &gfa.links {
        let amt = (l.overlap + 1) / 2;
        if l.from_plus { m.entry(l.from_id.clone()).and_modify(|v| *v = (*v).max(amt)).or_insert(amt); }
        if !l.to_plus  { m.entry(l.to_id.clone())  .and_modify(|v| *v = (*v).max(amt)).or_insert(amt); }
    }
    m
}
fn left_overlap(gfa: &Gfa) -> HashMap<String, usize> { /* mirror with l.overlap / 2 */ }

// Replace bluntify body (lines 156-183):

fn bluntify(gfa: Gfa) -> Gfa {     // no k parameter
    let rights = right_overlap(&gfa);
    let lefts  = left_overlap(&gfa);
    let segments = gfa.segments.into_iter().map(|s| {
        let l = *lefts .get(&s.id).unwrap_or(&0);
        let r = *rights.get(&s.id).unwrap_or(&0);
        Segment { id: s.id, seq: trim_seq(&s.seq, l, r) }
    }).collect();
    let links = gfa.links.into_iter().map(|l| Link { overlap: 0, ..l }).collect();
    let paths = gfa.paths.into_iter().map(|p| GfaPath {
        overlaps: p.overlaps.iter().map(|_| 0).collect(), ..p
    }).collect();
    Gfa { segments, links, paths }
}

// Delete infer_k (lines 152-154); change main (line 235):
//   * remove the k argument and the `k < 2` guard
//   * call bluntify(gfa) instead of bluntify(gfa, k)
```

The CLI signature changes from `bluntg [k]` to `bluntg` (k arg dropped
or accepted-but-ignored for backward compat). Update the doc comment
at the top of `src/main.rs` and the README accordingly.

---

## 8. Out of scope (intentionally)

* **Implementation** — this PR only documents the design; the Lean and
  Rust changes ship in follow-up tasks (`overlaps-lean`, the
  Rust track in the parallel batch).
* **Same-side `- +` bidirected edges** — already a known limitation
  per `lean/Bluntg/EvenK.lean:62-77` and SYNTHESIS.md §4. Variable
  overlap doesn't make this worse, and a fix requires porting stark's
  full node-split (`~/stark/src/main.cpp:200-241`).
* **GFA emission from syng / impg-syng-native with per-edge overlaps**
  — that emitter is in syng/impg's roadmap (the syng schema in
  `~/syng/syng.h:62-89` already encodes it), but is not in
  scope for the bluntg side. We just need to *consume* it correctly
  when it arrives.
* **`merge_nodes` (partial node merges)** — listed as follow-up in
  SYNTHESIS.md §4; orthogonal to overlap representation.
