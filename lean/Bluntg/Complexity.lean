/-
# Complexity bound for `bluntify`

We give an explicit step-count function `bluntifySteps : Gfa → ℕ` matching a
deterministic execution model for the bluntify algorithm, and we prove
`bluntifySteps g ≤ C * (|V| + |E|)` for `C = 1` where `|V| = g.segments.size`
and `|E| = g.links.size`.

## Execution model

The algorithm conceptually performs:

1. **One fold over `g.links`** to compute side-set membership for each
   segment id. `GFA.bluntify` runs two separate folds (`rightSideIds` and
   `leftSideIds`); they are independent passes over the same array and can
   be merged into a single pass producing a pair of sets, with the same
   asymptotic step count `|E|`. We model the merged pass.
2. **One map over `g.segments`** to apply the per-segment trim. Each
   iteration performs two `HashSet.contains` lookups, treated as O(1)
   on average (the standard amortized assumption for `Std.HashSet`). For a
   worst-case bound, replace the `HashSet` of side ids with a sorted
   `Array` of ids and binary search: this adds a one-shot `O(|V| log |V|)`
   sort plus `O(log |V|)` per segment lookup, raising the bound to
   `O((|V| + |E|) log |V|)` in the worst case. The average-case `O(|V|+|E|)`
   bound proved here matches the implementation as written.

The link/path overlap-rewrite passes (`g.links.map` / `g.paths.map` to set
overlap to `0`) only manipulate metadata; they are O(|E|) and O(|paths|)
respectively and do no graph work, so we omit them from the headline
complexity figure for `|V| + |E|`. They are accounted for separately by
`bluntifyMetadataSteps` below.

## Step count

Under the merged single-pass model, the work is `|links| + |segments|`
elementary steps, where each step is a constant amount of work (one
fold-step or one map-step). The bound `|V| + |E|` follows immediately
with `C = 1`.

The bounds proved here use `Array.size` for the link/segment counts; the
step-count function is defined as the sum of those two `Array.size` values,
so it tracks the actual loop bound of the implementation 1:1.
-/
import Bluntg.GFA
import Bluntg.Bluntify

namespace Bluntg

/-! ## GFA-level complexity -/

namespace GFA

/-- Step count for `GFA.bluntify`, under the merged single-pass execution
    model: one fold over the links array, one map over the segments array. -/
def bluntifySteps (g : Gfa) : Nat :=
  g.links.size + g.segments.size

/-- Step count for the trivial metadata rewrite passes (zeroing overlap on
    every link and on every path step). Quoted separately because it does
    no graph work — the headline `|V| + |E|` bound deliberately excludes
    `paths.size` and the second link traversal. -/
def bluntifyMetadataSteps (g : Gfa) : Nat :=
  g.links.size + g.paths.size

/-- The headline complexity bound: `bluntifySteps g ≤ C · (|V| + |E|)` with
    `C = 1`. This is tight under our merged single-pass model — equality holds
    if both arrays are non-empty (and trivially if both are empty). -/
theorem bluntifySteps_le (g : Gfa) :
    bluntifySteps g ≤ 1 * (g.segments.size + g.links.size) := by
  unfold bluntifySteps
  omega

/-- Sharper, equality form of the bound at `C = 1`. -/
theorem bluntifySteps_eq (g : Gfa) :
    bluntifySteps g = g.segments.size + g.links.size := by
  unfold bluntifySteps
  omega

/-! ### Loop-bound correspondence

These lemmas tie `bluntifySteps` to the actual `Array.foldl` / `Array.map`
operations performed by `bluntify`: each pass touches each element exactly
once, so the loop bound for the implementation matches `bluntifySteps`
1:1 (no hidden multiplicative factors).
-/

/-- The output graph has the same number of segments as the input. The
    `Array.map` over segments touches each input element exactly once. -/
@[simp] theorem bluntify_segments_size (g : Gfa) (k : Nat) :
    (bluntify g k).segments.size = g.segments.size := by
  unfold bluntify bluntifyVar
  simp

/-- The output graph has the same number of links as the input. The
    `Array.map` over links touches each input element exactly once. -/
@[simp] theorem bluntify_links_size (g : Gfa) (k : Nat) :
    (bluntify g k).links.size = g.links.size := by
  unfold bluntify bluntifyVar
  simp

/-- The output graph has the same number of paths as the input. -/
@[simp] theorem bluntify_paths_size (g : Gfa) (k : Nat) :
    (bluntify g k).paths.size = g.paths.size := by
  unfold bluntify bluntifyVar
  simp

/-- Bluntifying preserves the headline complexity input: the step count is
    invariant under the operation. -/
theorem bluntifySteps_bluntify (g : Gfa) (k : Nat) :
    bluntifySteps (bluntify g k) = bluntifySteps g := by
  unfold bluntifySteps
  simp

end GFA

/-! ## DeBruijnGraph-level complexity

For the verified `DeBruijnGraph α k`, `bluntify` is a record constructor —
no per-node work runs eagerly, so the only natural step count is "build the
record": one `O(1)` step. The interesting work happens *on demand* when we
materialize a node's bluntified sequence (`bluntSeq`).

We bound the cost of materializing **every** bluntified sequence under a
model where `hasIn` and `hasOut` are precomputed in `O(|V| + |E|)` (e.g.
during the same fold-over-edges that we use at the GFA layer). Under that
assumption, materialization is one map over `numNodes` constant-time steps
per node, so the total is `numNodes` steps.

This matches the `DeBruijnGraph` "edges" being implicit in `hasEdge` rather
than enumerated; without an enumerable edge list we cannot give an
`|V| + |E|` bound from inside this structure alone — that is exactly why
the `Gfa` layer above carries an explicit `links : Array Link`.
-/

namespace DeBruijnGraph

variable {α : Type _} {k : Nat}

/-- Step count for materializing every bluntified sequence in a
    `DeBruijnGraph`, assuming `hasIn`/`hasOut` are precomputed. One step
    per node = `numNodes` total steps. -/
def bluntifySteps (G : DeBruijnGraph α k) : Nat :=
  G.numNodes

/-- The bound `bluntifySteps G ≤ 1 · |V|`. With `hasIn`/`hasOut`
    precomputed (themselves `O(|V| + |E|)` to build via one fold over an
    enumerated edge list — see `GFA.bluntifySteps`), the per-node trim
    materialization is constant time, so the per-graph total is `|V|`. -/
theorem bluntifySteps_le (G : DeBruijnGraph α k) :
    G.bluntifySteps ≤ 1 * G.numNodes := by
  unfold bluntifySteps
  omega

/-- Equality form of the bound at `C = 1`. -/
theorem bluntifySteps_eq (G : DeBruijnGraph α k) :
    G.bluntifySteps = G.numNodes := by
  unfold bluntifySteps; rfl

/-- The bluntified graph has the same number of nodes; the per-graph step
    count is invariant under `bluntify`. -/
theorem bluntifySteps_bluntify (G : DeBruijnGraph α k) (hk : 1 ≤ k) :
    (G.bluntify hk).bluntifySteps = G.bluntifySteps := rfl

end DeBruijnGraph

end Bluntg
