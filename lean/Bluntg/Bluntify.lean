/-
The bluntify operation.

Given a De Bruijn graph `G` with overlap `k-1 ≥ 0`, we replace each node's
sequence by a trimmed window:

  • drop `(k-1)/2` from the front if the node has any incoming edge;
  • drop `k/2`     from the back  if the node has any outgoing edge.

The trimmed graph has overlap `0` (i.e. parameter `k = 1` in our type),
the same `numNodes`, the same `hasEdge` relation, and shorter sequences.

For odd `k` the two trim amounts are equal `((k-1)/2 = k/2)`, so each
junction sheds `(k-1)/2 + k/2 = k - 1` characters total — exactly the
overlap. This is the **lemma we exploit in the path-preservation proof.**

For even `k` the trims are asymmetric, but the sum is still `k - 1`, so
the *directed* (non-bidirected) bluntify is correct for any `k`. The
bidirected case for even `k` requires extra connector nodes; that is a
separate extension on top of this directed core.
-/
import Bluntg.Graph

namespace Bluntg
namespace DeBruijnGraph

variable {α : Type _} {k : Nat}

/-- Left trim amount for node `v` in `G`. -/
def leftTrim (G : DeBruijnGraph α k) (v : Fin G.numNodes) : Nat :=
  if G.hasIn v = true then (k - 1) / 2 else 0

/-- Right trim amount for node `v` in `G`. -/
def rightTrim (G : DeBruijnGraph α k) (v : Fin G.numNodes) : Nat :=
  if G.hasOut v = true then k / 2 else 0

theorem leftTrim_le (G : DeBruijnGraph α k) (v : Fin G.numNodes) :
    G.leftTrim v ≤ (k - 1) / 2 := by
  unfold leftTrim
  split <;> omega

theorem rightTrim_le (G : DeBruijnGraph α k) (v : Fin G.numNodes) :
    G.rightTrim v ≤ k / 2 := by
  unfold rightTrim
  split <;> omega

/-- Total trim is at most `k - 1`. This is the key arithmetic that drives
    the path-preservation theorem. -/
theorem trim_sum_le (G : DeBruijnGraph α k) (v : Fin G.numNodes) :
    G.leftTrim v + G.rightTrim v ≤ k - 1 := by
  have hl := G.leftTrim_le v
  have hr := G.rightTrim_le v
  -- `(k - 1)/2 + k/2 = k - 1` for any `k : ℕ`.
  omega

/-- The bluntified sequence of node `v`. -/
def bluntSeq (G : DeBruijnGraph α k) (v : Fin G.numNodes) : List α :=
  middle (G.seq v) (G.leftTrim v) (G.rightTrim v)

theorem bluntSeq_length_pos
    (G : DeBruijnGraph α k) (hk : 1 ≤ k) (v : Fin G.numNodes) :
    1 ≤ (G.bluntSeq v).length := by
  unfold bluntSeq
  rw [length_middle]
  have hsum := G.trim_sum_le v
  have hseq := G.seq_len v
  have hlt := G.leftTrim_le v
  -- min (n - l - r) (n - l) ≥ 1
  -- using n ≥ k, l + r ≤ k - 1, l ≤ (k-1)/2 ≤ k - 1
  simp only [Nat.le_min]
  refine ⟨?_, ?_⟩ <;> omega

/-- The bluntified graph. Has the same nodes and edges as `G` but with the
    trimmed sequences and overlap `0` (encoded as `k = 1`). -/
def bluntify (G : DeBruijnGraph α k) (hk : 1 ≤ k) : DeBruijnGraph α 1 where
  numNodes := G.numNodes
  seq      := G.bluntSeq
  hasEdge  := G.hasEdge
  seq_len  := G.bluntSeq_length_pos hk
  overlap  := by
    -- For k = 1 in the target graph, overlap length = 0, so both sides are `[]`.
    intro u v _
    simp [Suffix, Prefix]

@[simp] theorem bluntify_numNodes (G : DeBruijnGraph α k) (hk : 1 ≤ k) :
    (G.bluntify hk).numNodes = G.numNodes := rfl

@[simp] theorem bluntify_hasEdge (G : DeBruijnGraph α k) (hk : 1 ≤ k)
    (u v : Fin (G.bluntify hk).numNodes) :
    (G.bluntify hk).hasEdge u v = G.hasEdge u v := rfl

@[simp] theorem bluntify_seq (G : DeBruijnGraph α k) (hk : 1 ≤ k)
    (v : Fin (G.bluntify hk).numNodes) :
    (G.bluntify hk).seq v = G.bluntSeq v := rfl

/-- The "bluntified spell" of a walk, working directly on the original
    graph `G`: just concatenate per-node `bluntSeq` values. This is the
    cleanest version to reason about; we relate it to the spell of the
    actual bluntified graph in `bluntSpell_eq_bluntify_spell`. -/
def bluntSpell (G : DeBruijnGraph α k) : List (Fin G.numNodes) → List α
  | []        => []
  | v :: rest => G.bluntSeq v ++ G.bluntSpell rest

@[simp] theorem bluntSpell_nil (G : DeBruijnGraph α k) :
    G.bluntSpell [] = [] := rfl

theorem bluntSpell_cons (G : DeBruijnGraph α k)
    (v : Fin G.numNodes) (rest : List (Fin G.numNodes)) :
    G.bluntSpell (v :: rest) = G.bluntSeq v ++ G.bluntSpell rest := rfl

/-- The directly-defined `bluntSpell` equals the spell of the bluntified
    graph. (We avoid using this equality in the proofs below; it merely
    documents that the two formulations agree.) -/
theorem bluntSpell_eq_bluntify_spell
    (G : DeBruijnGraph α k) (hk : 1 ≤ k) :
    ∀ vs : List (Fin G.numNodes),
      G.bluntSpell vs = (G.bluntify hk).spell vs
  | []       => rfl
  | v :: rest => by
      rw [bluntSpell_cons]
      cases rest with
      | nil => rfl
      | cons w rest' =>
        rw [bluntSpell_eq_bluntify_spell G hk (w :: rest')]
        rfl

end DeBruijnGraph
end Bluntg
