/-
A De Bruijn graph in our setting is:

  • a finite set of `numNodes` nodes, identified by `Fin numNodes`;
  • a sequence `seq v : List α` of length ≥ `k` attached to each node;
  • a boolean adjacency `hasEdge u v` describing directed edges;
  • the **overlap invariant**: every edge `u → v` satisfies
      `Suffix (seq u) (k-1) = Prefix (seq v) (k-1)`.

This is the directed (non-bidirected) version, which is enough to state and
prove the odd-`k` bluntify correctness theorem.

Walks are lists of node ids whose consecutive entries are adjacent. The
**spelled string** of a walk concatenates the per-node sequences and drops
the (`k-1`)-character overlap at every junction.
-/
import Bluntg.Basic

namespace Bluntg

/-- A De Bruijn graph with overlap `k - 1`. -/
structure DeBruijnGraph (α : Type _) (k : Nat) where
  numNodes  : Nat
  seq       : Fin numNodes → List α
  hasEdge   : Fin numNodes → Fin numNodes → Bool
  seq_len   : ∀ v, k ≤ (seq v).length
  overlap   : ∀ u v, hasEdge u v = true →
    Suffix (seq u) (k - 1) = Prefix (seq v) (k - 1)

namespace DeBruijnGraph

variable {α : Type _} {k : Nat}

/-- A node `v` has an outgoing edge in `G`. Boolean form: scans all
    candidate targets and returns `true` iff at least one is connected. -/
def hasOut (G : DeBruijnGraph α k) (v : Fin G.numNodes) : Bool :=
  (List.finRange G.numNodes).any (fun w => G.hasEdge v w)

/-- A node `v` has an incoming edge in `G`. Boolean form. -/
def hasIn (G : DeBruijnGraph α k) (v : Fin G.numNodes) : Bool :=
  (List.finRange G.numNodes).any (fun u => G.hasEdge u v)

theorem hasOut_iff (G : DeBruijnGraph α k) (v : Fin G.numNodes) :
    G.hasOut v = true ↔ ∃ w, G.hasEdge v w = true := by
  unfold hasOut
  simp [List.any_eq_true, List.mem_finRange]

theorem hasIn_iff (G : DeBruijnGraph α k) (v : Fin G.numNodes) :
    G.hasIn v = true ↔ ∃ u, G.hasEdge u v = true := by
  unfold hasIn
  simp [List.any_eq_true, List.mem_finRange]

/-- `isWalk vs` means `vs` is a (possibly empty) walk in `G`: every
    consecutive pair `(u, v)` in `vs` is connected by an edge `u → v`. -/
def isWalk (G : DeBruijnGraph α k) : List (Fin G.numNodes) → Prop
  | []              => True
  | [_]             => True
  | u :: v :: rest  => G.hasEdge u v = true ∧ isWalk G (v :: rest)

/-- Concatenate the trimmed-tail sequences of a list of nodes:
    each subsequent node contributes its sequence with the `(k-1)`-prefix
    dropped. Helper for `spell`. -/
def spellTail (G : DeBruijnGraph α k) : List (Fin G.numNodes) → List α
  | []        => []
  | v :: rest => (G.seq v).drop (k - 1) ++ spellTail G rest

/-- Spell a walk: emit the first node's full sequence, then for each
    subsequent node append its sequence with the `(k-1)`-overlap dropped. -/
def spell (G : DeBruijnGraph α k) : List (Fin G.numNodes) → List α
  | []        => []
  | v :: rest => G.seq v ++ spellTail G rest

@[simp] theorem spell_nil (G : DeBruijnGraph α k) : G.spell [] = [] := rfl

@[simp] theorem spellTail_nil (G : DeBruijnGraph α k) : G.spellTail [] = [] := rfl

@[simp] theorem spell_singleton (G : DeBruijnGraph α k) (v : Fin G.numNodes) :
    G.spell [v] = G.seq v := by
  simp [spell, spellTail]

theorem spell_cons (G : DeBruijnGraph α k) (v : Fin G.numNodes)
    (rest : List (Fin G.numNodes)) :
    G.spell (v :: rest) = G.seq v ++ G.spellTail rest := rfl

theorem spellTail_cons (G : DeBruijnGraph α k) (v : Fin G.numNodes)
    (rest : List (Fin G.numNodes)) :
    G.spellTail (v :: rest) =
      (G.seq v).drop (k - 1) ++ G.spellTail rest := rfl

end DeBruijnGraph

end Bluntg
