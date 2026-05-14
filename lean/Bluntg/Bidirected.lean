/-
Bidirected layer.

A bidirected De Bruijn graph attaches a `+`/`-` orientation to every node.
Reading a node in `+` orientation gives its stored sequence; reading in
`-` orientation gives its reverse-complement. An edge `(u, su) — (v, sv)`
says the `(k-1)`-overlap at u's `su` end matches the `(k-1)`-overlap at
v's `sv` end (compared with the appropriate orientations).

This module:
  • defines `Orient`, the per-symbol `readSeq` helper, and the
    `BidirectedDeBruijnGraph` structure including its overlap invariant;
  • derives the **doubled** directed graph, in which each bidirected node
    splits into two directed nodes `(v, +)` and `(v, -)`. The doubling
    transports correctness from the directed `bluntify` to the bidirected
    setting: a bidirected walk corresponds to a directed walk in the
    doubled graph, and `bluntSpell_eq_middle_spell` lifts mechanically.
  • notes where the even-`k` connector-node fix-up plugs in.

`toDirected` is the lowering map; the rest is concrete enough that the
analogue path-preservation theorem can be derived without further
case analysis beyond the directed proof.
-/
import Bluntg.Bluntify

namespace Bluntg

/-- Strand orientation. -/
inductive Orient
  | plus
  | minus
  deriving DecidableEq, Repr, Inhabited

namespace Orient

/-- Flip `+ ↔ -`. -/
def flip : Orient → Orient
  | .plus  => .minus
  | .minus => .plus

@[simp] theorem flip_flip (o : Orient) : o.flip.flip = o := by
  cases o <;> rfl

end Orient

/-- Read a sequence in an orientation. `+` returns the stored list;
    `-` returns the reverse-complement. Lives outside the bidirected
    structure so it can appear in the structure's own invariants. -/
def readSeqAux {α : Type _} (sq : List α) (rc : α → α) (o : Orient) :
    List α :=
  match o with
  | .plus  => sq
  | .minus => sq.reverse.map rc

@[simp] theorem readSeqAux_plus {α : Type _} (sq : List α) (rc : α → α) :
    readSeqAux sq rc .plus = sq := rfl

@[simp] theorem readSeqAux_length {α : Type _} (sq : List α) (rc : α → α)
    (o : Orient) :
    (readSeqAux sq rc o).length = sq.length := by
  cases o <;> simp [readSeqAux]

/-- A bidirected De Bruijn graph. -/
structure BidirectedDeBruijnGraph (α : Type _) (k : Nat) where
  numNodes : Nat
  seq      : Fin numNodes → List α
  /-- Per-symbol complement; used to read a node in `-` orientation. -/
  revComp  : α → α
  /-- Bidirected adjacency. `hasEdge u suS v svS` says: leaving the
      `suS` side of `u` arrives at the `svS` side of `v`. -/
  hasEdge  : Fin numNodes → Orient → Fin numNodes → Orient → Bool
  /-- All node sequences are at least `k` long. -/
  seq_len  : ∀ v, k ≤ (seq v).length
  /-- Complementation is involutive. -/
  revComp_revComp : ∀ a, revComp (revComp a) = a
  /-- Edges are symmetric — the same undirected adjacency is observable
      from either endpoint. -/
  edge_symm : ∀ u suS v svS,
    hasEdge u suS v svS = hasEdge v svS u suS
  /-- Overlap: an edge `(u, su) — (v, sv)` matches the `(k-1)` chars at
      u's `su` end with the `(k-1)` chars at v's `sv` end. We express
      both ends as the suffix of `readSeq u su` and the prefix of
      `readSeq v sv.flip` (the latter is the orientation that *enters*
      v on its `sv` side). -/
  overlap :
    ∀ u su v sv, hasEdge u su v sv = true →
      Suffix (readSeqAux (seq u) revComp su) (k - 1) =
        Prefix (readSeqAux (seq v) revComp sv.flip) (k - 1)

namespace BidirectedDeBruijnGraph

variable {α : Type _} {k : Nat}

/-- Read a node in a given orientation. -/
def readSeq (G : BidirectedDeBruijnGraph α k) (v : Fin G.numNodes)
    (o : Orient) : List α :=
  readSeqAux (G.seq v) G.revComp o

@[simp] theorem readSeq_length (G : BidirectedDeBruijnGraph α k)
    (v : Fin G.numNodes) (o : Orient) :
    (G.readSeq v o).length = (G.seq v).length := by
  simp [readSeq]

/-! ## Doubling: lower a bidirected graph to a directed graph.

  Each bidirected node `v` becomes two directed nodes `(v, +)` and
  `(v, -)`, encoded into `Fin (2 * numNodes)` as
  `+: v.val`, `-: numNodes + v.val`. Each bidirected edge becomes one
  directed edge whose source-orientation matches `su` and whose
  target-orientation is `flip sv` (so that the directed graph's left/right
  ends align with the bidirected entry/exit sides). -/

/-- Doubled node count. -/
def doubledNumNodes (G : BidirectedDeBruijnGraph α k) : Nat :=
  2 * G.numNodes

/-- Pack `(v, o)` into a `Fin (2 * numNodes)`. -/
def encode (G : BidirectedDeBruijnGraph α k) (v : Fin G.numNodes)
    (o : Orient) : Fin G.doubledNumNodes :=
  match o with
  | .plus  => ⟨v.val, by
      unfold doubledNumNodes; have := v.isLt; omega⟩
  | .minus => ⟨G.numNodes + v.val, by
      unfold doubledNumNodes; have := v.isLt; omega⟩

/-- Decode a doubled-graph index. -/
def decode (G : BidirectedDeBruijnGraph α k) (ix : Fin G.doubledNumNodes) :
    Fin G.numNodes × Orient :=
  if h : ix.val < G.numNodes then
    (⟨ix.val, h⟩, .plus)
  else
    (⟨ix.val - G.numNodes, by
        have := ix.isLt; unfold doubledNumNodes at this; omega⟩,
     .minus)

theorem decode_encode (G : BidirectedDeBruijnGraph α k)
    (v : Fin G.numNodes) (o : Orient) :
    G.decode (G.encode v o) = (v, o) := by
  cases o
  case plus =>
    unfold encode decode
    have h : v.val < G.numNodes := v.isLt
    simp [h]
  case minus =>
    unfold encode decode
    have h : ¬ G.numNodes + v.val < G.numNodes := by omega
    simp [h]

/-- The doubled directed graph. -/
def toDirected (G : BidirectedDeBruijnGraph α k) (hk : 1 ≤ k) :
    DeBruijnGraph α k where
  numNodes := G.doubledNumNodes
  seq := fun ix =>
    let p := G.decode ix
    G.readSeq p.1 p.2
  hasEdge := fun ix iy =>
    let p := G.decode ix
    let q := G.decode iy
    G.hasEdge p.1 p.2 q.1 q.2.flip
  seq_len := fun ix => by
    show k ≤ (G.readSeq (G.decode ix).1 (G.decode ix).2).length
    rw [readSeq_length]
    exact G.seq_len _
  overlap := fun ix iy h_edge => by
    -- The directed overlap obligation:
    --   Suffix (readSeq u ou) (k-1) = Prefix (readSeq v ov) (k-1)
    -- where (u, ou) = decode ix and (v, ov) = decode iy.
    -- Apply the bidirected overlap to (u, ou, v, flip ov); using
    -- `flip_flip` brings the target's orientation back to `ov`.
    have hb := G.overlap (G.decode ix).1 (G.decode ix).2
                          (G.decode iy).1 (G.decode iy).2.flip h_edge
    simp [Orient.flip_flip] at hb
    show Suffix (G.readSeq _ _) (k - 1) = Prefix (G.readSeq _ _) (k - 1)
    simp [readSeq]
    exact hb

/-! ## Even-`k` connector nodes (TODO)

  For even `k`, the per-junction trim is asymmetric: `k/2` on one side and
  `(k-1)/2 = k/2 - 1` on the other. In a bidirected graph the same node
  can be traversed in either orientation, so the asymmetry is ill-defined.
  Stark resolves this by inserting a one-character "connector" node
  between every even-`k` edge.

  Sketch:
    • for each bidirected edge `(u, su) — (v, sv)` of an even-`k`
      graph, add a fresh node `c` whose sequence is the middle character
      of the original `(k-1)`-overlap;
    • replace the edge with two new edges `(u, su) — (c, +)` and
      `(c, +) — (v, sv)`, each with half the original overlap;
    • run odd-`k` bluntify on the result.

  Correctness reduces to a path bijection: any walk in the original
  graph lifts to a walk in the augmented graph spelling the same string,
  and conversely. -/

end BidirectedDeBruijnGraph
end Bluntg
