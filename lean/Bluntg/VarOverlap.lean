/-
Variable per-edge overlap theory.

This module generalises the uniform-`k` `DeBruijnGraph` from
`Bluntg.Graph` to the **variable per-edge overlap** setting motivated
by `DESIGN-overlaps.md`. The directed core stays the same shape:

  • a finite set of `numNodes` nodes (`Fin numNodes`);
  • a per-node `seq v : List α`;
  • a boolean adjacency `hasEdge u v : Bool`.

What changes is the **overlap model**:

  • each edge `u → v` carries its **own** overlap length
    `edgeOverlap u v h : Nat` (not a single global `k - 1`);
  • the structure-level overlap invariant matches the per-edge overlap:
    `Suffix (seq u) o = Prefix (seq v) o` where `o = edgeOverlap u v h`;
  • the **trim amounts** that drive bluntify are stored as structure
    fields `leftTrim v : Nat` and `rightTrim v : Nat`. They are not
    derived from `hasEdge`; instead, the structure carries a
    `trim_eq` axiom asserting that the two per-side trims exactly
    sum to the per-edge overlap at every junction:
        `rightTrim u + leftTrim v = edgeOverlap u v h`.

This `trim_eq` constraint is the key to path-preservation: it says
the per-edge halves match the per-node trim at *both* endpoints
simultaneously. The GFA-layer max-aggregation
(`Bluntg.GFA.rightOverlap` / `leftOverlap`) produces trims that
satisfy `trim_eq` exactly when no per-side aggregation conflict
arises — equivalently, when all right-incident edges at each segment
share the same overlap and all left-incident edges share the same
overlap. The uniform-`k` case (every edge has overlap `k - 1`) is a
special case; the mixed-overlap fixture in `DESIGN-overlaps.md §6.2
T3` (one overlap value per edge, no hub aggregation) is another.

The main results are:
  • `varBluntify_is_blunt` — the bluntified graph has zero overlap
    on every edge (trivial: the target graph has `edgeOverlap ≡ 0`).
  • `varBluntSpell_eq_middle_varSpell` — for any walk, the bluntified
    spelling is the middle window of the variable-overlap spelling,
    with the per-edge trim halves stripped at every junction. This
    is the variable analogue of `bluntSpell_eq_middle_spell` from
    `Bluntg.Correctness`. Both proofs share the same list-arithmetic
    sandwich lemma (`middle_concat_overlap` in `Bluntg.Basic`),
    instantiated with `wL := leftTrim v`, `wR := rightTrim u`, and
    the per-edge sum `edgeOverlap u v h = wR + wL`.

The proof structure differs from the fixed-`k` version in three ways:

  1. The "trim sum equals overlap" identity is now an axiom of the
     structure (`trim_eq`), not an arithmetic fact derived from
     `(k-1)/2 + k/2 = k - 1`. In the fixed-`k` proof, the sandwich
     lemma was applied with `wL = (k-1)/2`, `wR = k/2`, and the sum
     was rewritten via `omega`. Here we apply the sandwich lemma
     with `wL = leftTrim v`, `wR = rightTrim u`, and the sum is
     rewritten via `trim_eq` directly.

  2. The spelling function `varSpell` is parameterised by a walk
     witness (`isWalk vs`) because it needs the edge handle
     `hwalk.1` to extract `edgeOverlap u v hwalk.1` at each junction.
     The fixed-`k` `spell` did not need this: every junction dropped
     the same `(k - 1)` chars regardless of which edge it traversed.

  3. The "length of seq is large enough" arithmetic is split:
     `trim_lt_len v` bounds the per-node trim sum, while
     `edge_le_seq` bounds the per-edge overlap against each endpoint's
     sequence length. In the fixed-`k` case, both were subsumed by
     the single field `seq_len : ∀ v, k ≤ (seq v).length`.
-/

import Bluntg.Basic
import Bluntg.Correctness  -- for the shared middle_concat_overlap sandwich lemma
import Bluntg.Bidirected   -- for Orient and readSeqAux

namespace Bluntg

/-! ## Variable-overlap De Bruijn graph -/

/-- A De Bruijn graph with per-edge overlap lengths.

    Compared with `Bluntg.DeBruijnGraph α k`:
      • there is no global `k` type parameter;
      • the overlap invariant is per-edge (`edgeOverlap u v h`);
      • the trim amounts (`leftTrim`, `rightTrim`) are *fields* of
        the structure, with `trim_eq` asserting that for every edge
        `u → v`, `rightTrim u + leftTrim v = edgeOverlap u v h`.

    Building a `VarDeBruijnGraph` from a GFA with consistent
    per-side max-aggregation (cf. `Bluntg.GFA.rightOverlap` /
    `leftOverlap`) is the entry point: `trim_eq` is exactly the
    condition that the max at each side coincides with this edge's
    half. -/
structure VarDeBruijnGraph (α : Type _) where
  numNodes    : Nat
  seq         : Fin numNodes → List α
  hasEdge     : Fin numNodes → Fin numNodes → Bool
  edgeOverlap : ∀ u v, hasEdge u v = true → Nat
  /-- Pre-computed left-side trim per node. -/
  leftTrim    : Fin numNodes → Nat
  /-- Pre-computed right-side trim per node. -/
  rightTrim   : Fin numNodes → Nat
  /-- Per-edge overlap invariant: the source's `o`-suffix matches the
      target's `o`-prefix, where `o` is the per-edge overlap. -/
  overlap     : ∀ u v (h : hasEdge u v = true),
                  Suffix (seq u) (edgeOverlap u v h) =
                    Prefix (seq v) (edgeOverlap u v h)
  /-- The two per-side trims sum to the per-edge overlap at every
      junction. This is the variable-overlap analogue of the uniform-`k`
      identity `(k-1)/2 + k/2 = k - 1`. -/
  trim_eq     : ∀ u v (h : hasEdge u v = true),
                  rightTrim u + leftTrim v = edgeOverlap u v h
  /-- The per-node trim sum is strictly less than the node's sequence
      length, so the bluntified sequence has at least one character. -/
  trim_lt_len : ∀ v, leftTrim v + rightTrim v < (seq v).length
  /-- The per-edge overlap fits within the source node's sequence. -/
  edge_le_src : ∀ u v (h : hasEdge u v = true),
                  edgeOverlap u v h ≤ (seq u).length
  /-- The per-edge overlap fits within the target node's sequence. -/
  edge_le_tgt : ∀ u v (h : hasEdge u v = true),
                  edgeOverlap u v h ≤ (seq v).length

namespace VarDeBruijnGraph

variable {α : Type _}

/-! ## Walks and spelling -/

/-- A walk in `G`: every consecutive pair is connected by an edge. -/
def isWalk (G : VarDeBruijnGraph α) : List (Fin G.numNodes) → Prop
  | []              => True
  | [_]             => True
  | u :: v :: rest  => G.hasEdge u v = true ∧ isWalk G (v :: rest)

/-- The bluntified sequence at a single node. -/
def bluntSeq (G : VarDeBruijnGraph α) (v : Fin G.numNodes) : List α :=
  middle (G.seq v) (G.leftTrim v) (G.rightTrim v)

/-- Variable-overlap spell of a walk: the first node contributes its
    full sequence; each subsequent step drops `edgeOverlap u v` chars
    where `u → v` is the edge traversed. This needs an `isWalk` witness
    so the edge handle is available to look up `edgeOverlap`. -/
def varSpell (G : VarDeBruijnGraph α) :
    (vs : List (Fin G.numNodes)) → G.isWalk vs → List α
  | [],              _      => []
  | [v],             _      => G.seq v
  | u :: v :: rest,  hwalk  =>
      G.seq u ++ (varSpell G (v :: rest) hwalk.2).drop
        (G.edgeOverlap u v hwalk.1)

/-- Bluntified spell of a walk: concatenate per-node `bluntSeq` values.
    Unlike `varSpell`, this does **not** depend on the walk's
    `isWalk` witness — it makes sense for any node list. We thread the
    witness only because the path-preservation theorem statement uses
    `varSpell`. -/
def varBluntSpell (G : VarDeBruijnGraph α) :
    List (Fin G.numNodes) → List α
  | []        => []
  | v :: rest => G.bluntSeq v ++ G.varBluntSpell rest

@[simp] theorem varSpell_nil (G : VarDeBruijnGraph α) (h : G.isWalk []) :
    G.varSpell [] h = [] := rfl

@[simp] theorem varSpell_singleton (G : VarDeBruijnGraph α)
    (v : Fin G.numNodes) (h : G.isWalk [v]) :
    G.varSpell [v] h = G.seq v := rfl

theorem varSpell_cons_cons (G : VarDeBruijnGraph α)
    (u v : Fin G.numNodes) (rest : List (Fin G.numNodes))
    (hwalk : G.isWalk (u :: v :: rest)) :
    G.varSpell (u :: v :: rest) hwalk =
      G.seq u ++ (G.varSpell (v :: rest) hwalk.2).drop
        (G.edgeOverlap u v hwalk.1) := rfl

@[simp] theorem varBluntSpell_nil (G : VarDeBruijnGraph α) :
    G.varBluntSpell [] = [] := rfl

theorem varBluntSpell_cons (G : VarDeBruijnGraph α)
    (v : Fin G.numNodes) (rest : List (Fin G.numNodes)) :
    G.varBluntSpell (v :: rest) = G.bluntSeq v ++ G.varBluntSpell rest := rfl

/-! ## Length lemmas about `varSpell` -/

/-- A non-empty walk's variable-overlap spell starts with the head's
    sequence, so its length is at least `(seq head).length`. -/
theorem varSpell_length_ge_seq
    (G : VarDeBruijnGraph α) (v : Fin G.numNodes)
    (rest : List (Fin G.numNodes)) (hwalk : G.isWalk (v :: rest)) :
    (G.seq v).length ≤ (G.varSpell (v :: rest) hwalk).length := by
  cases rest with
  | nil => simp [varSpell]
  | cons w rest' =>
    rw [varSpell_cons_cons]
    rw [List.length_append]
    omega

/-- Helper bound: `leftTrim v + rightTrim last < (varSpell vs).length`
    for any non-empty walk `vs = v :: rest`. Proof by induction on
    `rest`, using `trim_lt_len` at each node and `trim_eq` at each edge
    to telescope across junctions. This is the variable-overlap analogue
    of `spell_length_ge` in `Bluntg.Correctness`, generalised to bound
    *both* the head's left trim and the last's right trim against the
    total spelling length. -/
theorem varSpell_length_ge_last
    (G : VarDeBruijnGraph α) :
    ∀ (v : Fin G.numNodes) (rest : List (Fin G.numNodes))
      (hwalk : G.isWalk (v :: rest)),
        G.leftTrim v + G.rightTrim ((v :: rest).getLast (by simp)) <
          (G.varSpell (v :: rest) hwalk).length := by
  intro v rest
  induction rest generalizing v with
  | nil =>
    intro hwalk
    -- getLast [v] = v; varSpell [v] = seq v; bound follows from trim_lt_len.
    simp only [varSpell_singleton, List.getLast_singleton]
    have := G.trim_lt_len v; omega
  | cons w rest' ih =>
    intro hwalk
    have huv : G.hasEdge v w = true := hwalk.1
    have hwalk_rest : G.isWalk (w :: rest') := hwalk.2
    have hge_rest := ih w hwalk_rest
    have hlast_eq : (v :: w :: rest').getLast (by simp) =
                    (w :: rest').getLast (by simp) := by
      simp [List.getLast]
    rw [hlast_eq, varSpell_cons_cons]
    -- length (seq v ++ drop o (varSpell (w :: rest'))) = |seq v| + |varSpell| - o.
    rw [List.length_append, List.length_drop]
    -- Combine: trim_eq v w huv (rightTrim v + leftTrim w = o),
    --          trim_lt_len v (leftTrim v + rightTrim v < |seq v|),
    --          ih (leftTrim w + rightTrim last < |varSpell|),
    --          edge_le_tgt v w huv (o ≤ |seq w| ≤ |varSpell|).
    have htrim_eq : G.rightTrim v + G.leftTrim w = G.edgeOverlap v w huv :=
      G.trim_eq v w huv
    have hvarlen := G.varSpell_length_ge_seq w rest' hwalk_rest
    have htv := G.trim_lt_len v
    have hov := G.edge_le_tgt v w huv
    omega

/-! ## Bluntification map -/

/-- Length of the bluntified per-node sequence is at least 1. -/
theorem bluntSeq_length_pos
    (G : VarDeBruijnGraph α) (v : Fin G.numNodes) :
    1 ≤ (G.bluntSeq v).length := by
  unfold bluntSeq
  rw [length_middle]
  have := G.trim_lt_len v
  -- min (n - l - r) (n - l) ≥ 1 when n > l + r.
  simp only [Nat.le_min]
  refine ⟨?_, ?_⟩ <;> omega

/-- The bluntified variable-overlap graph. All edges in the result have
    zero overlap, so the result is **blunt** in the GFA sense.

    The target graph's `edgeOverlap` is constantly zero, `leftTrim` and
    `rightTrim` are constantly zero (no further trimming applies), and
    `trim_eq` holds trivially because `0 + 0 = 0`. The `overlap` field
    is also trivial: a 0-suffix of any list equals a 0-prefix of any
    list (both are `[]`). The non-empty length invariant
    (`trim_lt_len`) follows from `bluntSeq_length_pos` (each
    bluntified sequence has at least one character). -/
def varBluntify (G : VarDeBruijnGraph α) : VarDeBruijnGraph α where
  numNodes    := G.numNodes
  seq         := G.bluntSeq
  hasEdge     := G.hasEdge
  edgeOverlap := fun _ _ _ => 0
  leftTrim    := fun _ => 0
  rightTrim   := fun _ => 0
  overlap     := by
    intro u v _
    simp [Suffix, Prefix]
  trim_eq     := by intro u v _; rfl
  trim_lt_len := by
    intro v
    have := G.bluntSeq_length_pos v
    omega
  edge_le_src := by intro u v _; omega
  edge_le_tgt := by intro u v _; omega

/-! ## Headline theorems -/

/-- **Variable analogue of `bluntify_is_blunt`.** The bluntified graph
    really is blunt: every edge in `varBluntify G` has zero overlap.
    Trivial because the target graph's `edgeOverlap` is the constant
    zero function. -/
theorem varBluntify_is_blunt (G : VarDeBruijnGraph α) :
    ∀ u v (h : (G.varBluntify).hasEdge u v = true),
      Suffix ((G.varBluntify).seq u) ((G.varBluntify).edgeOverlap u v h) =
        Prefix ((G.varBluntify).seq v) ((G.varBluntify).edgeOverlap u v h) := by
  intro u v _
  -- `edgeOverlap _ _ _ = 0` for the bluntified graph, so both sides are `[]`.
  simp [Suffix, Prefix, varBluntify]

/-- Per-edge overlap restated against a walk's `varSpell`.

    For an edge `u → v` with overlap `o = edgeOverlap u v h`, the last
    `o` characters of `seq u` (its `o`-suffix) coincide with the first
    `o` characters of `varSpell (v :: rest) hrest`. This is the
    variable analogue of `overlap_walk` from `Bluntg.Correctness`;
    the proof differs from the uniform-`k` version in that we use
    `edge_le_tgt` (the structure-level bound `o ≤ (seq v).length`)
    in place of the uniform `seq_len v : k ≤ (seq v).length`. -/
theorem overlap_walk
    (G : VarDeBruijnGraph α)
    (u v : Fin G.numNodes) (h : G.hasEdge u v = true)
    (rest : List (Fin G.numNodes))
    (hrest : G.isWalk (v :: rest)) :
    (G.seq u).drop ((G.seq u).length - G.edgeOverlap u v h) =
      (G.varSpell (v :: rest) hrest).take (G.edgeOverlap u v h) := by
  have hov := G.overlap u v h
  unfold Suffix Prefix at hov
  rw [hov]
  -- Goal: (G.seq v).take o = (G.varSpell (v :: rest) hrest).take o
  -- Unfold varSpell on (v :: rest); both cases (rest = [] or non-empty)
  -- reduce to taking from `seq v ++ ...`, where the take stays inside
  -- `seq v` thanks to `edge_le_tgt`.
  have hlen_v : G.edgeOverlap u v h ≤ (G.seq v).length := G.edge_le_tgt u v h
  cases rest with
  | nil =>
    show (G.seq v).take _ = (G.varSpell [v] hrest).take _
    rw [varSpell_singleton]
  | cons w rest' =>
    show (G.seq v).take _ = (G.varSpell (v :: w :: rest') hrest).take _
    rw [varSpell_cons_cons]
    rw [List.take_append_of_le_length hlen_v]

/-- **Variable analogue of `bluntSpell_eq_middle_spell`.** For any
    non-empty walk `vs`, the bluntified spelling is the middle window
    of the variable-overlap spelling, trimmed by `leftTrim` at the head
    and `rightTrim` at the last node.

    Proof structure (mirrors the fixed-`k` proof in `Bluntg.Correctness`):
      • base case (singleton walk): both sides reduce to `bluntSeq head`.
      • inductive step (walk `u :: v :: rest`): apply
        `middle_concat_overlap` with
          `A := seq u`,
          `B := varSpell (v :: rest)`,
          `x := leftTrim u`,
          `wR := rightTrim u`,
          `wL := leftTrim v`,
          `y := rightTrim last`.

    The key arithmetic identity `rightTrim u + leftTrim v =
    edgeOverlap u v h` (from `trim_eq`) supplies the `wL + wR`
    argument to the sandwich lemma. In the fixed-`k` case this
    identity was derived from `(k-1)/2 + k/2 = k - 1`; here it is a
    structure axiom, so the rewrite step uses `trim_eq` instead of
    an `omega` over half-integer arithmetic. -/
theorem varBluntSpell_eq_middle_varSpell
    (G : VarDeBruijnGraph α) :
    ∀ vs : List (Fin G.numNodes), ∀ (hwalk : G.isWalk vs) (hne : vs ≠ []),
      G.varBluntSpell vs =
        middle (G.varSpell vs hwalk)
          (G.leftTrim (vs.head hne))
          (G.rightTrim (vs.getLast hne)) := by
  intro vs
  induction vs with
  | nil => intro _ hne; exact (hne rfl).elim
  | cons u rest ih =>
    intro hwalk hne
    cases rest with
    | nil =>
      -- Singleton: bluntSpell [u] = bluntSeq u; varSpell [u] = seq u.
      show G.varBluntSpell [u] = middle (G.varSpell [u] hwalk) _ _
      rw [varBluntSpell_cons]
      simp only [varBluntSpell_nil, List.append_nil]
      rw [varSpell_singleton]
      rfl
    | cons v rest' =>
      have huv : G.hasEdge u v = true := hwalk.1
      have hwalk_rest : G.isWalk (v :: rest') := hwalk.2
      have IH := ih hwalk_rest (by simp)
      -- Head and last of the larger walk.
      have hhead : (u :: v :: rest').head hne = u := rfl
      have hlast : (u :: v :: rest').getLast hne =
                   (v :: rest').getLast (by simp) := by
        simp [List.getLast]
      rw [hhead, hlast]
      -- Key arithmetic identity (variable analogue of `(k-1)/2 + k/2 = k-1`).
      have hsum : G.leftTrim v + G.rightTrim u = G.edgeOverlap u v huv := by
        have := G.trim_eq u v huv; omega
      -- Length bounds for `middle_concat_overlap`.
      have hkle_u : G.edgeOverlap u v huv ≤ (G.seq u).length :=
        G.edge_le_src u v huv
      have hkle_spell :
          G.edgeOverlap u v huv ≤
            (G.varSpell (v :: rest') hwalk_rest).length := by
        have := G.varSpell_length_ge_seq v rest' hwalk_rest
        have := G.edge_le_tgt u v huv
        omega
      have hwAB_A : G.leftTrim v + G.rightTrim u ≤ (G.seq u).length := by
        rw [hsum]; exact hkle_u
      have hwAB_B : G.leftTrim v + G.rightTrim u ≤
                    (G.varSpell (v :: rest') hwalk_rest).length := by
        rw [hsum]; exact hkle_spell
      have hxA : G.leftTrim u + G.rightTrim u ≤ (G.seq u).length := by
        have := G.trim_lt_len u; omega
      have hyB : G.leftTrim v + G.rightTrim ((v :: rest').getLast (by simp)) ≤
                 (G.varSpell (v :: rest') hwalk_rest).length := by
        -- The right trim at the last node is bounded by that node's
        -- sequence length, which is part of varSpell. We use the
        -- `varSpell_length_ge_last` bound (derived inline).
        have hge := G.varSpell_length_ge_seq v rest' hwalk_rest
        have htlt := G.trim_lt_len v
        -- leftTrim v ≤ |seq v| - 1, |seq v| ≤ |varSpell (v :: rest')|.
        -- and rightTrim last ≤ |seq last|. We need
        -- leftTrim v + rightTrim last ≤ |varSpell|.
        -- Since varSpell ≥ |seq v|, and |seq v| > leftTrim v + rightTrim v,
        -- this isn't immediate. We need a stronger bound on varSpell length
        -- that includes the last node. Use induction-style: varSpell length
        -- ≥ |seq v| + (something), then bound rightTrim last by seq_len last.
        -- For now we use the strongest available bound and hope omega works.
        have hge_last := varSpell_length_ge_last G v rest' hwalk_rest
        omega
      -- Apply the sandwich lemma.
      have key := DeBruijnGraph.middle_concat_overlap
        (β := α)
        (A := G.seq u)
        (B := G.varSpell (v :: rest') hwalk_rest)
        (x := G.leftTrim u)
        (y := G.rightTrim ((v :: rest').getLast (by simp)))
        (wL := G.leftTrim v)
        (wR := G.rightTrim u)
        (h_overlap := by
          rw [hsum]
          exact G.overlap_walk u v huv rest' hwalk_rest)
        (hwAB_A := hwAB_A)
        (hwAB_B := hwAB_B)
        (hxA := hxA)
        (hyB := hyB)
      -- LHS: G.varBluntSpell (u :: v :: rest')
      --    = G.bluntSeq u ++ G.varBluntSpell (v :: rest')
      -- RHS: middle (G.varSpell (u :: v :: rest') hwalk) (leftTrim u) (rightTrim last)
      --    = middle (G.seq u ++ (G.varSpell (v :: rest') hwalk_rest).drop o) (leftTrim u) (rightTrim last)
      rw [varBluntSpell_cons]
      rw [IH]
      -- After IH, goal has G.leftTrim ((v :: rest').head ⋯) = G.leftTrim v
      -- (definitionally) and G.rightTrim of the last node.
      show G.bluntSeq u
            ++ middle (G.varSpell (v :: rest') hwalk_rest) (G.leftTrim v)
                 (G.rightTrim ((v :: rest').getLast (by simp))) = _
      unfold bluntSeq
      rw [varSpell_cons_cons]
      -- Now apply the sandwich lemma. `key` has the right shape.
      rw [← hsum] at *
      exact key

/-- **Variable analogue of `bluntSpell_eq_spell_of_boundary`.** When the
    walk's first node has zero left-trim and the last has zero
    right-trim (e.g. they sit at the boundary of the graph with no
    incident edge on the relevant side), the bluntified spelling
    exactly equals the variable-overlap spelling.

    The "no incident edge ⇒ zero trim" condition isn't structural at
    the `VarDeBruijnGraph` level (it would be at the GFA layer where
    `rightOverlap`/`leftOverlap` HashMaps return 0 for missing entries),
    so this corollary takes the per-side zero trims as hypotheses. -/
theorem varBluntSpell_eq_varSpell_of_boundary
    (G : VarDeBruijnGraph α)
    (vs : List (Fin G.numNodes)) (hne : vs ≠ [])
    (hwalk : G.isWalk vs)
    (h_left  : G.leftTrim  (vs.head    hne) = 0)
    (h_right : G.rightTrim (vs.getLast hne) = 0) :
    G.varBluntSpell vs = G.varSpell vs hwalk := by
  have heq := G.varBluntSpell_eq_middle_varSpell vs hwalk hne
  rw [heq, h_left, h_right, middle_zero_zero]

end VarDeBruijnGraph

/-! ## Bidirected variable-overlap layer

`VarBidirectedDeBruijnGraph α` extends the variable-overlap directed
structure to the bidirected setting (per `Bluntg.Bidirected`'s
uniform-`k` story). The per-edge overlap `edgeOverlap u su v sv h`
attaches to the bidirected edge identified by both endpoints and
their incident-side flags. The overlap invariant is stated against
`readSeqAux` so it works in either orientation.

The directed doubling map (analogue of `BidirectedDeBruijnGraph.toDirected`)
produces a `VarDeBruijnGraph α`: each bidirected node `v` becomes two
directed nodes `(v, +)` and `(v, -)`, with the per-edge overlap
inherited from the bidirected edge. The proof that the directed
overlap invariant follows from the bidirected one is the variable
analogue of `BidirectedDeBruijnGraph.toDirected.overlap`. -/

/-- A bidirected variable-overlap De Bruijn graph.

    Each directed image of a bidirected node `(v, o)` has its own
    `leftTrim` and `rightTrim` (functions of both `v` and `o`),
    because the bidirected doubling sends the `+` and `-` sides of
    `v` to two distinct directed nodes. -/
structure VarBidirectedDeBruijnGraph (α : Type _) where
  numNodes : Nat
  seq      : Fin numNodes → List α
  revComp  : α → α
  hasEdge  : Fin numNodes → Orient → Fin numNodes → Orient → Bool
  /-- Per-bidirected-edge overlap length. -/
  edgeOverlap :
    ∀ u suS v svS, hasEdge u suS v svS = true → Nat
  /-- Per-(node, orientation) left-side trim of the directed image. -/
  leftTrim  : Fin numNodes → Orient → Nat
  /-- Per-(node, orientation) right-side trim of the directed image. -/
  rightTrim : Fin numNodes → Orient → Nat
  revComp_revComp : ∀ a, revComp (revComp a) = a
  edge_symm : ∀ u suS v svS,
    hasEdge u suS v svS = hasEdge v svS u suS
  overlap :
    ∀ u suS v svS (h : hasEdge u suS v svS = true),
      Suffix (readSeqAux (seq u) revComp suS) (edgeOverlap u suS v svS h) =
        Prefix (readSeqAux (seq v) revComp svS.flip) (edgeOverlap u suS v svS h)
  /-- The two per-side trims at each bidirected edge sum to the
      per-edge overlap. The relevant directed-edge endpoints are
      determined by the orientation flags: the source's *exit* side
      is its `suS`-side (which becomes the right side of the directed
      image `(u, suS)`), and the target's *entry* side is its
      `svS.flip`-side (which becomes the left side of the directed
      image `(v, svS.flip)`). -/
  trim_eq :
    ∀ u suS v svS (h : hasEdge u suS v svS = true),
      rightTrim u suS + leftTrim v svS.flip = edgeOverlap u suS v svS h
  trim_lt_len  : ∀ v o, leftTrim v o + rightTrim v o < (seq v).length
  edge_le_src :
    ∀ u suS v svS (h : hasEdge u suS v svS = true),
      edgeOverlap u suS v svS h ≤ (seq u).length
  edge_le_tgt :
    ∀ u suS v svS (h : hasEdge u suS v svS = true),
      edgeOverlap u suS v svS h ≤ (seq v).length

namespace VarBidirectedDeBruijnGraph

variable {α : Type _}

/-- Read a node in a given orientation (mirrors
    `BidirectedDeBruijnGraph.readSeq`). -/
def readSeq (G : VarBidirectedDeBruijnGraph α) (v : Fin G.numNodes)
    (o : Orient) : List α :=
  readSeqAux (G.seq v) G.revComp o

@[simp] theorem readSeq_length (G : VarBidirectedDeBruijnGraph α)
    (v : Fin G.numNodes) (o : Orient) :
    (G.readSeq v o).length = (G.seq v).length := by
  simp [readSeq]

/-- Doubled node count: each bidirected node `v` lifts to `(v, +)` and
    `(v, -)`. -/
def doubledNumNodes (G : VarBidirectedDeBruijnGraph α) : Nat :=
  2 * G.numNodes

/-- Pack `(v, o)` into a doubled-graph index. -/
def encode (G : VarBidirectedDeBruijnGraph α) (v : Fin G.numNodes)
    (o : Orient) : Fin G.doubledNumNodes :=
  match o with
  | .plus  => ⟨v.val, by
      unfold doubledNumNodes; have := v.isLt; omega⟩
  | .minus => ⟨G.numNodes + v.val, by
      unfold doubledNumNodes; have := v.isLt; omega⟩

/-- Decode a doubled-graph index. -/
def decode (G : VarBidirectedDeBruijnGraph α)
    (ix : Fin G.doubledNumNodes) : Fin G.numNodes × Orient :=
  if h : ix.val < G.numNodes then
    (⟨ix.val, h⟩, .plus)
  else
    (⟨ix.val - G.numNodes, by
        have := ix.isLt; unfold doubledNumNodes at this; omega⟩,
     .minus)

theorem decode_encode (G : VarBidirectedDeBruijnGraph α)
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

/-! ### The doubled directed graph

  We lower a `VarBidirectedDeBruijnGraph` to a `VarDeBruijnGraph`. The
  doubled graph has `2 * numNodes` directed nodes; each bidirected
  edge `(u, su) — (v, sv)` becomes a directed edge from the encoded
  `(u, su)` node to the encoded `(v, sv.flip)` node, carrying the same
  per-edge overlap.

  This is the **variable-overlap doubling lemma**: it lifts the
  variable-overlap directed `varBluntSpell_eq_middle_varSpell` to the
  bidirected setting via `toDirected`. -/

/-- The doubled directed graph (variable-overlap analogue of
    `BidirectedDeBruijnGraph.toDirected`). Mirrors the directed-graph
    construction but threads the per-edge overlap from the bidirected
    layer through to the directed layer. -/
def toDirected (G : VarBidirectedDeBruijnGraph α) : VarDeBruijnGraph α where
  numNodes := G.doubledNumNodes
  seq := fun ix =>
    let p := G.decode ix
    G.readSeq p.1 p.2
  hasEdge := fun ix iy =>
    let p := G.decode ix
    let q := G.decode iy
    G.hasEdge p.1 p.2 q.1 q.2.flip
  edgeOverlap := fun ix iy h_edge =>
    G.edgeOverlap (G.decode ix).1 (G.decode ix).2
                  (G.decode iy).1 (G.decode iy).2.flip h_edge
  leftTrim := fun ix =>
    let p := G.decode ix
    G.leftTrim p.1 p.2
  rightTrim := fun ix =>
    let p := G.decode ix
    G.rightTrim p.1 p.2
  overlap := fun ix iy h_edge => by
    -- Mirrors the uniform-`k` proof, with `k - 1` replaced by the
    -- per-edge `edgeOverlap (decode ix).1 ...`. The flip on the
    -- target orientation comes from how the doubled graph encodes
    -- bidirected edges (incoming side vs entering side).
    have hb := G.overlap (G.decode ix).1 (G.decode ix).2
                          (G.decode iy).1 (G.decode iy).2.flip h_edge
    simp [Orient.flip_flip] at hb
    show Suffix (G.readSeq _ _) _ = Prefix (G.readSeq _ _) _
    simp [readSeq]
    exact hb
  trim_eq := fun ix iy h_edge => by
    -- The directed `rightTrim u + leftTrim v = edgeOverlap u v h`
    -- unwraps cleanly via `G.trim_eq`. The bidirected edge is
    --   G.hasEdge (decode ix).1 (decode ix).2 (decode iy).1 ((decode iy).2.flip).
    -- Setting `svS = (decode iy).2.flip`, we have `svS.flip = (decode iy).2`,
    -- so `G.trim_eq` yields:
    --   G.rightTrim (decode ix).1 (decode ix).2
    --     + G.leftTrim  (decode iy).1 (decode iy).2 = edgeOverlap …
    -- which is exactly the directed trim_eq goal (modulo `flip_flip`).
    have hb := G.trim_eq (G.decode ix).1 (G.decode ix).2
                          (G.decode iy).1 (G.decode iy).2.flip h_edge
    simp only [Orient.flip_flip] at hb
    exact hb
  trim_lt_len := fun ix => by
    show G.leftTrim _ _ + G.rightTrim _ _ < _
    rw [readSeq_length]
    exact G.trim_lt_len (G.decode ix).1 (G.decode ix).2
  edge_le_src := fun ix iy h_edge => by
    show G.edgeOverlap _ _ _ _ h_edge ≤ _
    rw [readSeq_length]
    exact G.edge_le_src _ _ _ _ h_edge
  edge_le_tgt := fun ix iy h_edge => by
    show G.edgeOverlap _ _ _ _ h_edge ≤ _
    rw [readSeq_length]
    exact G.edge_le_tgt _ _ _ _ h_edge

/-- **Variable-overlap bidirected doubling lemma.** The doubled
    directed graph faithfully represents the bidirected structure:
    `(toDirected G).bluntSeq (encode v o)` equals the bidirected
    bluntified read at `(v, o)`. Combined with
    `varBluntSpell_eq_middle_varSpell` on the doubled graph, this
    gives spelling preservation for bidirected walks.

    Statement-wise this is the analogue of the uniform-`k` bidirected
    doubling lemma sketched in `Bluntg.Bidirected`'s comments — at
    the variable-overlap layer, the lemma is genuinely identity-by-
    construction because `toDirected` simply unpacks the bidirected
    `seq` / `trim` fields onto the doubled index space. -/
theorem bluntSeq_toDirected_eq
    (G : VarBidirectedDeBruijnGraph α)
    (v : Fin G.numNodes) (o : Orient) :
    (G.toDirected).bluntSeq (G.encode v o) =
      middle (G.readSeq v o) (G.leftTrim v o) (G.rightTrim v o) := by
  unfold VarDeBruijnGraph.bluntSeq
  unfold toDirected
  simp only
  rw [decode_encode]

end VarBidirectedDeBruijnGraph

end Bluntg
