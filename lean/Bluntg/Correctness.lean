/-
Correctness theorems for `bluntify`.

We work primarily with `G.bluntSpell`, which is defined directly on the
original graph and just concatenates per-node `bluntSeq` values. The
result of the actual `G.bluntify` operation gives back the same sequence
(see `bluntSpell_eq_bluntify_spell` in `Bluntg.Bluntify`).

* `bluntify_is_blunt`         — the result graph has overlap 0 (proved).
* `bluntSpell_eq_middle_spell` — for any walk `vs` in `G`,
                                 `G.bluntSpell vs =`
                                 `middle (G.spell vs) (leftTrim head) (rightTrim last)`.
* `bluntSpell_eq_spell_of_boundary` — corollary for "complete" walks: when the
                                 head has no incoming edge and the last
                                 has no outgoing edge, the two spellings
                                 are *equal*.

The key list-arithmetic identity `middle_concat_overlap` is proved
below by a case split on whether the left trim has crossed the
`(wL+wR)`-overlap region.
-/
import Bluntg.Bluntify

namespace Bluntg
namespace DeBruijnGraph

variable {α : Type _} {k : Nat}

/-! ### Blunt-edge invariant of the result -/

/-- The bluntified graph really is blunt: every edge has zero overlap. -/
theorem bluntify_is_blunt (G : DeBruijnGraph α k) (hk : 1 ≤ k) :
    ∀ u v, (G.bluntify hk).hasEdge u v = true →
      Suffix ((G.bluntify hk).seq u) 0 = Prefix ((G.bluntify hk).seq v) 0 := by
  intro u v _
  simp [Suffix, Prefix]

/-! ### Spelling identities for the original graph -/

/-- The spell of `u :: v :: rest` written recursively in terms of
    `spell (v :: rest)`. -/
theorem spell_cons_cons
    (G : DeBruijnGraph α k) (hk : 1 ≤ k)
    (u v : Fin G.numNodes) (rest : List (Fin G.numNodes)) :
    G.spell (u :: v :: rest) =
      G.seq u ++ (G.spell (v :: rest)).drop (k - 1) := by
  rw [spell_cons, spellTail_cons, spell_cons]
  have hlen : k - 1 ≤ (G.seq v).length := by
    have := G.seq_len v; omega
  rw [List.drop_append_of_le_length hlen]

theorem spell_length_ge
    (G : DeBruijnGraph α k) (hk : 1 ≤ k)
    (v : Fin G.numNodes) (rest : List (Fin G.numNodes)) :
    k - 1 ≤ (G.spell (v :: rest)).length := by
  rw [spell_cons, List.length_append]
  have := G.seq_len v; omega

/-- The overlap invariant restated for walks. -/
theorem overlap_walk
    (G : DeBruijnGraph α k) (hk : 1 ≤ k)
    (u v : Fin G.numNodes) (h : G.hasEdge u v = true)
    (rest : List (Fin G.numNodes)) :
    (G.seq u).drop ((G.seq u).length - (k - 1)) =
      (G.spell (v :: rest)).take (k - 1) := by
  have hov := G.overlap u v h
  unfold Suffix Prefix at hov
  rw [hov, spell_cons, List.take_append_of_le_length]
  have := G.seq_len v; omega

/-! ### Sandwich lemma (key list-arithmetic step)

For lists `A` and `B` whose `wL + wR`-overlap agrees (last `wL+wR` of `A`
= first `wL+wR` of `B`), splicing the bluntified windows together yields
a window of their overlap-merged concatenation:

  middle A x wR ++ middle B wL y = middle (A ++ B.drop (wL + wR)) x y

Element-wise sketch (verified on paper):

  • For `i ∈ [0, |A| - x - wR)`, both sides read from `A` at position `x+i`.
  • For `i ∈ [|A| - x - wR, |A| - x)`, the LHS reads from `B` at position
    `wL + (i - (|A| - x - wR))`, the RHS continues reading `A` at `x + i`.
    These agree because `A[|A| - (wL+wR) + j] = B[j]` for `j ∈ [0, wL+wR)`,
    applied at `j = wL + (i - (|A| - x - wR))`.
  • For `i ≥ |A| - x`, the RHS reads `B.drop (wL+wR)` at `i - (|A|-x)`,
    i.e. `B[(wL+wR) + i - (|A|-x)]`. The LHS reads `B[wL + (i - (|A|-x-wR))]
    = B[(wL+wR) + i - (|A|-x)]`. They agree.

This is a list-induction-only proof; it has no dependency on the rest
of the development. -/
theorem middle_concat_overlap
    {β : Type _} (A B : List β) (x y wL wR : Nat)
    (h_overlap : A.drop (A.length - (wL + wR)) = B.take (wL + wR))
    (hwAB_A : wL + wR ≤ A.length)
    (hwAB_B : wL + wR ≤ B.length)
    (hxA  : x + wR ≤ A.length)
    (hyB  : wL + y ≤ B.length) :
    middle A x wR ++ middle B wL y =
      middle (A ++ B.drop (wL + wR)) x y := by
  -- Rewrite the merged concatenation via the overlap helper.
  rw [append_drop_eq_take_append A B (wL + wR) h_overlap]
  unfold middle
  -- Length of the merged sequence.
  have hLen : (A.take (A.length - (wL + wR)) ++ B).length =
              (A.length - (wL + wR)) + B.length := by
    rw [List.length_append, List.length_take]
    have : min (A.length - (wL + wR)) A.length = A.length - (wL + wR) :=
      Nat.min_eq_left (Nat.sub_le _ _)
    omega
  rw [hLen]
  by_cases hx : x + (wL + wR) ≤ A.length
  · -- Case 1: x is within the non-overlap prefix of A.
    -- RHS reductions.
    have hxleTake : x ≤ (A.take (A.length - (wL + wR))).length := by
      rw [List.length_take]
      have : min (A.length - (wL + wR)) A.length = A.length - (wL + wR) :=
        Nat.min_eq_left (Nat.sub_le _ _)
      omega
    rw [List.drop_append_of_le_length hxleTake]
    -- (A.take (n - w)).drop x = (A.drop x).take (n - w - x)
    have hTakeDrop : (A.take (A.length - (wL + wR))).drop x =
                     (A.drop x).take (A.length - (wL + wR) - x) :=
      List.drop_take
    rw [hTakeDrop]
    -- LHS first half: (A.drop x).take (n - x - wR)
    --                = (A.drop x).take (n - w - x) ++ B.take wL  (via overlap)
    have hxSum : A.length - x - wR = (A.length - (wL + wR) - x) + wL := by omega
    have hLHSfirst :
        (A.drop x).take (A.length - x - wR) =
        (A.drop x).take (A.length - (wL + wR) - x) ++ B.take wL := by
      rw [hxSum, List.take_add]
      -- now: (A.drop x).take (n - w - x) ++ ((A.drop x).drop (n - w - x)).take wL
      --    = (A.drop x).take (n - w - x) ++ B.take wL
      have h_drop_drop : (A.drop x).drop (A.length - (wL + wR) - x) =
                         A.drop (A.length - (wL + wR)) := by
        rw [List.drop_drop]
        congr 1; omega
      rw [h_drop_drop, h_overlap, List.take_take]
      have : min wL (wL + wR) = wL := Nat.min_eq_left (Nat.le_add_right _ _)
      rw [this]
    rw [hLHSfirst]
    -- Merge B.take wL ++ (B.drop wL).take (m - wL - y) = B.take (m - y).
    have hLHSmerge :
        B.take wL ++ (B.drop wL).take (B.length - wL - y) =
        B.take (B.length - y) := by
      have hsum : B.length - y = wL + (B.length - wL - y) := by omega
      rw [hsum, List.take_add]
    rw [List.append_assoc, hLHSmerge]
    -- RHS take: ((A.drop x).take (n - w - x) ++ B).take ((n - w + m) - x - y)
    --         = (A.drop x).take (n - w - x) ++ B.take (m - y)
    rw [List.take_append, List.length_take, List.length_drop]
    have hmin1 :
        min (A.length - (wL + wR) - x) (A.length - x) = A.length - (wL + wR) - x :=
      Nat.min_eq_left (by omega)
    rw [hmin1]
    -- The two `take`s on the right need to simplify.
    rw [List.take_take]
    have hmin2 :
        min (A.length - (wL + wR) + B.length - x - y) (A.length - (wL + wR) - x) =
        A.length - (wL + wR) - x :=
      Nat.min_eq_right (by omega)
    rw [hmin2]
    -- and the B.take argument simplifies via omega
    have hBtake :
        A.length - (wL + wR) + B.length - x - y - (A.length - (wL + wR) - x) =
        B.length - y := by omega
    rw [hBtake]
  · -- Case 2: x has crossed into the overlap region of A.
    -- We have x > n - w. Set s := x - (n - w); s satisfies 0 < s ≤ wL.
    have hx_gt : A.length - (wL + wR) < x := by omega
    -- Drop on the merged sequence: the take part contributes nothing.
    have h_first_le : (A.take (A.length - (wL + wR))).length ≤ x := by
      rw [List.length_take]
      have : min (A.length - (wL + wR)) A.length = A.length - (wL + wR) :=
        Nat.min_eq_left (Nat.sub_le _ _)
      omega
    rw [List.drop_append, List.drop_eq_nil_of_le h_first_le, List.nil_append]
    -- Now goal:
    --   (A.drop x).take (n - x - wR) ++ (B.drop wL).take (m - wL - y)
    --   = (B.drop (x - |A.take (n - w)|)).take ((n - w + m) - x - y)
    -- Simplify |A.take (n - w)| = n - w.
    have hTakeLen : (A.take (A.length - (wL + wR))).length = A.length - (wL + wR) := by
      rw [List.length_take]
      exact Nat.min_eq_left (Nat.sub_le _ _)
    rw [hTakeLen]
    -- Express A.drop x via overlap: A.drop x = (B.take w).drop s.
    have hAdrop_x_eq :
        A.drop x = (B.take (wL + wR)).drop (x - (A.length - (wL + wR))) := by
      rw [show A.drop x
            = (A.drop (A.length - (wL + wR))).drop
                (x - (A.length - (wL + wR))) from by
          rw [List.drop_drop]; congr 1; omega]
      rw [h_overlap]
    rw [hAdrop_x_eq]
    -- (B.take w).drop s = (B.drop s).take (w - s).
    rw [List.drop_take]
    -- ((B.drop s).take (w - s)).take (n - x - wR) = (B.drop s).take (min (n - x - wR) (w - s))
    rw [List.take_take]
    -- The min equals wL - s.
    have hmin_LHS_first :
        min (A.length - x - wR) (wL + wR - (x - (A.length - (wL + wR)))) =
        wL - (x - (A.length - (wL + wR))) := by
      have : wL - (x - (A.length - (wL + wR))) ≤ A.length - x - wR := by omega
      have : wL - (x - (A.length - (wL + wR))) ≤
             wL + wR - (x - (A.length - (wL + wR))) := by omega
      omega
    rw [hmin_LHS_first]
    -- LHS second half: B.drop wL = (B.drop s).drop (wL - s).
    have h_split_wL :
        B.drop wL = (B.drop (x - (A.length - (wL + wR)))).drop
                      (wL - (x - (A.length - (wL + wR)))) := by
      rw [List.drop_drop]
      congr 1
      omega
    rw [h_split_wL]
    -- LHS: (B.drop s).take (wL - s) ++ ((B.drop s).drop (wL - s)).take (m - wL - y)
    --    = (B.drop s).take ((wL - s) + (m - wL - y))
    rw [← List.take_add]
    -- (wL - s) + (m - wL - y) = m - s - y.
    have h_simplify_amt :
        (wL - (x - (A.length - (wL + wR)))) + (B.length - wL - y) =
        A.length - (wL + wR) + B.length - x - y := by
      omega
    rw [h_simplify_amt]

/-! ### Path-preservation theorem (working with `bluntSpell`) -/

/-- **Path preservation.** For any non-empty walk `vs` in `G`, the
    bluntified spelling is the middle window of the original spelling,
    trimmed by `leftTrim` at the head and `rightTrim` at the last. -/
theorem bluntSpell_eq_middle_spell
    (G : DeBruijnGraph α k) (hk : 1 ≤ k) :
    ∀ vs : List (Fin G.numNodes), G.isWalk vs → ∀ (hne : vs ≠ []),
      G.bluntSpell vs =
        middle (G.spell vs)
          (G.leftTrim (vs.head hne))
          (G.rightTrim (vs.getLast hne)) := by
  intro vs
  induction vs with
  | nil => intro _ hne; exact (hne rfl).elim
  | cons u rest ih =>
    intro hwalk hne
    cases rest with
    | nil =>
      -- Base case: walk is [u].
      show G.bluntSpell [u] = middle (G.spell [u]) _ _
      rw [bluntSpell_cons, bluntSpell_nil, List.append_nil, spell_singleton]
      rfl
    | cons v rest' =>
      -- Inductive case: walk is u :: v :: rest'.
      have huv : G.hasEdge u v = true := hwalk.1
      have hwalk_rest : G.isWalk (v :: rest') := hwalk.2
      have hin_v : G.hasIn v = true := by
        rw [hasIn_iff]; exact ⟨u, huv⟩
      have hlt_v : G.leftTrim v = (k - 1) / 2 := by
        unfold leftTrim; simp [hin_v]
      have hout_u : G.hasOut u = true := by
        rw [hasOut_iff]; exact ⟨v, huv⟩
      have hrt_u : G.rightTrim u = k / 2 := by
        unfold rightTrim; simp [hout_u]
      have IH := ih hwalk_rest (by simp)
      -- Compute head/getLast of the larger walk.
      have hhead : (u :: v :: rest').head hne = u := rfl
      have hlast : (u :: v :: rest').getLast hne =
                   (v :: rest').getLast (by simp) := by
        simp [List.getLast]
      rw [hhead, hlast]
      -- Apply the sandwich lemma.
      have hsum : (k - 1) / 2 + k / 2 = k - 1 := by omega
      have key := middle_concat_overlap
        (β := α)
        (A := G.seq u)
        (B := G.spell (v :: rest'))
        (x := G.leftTrim u)
        (y := G.rightTrim ((v :: rest').getLast (by simp)))
        (wL := (k - 1) / 2)
        (wR := k / 2)
        (h_overlap := by rw [hsum]; exact G.overlap_walk hk u v huv rest')
        (hwAB_A := by rw [hsum]; have := G.seq_len u; omega)
        (hwAB_B := by rw [hsum]; exact G.spell_length_ge hk v rest')
        (hxA := by have := G.seq_len u; have := G.leftTrim_le u; omega)
        (hyB := by
          have := G.spell_length_ge hk v rest'
          have := G.rightTrim_le ((v :: rest').getLast (by simp))
          omega)
      rw [hsum] at key
      -- LHS: G.bluntSpell (u :: v :: rest') = G.bluntSeq u ++ G.bluntSpell (v :: rest')
      -- RHS: middle (G.spell (u :: v :: rest')) (G.leftTrim u) (...)
      --    = middle (G.seq u ++ (G.spell (v :: rest')).drop (k-1)) (G.leftTrim u) (...)
      rw [bluntSpell_cons]
      rw [IH]
      -- After IH, the goal has `G.leftTrim ((v :: rest').head ⋯)`. This is
      -- definitionally `G.leftTrim v` (since `head (v :: _) = v`), so we
      -- reshape the goal explicitly.
      show G.bluntSeq u
            ++ middle (G.spell (v :: rest')) (G.leftTrim v)
                 (G.rightTrim ((v :: rest').getLast (by simp))) = _
      rw [hlt_v]
      unfold bluntSeq
      rw [hrt_u]
      rw [spell_cons_cons G hk u v rest']
      exact key

/-- **Boundary corollary.** When the walk starts at a node with no
    incoming edge and ends at a node with no outgoing edge in `G`, the
    bluntified spelling exactly equals the original spelling. -/
theorem bluntSpell_eq_spell_of_boundary
    (G : DeBruijnGraph α k) (hk : 1 ≤ k)
    (vs : List (Fin G.numNodes)) (hne : vs ≠ [])
    (hwalk : G.isWalk vs)
    (h_left  : G.hasIn  (vs.head hne)    = false)
    (h_right : G.hasOut (vs.getLast hne) = false) :
    G.bluntSpell vs = G.spell vs := by
  have heq := G.bluntSpell_eq_middle_spell hk vs hwalk hne
  have hlt : G.leftTrim (vs.head hne) = 0 := by
    unfold leftTrim; simp [h_left]
  have hrt : G.rightTrim (vs.getLast hne) = 0 := by
    unfold rightTrim; simp [h_right]
  rw [heq, hlt, hrt, middle_zero_zero]

/-- Same theorem stated for the actual bluntified graph. -/
theorem spell_eq_middle_spell
    (G : DeBruijnGraph α k) (hk : 1 ≤ k)
    (vs : List (Fin G.numNodes)) (hwalk : G.isWalk vs) (hne : vs ≠ []) :
    (G.bluntify hk).spell vs =
      middle (G.spell vs)
        (G.leftTrim (vs.head hne))
        (G.rightTrim (vs.getLast hne)) := by
  rw [← G.bluntSpell_eq_bluntify_spell hk vs]
  exact G.bluntSpell_eq_middle_spell hk vs hwalk hne

end DeBruijnGraph
end Bluntg
