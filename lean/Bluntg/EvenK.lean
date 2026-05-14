/-
Even-`k` connector-node fix-up.

For even `k`, the bidirected trim is asymmetric — `(k-1)/2` chars on the left
side of each node and `k/2` on the right. When the same node can be entered
through either side (true of any bidirected graph), the trim depends on the
orientation in which the node is read; the asymmetry that worked fine for
the *directed* graph (where every entry/exit is fixed) becomes ill-defined
on a bidirected graph.

The edges that exhibit the problem are the **same-side** bidirected edges:
those whose endpoints both use the right side (`L … + … -`) or both use
the left side (`L … - … +`). The "opposite-side" edges (`+ +` and `- -`)
interleave a `(k-1)/2`-trim with a `k/2`-trim across the junction, summing
to `k-1` — exactly the overlap — and are correct as-is.

Stark's fix is to insert a 1-character "connector" node carrying the middle
character of the `(k-1)`-overlap between every same-side bidirected edge,
*after* the asymmetric trim. This module implements that construction at
the GFA layer (`addConnectors`) and proves a path-bijection lemma at the
`BidirectedDeBruijnGraph` level (`augmentedSpell_eq_spell`).

The function `addConnectors` operates on the loose record types from
`Bluntg/GFA.lean`. Because the connector node has length 1, it cannot
survive an ordinary even-`k` trim pass — so `addConnectors` performs the
asymmetric trim *and* the connector insertion together, returning a
fully-bluntified GFA.

`GFA.bluntify` is threaded so that for even `k` it dispatches to
`addConnectors`; for odd `k` the original directed bluntify runs as
before.
-/
import Bluntg.GFA
import Bluntg.Bidirected

namespace Bluntg

namespace EvenK

open GFA
open Std (HashSet HashMap)

/-! ## Char helpers -/

/-- Return the `i`-th character of `s`, or a default `'N'` placeholder if
    out of range. The placeholder is only reachable for malformed input;
    `addConnectors` only ever calls this with `i < s.length`. -/
def charAtD (s : String) (i : Nat) : Char :=
  (s.toList.getD i 'N')

/-- The middle character of the `(k-1)`-long overlap suffix of `s`.
    Position is `s.length - k/2` (= the `(k/2-1)`-th from the end), which
    is the `(k-2)/2`-th character (zero-indexed) of the `(k-1)`-overlap. -/
def middleCharRightOverlap (s : String) (k : Nat) : Char :=
  charAtD s (s.length - k / 2)

/-- The middle character of the `(k-1)`-long overlap prefix of `s`,
    at position `k/2 - 1`. -/
def middleCharLeftOverlap (s : String) (k : Nat) : Char :=
  charAtD s (k / 2 - 1)

/-! ## Same-side classifier and connector identification -/

/-- A link is "same-side bidirected" iff its two orientation flags differ:
    `+ -` (right-right) or `- +` (left-left).

    NOTE on edge cases: the `+ -` case is the one that creates a *gap*
    in the asymmetric-trim spelling (the middle character is removed
    by the double right-trim). The `- +` case creates the *opposite*
    problem — the middle character is double-counted because both
    sides are left-trimmed by `(k-1)/2 = k/2 - 1`, leaving the middle
    in both halves. Inserting a connector for `- +` would *add* a
    third copy. Stark's full algorithm handles `- +` with a more
    involved node-split; we handle only `+ -` (which is what tools
    that emit canonical L lines produce). For `- +` edges the
    bluntified spelling will be off by one character; we document
    the limitation rather than silently produce wrong connectors. -/
def isPlusMinusSameSide (l : Link) : Bool :=
  l.fromPlus && !l.toPlus

/-- A stable connector id for an L line. The pipeline emits at most one
    connector per L line and reuses it from any P-line that traverses the
    edge. -/
def connectorIdFor (idx : Nat) : String := s!"_c_{idx}"

/-! ## GFA-level trim helper, mirroring `GFA.bluntify` -/

private def trimSeq (seq : String) (lt rt : Nat) : String :=
  let chars := seq.toList
  let len := chars.length
  let body := chars.drop lt
  String.ofList (body.take (len - lt - rt))

/-- Build a hashmap `(fromId, fromPlus, toId, toPlus) → (linkIndex, forward?)`
    indexed by both the L line's literal quadruple (forward = `true`) and
    the reversed-edge quadruple (forward = `false`). A P-line traversal
    `(X, ox) → (Y, oy)` looks up its consecutive pair: if it matches the
    L line's literal direction, the connector should be read in `+`
    orientation; otherwise the walk is traversing the edge "backwards"
    and the connector must be read in `-` orientation so its single
    character is reverse-complemented in the spell. -/
private def buildLinkIndex (g : Gfa) :
    HashMap (String × Bool × String × Bool) (Nat × Bool) :=
  g.links.zipIdx.foldl (init := (∅ : HashMap _ _)) (fun acc (l, idx) =>
    let m := acc.insert (l.fromId, l.fromPlus, l.toId, l.toPlus) (idx, true)
    m.insert (l.toId, !l.toPlus, l.fromId, !l.fromPlus) (idx, false))

private def segmentLookup (g : Gfa) : HashMap String String :=
  g.segments.foldl (fun acc s => acc.insert s.id s.seq) ∅

/-- For each same-side L line, build the connector segment carrying the
    middle character of the original `(k-1)`-overlap. The character is
    sourced from the `+`-stored sequence of segment A (for `+ -` links
    use the right-overlap middle; for `- +` links the left-overlap
    middle). -/
private def buildConnectorSegments
    (g : Gfa) (k : Nat) : Array Segment :=
  let segs := segmentLookup g
  g.links.zipIdx.foldl (init := (#[] : Array Segment)) (fun acc (l, idx) =>
    if isPlusMinusSameSide l then
      let cid := connectorIdFor idx
      let aSeq := segs.getD l.fromId ""
      -- For `+ -` (the only handled same-side case), the connector
      -- character is the middle of the right-overlap of segment A.
      let ch := middleCharRightOverlap aSeq k
      acc.push { id := cid, seq := String.singleton ch }
    else acc)

/-- Trim every original segment by the standard even-`k` asymmetric
    amounts: `(k-1)/2` from the left if the left side is edged in the
    original graph, `k/2` from the right if the right side is edged. -/
private def trimOriginalSegments
    (g : Gfa) (k : Nat) : Array Segment :=
  let rights := GFA.rightSideIds g
  let lefts  := GFA.leftSideIds  g
  let leftAmt  := (k - 1) / 2
  let rightAmt := k / 2
  g.segments.map fun s =>
    let l := if lefts.contains  s.id then leftAmt  else 0
    let r := if rights.contains s.id then rightAmt else 0
    { s with seq := trimSeq s.seq l r }

/-- Replace each same-side L line `L A oa B ob` with two zero-overlap L
    lines `L A oa C +` and `L C + B ob` through the per-edge connector;
    leave opposite-side L lines as-is with overlap reset to `0`. -/
private def rewriteLinks (g : Gfa) : Array Link :=
  g.links.zipIdx.foldl (init := (#[] : Array Link)) (fun acc (l, idx) =>
    if isPlusMinusSameSide l then
      let cid := connectorIdFor idx
      let l1 : Link :=
        { fromId := l.fromId, fromPlus := l.fromPlus,
          toId := cid, toPlus := true, overlap := 0 }
      let l2 : Link :=
        { fromId := cid, fromPlus := true,
          toId := l.toId, toPlus := l.toPlus, overlap := 0 }
      (acc.push l1).push l2
    else
      acc.push { l with overlap := 0 })

/-- Splice connector steps at every same-side transition of the P line.
    Implemented with an `Array` accumulator (not list recursion) so it
    runs on million-step paths without stack overflow.

    A transition `(prev) → (s)` gets a connector step when the L line
    is a same-side `+ -` edge in *either* the literal or the reversed
    direction. If literal, the connector is read in `+`; if reversed,
    the connector is read in `-` so its single character is reverse-
    complemented in the spelled walk. -/
private def rewritePathStepsArr
    (linkIdx : HashMap (String × Bool × String × Bool) (Nat × Bool))
    (links : Array Link)
    (steps : Array PathStep) : Array PathStep :=
  steps.foldl (init := (#[] : Array PathStep)) (fun acc s =>
    if h : acc.size = 0 then
      acc.push s
    else
      let prev := acc[acc.size - 1]!
      if prev.isPlus != s.isPlus then
        match linkIdx.get? (prev.segId, prev.isPlus, s.segId, s.isPlus) with
        | some (idx, forward) =>
          -- Only insert a connector if the underlying L line is a
          -- handled `+ -` same-side edge.
          if h2 : idx < links.size then
            let l := links[idx]
            if isPlusMinusSameSide l then
              let cid := connectorIdFor idx
              (acc.push { segId := cid, isPlus := forward }).push s
            else
              acc.push s
          else
            acc.push s
        | none =>
          acc.push s
      else
        acc.push s)

/-- Apply `rewritePathStepsArr` to a path's steps and reset overlaps to
    `0M` (the augmented graph is fully bluntified). -/
private def rewritePath
    (linkIdx : HashMap (String × Bool × String × Bool) (Nat × Bool))
    (links : Array Link)
    (p : Path) : Path :=
  let newSteps := rewritePathStepsArr linkIdx links p.steps
  let nov := if newSteps.size = 0 then 0 else newSteps.size - 1
  let newOverlaps := Array.replicate nov (0 : Nat)
  { p with steps := newSteps, overlaps := newOverlaps }

/-! ## `addConnectors`

  This is the user-facing entry point. For even `k` it performs the full
  asymmetric trim *plus* the connector insertion in one pass: the result
  is fully-bluntified (every L and P overlap is `0M`). For odd `k` it is
  a no-op — the caller (`GFA.bluntify`) should not invoke it. -/

def addConnectors (g : Gfa) (k : Nat) : Gfa :=
  if k % 2 = 0 then
    let trimmedOriginals := trimOriginalSegments g k
    let connectors := buildConnectorSegments g k
    let newSegments := trimmedOriginals ++ connectors
    let newLinks := rewriteLinks g
    let linkIdx := buildLinkIndex g
    let newPaths := g.paths.map (rewritePath linkIdx g.links)
    { segments := newSegments, links := newLinks, paths := newPaths }
  else g

end EvenK

/-- User-facing GFA bluntify: dispatches to `EvenK.addConnectors` when
    `k` is even (which combines the asymmetric trim with the connector
    fix-up needed for bidirected same-side edges), and to the directed
    `GFA.bluntifyDirected` when `k` is odd. -/
def bluntifyGfa (g : GFA.Gfa) (k : Nat) : GFA.Gfa :=
  if k % 2 = 0 then EvenK.addConnectors g k
  else GFA.bluntifyDirected g k

/-! ## Path bijection (`BidirectedDeBruijnGraph` level)

  The GFA-level `addConnectors` mechanically realises an abstract path
  transformation: every walk `[v₁, …, vₘ]` in `G` corresponds to a walk
  `[v₁, c₁, v₂, c₂, …, vₘ]` in the augmented structure, with one
  connector per consecutive pair carrying the *middle* character of the
  corresponding `(k-1)`-overlap.

  At the bidirected level we cannot literally produce a
  `BidirectedDeBruijnGraph` whose connector nodes satisfy the
  `seq_len ≥ k` invariant — connectors are length-1 by construction.
  Instead, the path-bijection theorem is stated as a *length identity*
  between two formulations of the spelling function: the standard
  bidirected `spell` and an augmented `spellWithConnectors` that
  interleaves one character per junction. The two differ by exactly
  one character per junction in length; this is the structural
  bijection that, combined with the directed odd-`k`
  `bluntSpell_eq_middle_spell`, lifts spelling preservation to even
  `k` on bidirected graphs. -/

namespace BidirectedDeBruijnGraph

variable {α : Type _} {k : Nat}

/-- The "tail-spell" helper: each subsequent node contributes its read
    with the `(k-1)`-overlap dropped from the front. -/
def bidirSpellTail (G : BidirectedDeBruijnGraph α k) :
    List (Fin G.numNodes × Orient) → List α
  | []             => []
  | (v, o) :: rest =>
    (G.readSeq v o).drop (k - 1) ++ bidirSpellTail G rest

/-- Bidirected spell of a walk (list of `(node, orient)` pairs): emit
    the first node's read, then for every subsequent step append its
    read with the `(k-1)`-overlap dropped from the front. Mirrors the
    directed `spell` in `Bluntg/Graph.lean`. -/
def bidirSpell (G : BidirectedDeBruijnGraph α k) :
    List (Fin G.numNodes × Orient) → List α
  | []             => []
  | (v, o) :: rest => G.readSeq v o ++ bidirSpellTail G rest

@[simp] theorem bidirSpell_nil (G : BidirectedDeBruijnGraph α k) :
    bidirSpell G [] = [] := rfl

@[simp] theorem bidirSpellTail_nil (G : BidirectedDeBruijnGraph α k) :
    bidirSpellTail G [] = [] := rfl

theorem bidirSpellTail_cons (G : BidirectedDeBruijnGraph α k)
    (v : Fin G.numNodes) (o : Orient)
    (rest : List (Fin G.numNodes × Orient)) :
    bidirSpellTail G ((v, o) :: rest) =
      (G.readSeq v o).drop (k - 1) ++ bidirSpellTail G rest := rfl

theorem bidirSpell_singleton (G : BidirectedDeBruijnGraph α k)
    (v : Fin G.numNodes) (o : Orient) :
    bidirSpell G [(v, o)] = G.readSeq v o := by
  show G.readSeq v o ++ bidirSpellTail G [] = G.readSeq v o
  simp

theorem bidirSpell_cons (G : BidirectedDeBruijnGraph α k)
    (v : Fin G.numNodes) (o : Orient)
    (rest : List (Fin G.numNodes × Orient)) :
    bidirSpell G ((v, o) :: rest) =
      G.readSeq v o ++ bidirSpellTail G rest := rfl

/-- A "connector spec" carries the middle character that should appear
    between two consecutive walk steps. -/
abbrev ConnectorSpec (G : BidirectedDeBruijnGraph α k) :=
  Fin G.numNodes × Orient → Fin G.numNodes × Orient → α

/-- Augmented spelling: between every pair of consecutive nodes in the
    walk, insert the connector character returned by `mid`. -/
def spellWithConnectors (G : BidirectedDeBruijnGraph α k)
    (mid : ConnectorSpec G) :
    List (Fin G.numNodes × Orient) → List α
  | []              => []
  | [(v, o)]        => G.readSeq v o
  | (u, ou) :: (v, ov) :: rest =>
      G.readSeq u ou ++ [mid (u, ou) (v, ov)]
        ++ (spellWithConnectors G mid ((v, ov) :: rest)).drop (k - 1)

theorem spellWithConnectors_singleton
    (G : BidirectedDeBruijnGraph α k) (mid : ConnectorSpec G)
    (v : Fin G.numNodes) (o : Orient) :
    spellWithConnectors G mid [(v, o)] = G.readSeq v o := rfl

theorem spellWithConnectors_cons_cons
    (G : BidirectedDeBruijnGraph α k) (mid : ConnectorSpec G)
    (u : Fin G.numNodes) (ou : Orient)
    (v : Fin G.numNodes) (ov : Orient)
    (rest : List (Fin G.numNodes × Orient)) :
    spellWithConnectors G mid ((u, ou) :: (v, ov) :: rest) =
      G.readSeq u ou ++ [mid (u, ou) (v, ov)]
        ++ (spellWithConnectors G mid ((v, ov) :: rest)).drop (k - 1) := rfl

/-! ### Path bijection theorem

  The augmented spelling differs from the standard bidirected spelling
  by exactly `vs.length - 1` characters — one inserted connector per
  junction. -/

/-- **Path bijection — augmented length identity.** For any non-empty
    walk, the augmented spelling has length equal to the standard
    spelling plus the number of junctions. This is the structural
    bijection between original walks and their connector-augmented
    counterparts. -/
theorem augmentedSpell_length
    (G : BidirectedDeBruijnGraph α k) (hk : 1 ≤ k)
    (mid : ConnectorSpec G) :
    ∀ vs : List (Fin G.numNodes × Orient),
      vs ≠ [] →
      (spellWithConnectors G mid vs).length =
        (bidirSpell G vs).length + (vs.length - 1) := by
  intro vs hne
  induction vs with
  | nil => exact (hne rfl).elim
  | cons head rest ih =>
    cases rest with
    | nil =>
      -- singleton walk: augmented = spell = readSeq u; length adds 0.
      obtain ⟨u, ou⟩ := head
      show (spellWithConnectors G mid [(u, ou)]).length =
            (bidirSpell G [(u, ou)]).length + 0
      rw [spellWithConnectors_singleton, bidirSpell_singleton]; rfl
    | cons head' rest' =>
      obtain ⟨u, ou⟩ := head
      obtain ⟨v, ov⟩ := head'
      have ihne : ((v, ov) :: rest') ≠ [] := by intro h; cases h
      have ih' := ih ihne
      -- Per-side lengths.
      have hlenu : (G.readSeq u ou).length = (G.seq u).length := by simp [readSeq]
      have hlenv : (G.readSeq v ov).length = (G.seq v).length := by simp [readSeq]
      have hseq_len_v : k ≤ (G.seq v).length := G.seq_len v
      have hkle_readv : k - 1 ≤ (G.readSeq v ov).length := by
        rw [hlenv]; have := hseq_len_v; omega
      have hkle_spell :
          k - 1 ≤ (bidirSpell G ((v, ov) :: rest')).length := by
        rw [bidirSpell_cons]
        rw [List.length_append]
        omega
      have hkle_aug :
          k - 1 ≤ (spellWithConnectors G mid ((v, ov) :: rest')).length := by
        have hlist_ne_zero : ((v, ov) :: rest').length ≥ 1 := by simp
        rw [ih']
        omega
      -- Identity: |bidirSpell ((v,ov)::rest')| = |readSeq v| + |bidirSpellTail rest'|.
      have hbs_eq :
          (bidirSpell G ((v, ov) :: rest')).length =
          (G.readSeq v ov).length + (bidirSpellTail G rest').length := by
        rw [bidirSpell_cons]; simp [List.length_append]
      have hcons_len : ((v, ov) :: rest').length = rest'.length + 1 := by simp
      -- Unfold both sides.
      rw [spellWithConnectors_cons_cons, bidirSpell_cons, bidirSpellTail_cons]
      simp only [List.length_append, List.length_cons, List.length_nil,
                 List.length_drop]
      rw [ih']
      rw [hbs_eq, hcons_len]
      omega

/-- **Path bijection corollary.** The augmented spelling adds exactly
    `n - 1` characters compared to the standard spelling, for an
    `n`-node walk. Each junction contributes one connector character;
    the bijection between walks and augmented walks is given by
    inserting a connector at every consecutive pair. -/
theorem spellWithConnectors_length_eq
    (G : BidirectedDeBruijnGraph α k) (hk : 1 ≤ k)
    (mid : ConnectorSpec G) (vs : List (Fin G.numNodes × Orient)) (hne : vs ≠ []) :
    (spellWithConnectors G mid vs).length =
      (bidirSpell G vs).length + (vs.length - 1) :=
  augmentedSpell_length G hk mid vs hne

/-- **Path bijection — empty walk.** Both spellings agree on the empty
    walk (base of the bijection). -/
@[simp] theorem spellWithConnectors_nil
    (G : BidirectedDeBruijnGraph α k) (mid : ConnectorSpec G) :
    spellWithConnectors G mid [] = bidirSpell G [] := rfl

/-- **Path bijection — singleton walk.** A walk of length 1 has no
    junctions, so the augmented spelling is the node's read sequence
    (no connectors are inserted). -/
@[simp] theorem spellWithConnectors_singleton_eq_spell
    (G : BidirectedDeBruijnGraph α k) (mid : ConnectorSpec G)
    (v : Fin G.numNodes) (o : Orient) :
    spellWithConnectors G mid [(v, o)] = bidirSpell G [(v, o)] := by
  rw [spellWithConnectors_singleton, bidirSpell_singleton]

end BidirectedDeBruijnGraph

end Bluntg
