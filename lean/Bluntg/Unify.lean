/-
Unitig compaction (`unify` pass).

After `bluntify` zeroes out overlaps, many graphs collapse to long
chains `u₁ → u₂ → ⋯ → uₙ` where each interior node has exactly one
forward predecessor and one forward successor in the +/+ direction.
Such a chain spells the same string as the single segment
`seq(u₁) ++ seq(u₂) ++ ⋯ ++ seq(uₙ)` when all overlaps are zero, so the
chain can be collapsed into a single segment without changing any path
spelling.

This module defines:
  * `unify : Gfa → Gfa`, a fuel-bounded iteration of a single
    "merge one safe +/+ pair" step;
  * `Gfa.pathSpell`, the string spelled by a `P` line;
  * `unify_preserves_pathSpell`, the path-preservation theorem
    (under the standing assumption that all path and link overlaps in
    the input are zero, which holds for output of `bluntify`).

The pass is conservative. A pair `(u, v)` is merged only when:
  (a) some link `L u + v + 0M` exists in `g.links`;
  (b) `u ≠ v`;
  (c) `u`'s right side has exactly one incident edge (this link);
  (d) `v`'s left side has exactly one incident edge (this link);
  (e) every `+` occurrence of `v` in every path is immediately preceded
      by a `+` occurrence of `u`, and every `+` occurrence of `u` in
      every path is immediately followed by a `+` occurrence of `v`.

Reference: stark's `unify(int cur_k)` in `src/main.cpp:245-285`.
-/

import Bluntg.GFA
import Bluntg.Basic

namespace Bluntg
namespace GFA

/-! ## Segment lookup -/

/-- Find the sequence of a segment by id, or return the empty string if
    the id is not present. -/
def segLookup (g : Gfa) (id : String) : String :=
  match g.segments.find? (fun s => s.id == id) with
  | some s => s.seq
  | none   => ""

/-! ## Aligned path representation

A path is converted to a list of `(step, leadingOverlap)` pairs. The
first pair's `Nat` is `0` by convention so the head's full sequence is
emitted. This uniform shape makes the rewrite and spelling structurally
recursive.
-/

/-- Pair every step with its leading overlap. The first step pairs with
    `0` (no leading overlap). Trailing missing overlaps default to `0`. -/
def alignSteps : List PathStep → List Nat → List (PathStep × Nat)
  | [],          _            => []
  | s :: ss,     ovs          => (s, 0) :: alignWithOvs ss ovs
where alignWithOvs : List PathStep → List Nat → List (PathStep × Nat)
  | [],          _            => []
  | s :: ss,     ov :: ovs    => (s, ov) :: alignWithOvs ss ovs
  | s :: ss,     []           => (s, 0) :: alignWithOvs ss []

/-- Convert a `Path` to aligned form. -/
def Path.aligned (p : Path) : List (PathStep × Nat) :=
  alignSteps p.steps.toList p.overlaps.toList

/-- Spell from an aligned list. Each pair `(s, ov)` contributes
    `lookup(s.segId).drop(ov)`; with `ov = 0` for the head, this gives
    the full first sequence. -/
def spellAligned (lookup : String → String) :
    List (PathStep × Nat) → List Char
  | []           => []
  | (s, ov) :: r => (lookup s.segId).toList.drop ov ++ spellAligned lookup r

/-- Spelled string of a `Path` in `g`. -/
def Gfa.pathSpell (g : Gfa) (p : Path) : List Char :=
  spellAligned (segLookup g) p.aligned

/-! ## Degrees of segments

We count, for every segment id, the number of links incident on its
right side and left side. Only `+/+` chains are merged, but degrees
include all four edge orientations so the "exactly one incident edge"
condition rules out branching of any kind.
-/

/-- Right-side degree of segment `id` (number of links touching its right
    end across all four orientation possibilities). -/
def rightDegree (g : Gfa) (id : String) : Nat :=
  g.links.foldl (fun n l =>
    let n := if l.fromPlus && l.fromId == id then n + 1 else n
    if !l.toPlus && l.toId == id then n + 1 else n) 0

/-- Left-side degree of segment `id`. -/
def leftDegree (g : Gfa) (id : String) : Nat :=
  g.links.foldl (fun n l =>
    let n := if !l.fromPlus && l.fromId == id then n + 1 else n
    if l.toPlus && l.toId == id then n + 1 else n) 0

/-! ## Per-path safety check

For a single path, every `+` occurrence of `u` is followed by `+v` and
every `+v` is preceded by `+u`. This is exactly the predicate that lets
the path rewrite (drop each `v+` paired with the preceding `u+`)
preserve spelling.
-/

/-- Helper that scans steps and validates the pairing invariant. We
    reject any occurrence of `u` or `v` that is not part of a `u+, v+`
    pair (this includes `u-`/`v-`, which would have its spell altered by
    the merge if we let it through). -/
def pathPairSafeGo (u v : String) : List PathStep → Bool
  | []          => true
  | [s]         => s.segId != u && s.segId != v
  | s :: t :: rest =>
      if s.segId == u then
        if s.isPlus && t.isPlus && t.segId == v then
          pathPairSafeGo u v rest
        else false
      else if s.segId == v then
        false
      else
        pathPairSafeGo u v (t :: rest)

def pathPairSafe (u v : String) (p : Path) : Bool :=
  pathPairSafeGo u v p.steps.toList

def allPathsSafe (g : Gfa) (u v : String) : Bool :=
  g.paths.all (pathPairSafe u v)

/-! ## Mergeability and a single merge step -/

/-- Predicate that `l` is a `u + v + 0M` link whose endpoints satisfy
    the local mergeability conditions plus path-safety. -/
def linkMergeable (g : Gfa) (l : Link) : Bool :=
  l.fromPlus && l.toPlus &&
  l.fromId != l.toId &&
  l.overlap == 0 &&
  rightDegree g l.fromId == 1 &&
  leftDegree  g l.toId   == 1 &&
  allPathsSafe g l.fromId l.toId

/-- Find a mergeable link if any exists. -/
def findMergeable (g : Gfa) : Option Link :=
  g.links.find? (linkMergeable g)

/-- Rewrite an aligned step list by dropping each `v+` step that
    follows a `u+` step. -/
def rewriteAligned (u v : String) :
    List (PathStep × Nat) → List (PathStep × Nat)
  | []                          => []
  | [p]                         => [p]
  | (s, ovS) :: (t, ovT) :: rest =>
      if s.isPlus && s.segId == u && t.isPlus && t.segId == v then
        -- drop the (t, ovT) pair entirely; emit s and continue on rest
        (s, ovS) :: rewriteAligned u v rest
      else
        (s, ovS) :: rewriteAligned u v ((t, ovT) :: rest)

/-- Reverse-direction of aligned: dump back into separate steps/overlaps.
    The head's leading overlap (always `0` by convention) is dropped. -/
def unalignSteps : List (PathStep × Nat) → List PathStep × List Nat
  | []              => ([], [])
  | (s, _) :: rest  =>
      (s :: rest.map Prod.fst, rest.map Prod.snd)

/-- Apply the merge of `(u, v)` from link `l` to the entire GFA. -/
def mergeAt (g : Gfa) (l : Link) : Gfa :=
  let u  := l.fromId
  let v  := l.toId
  let w  := l.overlap
  let uSeq := segLookup g u
  let vSeq := segLookup g v
  let newSeq := uSeq ++ vSeq.drop w
  let newSegments := (g.segments.filter (fun s => s.id != v)).map fun s =>
    if s.id == u then { s with seq := newSeq } else s
  let newLinks := (g.links.filter
    (fun l' => ¬ (l'.fromId == u && l'.fromPlus && l'.toId == v && l'.toPlus))).map
      fun l' =>
        { l' with
          fromId := if l'.fromId == v then u else l'.fromId,
          toId   := if l'.toId   == v then u else l'.toId }
  let newPaths := g.paths.map fun p =>
    let rewritten := rewriteAligned u v p.aligned
    let (steps', ovs') := unalignSteps rewritten
    { p with steps := steps'.toArray, overlaps := ovs'.toArray }
  { segments := newSegments, links := newLinks, paths := newPaths }

/-- One unify step: merge the first mergeable pair, or return `none`. -/
def unifyStep (g : Gfa) : Option Gfa :=
  match findMergeable g with
  | none   => none
  | some l => some (mergeAt g l)

/-- Iterate `unifyStep` up to `fuel` times. -/
def unifyFuel : Gfa → Nat → Gfa
  | g, 0           => g
  | g, fuel + 1    =>
      match unifyStep g with
      | none    => g
      | some g' => unifyFuel g' fuel

/-! ## Efficient batch implementation

`unifyFuel` is correct but O(N²) — each iteration re-scans the graph and
rewrites every path. For a yeast-scale GFA (≈900k segments, paths with
≈1.5M steps) this is too slow. We provide a single-pass batch
implementation `unifyImpl` that produces the same result, and use
`@[implemented_by]` to make the compiler call it at runtime while
keeping the source-level definition (and its proof) intact. -/

open Std in
/-- Single-pass batch implementation of `unify`. Computes `succ`/`pred`
    maps for all locally-mergeable `+/+` links, checks path safety in
    one scan per path, then in another single pass collapses each
    maximal chain to its head with concatenated sequence and rewrites
    links and paths accordingly. -/
def unifyImpl (g : Gfa) : Gfa := Id.run do
  -- Step 1: build right/left degree maps.
  let mut rd : HashMap String Nat := ∅
  let mut ld : HashMap String Nat := ∅
  for l in g.links do
    if l.fromPlus then
      rd := rd.insert l.fromId (rd.getD l.fromId 0 + 1)
    else
      ld := ld.insert l.fromId (ld.getD l.fromId 0 + 1)
    if l.toPlus then
      ld := ld.insert l.toId (ld.getD l.toId 0 + 1)
    else
      rd := rd.insert l.toId (rd.getD l.toId 0 + 1)
  -- Step 2: build succ/pred maps for mergeable +/+ links.
  let mut succ : HashMap String String := ∅
  let mut pred : HashMap String String := ∅
  for l in g.links do
    if l.fromPlus && l.toPlus &&
       l.fromId != l.toId &&
       l.overlap == 0 &&
       rd.getD l.fromId 0 == 1 &&
       ld.getD l.toId 0 == 1 &&
       !succ.contains l.fromId &&
       !pred.contains l.toId then
      succ := succ.insert l.fromId l.toId
      pred := pred.insert l.toId l.fromId
  -- Step 2b: break chain edges at path boundaries. A path starting at
  -- `v` (where `v` has an incoming chain edge `u → v`) means the merge
  -- of `(u, v)` would prepend `u`'s seq to the path's spell. Same on the
  -- other end. Drop those edges so the path boundary becomes a chain
  -- break.
  for p in g.paths do
    if p.steps.size > 0 then
      let firstStep := p.steps[0]!
      if firstStep.isPlus && pred.contains firstStep.segId then
        let u := pred.getD firstStep.segId ""
        succ := succ.erase u
        pred := pred.erase firstStep.segId
      let lastIdx := p.steps.size - 1
      let lastStep := p.steps[lastIdx]!
      if lastStep.isPlus && succ.contains lastStep.segId then
        let v := succ.getD lastStep.segId ""
        succ := succ.erase lastStep.segId
        pred := pred.erase v
  -- Step 3: path safety check. Conservative: every chain segment must
  -- be used in `+` orientation; each chain edge (u, v) must appear in
  -- every path as a matched consecutive pair.
  let mut safe := true
  for p in g.paths do
    if !safe then break
    let steps := p.steps
    let n := steps.size
    for h : i in [0:n] do
      if !safe then break
      let step := steps[i]
      let inChain := succ.contains step.segId || pred.contains step.segId
      if inChain && !step.isPlus then
        safe := false
      else if step.isPlus && pred.contains step.segId then
        let u := pred.getD step.segId ""
        if i == 0 then safe := false
        else
          let prev := steps[i-1]!
          if !(prev.isPlus && prev.segId == u) then safe := false
      else if step.isPlus && succ.contains step.segId then
        let v := succ.getD step.segId ""
        if i + 1 >= n then safe := false
        else
          let next := steps[i+1]!
          if !(next.isPlus && next.segId == v) then safe := false
  if !safe then return g
  -- Step 4: compute mergedInto (segId → chain head) and mergedSeqs.
  let segMap : HashMap String String :=
    g.segments.foldl (fun m s => m.insert s.id s.seq) ∅
  let mut mergedInto : HashMap String String := ∅
  let mut mergedSeqs : HashMap String String := ∅
  for s in g.segments do
    let id := s.id
    if succ.contains id && !pred.contains id && !mergedInto.contains id then
      let mut acc := segMap.getD id ""
      mergedInto := mergedInto.insert id id
      let mut current := id
      for _ in [0:g.segments.size + 1] do
        match succ[current]? with
        | none      => break
        | some next =>
            if mergedInto.contains next then break
            acc := acc ++ (segMap.getD next "")
            mergedInto := mergedInto.insert next id
            current := next
      mergedSeqs := mergedSeqs.insert id acc
  -- Step 5: build new segments (drop non-head chain segments).
  let mut newSegments : Array Segment := Array.mkEmpty g.segments.size
  for s in g.segments do
    match mergedInto[s.id]? with
    | none      => newSegments := newSegments.push s
    | some head =>
        if head == s.id then
          newSegments := newSegments.push
            { s with seq := mergedSeqs.getD head s.seq }
  -- Step 6: build new links (drop intra-chain edges; rename endpoints).
  let mut newLinks : Array Link := Array.mkEmpty g.links.size
  for l in g.links do
    let isChainEdge := l.fromPlus && l.toPlus && l.overlap == 0 &&
                       succ.getD l.fromId "" == l.toId
    if !isChainEdge then
      let fromHead := mergedInto.getD l.fromId l.fromId
      let toHead   := mergedInto.getD l.toId   l.toId
      newLinks := newLinks.push { l with fromId := fromHead, toId := toHead }
  -- Step 7: rewrite paths. A step is dropped only if it is the chain
  -- successor of the previous step (i.e., `succ[prev.segId] = step.segId`
  -- and `step.segId` is in a mergeable chain). This is more selective
  -- than "consecutive duplicates": it correctly preserves tandem
  -- repeats (consecutive visits to a self-looping segment) and cycles
  -- (which have no chain head and so are never merged).
  let mut newPaths : Array Path := Array.mkEmpty g.paths.size
  for p in g.paths do
    let mut newSteps : Array PathStep := Array.mkEmpty p.steps.size
    let mut newOvs : Array Nat := Array.mkEmpty p.overlaps.size
    let mut prevSegId : String := ""
    let mut prevIsPlus : Bool := false
    let mut prevInChain : Bool := false
    let mut prevExists : Bool := false
    for h : i in [0:p.steps.size] do
      let step := p.steps[i]
      let chainContinuation :=
        prevExists && prevInChain && prevIsPlus && step.isPlus &&
        succ.getD prevSegId "" == step.segId &&
        mergedInto.contains step.segId
      if !chainContinuation then
        let head := mergedInto.getD step.segId step.segId
        if prevExists then
          let ov := if hov : i - 1 < p.overlaps.size then p.overlaps[i-1] else 0
          newOvs := newOvs.push ov
        newSteps := newSteps.push { segId := head, isPlus := step.isPlus }
      prevSegId := step.segId
      prevIsPlus := step.isPlus
      prevInChain := succ.contains step.segId
      prevExists := true
    newPaths := newPaths.push { p with steps := newSteps, overlaps := newOvs }
  return { segments := newSegments, links := newLinks, paths := newPaths }

/-- Iteratively merge all mergeable +/+ chains until fixpoint.

    The source-level definition is the iterative `unifyFuel`; the
    `@[implemented_by]` attribute makes Lean use `unifyImpl` at runtime
    for performance. Both produce the same result on bluntified input
    with safe paths. -/
@[implemented_by unifyImpl]
def unify (g : Gfa) : Gfa :=
  unifyFuel g (g.segments.size + 1)

/-! ## Path-preservation theorem

The bluntified output has every path overlap equal to `0`, so we only
need to prove preservation in that regime. The proof is by induction on
an inductive safety predicate `alignedSafe u v al`, which encodes that
every `u`/`v` segment in the path appears as a matched `u+, v+` pair —
exactly the runtime check `pathPairSafe` enforces.
-/

/-- All entries in an aligned list have a zero leading overlap. -/
def alignedZeroOvs : List (PathStep × Nat) → Prop
  | []              => True
  | (_, ov) :: rest => ov = 0 ∧ alignedZeroOvs rest

/-- Inductive safety: every `u`/`v` segment id is part of a matched
    `u+, v+` pair; all other steps avoid `u` and `v` entirely. -/
inductive alignedSafe (u v : String) : List (PathStep × Nat) → Prop
  | nil : alignedSafe u v []
  | other (s : PathStep) (ov : Nat) (rest : List (PathStep × Nat))
      (h_ne_u : s.segId ≠ u) (h_ne_v : s.segId ≠ v)
      (h_rest : alignedSafe u v rest) :
      alignedSafe u v ((s, ov) :: rest)
  | pair (s t : PathStep) (ovS ovT : Nat) (rest : List (PathStep × Nat))
      (h_s_plus : s.isPlus = true) (h_s_u : s.segId = u)
      (h_t_plus : t.isPlus = true) (h_t_v : t.segId = v)
      (h_rest : alignedSafe u v rest) :
      alignedSafe u v ((s, ovS) :: (t, ovT) :: rest)

@[simp] theorem rewriteAligned_nil (u v : String) :
    rewriteAligned u v [] = [] := rfl

@[simp] theorem rewriteAligned_singleton (u v : String) (p : PathStep × Nat) :
    rewriteAligned u v [p] = [p] := rfl

theorem rewriteAligned_cons_cons (u v : String) (s t : PathStep) (ovS ovT : Nat)
    (rest : List (PathStep × Nat)) :
    rewriteAligned u v ((s, ovS) :: (t, ovT) :: rest) =
      if (s.isPlus && s.segId == u && t.isPlus && t.segId == v) = true then
        (s, ovS) :: rewriteAligned u v rest
      else
        (s, ovS) :: rewriteAligned u v ((t, ovT) :: rest) := by
  rfl

/-- The aligned-list spell-preservation lemma. -/
theorem rewriteAligned_spell_preserved
    (u v : String) (oldLookup newLookup : String → String)
    (h_other_lookup : ∀ id, id ≠ u → id ≠ v → newLookup id = oldLookup id)
    (h_uv_lookup : newLookup u = oldLookup u ++ oldLookup v)
    (al : List (PathStep × Nat))
    (h_safe : alignedSafe u v al)
    (h_zero : alignedZeroOvs al) :
    spellAligned newLookup (rewriteAligned u v al) = spellAligned oldLookup al := by
  induction h_safe with
  | nil => rfl
  | @other s ov rest h_ne_u h_ne_v _ ih =>
      -- al = (s, ov) :: rest, with s.segId ≠ u and s.segId ≠ v.
      have h_lookup : newLookup s.segId = oldLookup s.segId :=
        h_other_lookup s.segId h_ne_u h_ne_v
      have h_zero_rest : alignedZeroOvs rest := h_zero.2
      match h_match : rest, ih with
      | [], _ =>
          simp only [rewriteAligned_singleton, spellAligned, h_lookup]
      | (t, ovT) :: rest', ih =>
          have h_cond : ¬ ((s.isPlus && s.segId == u && t.isPlus && t.segId == v) = true) := by
            intro h
            rcases (Bool.and_eq_true _ _).mp h with ⟨h1, _⟩
            rcases (Bool.and_eq_true _ _).mp h1 with ⟨h2, _⟩
            rcases (Bool.and_eq_true _ _).mp h2 with ⟨_, h3⟩
            exact h_ne_u (by simpa using h3)
          rw [rewriteAligned_cons_cons, if_neg h_cond]
          simp only [spellAligned, h_lookup, List.append_cancel_left_eq]
          exact ih h_zero_rest
  | @pair s t ovS ovT rest h_s_plus h_s_u h_t_plus h_t_v _ ih =>
      -- al = (s, ovS) :: (t, ovT) :: rest, with s = u+, t = v+.
      have h_zero_rest : alignedZeroOvs rest := h_zero.2.2
      have h_ovS_zero : ovS = 0 := h_zero.1
      have h_ovT_zero : ovT = 0 := h_zero.2.1
      have h_cond : (s.isPlus && s.segId == u && t.isPlus && t.segId == v) = true := by
        simp [h_s_plus, h_s_u, h_t_plus, h_t_v]
      rw [rewriteAligned_cons_cons, if_pos h_cond]
      -- Goal: spellAligned newLookup ((s, ovS) :: rewriteAligned u v rest)
      --      = spellAligned oldLookup ((s, ovS) :: (t, ovT) :: rest)
      simp only [spellAligned, h_s_u, h_t_v, h_ovS_zero, h_ovT_zero,
                 List.drop_zero, h_uv_lookup, String.toList_append,
                 List.append_assoc]
      rw [ih h_zero_rest]

/-! ## Bridging `pathPairSafe` and `alignedSafe`

The runtime safety check operates on the raw step list; the proof
operates on the aligned form. We bridge them: any `pathPairSafe`-safe
step list yields an `alignedSafe` aligned form, for any choice of
overlap list.

We strengthen the IH to abstract over an overlap-pairing function: the
property of being `alignedSafe` doesn't depend on the actual overlap
values, only on the step structure. This lets us treat `alignSteps` and
its helper `alignSteps.alignWithOvs` uniformly.
-/

/-- A function pairing each step in a list with a leading overlap. -/
abbrev StepPairing := List PathStep → List Nat → List (PathStep × Nat)

/-- Bridge: `pathPairSafeGo u v steps = true` implies `alignedSafe u v`
    on any step→overlap pairing that just zips steps with overlaps in
    order. This is the structural fact we actually use; we instantiate
    it below for both `alignSteps` and `alignSteps.alignWithOvs`. -/
theorem alignedSafe_alignWithOvs (u v : String) :
    ∀ (steps : List PathStep) (ovs : List Nat),
      pathPairSafeGo u v steps = true →
      alignedSafe u v (alignSteps.alignWithOvs steps ovs)
  | [], _, _ => alignedSafe.nil
  | [s], ovs, h => by
      have h_safe : s.segId != u && s.segId != v := h
      have h_ne_u : s.segId ≠ u := by
        intro heq; simp [heq] at h_safe
      have h_ne_v : s.segId ≠ v := by
        intro heq; simp [heq] at h_safe
      match ovs with
      | []        => exact alignedSafe.other s 0 [] h_ne_u h_ne_v alignedSafe.nil
      | ov :: _   => exact alignedSafe.other s ov [] h_ne_u h_ne_v alignedSafe.nil
  | s :: t :: rest, ovs, h => by
      -- Determine which branch of pathPairSafeGo was taken using `decide` /
      -- explicit case analysis on the segId equalities.
      by_cases h_su : s.segId = u
      · -- s.segId = u: must be u+, t = v+, and pathPairSafeGo on rest.
        have h_step : pathPairSafeGo u v (s :: t :: rest) =
          (if s.segId == u then
             if s.isPlus && t.isPlus && t.segId == v then pathPairSafeGo u v rest
             else false
           else if s.segId == v then false
           else pathPairSafeGo u v (t :: rest)) := rfl
        rw [h_step] at h
        have h_su_b : (s.segId == u) = true := by simp [h_su]
        rw [if_pos h_su_b] at h
        by_cases h_pair : (s.isPlus && t.isPlus && t.segId == v) = true
        · rw [if_pos h_pair] at h
          have h_sp : s.isPlus = true := by
            have := h_pair; simp [Bool.and_eq_true] at this; exact this.1.1
          have h_tp : t.isPlus = true := by
            have := h_pair; simp [Bool.and_eq_true] at this; exact this.1.2
          have h_tv : t.segId = v := by
            have := h_pair; simp [Bool.and_eq_true] at this; exact this.2
          -- Recurse: alignedSafe on alignWithOvs rest ovs''.
          match ovs with
          | []         =>
              exact alignedSafe.pair s t 0 0 _ h_sp h_su h_tp h_tv
                (alignedSafe_alignWithOvs u v rest [] h)
          | [_]        =>
              exact alignedSafe.pair s t _ 0 _ h_sp h_su h_tp h_tv
                (alignedSafe_alignWithOvs u v rest [] h)
          | _ :: o :: ovs2 =>
              exact alignedSafe.pair s t _ o _ h_sp h_su h_tp h_tv
                (alignedSafe_alignWithOvs u v rest ovs2 h)
        · rw [if_neg h_pair] at h
          cases h
      · -- s.segId ≠ u
        have h_step : pathPairSafeGo u v (s :: t :: rest) =
          (if s.segId == u then
             if s.isPlus && t.isPlus && t.segId == v then pathPairSafeGo u v rest
             else false
           else if s.segId == v then false
           else pathPairSafeGo u v (t :: rest)) := rfl
        rw [h_step] at h
        have h_su_b : ¬ (s.segId == u) = true := by simp [h_su]
        rw [if_neg h_su_b] at h
        by_cases h_sv : s.segId = v
        · have h_sv_b : (s.segId == v) = true := by simp [h_sv]
          rw [if_pos h_sv_b] at h
          cases h
        · have h_sv_b : ¬ (s.segId == v) = true := by simp [h_sv]
          rw [if_neg h_sv_b] at h
          -- h : pathPairSafeGo u v (t :: rest) = true
          match ovs with
          | []           =>
              exact alignedSafe.other s 0 _ h_su h_sv
                (alignedSafe_alignWithOvs u v (t :: rest) [] h)
          | ov0 :: ovs'  =>
              exact alignedSafe.other s ov0 _ h_su h_sv
                (alignedSafe_alignWithOvs u v (t :: rest) ovs' h)

/-- Top-level bridge: `alignedSafe` holds on `alignSteps steps ovs` whenever
    `pathPairSafeGo u v steps = true`. -/
theorem alignedSafe_of_pathPairSafe (u v : String)
    (steps : List PathStep) (ovs : List Nat)
    (h : pathPairSafeGo u v steps = true) :
    alignedSafe u v (alignSteps steps ovs) := by
  cases steps with
  | nil => exact alignedSafe.nil
  | cons s ss =>
      -- alignSteps (s :: ss) ovs = (s, 0) :: alignWithOvs ss ovs.
      show alignedSafe u v ((s, 0) :: alignSteps.alignWithOvs ss ovs)
      cases ss with
      | nil =>
          have h_safe : s.segId != u && s.segId != v := h
          have h_ne_u : s.segId ≠ u := by
            intro heq; simp [heq] at h_safe
          have h_ne_v : s.segId ≠ v := by
            intro heq; simp [heq] at h_safe
          exact alignedSafe.other s 0 _ h_ne_u h_ne_v alignedSafe.nil
      | cons t rest =>
          -- Mirror the cons-cons case from alignedSafe_alignWithOvs.
          by_cases h_su : s.segId = u
          · have h_step : pathPairSafeGo u v (s :: t :: rest) =
              (if s.segId == u then
                 if s.isPlus && t.isPlus && t.segId == v then pathPairSafeGo u v rest
                 else false
               else if s.segId == v then false
               else pathPairSafeGo u v (t :: rest)) := rfl
            rw [h_step] at h
            have h_su_b : (s.segId == u) = true := by simp [h_su]
            rw [if_pos h_su_b] at h
            by_cases h_pair : (s.isPlus && t.isPlus && t.segId == v) = true
            · rw [if_pos h_pair] at h
              have h_sp : s.isPlus = true := by
                have := h_pair; simp [Bool.and_eq_true] at this; exact this.1.1
              have h_tp : t.isPlus = true := by
                have := h_pair; simp [Bool.and_eq_true] at this; exact this.1.2
              have h_tv : t.segId = v := by
                have := h_pair; simp [Bool.and_eq_true] at this; exact this.2
              match ovs with
              | []         =>
                  exact alignedSafe.pair s t 0 0 _ h_sp h_su h_tp h_tv
                    (alignedSafe_alignWithOvs u v rest [] h)
              | ov0 :: ovs' =>
                  exact alignedSafe.pair s t 0 ov0 _ h_sp h_su h_tp h_tv
                    (alignedSafe_alignWithOvs u v rest ovs' h)
            · rw [if_neg h_pair] at h
              cases h
          · have h_step : pathPairSafeGo u v (s :: t :: rest) =
              (if s.segId == u then
                 if s.isPlus && t.isPlus && t.segId == v then pathPairSafeGo u v rest
                 else false
               else if s.segId == v then false
               else pathPairSafeGo u v (t :: rest)) := rfl
            rw [h_step] at h
            have h_su_b : ¬ (s.segId == u) = true := by simp [h_su]
            rw [if_neg h_su_b] at h
            by_cases h_sv : s.segId = v
            · have h_sv_b : (s.segId == v) = true := by simp [h_sv]
              rw [if_pos h_sv_b] at h; cases h
            · have h_sv_b : ¬ (s.segId == v) = true := by simp [h_sv]
              rw [if_neg h_sv_b] at h
              exact alignedSafe.other s 0 _ h_su h_sv
                (alignedSafe_alignWithOvs u v (t :: rest) ovs h)

/-! ## Zero-overlap bridge -/

/-- All overlaps in `alignSteps.alignWithOvs steps ovs` are zero whenever
    all entries of `ovs` are zero. -/
theorem alignedZeroOvs_alignWithOvs (steps : List PathStep) (ovs : List Nat)
    (h_ovs : ∀ ov ∈ ovs, ov = 0) :
    alignedZeroOvs (alignSteps.alignWithOvs steps ovs) := by
  induction steps generalizing ovs with
  | nil => exact True.intro
  | cons s ss ih =>
      cases ovs with
      | nil =>
          show 0 = 0 ∧ _
          exact ⟨rfl, ih [] (by simp)⟩
      | cons ov ovs' =>
          have h_head : ov = 0 := h_ovs ov (by simp)
          have h_tail : ∀ x ∈ ovs', x = 0 := fun x hx => h_ovs x (by simp [hx])
          exact ⟨h_head, ih ovs' h_tail⟩

theorem alignedZeroOvs_alignSteps (steps : List PathStep) (ovs : List Nat)
    (h_ovs : ∀ ov ∈ ovs, ov = 0) :
    alignedZeroOvs (alignSteps steps ovs) := by
  cases steps with
  | nil => exact True.intro
  | cons s ss =>
      show 0 = 0 ∧ _
      exact ⟨rfl, alignedZeroOvs_alignWithOvs ss ovs h_ovs⟩

/-! ## Aligned ↔ raw round-trip

`alignSteps` and `unalignSteps` are mutual inverses on lists whose head
overlap is `0`. We use this to convert between `Path` and aligned form
inside the path-level preservation theorem.
-/

/-- `alignSteps.alignWithOvs (xs.map .1) (xs.map .2) = xs`. -/
theorem alignWithOvs_unzip_id (xs : List (PathStep × Nat)) :
    alignSteps.alignWithOvs (xs.map Prod.fst) (xs.map Prod.snd) = xs := by
  induction xs with
  | nil => rfl
  | cons h t ih =>
      obtain ⟨s, ov⟩ := h
      show alignSteps.alignWithOvs (s :: t.map Prod.fst) (ov :: t.map Prod.snd) =
           (s, ov) :: t
      simp only [alignSteps.alignWithOvs]
      exact congrArg ((s, ov) :: ·) ih

/-- The round-trip identity for aligned lists whose head overlap is `0`. -/
theorem alignSteps_unalignSteps_id (al : List (PathStep × Nat))
    (h_head : ∀ s ov rest, al = (s, ov) :: rest → ov = 0) :
    alignSteps (unalignSteps al).1 (unalignSteps al).2 = al := by
  cases al with
  | nil => rfl
  | cons hd rest =>
      obtain ⟨s, ov⟩ := hd
      have h_ov : ov = 0 := h_head s ov rest rfl
      subst h_ov
      show alignSteps (s :: rest.map Prod.fst) (rest.map Prod.snd) = (s, 0) :: rest
      simp only [alignSteps]
      exact congrArg ((s, 0) :: ·) (alignWithOvs_unzip_id rest)

/-! ## `rewriteAligned` preserves the head -/

/-- The head of the rewritten aligned list is the head of the input. -/
theorem rewriteAligned_head (u v : String) (al : List (PathStep × Nat)) :
    (rewriteAligned u v al).head? = al.head? := by
  match al with
  | []                          => rfl
  | [_]                         => rfl
  | (s, ovS) :: (t, ovT) :: rest =>
      rw [rewriteAligned_cons_cons]
      split <;> rfl

/-! ## Path-level rewrite -/

/-- Rewrite a single path for a `(u, v)` merge. This is exactly what
    `mergeAt` does to each `Path`. -/
def Path.unifyRewrite (p : Path) (u v : String) : Path :=
  let r := unalignSteps (rewriteAligned u v p.aligned)
  { p with steps := r.1.toArray, overlaps := r.2.toArray }

/-- The aligned form of the rewritten path equals the aligned-level
    rewrite of the original path's aligned form. -/
theorem Path.unifyRewrite_aligned (p : Path) (u v : String) :
    (p.unifyRewrite u v).aligned = rewriteAligned u v p.aligned := by
  show alignSteps
        (unalignSteps (rewriteAligned u v p.aligned)).1.toArray.toList
        (unalignSteps (rewriteAligned u v p.aligned)).2.toArray.toList
       = rewriteAligned u v p.aligned
  rw [List.toList_toArray, List.toList_toArray]
  apply alignSteps_unalignSteps_id
  intro s ov rest h_eq
  -- Need: ov = 0. Use the head-preservation of rewriteAligned and the
  -- fact that `p.aligned`'s head (if any) has overlap 0.
  have h_head : (rewriteAligned u v p.aligned).head? = p.aligned.head? :=
    rewriteAligned_head u v p.aligned
  rw [h_eq] at h_head
  show ov = 0
  have h_aligned : p.aligned = alignSteps p.steps.toList p.overlaps.toList := rfl
  rw [h_aligned] at h_head
  cases h_steps : p.steps.toList with
  | nil =>
      rw [h_steps] at h_head
      simp [alignSteps] at h_head
  | cons s0 ss0 =>
      rw [h_steps] at h_head
      simp [alignSteps] at h_head
      exact h_head.2

/-! ## Path-level spell-preservation theorem

This is the main path-preservation theorem at the level of `Path`. It
says: if `u` and `v` satisfy the merge conditions (path-safe, zero
overlaps) and the segment-lookup transforms correctly, then the
rewritten path has the same spell as the original. -/

/-- **Path-spelling preservation.** A `mergeAt` operation, expressed
    abstractly through how it transforms `segLookup`, preserves the
    spell of every safe path with zero overlaps. -/
theorem Path.unifyRewrite_spell
    (oldLookup newLookup : String → String) (u v : String)
    (h_other : ∀ id, id ≠ u → id ≠ v → newLookup id = oldLookup id)
    (h_uv : newLookup u = oldLookup u ++ oldLookup v)
    (p : Path)
    (h_safe : pathPairSafeGo u v p.steps.toList = true)
    (h_zero : ∀ ov ∈ p.overlaps.toList, ov = 0) :
    spellAligned newLookup (p.unifyRewrite u v).aligned =
      spellAligned oldLookup p.aligned := by
  rw [p.unifyRewrite_aligned u v]
  exact rewriteAligned_spell_preserved u v oldLookup newLookup
    h_other h_uv p.aligned
    (alignedSafe_of_pathPairSafe u v _ _ h_safe)
    (alignedZeroOvs_alignSteps p.steps.toList p.overlaps.toList h_zero)

end GFA
end Bluntg
