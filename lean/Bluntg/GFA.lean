/-
GFA1 parser / printer and a direct bluntify implementation over the
"loose" record types used for I/O.

This is the unverified front-end. The verified mathematical core is in
`Bluntg.Bluntify` / `Bluntg.Correctness` and operates on the dependent
type `DeBruijnGraph α k`. The function defined here, `bluntifyGfa`, is
intended to mirror that algorithm exactly so the formal correctness
theorems apply to the values it computes — but cross-checking the two
definitions is left as a follow-up.

We support only the subset of GFA1 that `gen-gfa` emits:
  • optional `H` header line (ignored);
  • `S <id> <seq>` segments;
  • `L <from> ± <to> ± NM` links (orientation `+` or `-`, overlap `NM`);
  • `P <name> <id±,id±,...> <NM,NM,...|*>` paths.

Any other field tags after the required ones are ignored.
-/
import Bluntg.Basic
import Std.Data.HashSet
import Std.Data.HashMap

namespace Bluntg
namespace GFA

open Std (HashSet HashMap)

structure Segment where
  id : String
  seq : String
  deriving Repr, Inhabited

structure Link where
  fromId   : String
  fromPlus : Bool
  toId     : String
  toPlus   : Bool
  overlap  : Nat
  deriving Repr, Inhabited

structure PathStep where
  segId  : String
  isPlus : Bool
  deriving Repr, Inhabited

structure Path where
  name     : String
  steps    : Array PathStep
  overlaps : Array Nat
  deriving Repr, Inhabited

structure Gfa where
  segments : Array Segment := #[]
  links    : Array Link    := #[]
  paths    : Array Path    := #[]
  deriving Repr, Inhabited

/-! ## Parsing -/

inductive ParsedLine
  | segment : Segment → ParsedLine
  | link    : Link    → ParsedLine
  | path    : Path    → ParsedLine
  | other   : ParsedLine
  deriving Inhabited

/-- `"+"`/`"-"` → `Bool`; everything else → `none`. -/
def parseOrient (s : String) : Option Bool :=
  match s with
  | "+" => some true
  | "-" => some false
  | _   => none

/-- Parse `"<N>M"` CIGAR. `"*"` is treated as 0. -/
def parseOverlap (s : String) : Option Nat :=
  if s == "*" then some 0
  else if s.endsWith "M" then
    (s.dropEnd 1).toString.toNat?
  else
    none

/-- Parse a path step like `"42+"` into `{ segId := "42", isPlus := true }`. -/
def parsePathStep (s : String) : Option PathStep :=
  if s.length < 2 then none
  else
    let last := (s.takeEnd 1).toString
    let head := (s.dropEnd 1).toString
    match parseOrient last with
    | some o => some { segId := head, isPlus := o }
    | none   => none

/-- Parse a single GFA line. Unknown line types map to `.other`. -/
def parseLine (line : String) : ParsedLine :=
  let parts := line.splitOn "\t"
  match parts with
  | "S" :: id :: seq :: _ =>
      .segment { id, seq }
  | "L" :: frm :: fo :: to :: too :: ov :: _ =>
      match parseOrient fo, parseOrient too, parseOverlap ov with
      | some fp, some tp, some w =>
          .link { fromId := frm, fromPlus := fp, toId := to, toPlus := tp, overlap := w }
      | _, _, _ => .other
  | "P" :: name :: segs :: ovs :: _ =>
      let stepStrs := segs.splitOn ","
      let steps : Array PathStep :=
        stepStrs.foldl (fun acc s => match parsePathStep s with
          | some st => acc.push st | none => acc) #[]
      let overlaps : Array Nat :=
        if ovs == "*" then #[]
        else
          (ovs.splitOn ",").foldl (fun acc s => match parseOverlap s with
            | some w => acc.push w | none => acc) #[]
      .path { name, steps, overlaps }
  | _ => .other

/-- Parse a full GFA string. -/
def parse (input : String) : Gfa :=
  let lines := input.splitOn "\n"
  lines.foldl (fun (acc : Gfa) line =>
    match parseLine line with
    | .segment s => { acc with segments := acc.segments.push s }
    | .link l    => { acc with links    := acc.links.push l }
    | .path p    => { acc with paths    := acc.paths.push p }
    | .other     => acc) {}

/-! ## Printing -/

def writeSegment (s : Segment) : String := s!"S\t{s.id}\t{s.seq}"

def writeLink (l : Link) : String :=
  let fo := if l.fromPlus then "+" else "-"
  let to := if l.toPlus then "+" else "-"
  s!"L\t{l.fromId}\t{fo}\t{l.toId}\t{to}\t{l.overlap}M"

def writePath (p : Path) : String :=
  let segs : List String := p.steps.toList.map fun st =>
    let o := if st.isPlus then "+" else "-"
    s!"{st.segId}{o}"
  let segStr := String.intercalate "," segs
  let ovStr :=
    if p.overlaps.isEmpty then "*"
    else String.intercalate "," (p.overlaps.toList.map fun w => s!"{w}M")
  s!"P\t{p.name}\t{segStr}\t{ovStr}"

def write (g : Gfa) : String :=
  let header := "H\tVN:Z:1.0"
  let lines := [header]
                ++ g.segments.toList.map writeSegment
                ++ g.links.toList.map writeLink
                ++ g.paths.toList.map writePath
  String.intercalate "\n" lines ++ "\n"

/-! ## Direct bluntify

  Bidirected accounting: every `L` line participates with one of `from`'s
  ends and one of `to`'s ends.

    `L A from_o B to_o`:
      • from_o = '+': uses A's *right* end (suffix of A's sequence)
      • from_o = '-': uses A's *left*  end (prefix of A's sequence)
      • to_o   = '+': uses B's *left*  end (prefix of B's sequence)
      • to_o   = '-': uses B's *right* end (suffix of B's sequence)

  **Variable per-edge overlap.** Each `L` line carries its own `overlap`
  field. For an edge with overlap `o`, the bluntify trims the source's
  contributing side by `(o + 1) / 2` and the target's contributing side
  by `o / 2`. These two halves sum to `o` exactly, so removing them from
  both endpoints together strips the entire overlap region from the
  junction. When a segment side has multiple incident edges (e.g. one
  side of a hub node connects to several others with different overlap
  lengths), we aggregate by `max`: the side is trimmed enough to cover
  every incident edge's half. For uniform-`k` inputs (every L line has
  the same `overlap = k - 1`), max-aggregation collapses to the constant
  `(k-1)/2` / `k/2` trim of the original fixed-`k` algorithm — making
  the new code byte-identical on those inputs (see §5.1 of
  DESIGN-overlaps.md).

  See `DESIGN-overlaps.md §2-§3` for the design rationale; see
  `Bluntg.VarOverlap` for the verified Lean correctness theorem under
  the per-side max-aggregation model. -/

/-- Update a hashmap entry to the `max` of its current value (or 0 if
    absent) and the supplied amount. Used by `rightOverlap`/`leftOverlap`
    to aggregate per-edge halves into a per-segment-side trim amount. -/
def mapMaxInsert (m : HashMap String Nat) (k : String) (v : Nat) :
    HashMap String Nat :=
  match m.get? k with
  | some old => m.insert k (Nat.max old v)
  | none     => m.insert k v

/-- Per-segment **right-side trim amount**: the largest `(o+1)/2` over
    all L lines incident at that segment's right end. A right-incident
    edge is one whose `from` end is `+` (uses the source's right side)
    or whose `to` end is `-` (uses the target's right side). Absent ⇒
    no edge ⇒ no trim. -/
def rightOverlap (g : Gfa) : HashMap String Nat :=
  g.links.foldl (init := (∅ : HashMap String Nat)) (fun acc l =>
    let amt := (l.overlap + 1) / 2
    let acc := if l.fromPlus then mapMaxInsert acc l.fromId amt else acc
    if !l.toPlus then mapMaxInsert acc l.toId amt else acc)

/-- Per-segment **left-side trim amount**: the largest `o/2` over all L
    lines incident at that segment's left end. Absent ⇒ no edge ⇒ no
    trim. -/
def leftOverlap (g : Gfa) : HashMap String Nat :=
  g.links.foldl (init := (∅ : HashMap String Nat)) (fun acc l =>
    let amt := l.overlap / 2
    let acc := if !l.fromPlus then mapMaxInsert acc l.fromId amt else acc
    if l.toPlus then mapMaxInsert acc l.toId amt else acc)

/-- *Legacy* set of segment IDs whose right end has at least one edge
    incident. Used by `EvenK.lean` (the connector-node fix-up needs the
    "is this side edged?" bit, not the trim amount, when it builds
    connectors). -/
def rightSideIds (g : Gfa) : HashSet String :=
  g.links.foldl (fun acc l =>
    let acc := if l.fromPlus then acc.insert l.fromId else acc
    if !l.toPlus then acc.insert l.toId else acc) ∅

/-- *Legacy* set of segment IDs whose left end has at least one edge
    incident. -/
def leftSideIds (g : Gfa) : HashSet String :=
  g.links.foldl (fun acc l =>
    let acc := if !l.fromPlus then acc.insert l.fromId else acc
    if l.toPlus then acc.insert l.toId else acc) ∅

def trimSeq (seq : String) (lt rt : Nat) : String :=
  let chars := seq.toList
  let len := chars.length
  let body := chars.drop lt
  String.ofList (body.take (len - lt - rt))

/-- **Variable-overlap bluntify.** Trims each segment by its computed
    per-side amount: `leftOverlap[s]` chars from the left if any
    left-incident edge exists, `rightOverlap[s]` chars from the right if
    any right-incident edge exists. All link and path overlap CIGARs
    become `0M`. This is the directed bluntify: correct for any per-edge
    overlap on opposite-side edges (`+ +` / `- -`). Same-side bidirected
    edges (`+ -` / `- +`) with even overlap need a connector node — see
    `Bluntg/EvenK.lean`.

    On uniform-`k` inputs (every L line has `overlap = k - 1`), this
    function reduces to the original constant-`k` trim: every right side
    gets `(k-1+1)/2 = k/2` and every left side gets `(k-1)/2`, exactly
    as before. -/
def bluntifyVar (g : Gfa) : Gfa :=
  let rights := rightOverlap g
  let lefts  := leftOverlap  g
  let newSegments := g.segments.map fun s =>
    let l := lefts.getD  s.id 0
    let r := rights.getD s.id 0
    { s with seq := trimSeq s.seq l r }
  let newLinks := g.links.map fun l => { l with overlap := 0 }
  let newPaths := g.paths.map fun p =>
    { p with overlaps := p.overlaps.map (fun _ => 0) }
  { segments := newSegments, links := newLinks, paths := newPaths }

/-- *Backward-compatible* fixed-`k` bluntify. Calls `bluntifyVar`
    internally; the `k` argument is kept for the existing odd-`k` /
    even-`k` dispatch in `EvenK.lean` (which still needs `k` for the
    *uniform* case) and for the `Complexity.lean` step-count lemmas
    that assert per-segment / per-link work. With per-edge overlap
    in the input, the value of `k` is irrelevant — the trims are
    derived from the links themselves. -/
def bluntify (g : Gfa) (_k : Nat) : Gfa := bluntifyVar g

/-- Alias for `bluntify` — the connector-aware wrapper in
    `Bluntg/EvenK.lean` calls into this for the odd-`k` branch. -/
abbrev bluntifyDirected (g : Gfa) (k : Nat) : Gfa := bluntify g k

def inferK (g : Gfa) : Nat :=
  if h : g.links.size > 0 then
    g.links[0].overlap + 1
  else 1

end GFA
end Bluntg
