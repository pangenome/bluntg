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

  A segment's left end is trimmed by `(k-1)/2` if *any* edge in the graph
  touches that end (regardless of in/out direction). Likewise the right
  end is trimmed by `k/2` if any edge touches it. For odd `k` these are
  equal; for even `k` they differ and the connector-node fix-up applies
  (not yet implemented at the GFA level). -/

/-- Set of segment IDs whose **right** end (= `+` side) has at least one
    edge incident in the graph. -/
private def rightSideIds (g : Gfa) : HashSet String :=
  g.links.foldl (fun acc l =>
    let acc := if l.fromPlus then acc.insert l.fromId else acc
    if !l.toPlus then acc.insert l.toId else acc) ∅

/-- Set of segment IDs whose **left** end (= `-` side) has at least one
    edge incident in the graph. -/
private def leftSideIds (g : Gfa) : HashSet String :=
  g.links.foldl (fun acc l =>
    let acc := if !l.fromPlus then acc.insert l.fromId else acc
    if l.toPlus then acc.insert l.toId else acc) ∅

private def trimSeq (seq : String) (lt rt : Nat) : String :=
  let chars := seq.toList
  let len := chars.length
  let body := chars.drop lt
  String.ofList (body.take (len - lt - rt))

/-- Bluntify a (possibly bidirected) GFA. Trims each segment by `(k-1)/2`
    on its left end and `k/2` on its right end when those ends carry any
    edge; all link/path overlap CIGARs become `0M`. -/
def bluntify (g : Gfa) (k : Nat) : Gfa :=
  let rights := rightSideIds g
  let lefts  := leftSideIds  g
  let leftAmt   := (k - 1) / 2
  let rightAmt  := k / 2
  let newSegments := g.segments.map fun s =>
    let l := if lefts.contains  s.id then leftAmt  else 0
    let r := if rights.contains s.id then rightAmt else 0
    { s with seq := trimSeq s.seq l r }
  let newLinks := g.links.map fun l => { l with overlap := 0 }
  let newPaths := g.paths.map fun p =>
    { p with overlaps := p.overlaps.map (fun _ => 0) }
  { segments := newSegments, links := newLinks, paths := newPaths }

def inferK (g : Gfa) : Nat :=
  if h : g.links.size > 0 then
    g.links[0].overlap + 1
  else 1

end GFA
end Bluntg
