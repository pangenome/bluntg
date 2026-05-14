/-
Entry point for the `bluntg` executable.

Usage:
    bluntg [k]                # k from argv if given, otherwise inferred
                              # reads GFA on stdin, writes bluntified GFA on stdout

The CLI auto-detects **variable per-edge overlap** inputs: if any two L
lines differ in their CIGAR length, the executable dispatches through
`GFA.bluntifyVar` (which handles per-side max-aggregation of variable
overlaps) instead of the uniform-`k` `bluntifyGfa`. The latter still
handles same-side `+ -` bidirected edges via `EvenK.addConnectors`,
which the variable-overlap path does not (a known limitation tracked
in `DESIGN-overlaps.md §4.4`).
-/
import Bluntg

open Bluntg

/-- Detect whether every link in `g` has the same overlap length. -/
def isUniformOverlap (g : GFA.Gfa) : Bool :=
  if h : g.links.size > 0 then
    let first := g.links[0].overlap
    g.links.all (fun l => l.overlap == first)
  else
    true

def main (args : List String) : IO UInt32 := do
  let stdin  ← IO.getStdin
  let stdout ← IO.getStdout
  let input  ← stdin.readToEnd
  let gfa    := GFA.parse input
  let k :=
    match args with
    | s :: _ => match s.toNat? with
                | some n => n
                | none   => GFA.inferK gfa
    | []     => GFA.inferK gfa
  let uniform := isUniformOverlap gfa
  -- The `k < 2` guard only applies to the uniform-`k` path; variable
  -- overlap mode derives all trim amounts from per-link CIGARs and
  -- doesn't use a global `k` at all.
  if uniform && k < 2 then
    IO.eprintln s!"bluntg: refusing to run with k = {k} (need k ≥ 2)"
    return 2
  let blunted :=
    if uniform then
      -- Uniform-`k` input: keep the byte-identical fixed-`k` path
      -- (which includes the even-`k` connector-node fix-up in
      -- `EvenK.lean` for same-side `+ -` bidirected edges).
      bluntifyGfa gfa k
    else
      -- Variable per-edge overlap input: use the per-side max-aggregation
      -- bluntify. Note this does NOT install connectors for same-side
      -- `+ -` edges with even overlap — those would need a per-link
      -- connector-aware variant (cf. DESIGN-overlaps.md §3.3).
      GFA.bluntifyVar gfa
  stdout.putStr (GFA.write blunted)
  return 0
