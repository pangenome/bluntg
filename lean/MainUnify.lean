/-
Entry point for the `unify` executable.

Usage:
    unify                       # reads GFA on stdin, writes unified GFA on stdout

Collapses simple `+/+` chains in a bluntified GFA (every `L u + v + 0M`
where `u` has a single right-side edge and `v` has a single left-side
edge, with safe path containment) into single segments with concatenated
sequences. Path spellings are preserved (see `Bluntg.Unify`).
-/
import Bluntg

open Bluntg

def main (_args : List String) : IO UInt32 := do
  let stdin  ← IO.getStdin
  let stdout ← IO.getStdout
  let input  ← stdin.readToEnd
  let gfa    := GFA.parse input
  let unified := GFA.unify gfa
  stdout.putStr (GFA.write unified)
  return 0
