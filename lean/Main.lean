/-
Entry point for the `bluntg` executable.

Usage:
    bluntg [k]                # k from argv if given, otherwise inferred
                              # reads GFA on stdin, writes bluntified GFA on stdout
-/
import Bluntg

open Bluntg

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
  if k < 2 then
    IO.eprintln s!"bluntg: refusing to run with k = {k} (need k ≥ 2)"
    return 2
  let blunted := bluntifyGfa gfa k
  stdout.putStr (GFA.write blunted)
  return 0
