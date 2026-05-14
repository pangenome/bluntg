# bluntg

A formally-verified bluntifier for De Bruijn graphs in GFA format, with a
companion Rust k-mer-DBG builder for generating test input.

`bluntg` mirrors the **bluntify** step of [stark](https://github.com/hnikaein/stark):
given a De Bruijn graph whose nodes share `(k-1)`-character overlaps, it
trims each node's sequence so the resulting graph has zero overlap (a
"variation graph"-shaped output). The trim is `(k-1)/2` chars on any
side with an incoming edge and `k/2` chars on any side with an outgoing
edge. Path spellings are preserved up to the trim amounts at the walk
endpoints — and this preservation is **machine-checked in Lean 4** in
this repo.

## What's verified (Lean 4)

The core algorithm lives in `lean/Bluntg/`. There are **zero `sorry`s** in
the proof source. The headline theorems:

| Theorem | Statement |
|---|---|
| `bluntify_is_blunt` | the bluntified graph has zero overlap on every edge |
| `bluntSpell_eq_middle_spell` | for any walk `vs` in `G`, the bluntified spelling equals `middle (spell vs) (leftTrim vs.head) (rightTrim vs.last)` |
| `bluntSpell_eq_spell_of_boundary` | when the walk starts at a node with no incoming edge and ends at a node with no outgoing edge, the spellings are *equal* |
| `middle_concat_overlap` | the key list-arithmetic identity for sandwich+overlap composition |
| `rewriteAligned_spell_preserved` | a single `unify` merge of a `u + v +` chain preserves the spelling of every safe path with zero overlaps |
| `Path.unifyRewrite_spell` | the same preservation lifted to `Path` and `Gfa.pathSpell` |

`Bluntg/Bidirected.lean` defines the bidirected layer (`Orient`,
`BidirectedDeBruijnGraph` with the side-aware overlap invariant) and
proves the **doubling** to a directed graph — every bidirected node
splits into a `+` and `-` directed copy, every bidirected edge becomes
one directed edge with `target.orient := flip(target.bidir_side)`. This
transports the directed correctness theorems to the bidirected case
mechanically.

Not yet wired up:
- Linear-time bound as a formal complexity proof.
- The even-`k` connector-node construction (sketched in
  `Bidirected.lean` — needed for the asymmetric trim case).
- Connecting the bidirected `bluntify` definition through to GFA I/O.

## End-to-end pipeline

```bash
# Build everything
cargo build --release            # Rust: gen-gfa test-input generator
(cd lean && lake build)          # Lean:  bluntg + unify executables + library

# Generate a De Bruijn graph from a FASTA (also accepts .gz / .bgz)
./target/release/gen-gfa 31 data/yeast.chrV.fa.gz > yeast.k31.gfa

# Bluntify (reads stdin, writes stdout; k inferred from first L overlap)
./lean/.lake/build/bin/bluntg < yeast.k31.gfa > yeast.k31.blunt.gfa

# Optional: collapse simple +/+ chains. For yeast chrV this reduces
# ~890k segments to ~24k while leaving every P line's spelling unchanged.
./lean/.lake/build/bin/unify < yeast.k31.blunt.gfa > yeast.k31.unified.gfa
```

`gen-gfa` emits one `S` line per distinct k-mer (numbered `1..`), one
deduplicated `L` line per `(k-1)`-overlap adjacency, and one `P` line
per input FASTA record (the walk through the k-mers spelling that
record).

`bluntg` reads GFA1 (`S`/`L`/`P` lines), trims every segment, sets every
link/path overlap to `0M`, and writes the result. Edges are accounted
for **bidirectionally**: each L line is mapped to the appropriate
*side* of each endpoint (left/right based on the orientation column),
and each segment's left end is trimmed by `(k-1)/2` iff any edge
touches that side, right end by `k/2` likewise. For odd `k` the trims
are equal; for even `k` they're asymmetric and a connector-node
fix-up is needed before bluntify (not yet plumbed at the GFA level).

## Repo layout

```
.
├── Cargo.toml
├── data/                       # yeast chrV haplotypes (for testing)
├── src/
│   ├── main.rs                 # placeholder for an eventual Rust bluntify
│   └── bin/gen-gfa.rs          # k-mer DBG builder
└── lean/
    ├── lakefile.toml
    ├── lean-toolchain
    ├── Main.lean               # bluntg executable entry point
    ├── MainUnify.lean          # unify executable entry point
    └── Bluntg/
        ├── Basic.lean          # list helpers (prefix / suffix / middle)
        ├── Graph.lean          # DeBruijnGraph structure, walks, spelling
        ├── Bluntify.lean       # bluntify function + bluntSpell
        ├── Correctness.lean    # path-preservation theorems
        ├── Bidirected.lean     # bidirected layer + doubling
        ├── GFA.lean            # GFA1 parser / printer / bluntify-on-records
        └── Unify.lean          # unitig compaction + path-preservation proof
```

## Status of "is this stark in Lean 4?"

For the **directed, odd-`k`** subset, yes: `bluntg` runs end-to-end on
GFA, the trim is the same as stark's, and the path-preservation
guarantee is now a machine-checked theorem rather than a comment in C++.

Not yet done relative to stark:
- bidirected GFA edges with `-` orientations are passed through but not
  treated bidirectionally;
- the even-`k` connector-node fix-up isn't applied;
- `merge_nodes` (partial node merges) isn't ported. `unify` (unitig
  compaction) is ported with a machine-checked path-preservation proof.

A native-Rust port is planned for parity-with-stark performance; the
Lean library will continue to serve as the correctness reference.
