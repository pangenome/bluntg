# IMPG-HANDOFF — variable-overlap GFA1 emitter for the syng-native path

This document is the entry point for anyone (subagent or human) picking up
the **impg side** of the syng→bluntg integration. It explains what needs
to change in `~/impg` (and possibly `~/syng`) so that impg can emit
**variable-overlap GFA1** directly from syncmer data — skipping seqwish —
so that bluntg can consume it end-to-end.

The bluntg side already knows how to consume variable-overlap GFA1: the
design is in `DESIGN-overlaps.md` at the bluntg repo root, and the Lean
and Rust ports of the consumer will land via the `overlaps-lean` /
`overlaps-rust` tracks. This document is the **producer-side** spec.

---

## 1. Goal

Add a **syng-native GFA1 emitter** to impg that walks syng's GBWT
(`SyngBWT` from `~/syng/syng.h:27-37`) directly and produces a GFA whose
`L` lines carry the **per-edge overlap length** in their `<N>M` CIGAR
field, computed as `len(A) - offset(A→B)` from the syng edge offsets
(`~/syng/syng.h:76-77`). This bypasses the entire
`syng → BiWFA → PAF → seqwish` chain in `~/impg/src/syng_graph.rs` and
gives bluntg a graph it can bluntify directly — making the
**impg → bluntg** pipeline useful end-to-end. The current
`-o gfa` output is uniformly `0M` (already pre-bluntified by seqwish),
which makes bluntg a no-op; the new emitter is the missing piece that
turns variable-overlap data into something bluntg can do real work on.

---

## 2. Current pipeline (what we are routing around)

```
   FASTA / AGC
        │
        ▼
   impg syng        (syng C-FFI: syngBWT* in ~/impg/src/syng_ffi.rs:148-188)
        │           builds GBWT in-memory; writes .1khash + .1gbwt
        ▼
   SyngBWT (in RAM) — nodes carry length (fixedLen = w+k = 63)
        │                edges carry per-path offset (syng.h:76-77)
        │
        ▼
   impg query --syng -o gfa  (lib.rs:517 GfaEngine::SyngNative arm)
        │
        ▼
   syng_graph::build_paf_anchor_seeded   (~/impg/src/syng_graph.rs:512+)
        │   or
        ▼
   syng_graph::build_gfa_syng_native_from_sequences   (syng_graph.rs:432)
        │   (above: pairwise BiWFA over members → PAF text)
        ▼
   syng_graph::build_gfa_from_paf_and_sequences       (syng_graph.rs:455)
        │   writes combined FASTA + PAF tempfile,
        │   calls commands::graph::induce_graph_from_alignment
        ▼
   commands::graph::induce_graph_from_alignment       (graph.rs:161)
        │   unpack_paf_alignments → compute_transitive_closures
        │   → compact_nodes → derive_links
        ▼
   seqwish::gfa::emit_gfa                              (graph.rs:30, 356)
        │   (vendored seqwish at
        │    ~/.cargo/git/checkouts/seqwish-be7416204a0fe48d/15aee55/src/gfa.rs:89)
        │   writes every L line as `L … 0M` — seqwish bluntifies in C++
        │   before emit, so impg never sees per-edge overlap lengths.
        ▼
   unchop_gfa / normalize_and_sort (gfasort)
        │
        ▼
   stdout: GFA1 with `0M` on every L line
```

The function we want to **branch around** is the whole
`syng_graph::build_gfa_*` family (`syng_graph.rs:432-510`) and the
`induce_graph_from_alignment` call site (`graph.rs:161`,
`graph.rs:356`). All of that exists because the original design was
"syng tells us which pairs to align; BiWFA + seqwish do the rest".
A syng-native emitter does not need any of it: the GBWT already has
nodes (syncmers), edges (with offsets), and paths (encoded as GBWT
traversals). The overlap length is `parent.length - edge.offset` by
construction.

Reference points the new code reads from but does not replace:

* `~/impg/src/syng.rs:13-21` — `read_u64`/`write_u64`, generic LE helpers
* `~/impg/src/syng.rs:84-92` — `SampledPositions` sidecar
* `~/impg/src/syng_ffi.rs:48-57` — `SyngBWT` Rust mirror of `~/syng/syng.h:27-37`
* `~/impg/src/syng_ffi.rs:61-68` — `SyngBWTpath` mirror of `~/syng/syng.h:39-43`
* `~/impg/src/syng_ffi.rs:148-192` — `extern "C"` bindings for the GBWT API

---

## 3. Proposed pipeline (`syng → variable-overlap GFA1`)

```
   SyngBWT (in RAM, from impg syng)
        │
        ▼
   emit_gfa_syng_native(&SyngIndex, &mut Write) -> io::Result<()>
        │
        ├──► H line: `H\tVN:Z:1.0`
        │
        ├──► For each node n in sb->node (Array of Node, ~/syng/syngbwt3.c:30-33):
        │       seq[n]  = reconstructed syncmer sequence
        │                  (length = sb->fixedLen == w+k == 63, default)
        │       S line: `S\t<id>\t<seq>`
        │
        ├──► For each edge n → m on the GBWT (walk via syngBWTpathStartOld
        │       / syngBWTpathNext, ~/syng/syng.h:54-55):
        │       offset = the U32 stored on that edge (~/syng/syng.h:76)
        │       o_e    = sb->fixedLen - offset      // per-edge overlap length
        │       L line: `L\t<id_n>\t+\t<id_m>\t+\t<o_e>M`
        │
        └──► For each path p in sb->path (Array of SyngPath, ~/syng/syng.h:23-25):
                walk via syngBWTmatchStart / syngBWTmatchNext
                  (~/syng/syng.h:56-57)
                emit P line with the syncmer-id sequence and the per-edge
                overlap list:
                P line: `P\t<name>\t<id1>+,<id2>+,...,<idK>+\t<o1>M,<o2>M,...`
```

The output is exactly what `DESIGN-overlaps.md` §1.3 / §6.2 (R1)
calls for: a GFA1 whose `L` lines and per-`P` overlaps carry the
**syncmer-derived per-edge length**.

### 3.1 Where each piece of data comes from in syng

| GFA1 column | syng source | File:line |
|---|---|---|
| segment `id` | node index `i` into `sb->node` (Array) | `~/syng/syng.h:29-31`, `~/syng/syngbwt3.c:30-33` |
| segment `seq` | `kmerHashSeq(kh, i, buf)` — syncmer sequence reconstructed from the kmer hash sidecar | `~/impg/src/syng_ffi.rs:212` |
| segment length | `sb->fixedLen` (== `w + k`, default 63) or `arr(sb->length, i, I32)` if `fixedLen == 0` | `~/syng/syng.h:28-31`, `~/syng/syngbwt3.c:117-127` |
| L `from`/`to` | the two endpoints visited by `syngBWTpathNext` | `~/syng/syng.h:55`, `~/syng/syngbwt3.c:371-374` |
| L orientation | sign of `nextNode` (negative if reversed; same convention as the `E` schema entry) | `~/syng/syng.h:76-77` |
| L overlap (the variable part) | `fixedLen - nextPos` where `nextPos` is the offset returned by `syngBWTpathNext` | `~/syng/syng.h:55`, `~/syng/syngbwt3.c:373-383` |
| P walk | `syngBWTmatchStart` + repeated `syngBWTmatchNext` until exhausted | `~/syng/syng.h:56-57` |
| P overlaps | same per-edge `fixedLen - offset` rule | derived |

### 3.2 Why this is correct (one-paragraph sketch)

A syncmer node `A` of length `L_A` is followed on path `P` by node `B`
at offset `off_A→B` *from the start of `A` along `P`*. By the syncmer
construction, the last `L_A − off_A→B` bases of `A`'s sequence are
identical to the first `L_A − off_A→B` bases of `B`'s sequence — that
is exactly what the GFA L-line `<N>M` overlap means. The same
`(A, off)` pair can appear in multiple paths and produce the same edge,
so the overlap is a property of the edge, not of the path. Variable
overlaps arise naturally: A's outgoing edges to B, C, D can have
different offsets and therefore different overlap lengths
(`DESIGN-overlaps.md` §1.3 / §1.4).

---

## 4. Concrete code-level work plan

### 4.1 `~/impg/src/syng_graph.rs` — add the emitter

Add a sibling to `build_gfa_syng_native_from_sequences` (`syng_graph.rs:432`):

```rust
/// Emit a GFA1 string directly from a SyngBWT, with one S line per
/// syncmer node and one L line per GBWT edge, carrying the
/// per-edge overlap length in `<N>M` form (variable-overlap GFA1).
///
/// Bypasses the BiWFA → PAF → seqwish pipeline used by
/// `build_gfa_syng_native_from_sequences`. The output is meant to
/// be consumed by bluntg directly (see DESIGN-overlaps.md in the
/// bluntg repo).
pub fn emit_gfa_syng_native<W: std::io::Write>(
    syng: &crate::syng::SyngIndex,
    out: &mut W,
) -> std::io::Result<()>;
```

Module placement: this can live in `syng_graph.rs` next to the other
GFA builders, **or** in a new module `syng_emit_gfa.rs`. Recommendation:
new module, because `syng_graph.rs` is already 876 lines and is
exclusively the PAF/seqwish path; mixing a non-seqwish emitter into it
muddies the staging plan documented at `syng_graph.rs:14-18`. See §6
open question.

### 4.2 `~/impg/src/syng.rs` — expose what the emitter needs

The emitter needs read access to:

* the GBWT node array (`sb->node`, `~/impg/src/syng_ffi.rs:50`)
* per-node length (`sb->fixedLen` for default mode; `sb->length` for
  variable mode — `~/impg/src/syng_ffi.rs:49,52`)
* per-edge `(next_node, offset)` pairs, reachable via
  `syngBWTpathStartOld` + `syngBWTpathNext`
  (`~/impg/src/syng_ffi.rs:160-170`)
* syncmer sequences via `kmerHashSeq` (`~/impg/src/syng_ffi.rs:212`)
* path metadata (`SyngPath { file, path, length }` — `~/impg/src/syng_ffi.rs:39-43`,
  matching `~/syng/syng.h:21-25`)

`syng.rs` already wraps most of this for the building-and-querying
paths (e.g. `SyngIndex`, `SampledPositions`, the various
`syng_*_path()` sidecars at `~/impg/src/syng.rs:41-77`). The emitter
just needs a `walk_edges(&self, cb: impl FnMut(node_id, edge: Edge))`
or equivalent iterator. Add:

```rust
impl SyngIndex {
    /// Iterate every (node, outgoing-edge) pair in the GBWT.
    /// Edge = (from_node_id, to_node_id, to_offset, count).
    pub fn for_each_edge<F: FnMut(SyngEdge)>(&self, mut f: F);

    /// Iterate every encoded path (sequence of node ids and the
    /// per-step offset). Yields one PathRecord per path.
    pub fn for_each_path<F: FnMut(SyngPathRecord)>(&self, mut f: F);
}
```

The iterator implementation walks `sb->node` (Array) and for each
node uses `syngBWTmatchStart` / `syngBWTmatchNext` to enumerate
distinct outgoing edges. (See §6.2 — this may need a thin C-side
extension if the existing public API doesn't expose `node.out` cleanly.)

### 4.3 `~/impg/src/commands/graph.rs` — wire up the CLI

The current `-o gfa` path is routed through
`lib.rs:dispatch_gfa_engine` (`~/impg/src/lib.rs:402-603`). Two
reasonable plumbing options:

**(a) New CLI flag `--native-overlaps` on the existing GFA output.**
At `~/impg/src/main.rs:787-801` (engine-name parsing), add a sibling
boolean on `EngineCliOpts` and gate the dispatch in
`lib.rs:GfaEngine::SyngNative` (`lib.rs:517`) so that when
`--native-overlaps` is set, we skip the BiWFA → seqwish path and
call `emit_gfa_syng_native` instead. The flag is meaningful only
under `--gfa-engine syng-native`; reject the combo with other engines
in `validate_engine_params` (`~/impg/src/main.rs:812-855`).

**(b) New engine value `syng-native-direct`.** Add a fourth variant
to `GfaEngine` (`~/impg/src/lib.rs:29-50`). Parsing change at
`~/impg/src/main.rs:791`. Cleaner conceptually but adds a long-lived
variant.

Recommendation: **(a)** — see §6 open question.

### 4.4 Tests

Add at `~/impg/tests/syng_native_gfa.rs`:

* A tiny round-trip: build a GBWT over 3 short sequences with known
  syncmer overlap structure, call `emit_gfa_syng_native`, parse the
  output, assert per-link `<N>M` values match the expected
  `fixedLen - offset` formula.
* A bluntg round-trip: pipe the emitter output through bluntg
  (the binary at `lean/.lake/build/bin/bluntg` or
  `target/release/bluntg` in the bluntg repo) and confirm that every
  P-line spelling in the bluntified output equals the original input
  sequence. The bluntg side already enforces this as its universal
  correctness criterion (`DESIGN-overlaps.md` §6.2).

Add a smoke scenario at
`~/impg/tests/smoke/syng_native_gfa.sh` (if impg has a smoke harness;
otherwise leave the integration test as the gate).

---

## 5. Validation contract (how the impg agent verifies success)

The bluntg repo already ships two binary bluntifiers (the Lean one and
the Rust one) and the yeast chrV fixture. The end-to-end smoke test
the impg agent should run is:

```bash
# 1. Build the new emitter
cd ~/impg
cargo build --release

# 2. Build a GBWT over the yeast fixture (already used elsewhere in impg)
./target/release/impg syng -f ~/impg/tests/test_data/yeast.chrV.fa.gz \
    -o /tmp/yeast.syng

# 3. Emit variable-overlap GFA1 via the new path
./target/release/impg query --syng /tmp/yeast.syng \
    -f ~/impg/tests/test_data/yeast.chrV.fa.gz \
    -r chrV \
    --gfa-engine syng-native --native-overlaps \
    -o gfa > /tmp/yeast.syngnative.gfa

# 4. Confirm L lines actually carry variable per-edge overlaps
awk '$1=="L"{print $6}' /tmp/yeast.syngnative.gfa | sort -u | head
#   ^ expect a *set* of distinct <N>M values, NOT just 0M.
#   If you see only "0M", the emitter is still going through seqwish.

# 5. Pipe through bluntg (Lean binary)
~/bluntg/lean/.lake/build/bin/bluntg \
    < /tmp/yeast.syngnative.gfa \
    > /tmp/yeast.bluntified.gfa

# 6. Pipe through bluntg (Rust binary, once overlaps-rust lands)
~/bluntg/target/release/bluntg \
    < /tmp/yeast.syngnative.gfa \
    > /tmp/yeast.bluntified.rust.gfa

# 7. Confirm output is blunt (every L line has 0M after bluntg)
awk '$1=="L"{print $6}' /tmp/yeast.bluntified.gfa | sort -u
#   expected: 0M  (one and only one value)

# 8. Confirm every P-line spelling round-trips to the original input
~/bluntg/scripts/check_pline_spellings.sh /tmp/yeast.bluntified.gfa \
    ~/impg/tests/test_data/yeast.chrV.fa.gz
#   expected: "7/7 path spellings preserved"
#   (this is the same harness used for the k=30 even-k test in
#    SYNTHESIS.md §3, just pointed at the new fixture)
```

Success criteria, in order:

1. Step 4 produces multiple distinct overlap values (the whole point —
   if every L is `0M` the emitter is still going through seqwish).
2. Step 7 produces exactly one value, `0M` (bluntg is doing real work).
3. Step 8 reports 100% P-line spelling preservation (the overlap
   aggregation in `DESIGN-overlaps.md` §2.2 is internally consistent
   on real syng output).

If step 3 fails on `+ -` or `- +` same-side bidirected edges
specifically, that is the known limitation documented at
`~/bluntg/lean/Bluntg/EvenK.lean:62-77` and not a regression — the
impg emitter should still emit those edges, and the bluntg side will
flag them.

---

## 6. Open questions / decisions for the impg agent

These are things the bluntg side cannot pre-decide.

1. **New module or extend `syng_graph.rs`?**
   `syng_graph.rs` is named for and currently means "the
   syng→BiWFA→PAF→seqwish path" (`syng_graph.rs:14-18`). Putting a
   syng→GFA1-direct emitter into the same file blurs that meaning.
   Recommendation: new module `syng_emit_gfa.rs` (or
   `commands/syng_native_gfa.rs`); leave `syng_graph.rs` as the
   seqwish-PAF path. The impg agent owns this call.

2. **Does the existing syng C API expose what's needed, or does
   `~/syng` need a thin extension first?**
   `~/syng/syng.h:46-60` exports `syngBWTpathStartOld`, `syngBWTpathNext`,
   `syngBWTmatchStart`, `syngBWTmatchNext` — the path-walking primitives.
   What it does **not** export is a direct iterator over a node's outgoing
   edges independent of any path traversal. `Node.out` (the union of a
   single offset/count tuple or an Rskip list, `~/syng/syngbwt3.c:21-33`)
   is private to `syngbwt3.c`. Walking edges via the path API yields
   every edge, but with duplication proportional to coverage — fine for
   the first version, costly for large indexes.

   Decision the impg agent needs to make:
   * **(i) Live with path-walk duplication** — emit one L line per edge,
     deduplicate via a `HashSet<(from, to, offset)>` on the impg side.
     Zero changes to `~/syng`. Recommended for v0.
   * **(ii) Add a `syngBWTedges` iterator** to `~/syng/syngbwt3.c` that
     yields each `(from, to, offset)` exactly once, exposed in
     `~/syng/syng.h` and bound in `~/impg/src/syng_ffi.rs`. Cleaner;
     small upstream patch.

3. **How does this interact with impg's existing `-o gfa` semantics?**
   `~/impg/src/main.rs:787-801` parses the engine name and the existing
   `-o gfa` always means "go through seqwish, get 0M output". Three
   options were enumerated in §4.3; the recommendation is the new
   `--native-overlaps` flag gated under `--gfa-engine syng-native`. This
   keeps the existing default behaviour byte-for-byte unchanged and
   adds a single opt-in. The impg agent owns the final shape of the
   CLI.

4. **Variable-length node mode (`fixedLen == 0`).**
   `~/syng/syngbwt3.c:119` currently dies on `fixedLen == 0`
   (`"syngBWT does not yet support variable length sequences"`), so the
   v0 emitter only needs the fixed-length path
   (`length = sb->fixedLen`, default 63). When `~/syng` lifts that
   restriction, the emitter should switch to `arr(sb->length, i, I32)`
   per node. This is a single conditional in the emitter and not a
   design decision; just keep both code paths in mind.

5. **Bidirected GFA conventions on `+ -` / `- +` edges.**
   The syng `E` schema entry `~/syng/syng.h:76-77` encodes orientation
   via the sign of the adjacent node id. The emitter should translate
   that sign into the GFA `+`/`-` columns directly. The bluntg side
   handles `+ +` and `- -` correctly; same-side `+ -` even-overlap
   edges are handled by the connector-node trick in
   `~/bluntg/lean/Bluntg/EvenK.lean`; same-side `- +` is the known
   unhandled case (`~/bluntg/lean/Bluntg/EvenK.lean:62-77`). The
   impg emitter does not need to do anything special — just emit
   what the GBWT says — bluntg's side will either consume or flag.

---

## 7. Pointers to bluntg-side reference material

* **Design for variable-overlap consumption:**
  `~/bluntg/DESIGN-overlaps.md` — the design produced by the
  overlaps-research track. Especially:
  * §1.3 (what syng natively encodes) — the data model assumption
    on this end.
  * §2 (data model change) and §2.2 (max-over-incident-edges
    aggregation) — the bluntg-side trim rule. **This is settled and not
    open for renegotiation.**
  * §6.2 (R1) — explicit reference to "`impg syng + impg query --syng -o gfa`"
    over yeast chrV as the integration test, which is exactly the
    pipeline this handoff is enabling.

* **Lean specification of bluntify:**
  `~/bluntg/lean/Bluntg/GFA.lean:171-212` — current `rightSideIds` /
  `leftSideIds` / `bluntify`, the structure that the variable-overlap
  port (in flight on the `overlaps-lean` track) replaces with the
  `HashMap String Nat` shape from `DESIGN-overlaps.md` §7.1.

* **Rust port of bluntify (target consumer):**
  `~/bluntg/src/main.rs:124-183` — `right_side_ids` / `left_side_ids` /
  `bluntify`. The `overlaps-rust` track converts these to per-side
  `HashMap<String, usize>` per `DESIGN-overlaps.md` §7.4.

* **Bluntg binaries (use these for the validation in §5):**
  * Lean: `~/bluntg/lean/.lake/build/bin/bluntg`
  * Rust: `~/bluntg/target/release/bluntg`
  * k-mer DBG GFA generator (not needed here, but it's how the
    existing bluntg validation harness is shaped):
    `~/bluntg/target/release/gen-gfa`

* **Synthesis context:**
  `~/bluntg/SYNTHESIS.md` — track-merge state, theorem inventory,
  benchmark numbers. Especially §3 (yeast chrV byte-identity between
  Lean and Rust at k=15 / k=31) — the regression that this work must
  not break.

* **Reference upstream for the bluntifier algorithm:**
  `~/stark/src/main.cpp:88-91` — the assertion
  `if (k != match + 1) logger->error("Error! different k's: %d - %d", …)`
  is the exact uniform-`k` assumption being removed. The impg
  emitter is what makes removing that assumption useful.

---

## 8. Anti-scope (do **not** do these inside this handoff's follow-up)

* Do **not** redesign bluntg's overlap aggregation rule. That is settled
  by `DESIGN-overlaps.md` §2.2. The emitter just emits the per-edge
  values; aggregation is on the consumer side.
* Do **not** design a CIGAR-richer (`I`/`D`/`X`) overlap path. The whole
  point of skipping seqwish is that syncmer-derived overlaps are pure
  matches by construction. Out of scope per `DESIGN-overlaps.md` §8.
* Do **not** change `seqwish::gfa::emit_gfa`. The seqwish path stays
  exactly as-is and remains the default for non-syng engines.
* Do **not** port the bluntifier into impg. impg emits; bluntg consumes.
