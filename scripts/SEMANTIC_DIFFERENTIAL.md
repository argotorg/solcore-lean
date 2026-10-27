# Generated semantic comparisons

The implementation plan and completion criteria are in
[Semantic differential testing milestones](../docs/design/semantic-differential-testing.md).
The reference Rust revision remains `2a745e12974c373c3799fec81b48a53c7dce2ab4`.

For pinned tool preparation, all-profile fixed and random suites, CI scheduling
and retained findings, see [Running the semantic test suite](SEMANTIC_CI.md).

## Generate and inspect source cases

Build the native tools once:

```sh
lake build semanticCaseTool rustHullContract rustHullScenario
```

The first source emitter supports checked, closed G0 Word programs with Boolean
subexpressions, local Word bindings, conditionals, Boolean and Word negation,
addition, subtraction, multiplication, bitwise and/or/xor, equality and unsigned
greater-than. Unsupported operations are explicit exclusions, including in
branches that would not execute. The original Core generator is unchanged.

Generate twelve cases with a 24-node budget, at most 2,000 attempts, and one
million Core execution steps per case:

```sh
mkdir -p .upstream/semantic-cases
.lake/build/bin/semantic-case-tool generate 0 24 12 2000 1000000 > .upstream/semantic-cases/corpus.json
```

The arguments are `SEED NODES COUNT ATTEMPTS FUEL`. Seed search uses consecutive
64-bit seeds beginning at `SEED`. Every attempted seed and exclusion contributes
to the reported counts. Inspect the corpus `status`: `generation-exhausted`
means the requested number of supported cases was not produced, even if the
tool successfully wrote its report. It is not a successful test campaign.

Each case contains the original Core Wire program, emitted source, versioned
provenance, contract metadata and a fresh direct Core observation. The wrapper
is `SynthesizedG0.run()`, returning a single ABI `uint256` with no inputs.

The same tool accepts:

```text
semantic-case-tool emit PROGRAM.json [FUEL]
semantic-case-tool observe CASE.json [FUEL]
semantic-case-tool replay CASE.json [FUEL]
semantic-case-tool shrink CASE.json LIMIT [FUEL]
```

`emit` checks an externally supplied Core Wire program against G0 before
rendering it. `observe` evaluates its original Core expression. `replay`
rechecks the program, regenerates seeded cases, compares source and wrapper
metadata, and computes the result again. A saved `directCore` field is never a
trusted expected result. `shrink` returns checked, smaller, re-emitted
candidates; it does not by itself establish that any candidate preserves an
observed mismatch.

Generation is bounded to 512 nodes, 1,024 requested cases and 10,000 attempts per
invocation. The seed must be an exact unsigned 64-bit decimal integer. Explicit
case-tool fuel is at most 10,000,000. Corpus generation never silently replaces
an unsupported expression with a different computation.

## G0 generator revisions

The G0 generator has four replay revisions, all layered on the unchanged
`lcg64-v1` draws. A case records its revision in `generatorVersion`. The
primitive profile records `core-primitives-v1/` followed by the revision there,
and the plain revision in `baseGeneratorVersion`.

| Revision | `generatorVersion` | Used by |
| --- | --- | --- |
| v1 | `core-g0-v1/lcg64-v1` | fixed corpora, imported programs, the case tool without a version |
| v2 | `core-g0-v2/lcg64-v1` | `--g0-version` for the pure and stateful profiles |
| v3 | `core-g0-v3/lcg64-v1` | random generation of every stateful step; `--g0-version` for the pure profiles |
| v4 | `core-g0-v4/lcg64-v1` | random generation of the fourteen G0-based pure profiles |

The fourteen are `closed-g0`, `runtime-word`, `runtime-primitives`,
`runtime-assembly`, `runtime-functions`, `runtime-mutation`,
`runtime-aggregates`, `runtime-loops`, `runtime-nested-loops`,
`runtime-recursion`, `runtime-generics`, `runtime-closures`,
`runtime-comptime` and `runtime-modules`. The three call-graph profiles use their own grammars.

v1 takes each choice as the raw LCG state modulo its bound. Bit 0 of that state
alternates on every draw, and the other low bits have short periods. A v1
literal is an edge value when its first draw is even, so the edge decision of
a literal depends on its position in the stream. v1 stays bit for bit: the fixed
corpora regenerate it from their seeds.

v2 keeps v1's forms and budget split. Each draw passes the new LCG state through
the SplitMix64 finalizer, a bijection, and each choice is the upper 32 bits of
the result modulo the bound. Mixing also separates the streams of consecutive
seeds, which campaigns and helper chains use. Operator choices are uniform; v1's
odd bounds only worked around its low bits. Every literal consumes six draws:
edge versus random with one half each, a uniform index into a 32-value bank, and
four limbs of a random 256-bit Word. The bank is 0, 1, 2, 3, 7, 8, 30, 31, 32,
63, 64, 127, 128, 255, 256, 257, 2^16−1, 2^16, 2^32−1, 2^32, 2^64−1, 2^64,
2^128−1, 2^128, 2^160−1, 2^192, 2^248, 2^255−1, 2^255, 2^255+1, 2^256−2 and
2^256−1. These are shift counts and byte or sign-extension indices with their
neighbours, fixed-width masks and their successors, 64-bit limb boundaries, the
address mask, and the int256 limits with their neighbours.

Over 1,024 consecutive seeds at a 32-node budget, the sample of the registered
Lean test:

| Measure | v1 | v2 |
| --- | ---: | ---: |
| Adjacent literals both edge / mixed / both random | 0.2% / 51.2% / 48.7% | 25.6% / 50.5% / 23.9% |
| Literal operands of one binary operation, both edge | 0 of 380 | 105 of 359 |
| Literals from the edge bank | 22.8% | 50.6% |
| Adjacent Bool literals that differ | 56.5% | 53.4% |
| Consecutive seeds with the same root form | 0% | 15.2% |
| Root-form steps between consecutive seeds, mod 6 | 3 and 5 only | all six |

Every v2 bank value appeared at least 73 times. Taking only the upper bits of
the raw state, without the finalizer, fixes the literal pairing but still
locks consecutive seeds together: their root-form steps were 0, 1, 2 and 5 only.

Position also fixed v1's literal kind. A Word binary operation's form draw is
even, so a leaf left operand starts at an odd draw: outside every `let` it is a
random Word, and inside one it is always a variable. Over 2,000 seeds at the
primitive profile's 94-node G0 budget, none of v1's 180 literal `byte` or
`signextend` indices was below 256, against 49 of 221 for v2. Literal shift
counts below 256 rose from 48 of 330 to 88 of 378, and v2 also produced 17
shift counts of 2^16, 2^32 or 2^64.

The G0-based generation commands take an optional version after `FUEL`:

```text
semantic-case-tool generate|input-generate|primitive-generate|function-generate|mutation-generate|aggregate-generate|loop-generate|generic-generate|closure-generate|comptime-generate|module-generate SEED NODES COUNT ATTEMPTS FUEL [VERSION]
```

Without `VERSION` they generate v1, so the fixed manifests and their validators
regenerate unchanged; an unknown version is rejected. `replay` regenerates a
seeded case with its recorded revision, and `shrink` gives each reduction its
parent's revision. The call-graph commands take no version.

`scripts/semantic-campaign.py` passes `core-g0-v4/lcg64-v1` in random mode for
the twelve profiles; `--g0-version` selects a revision explicitly. With
`--corpus` it passes the manifest's version, and with `--case` it keeps the
saved case's; a disagreeing `--g0-version` is refused. The campaign summary
records `configuration.g0Version` and the generated cases' versions in
`generation.generatorVersions`. `semantic-suite.py --mode random` therefore
generates v4 for these profiles, and fixed mode stays on v1. The stateful
profiles build their random aggregate steps with v3 under their own tools,
which record, replay and pass on each case's mask but reject v4, and their
fixed corpora stay on v1 (see
[storage campaigns](#run-and-reduce-storage-campaigns)).

### Revision three: swarm masks

v3 is v2's grammar restricted by a swarm mask drawn once per case. The mask
covers the 26 operators and non-leaf forms: Bool and Word negation, leading
zeros, the nineteen binary operators including the three comparisons,
`addmod`, `mulmod`, `let` and `if`. Literals and locals always stay available.
Each is enabled by its own bit of one mixed, domain-separated SplitMix64 draw
from the case seed, so about half are enabled; every G0 program of a case,
such as each helper and a comptime constant, uses the same mask.

A form stays available while the mask enables it or one of its operators, and
an operator is then chosen uniformly among the enabled ones. Choosing a form
first draws as v2 does. Only when that form is disabled does a second draw pick
uniformly among the enabled non-leaf forms, so leaves keep v2's probability
and masked programs keep v2's size instead of ending early. With the full mask
nothing is redrawn and v3 is v2 exactly.

A v3 case records the enabled features in `provenance.swarmMask`, as
`features` names in catalog order. Replay requires the mask of a v3 case,
checks that a seeded case's mask is its seed's, and rejects a mask on any other
revision. A reduction copies its parent's mask. Random campaigns have no
coverage requirements of their own, since required features, literals and
inputs come only from a manifest, so masks cannot fail a random run on
coverage.

Over 1,024 consecutive seeds, the registered Lean test's sample:

| Measure, per 1,024 programs | v2, 32 nodes | v3, 32 nodes | v2, 64 nodes | v3, 64 nodes |
| --- | ---: | ---: | ---: | ---: |
| Operators | 7,281 | 7,153 | 12,059 | 12,035 |
| Distinct operators | 4,670 | 3,810 | 6,201 | 4,866 |
| Distinct parent-child operator pairs | 5,810 | 5,187 | 9,638 | 8,292 |
| Sum of maximum operator depths | 4,205 | 4,322 | 5,363 | 5,469 |
| An operator directly inside itself, besides `let` | 486 | 934 | 898 | 1,674 |
| Programs using one operator three times or more | 464 | 564 | 616 | 673 |
| Distinct operator pairs in the whole sample | 428 | 508 | 504 | 551 |

The masks enable 13.0 of the 26 features on average, and each feature is
enabled in 900 to 1,148 of 2,048 masks. Both revisions use all 26 features over
the sample. Before the second draw, a disabled form fell to a leaf instead;
those programs had 5,561 operators at 32 nodes, a quarter fewer than v2.

### Revision four: masks within the emitter

v4 is v3 with each case's swarm mask restricted to the G0 features the
profile's emitter renders. Each emitter declares them from its renderer's own
operator predicates (`featureSupport` in the emitter modules), and a registered
Lean test probes every catalog feature through every pure emitter: a feature
emits exactly when it is declared.

| Renderer | Features | Programs |
| --- | --- | --- |
| Scalar | Bool and Word negation; add, sub, mul, and, or, xor, `==` and `>`; `let` and `if` (12 of 26) | `closed-g0`, `runtime-word`, `runtime-functions` and `runtime-mutation`; comptime and module constants |
| Primitive, call-graph and aggregate | all 26 | `runtime-primitives`, `runtime-aggregates`, `runtime-loops`, `runtime-generics` and `runtime-closures`; comptime and module steps |
| Inline Yul, in each of its three forms | all 26 | `runtime-assembly` |

Where the emitter renders every feature, v4 is v3 apart from its version:
`runtime-primitives`, `runtime-aggregates`, `runtime-loops`,
`runtime-generics` and `runtime-closures`. The four scalar profiles restrict
the mask of every G0 program of the case. A comptime or module case records
its step's mask, which is the unrestricted v3 mask, and its constant uses that
mask restricted to the scalar renderer's features.

When the restriction removes every operator the mask enabled, the case uses the
emitter's whole feature set instead, so it never draws programs of leaves,
`let` and `if` alone where v3 had operators. Under the scalar renderer that
happens for about one seed in a thousand (18 of the first 20,000; seed 323 is
the first). A v3 mask that enables no operator, of which the first 200,000
seeds have none, restricts plainly.

A v4 case records its effective mask in `provenance.swarmMask`. Replay
requires it, rejects a mask outside the profile's features and checks a seeded
case's mask against its seed; a reduction copies its parent's mask. The
stateful tools parse versions only up to v3, so they reject v4 as an unknown
version. The pure case tool accepts all four.

Over the first 256 functions accepted from seed 1 at the campaign's default
budgets, with seeded inputs, v4 left no exclusion for an unsupported operator.
An identity function returned each of its eight to twelve recorded inputs
under direct Core evaluation; for `closed-g0` the column counts programs that
are one literal. No accepted function was constant, since every runtime
profile rejects functions whose boundary outputs agree.

| Profile | Distinct sources | Identity | Attempts per function | Unsupported-operator exclusions | Other v4 exclusions |
| --- | ---: | ---: | ---: | ---: | --- |
| `closed-g0` | 193 → 245 | 174 → 41 | 4.08 → 1.00 | 788 → 0 | none |
| `runtime-word` | 39 → 188 | 210 → 82 | 4.52 → 1.54 | 873 → 0 | 137 equal boundary outputs |
| `runtime-functions` | 133 → 220 | 110 → 36 | 6.25 → 1.89 | 771 → 0 | 161 template budget, 67 equal boundary outputs |
| `runtime-mutation` | 253 → 256 | 4 → 3 | 9.79 → 1.04 | 2,147 → 0 | 10 template budget |
| `runtime-comptime` | 256 → 256 | 0 → 4 | 6.09 → 1.48 | 930 → 0 | 120 constants without an operation, 2 equal boundary outputs |
| `runtime-modules` | 256 → 256 | 0 → 0 | 6.98 → 1.57 | 995 → 0 | 113 constants without an operation, 33 template budget |
| `runtime-primitives` | 150 | 103 | 2.29 | 0 | 331 equal boundary outputs |
| `runtime-aggregates` | 256 | 24 | 1.00 | 0 | none |
| `runtime-loops` | 256 | 0 | 1.13 | 0 | 34 loops that returned every positive-trip input unchanged |
| `runtime-generics` | 256 | 0 | 1.00 | 0 | none |
| `runtime-closures` | 256 | 0 | 1.00 | 0 | none |

Single values are the same under both revisions. Duplicates no longer form
the majority of any profile, but the identity stays common where a one-leaf
program always passes and many larger ones give equal boundary outputs: 82 of
256 `runtime-word` functions under v4 and 103 of 256 `runtime-primitives`
functions under both revisions. v4 does not deduplicate sources.

Frozen sixteen-case random matrices of the eleven profiles, from root seed 1
with shared compilation, matched all 176 v4 cases on O0 in 279 seconds and on
O2 in 303 seconds, against 268 and 363 seconds for v3. Both revisions compiled
35 distinct sources, since sixteen cases hold one or two functions of each
runtime profile. v4 needed 16 `closed-g0` generation attempts instead of 70, 3
for `runtime-functions` instead of 50, 2 for `runtime-mutation` instead of 21
and 2 for `runtime-modules` instead of 18. v3's O2 matrix again crashed the
compiler on all eight inputs of the recorded `runtime-comptime` plan seed
`13439332813997308049`. v4 accepts the preceding seed, which v3 excluded for an
unsupported operator, so its sixteen cases end before that plan; generated
under v4, the plan still crashes.

With whole functions, sixteen per profile on O0 and both revisions from the
same root, v4 found 14 distinct `runtime-word` sources against 3 (4.2 against
1.5 per minute) in 23 attempts against 81, 15 `runtime-functions` sources
against 13, and 11 `runtime-primitives` sources under both. Sixty-four
`closed-g0` cases had 63 distinct sources in 64 attempts, while v3 exhausted
its 256 default attempts after 58 programs with 47 sources. Other work loaded
the machine heavily during these runs, with load averages up to 60, so their
times are approximate; source and attempt counts do not depend on load.

## Seeded runtime inputs

Random campaigns of the sixteen runtime-input pure profiles, every pure
profile except `closed-g0`, run each accepted function at its boundary inputs
and then at four inputs derived from the case seed. Fixed corpora keep the
boundary inputs alone. The four come from a SplitMix64 stream that starts at
the case seed XOR a fixed domain constant, five outputs each:

1. a full random 256-bit Word;
2. a random Word whose bit width is uniform from one to 256;
3. a small value below 512;
4. the two's-complement negation of another uniform-width value.

A seeded input can coincide with a boundary input. The generated origin then
records `"inputSelection": "seeded-inputs-v1/splitmix64"`, and `inputIndex`
counts the boundary inputs first. Replay recomputes the list from the recorded
seed; it rejects a seeded index whose origin names no selection, an unknown
selection and a changed input. A reduction keeps its input as data, like any
reduced case. An origin without the field, as in every fixed corpus, means the
boundary inputs alone.

One function now gives eight random cases in the four-input profiles, ten in
the two loop profiles and twelve in `runtime-primitives`, `runtime-assembly`,
`runtime-call-graphs` and `runtime-aggregate-call-graphs`. `--cases` still
counts inputs, so a sixteen-case run of a four-input profile covers two
functions rather than four. The admission filters still use the boundary
inputs only.

A random runtime-input campaign can instead ask for whole functions:
`--functions N` generates N accepted functions with all of their inputs. It
replaces `--cases` with N times the profile's inputs per function, and every
count stays per case. The case tool returns at most 1,024 cases, which bounds
N:

| Profiles | Inputs per function, seeded (boundary) | Largest N, seeded (boundary) |
| --- | ---: | ---: |
| `runtime-word`, `runtime-functions`, `runtime-mutation`, `runtime-aggregates`, `runtime-generics`, `runtime-closures`, `runtime-comptime`, `runtime-modules` | 8 (4) | 128 (256) |
| `runtime-loops`, `runtime-call-graph-loops`, `runtime-nested-loops` | 10 (6) | 102 (170) |
| `runtime-primitives`, `runtime-call-graphs`, `runtime-aggregate-call-graphs` | 12 (8) | 85 (128) |
| `runtime-recursion` | 11 (7) | 93 (146) |

The summary records `configuration.functions`,
`generation.requestedFunctions` and `generation.inputsPerFunction`, all null
without the option.

The campaign limits each case-tool response to 2 MiB, which at the suite's
node budgets holds about 64 whole `runtime-word` functions but only 6
`runtime-loops` functions. Random generation therefore takes as many requests
as it needs:

- The first request asks for every case.
- A response over the limit is requested again from the same seed for half as
  many whole functions, and later requests keep that size.
- Each later request starts at the seed after the previous request's last
  attempt, modulo 2^64 as the case tool's `Seed.ofNat` reduces it, with the
  attempts left. Every request but the last asks for whole functions.

The merged cases, exclusions, attempts and status therefore equal one
request's for any request sizes. One function whose cases alone exceed the
limit stays an inconclusive `output-limit`. The summary and `generation.json`
record `generation.requests` and `generation.outputLimitRetries`, both null
for a corpus or a saved case. `Tests/scripts/test-semantic-chunked-generation.py`
compares one native request with one-function, two-function and halving
requests byte for byte for every pure profile, from seed 1 and from two below
2^64, and with an exhausted attempt budget.

With `--functions`, the default attempt budget is at least 16 candidates per
function, up to the case tool's 10,000, in the campaign and in the suite. From
six start seeds at each profile's bound, the most a profile needed was 6.8 per
function (`runtime-aggregate-call-graphs`); `runtime-call-graph-loops` needed
5.0, `runtime-call-graphs` 4.7, `runtime-primitives` 4.5, `runtime-word` 2.5
and every other profile at most 1.7. The suite derives each profile's seed
from that budget, so `--functions` runs from a root seed draw other seeds than
before. The 1,024-case limit of a campaign, and so the bounds above, are
unchanged. A frozen O0 random matrix from root seed 1 at `--functions 102`
matched all 1,020 `runtime-loops` cases in 31 requests with 5 retries and all
816 `runtime-closures` cases in 17 requests with 4 retries, with 102 distinct
sources each, at 2.8 and 3.6 sources per minute; neither stopped at
`output-limit`. The campaign refuses `--functions` with `--cases`, with a
corpus or a saved case, for `closed-g0` and outside the bounds above.

These profiles' generation commands take the selection after `FUEL`, in either
order with a G0 version:

```text
semantic-case-tool input-generate SEED NODES COUNT ATTEMPTS FUEL [VERSION] [seeded-inputs-v1/splitmix64]
semantic-case-tool call-graph-generate SEED NODES COUNT ATTEMPTS FUEL [seeded-inputs-v1/splitmix64]
```

`scripts/semantic-campaign.py` passes it in random mode, and
`--input-selection boundary` returns to the boundary inputs. A corpus refuses
the seeded selection and `--case` keeps the saved case's. The summary records
`configuration.inputSelection` and the generated cases' selections in
`generation.inputSelections`.

Over 2,048 consecutive seeds, the registered Lean test requires the top bit of
the full random input in 900 to 1,148 cases (1,024 expected), widths from at
most eight bits to more than 248, more than 400 distinct small values with some
below 32 and some from 256, and a negative fourth input in at least 2,000.

## Boundary identities

Random campaigns of the runtime-input profiles whose generated functions can be
identities apply the acceptance filter `exclude-boundary-identity-v1`. After the
profile's own filters, it excludes a function that returns each of its boundary
inputs unchanged, with the reason `every boundary input returned itself` and
the code `boundary-identity`. Such a function exercises only each path's ABI
decoding and return, yet costs a compilation and every input's deployment and
execution. The filter decides on the boundary results the profile already
computes; seeded inputs never take part, so a function the filter keeps can
still return some seeded input unchanged.

| Profiles | Identity filter |
| --- | --- |
| `runtime-word`, `runtime-primitives`, `runtime-assembly`, `runtime-functions`, `runtime-mutation`, `runtime-aggregates`, `runtime-closures`, `runtime-comptime`, `runtime-modules`, `runtime-call-graphs`, `runtime-aggregate-call-graphs` | applied |
| `runtime-loops`, `runtime-call-graph-loops`, `runtime-nested-loops`, `runtime-recursion` | not needed: a loop must already change a positive-trip boundary input, and a nested loop or a recursion some boundary input |
| `runtime-generics` | not needed: input 0 returns the result of input 1 (Word and pair variants) or its successor (sum), so a generic function never returns both 0 and 1 |

A closure returns `5 * step(x) + 4 * x + 4` (snapshot) or `+ 5`
(independent), and a module combines its constant with step results, so both
are identities only for steps that hit specific Words at every boundary input.
None occurred in the measurements below, but the generators allow them, so
both profiles apply the filter. `closed-g0` has no runtime input.

The filter is versioned on its own rather than as a G0 revision. Acceptance
belongs to each profile's case module, not to the G0 expression generator, and
two of the eleven profiles do not use G0. Only generated cases pass filters:
imported cases and reductions never did, and a reduction may itself be an
identity. So the filter lives in the generated origin next to
`inputSelection`, while a G0 revision is copied into every reduction. It
composes with every G0 revision and input selection, and the stateful profiles,
whose steps are not runtime-input functions, are untouched.

A filtered origin records `"acceptance": "exclude-boundary-identity-v1"`; an
origin without the field, as in every fixed corpus, applied the profile's own
filters only. Replay applies the recorded filter again: a saved identity that
claims it is refused with the exclusion reason, and an unknown value with
`unsupported acceptance filter`. Without the field, a filtered case is also a
valid case of the profile's own filters, since the filter only narrows
acceptance. Reductions record no filter. The generation commands of the eleven
profiles take the filter after `FUEL`, in any order with a G0 version and an
input selection; the others refuse it:

```text
semantic-case-tool input-generate SEED NODES COUNT ATTEMPTS FUEL [VERSION] [seeded-inputs-v1/splitmix64] [exclude-boundary-identity-v1]
```

`scripts/semantic-campaign.py` passes the filter in random mode, and
`--acceptance profile` returns to the profile's own filters. A corpus refuses
the filter and `--case` keeps the saved case's. The summary records
`configuration.acceptance` and the generated cases' filters in
`generation.acceptances`; both are null for the other profiles. With the
filter, every generation request without the option is byte for byte the same
as before: 666 generation runs of all fourteen commands under every G0
revision and input selection, and replay, observation and reduction of 1,332
of their cases, matched the tool before the filter.

Over the first 256 functions accepted from seed 1 at the campaign's default
budgets with seeded inputs, under v4 and then also under the filter, no
accepted function returned all of its eight to twelve recorded inputs
unchanged:

| Profile | Distinct sources | Identity | Attempts per function | Identity exclusions | Other exclusions |
| --- | ---: | ---: | ---: | ---: | --- |
| `runtime-word` | 188 → 240 | 82 → 0 | 1.54 → 2.15 | 116 | 137 → 179 equal boundary outputs |
| `runtime-primitives` | 150 → 226 | 103 → 0 | 2.29 → 3.98 | 189 | 331 → 575 equal boundary outputs |
| `runtime-functions` | 220 → 243 | 36 → 0 | 1.89 → 2.21 | 40 | 161 → 189 template budget, 67 → 82 equal boundary outputs |
| `runtime-mutation` | 256 | 3 → 0 | 1.04 → 1.05 | 3 | 10 template budget |
| `runtime-aggregates` | 256 | 24 → 0 | 1.00 → 1.11 | 28 | none |
| `runtime-closures` | 256 | 0 | 1.00 | 0 | none |
| `runtime-comptime` | 256 | 4 → 0 | 1.48 → 1.50 | 4 | 120 → 121 constants without an operation, 2 equal boundary outputs |
| `runtime-modules` | 256 | 0 | 1.57 | 0 | 113 constants without an operation, 33 template budget |
| `runtime-call-graphs` | 256 | 46 → 0 | 3.41 → 4.07 | 57 | 322 → 377 entries without a call, 294 → 353 equal boundary outputs |
| `runtime-aggregate-call-graphs` | 256 | 72 → 0 | 4.87 → 6.81 | 99 | 567 → 814 entries without a call, 309 → 418 equal boundary outputs, 115 → 156 without an aggregate call composition |

The unchanged profiles had no identity: `runtime-loops` (1.13 attempts per
function), `runtime-call-graph-loops` (4.28) and `runtime-generics` (1.00).
Distinct behaviours on the boundary inputs, which every function of a profile
shares, rose from 159 to 228 in `runtime-word`, 135 to 218 in
`runtime-primitives`, 190 to 221 in `runtime-functions`, 216 to 235 in
`runtime-aggregates`, 190 to 231 in `runtime-call-graphs` and 150 to 205 in
`runtime-aggregate-call-graphs`.

No other trivial class forms a majority of a profile under the filter. On the
recorded inputs, `runtime-mutation` adds a constant to its input in 112 of 256
functions (44 %), unchanged by the filter, since its templates fold a closed
scalar into the input. `runtime-comptime` adds a constant in 49 and
`runtime-aggregates` in 37. In `runtime-word`, 45 functions XOR a constant, 23
add one and 20 subtract the input from one, 88 of 256 (34 %); in
`runtime-functions` 58 (23 %) and `runtime-primitives` 33 (13 %) fall in these
classes. Closures and modules have none. The filter excludes none of them.

The filter raises the attempts per function. From seed 1, the campaign's
default of 256 attempts covers about 119 whole `runtime-word` functions,
below its bound of 128, and about 37 `runtime-aggregate-call-graphs`
functions; 512 attempts cover about 75 of the latter, below their bound of 85.
The default budget of a whole-function campaign now scales with N (see
[seeded runtime inputs](#seeded-runtime-inputs)).

Frozen random matrices from root seed 1 ran the eleven G0 profiles and both
call-graph profiles before the filter (`8d62b8e2b`) and with it (`83f590764`)
side by side, with eight whole functions per runtime profile and sixteen
`closed-g0` cases:

| Matrix | Matched | Distinct sources | Seconds | Sources per minute |
| --- | ---: | ---: | ---: | ---: |
| O0 before | 752/752 | 92 | 981 | 5.6 |
| O0 with the filter | 752/752 | 95 | 996 | 5.7 |
| O2 before | 744/752 | 84 | 876 | 5.8 |
| O2 with the filter | 744/752 | 87 | 889 | 5.9 |

Sources and seconds count the profiles that completed; O2 sources and seconds
leave out `runtime-comptime`, whose third function is the recorded plan
`13439332813997308049` and crashed O2 code-image export on all eight of its
inputs on both sides. `runtime-word` rose from 7 to 8 distinct sources of 8
functions and `runtime-primitives` from 5 to 7, in 19 and 26 generation
attempts instead of 10 and 17; every other profile compiled 8 sources on both
sides. With a fixed number of whole functions the rate moves little: each
excluded identity is replaced by another function with as many cases, so the
gain is the repeated sources the identities would have been. `runtime-loops` and `runtime-closures` stopped at generation on both
sides, since one request's 80 and 64 cases exceeded the 2 MiB limit on a tool
response (see [seeded runtime inputs](#seeded-runtime-inputs)); with four
whole functions both matched all 40 and 32 cases on O0 and on O2 on both
sides, with four sources each.

## Validate the emitter against Rust

Prepare the checked Hull exporter as described in
[Rust runtime compatibility checks](RUST_PARITY.md). Then run:

```sh
python3 scripts/test-source-synthesis-rust.py
```

The default validation checks 27 explicit operation, boundary-value and scope
cases, plus twelve generated cases. Each emitted source passes the actual
public Rust checking pipeline. Its imported Hull then executes through the
native Core contract runner and must return exactly the ABI encoding of the
original Core result. Temporary source files and exports are removed at the end.

This command does not execute an EVM. It verifies source acceptance and the
imported-Hull path; it is not the complete three-path differential campaign.
For the closed G0, runtime-input, named-helper, raw-primitive, call-graph,
private-mutation, aggregate, aggregate call-graph, call-graph loop, aggregate loop, generic, two-slot storage, storage rollback, keyed storage and event-log emitters, a kernel-checked theorem relates the emitted text to
the original Core result, for the storage and event-log emitters its top-level transaction, under an independent source semantics. It assumes Rust parsing, typing, compilation and execution; see
[scalar emitter meaning](../docs/design/scalar-emitter-meaning.md). Core typing
of admitted generated/reduced programs is established by the existing checker
soundness theorem.

Closed G0 computations can be folded during Rust specialization or optimization.
Source-feature coverage therefore does not imply execution of those arithmetic
opcodes in the resulting bytecode. A runtime-input profile is needed to make a
separate backend opcode-coverage claim.

## Validation and retained artifacts

The emitter and case-tool regressions are registered in `Tests/Main.lean`.
They check full-width values, scope, branch-local computations, unsupported
operations, replay tampering, fuel exhaustion and checked reduction candidates.

Keep regression cases and replay metadata that explain a finding. Remove
disposable verification exports and logs after recording the results. Never
count source rejection, missing execution or resource exhaustion as agreement.
Core execution fuel and EVM gas have separate meanings and budgets.

## Compare one case on all three paths

Install the pinned-compatible Anvil toolchain and build the Rust code-image
exporter as described in [RUST_PARITY.md](RUST_PARITY.md). The runner starts its
own loopback-only Anvil and needs an environment that permits local listening
sockets. It never uses an existing chain or a remote RPC endpoint.

Extract one generated case from the corpus above:

```sh
python3 - <<'PY'
import json
from pathlib import Path
root = Path('.upstream/semantic-cases')
corpus = json.loads((root / 'corpus.json').read_text())
assert corpus['status'] == 'complete' and corpus['cases']
(root / 'case.json').write_text(json.dumps(corpus['cases'][0], indent=2) + '\n')
PY
python3 scripts/semantic-differential.py \
  --case .upstream/semantic-cases/case.json \
  --output .upstream/semantic-cases/run
```

The output directory must be new. A run rechecks and re-emits the case, computes
the original Core result, compiles checked Rust Hull and exact Sonatina
images, deploys those bytes on Anvil, and executes the same imported contract
through Core. Every passing run has three completed observations and three
matching pairwise comparisons. No saved expected result is trusted.

The default backend is `sonatina-o0`. Select `--backend sonatina-o2` to compile
the same source with the real O2 pipeline. Both choices use the pinned
Sonatina revision and its authoritative linker symbol extents. The pure,
storage and call adapters, their campaigns and `semantic-suite.py` accept the
same option. Run separate output directories for each backend; each has its
own observations, compilation failures and finding fingerprint.

For the seventeen pure profiles, `--backend yul --solc PATH` instead runs the checked
Rust Yul output through solc `0.8.35+commit.47b9dedd` with optimization and Osaka
enabled. The EVM deploys the creation bytes and checks its installed runtime
against the deployed bytes from the same solc compilation. Imported Hull uses
separately validated Sonatina O0 images, recorded explicitly in `pathBackends`.
This compares the same pure result without claiming Yul-linked Hull execution.
The stateful adapters reject Yul. No backend silently falls back to another.

The result is `report.json`. It records tool versions and hashes, pinned
compiler/exporter receipts, source and artifact hashes, deployment and call
inputs, budgets, process outcomes, raw observations and normalized comparisons.
It preserves a valid returned payload of the wrong ABI length as an observable
semantic mismatch; malformed transport remains an adapter error.

Replay the complete archive into another new directory:

```sh
python3 scripts/semantic-differential.py \
  --replay .upstream/semantic-cases/run \
  --output .upstream/semantic-cases/replay
```

Replay verifies all recorded archive members, rejects missing or changed files
and tool drift, restores the saved budgets and backend, and performs fresh
executions. An explicit conflicting backend is rejected. A legacy report with
no backend field denotes O0; invalid or null fields do not. Both artifact and
export provenance must agree with the selected optimization level.
Yul additionally retains and checks the exact compiler input/output, Yul source,
compiler identity and matching main/Yul Hull artifacts. Both original and
reduced module archives can be moved before replay; compiler settings and
recorded binary hashes remain fixed. `--solc` may identify the same executable
at another path, but cannot change its hash or full version during exact replay.
To deliberately change budgets, backend or tools, use the saved `case.json` with
`--case` instead. This starts a new experiment rather than an exact replay.

Useful limits are `--direct-fuel`, `--core-fuel`, `--gas`, `--timeout`,
`--total-timeout`, `--output-limit` and `--artifact-limit`; see `--help` for
defaults. The runner exits zero only for `matched`. Rejection, compiler crashes,
execution errors, semantic mismatches, unsupported scope and inconclusive
resource limits remain distinct in the report. In particular, insufficient
deployment gas does not count as a mismatched return value.

Run the runner's protocol and resource regressions with:

```sh
python3 scripts/test-semantic-differential.py
```

These include real child-process timeouts/output limits and artifact tampering.
They complement actual Anvil integration; unit tests alone do not establish
that all three execution paths ran.

## Run a bounded campaign

Run the fixed corpus after building the tools and exporters above:

```sh
python3 scripts/semantic-campaign.py \
  --corpus scripts/semantic-corpus.json \
  --output .upstream/semantic-ci \
  --seconds 300 --disk-bytes 134217728
```

The manifest fixes sixteen seed/node-budget pairs and their expected versions
and AST features. Its required coverage includes every enabled operation,
bindings, branches, and Word literals zero, one, maximum and the high bit. Only
cases that actually match across all three paths contribute to passing
coverage. This is source AST coverage, not runtime opcode coverage.

For a seed search instead of the fixed corpus:

```sh
python3 scripts/semantic-campaign.py \
  --seed 78 --nodes 32 --cases 16 --attempts 256 \
  --output .upstream/semantic-search \
  --seconds 300 --disk-bytes 134217728 --shrink-attempts 32
```

This search generates with [G0 revision four](#g0-generator-revisions); add
`--g0-version` with another revision to search that one instead.
`--attempts` bounds generation attempts. `--shrink-attempts` bounds candidate
executions across the entire campaign, and `--shrink-candidates` bounds each
candidate batch. Core fuel, EVM gas, per-case time, total campaign time and
retained directory size have separate limits. Time and disk usage are checked
during child-process execution; these are polling limits, not OS quotas.
An interrupt or SIGTERM stops owned children and writes the campaign summary.

The command prints per-case results and a final summary. `summary.json` records
generated, excluded, executed, completed, matched, mismatched, inconclusive,
error and unexecuted counts, with source/compiler rejections counted separately
within errors. Generation exhaustion, incomplete coverage and interrupted or
resource-limited runs never pass. Exit zero requires every requested case to
match and every required coverage item to be present.

All generated cases and compact execution reports remain in `cases/` and
`results/`. Successful runs' large exports and logs are removed. These compact
reports retain receipts and observations but cannot serve as exact archives;
use their saved case with `--case` to execute a new experiment.

Each finding retains complete original and final reduced archives under
`findings/`, plus `shrink.json`. A candidate must retain the failure category,
stage, disagreeing paths, and each path's outcome and payload form. A wrong
return value cannot shrink into a revert or a resource failure. Other genuine
findings encountered during reduction are retained separately, without recursive
reduction. Exact replay uses the single-case runner's `--replay ARCHIVE` option.

## Shared compilation in campaigns

Checked Hull export and code-image export read a case's source files, not its
runtime input, and they took most of each case's time: 3.9 of 4.5 seconds per
case in a random `runtime-word` run on O0. With seeded inputs one function has
eight to twelve cases. A pure campaign therefore compiles each distinct source
once per backend and shares the result.

Before compiling, the runner computes the case's compilation identity: the
SHA-256 digests of its own source files (all four bundle files for modules),
the backend and the optimization of the linked images, every standard-library
source, both compiler binaries and their build receipts, the four exporter
files, the runner itself and the Python interpreter; Yul adds solc's digest
and full version and the Yul exporter and transport. Cases whose identities
are equal share one compilation. No case is matched by its position: cases of
two seeds that emit byte-identical sources share too.

The compilation runs once in `.work/compilations/DIGEST/`, named by the
identity's digest, so every case using it was compiled from the same paths.
Each case copies all of its outputs into its own run directory and checks
their digests, so its archive stays self-contained. Hull provenance names the
shared directory's `case.sol`; validation checks that the case's own
`case.sol` has exactly the digest compiled there, and a module case's bundle
receipt names the shared files the same way. `report.json` records
`compilation` (`solcore-lean.semantic-compilation.v1`): the identity and its
digest, the shared directory, the output digests and whether this case
compiled or reused it. A reusing case lists the shared compiler processes in
`processes` with `reused: true` and their original times. Every case still
runs its own direct Core replay, deployment, EVM call and imported Hull
execution, so a matched case executed all three paths at its own input.

A rejection or crash of a shared source stays with its compilation. Every case
with that source reports the first case's category, stage, detail and
fingerprint, keeps the partial outputs in its own archive and counts as an
error and a finding, without compiling again. The failure is raised where its
stage would have run, so a Yul export failure follows the check of the copied
Sonatina exports. A timeout, output limit, interruption or adapter failure is
not kept, and the next case with that source compiles again. At most eight
compilations are kept, the least recently used being deleted first; the rest
are deleted with the work directory.

Reduction candidates compile in their own run directories, as before. Exact
replay of any archive, including one whose case reused a compilation, compiles
from that archive's own case. `summary.json` records `compilation` with the
counts `distinctSources`, `compiled` and `reused`, and each case row records
`compilation` as `compiled`, `reused` or null when the case reached no
compiler, for example after a direct Core resource limit. Fixed corpora share
compilations the same way; their cases, categories, fingerprints and coverage
are unchanged.

With root seed 1, sixteen random cases each of `runtime-word`,
`runtime-primitives`, `runtime-loops` and `runtime-call-graphs` took 71 seconds
on O0 and on O2 instead of 303 and 306; their 64 cases needed seven
compilations. The fixed corpora of the same profiles, 213 cases with 74
distinct sources, took 455 seconds on each backend instead of 1,032 and 1,020.
Every case, category, fingerprint and coverage set equaled the run without
sharing. Per profile on O0 (O2 was within 4%):

| Profile | Cases | Distinct sources | Cases per minute | Distinct sources per minute |
| --- | ---: | ---: | ---: | ---: |
| `runtime-word`, random | 16 | 2 | 13.3 → 52.6 | 1.66 → 6.58 |
| `runtime-primitives`, random | 16 | 1 | 13.1 → 66.8 | 0.82 → 4.17 |
| `runtime-loops`, random | 16 | 2 | 11.9 → 48.6 | 1.49 → 6.08 |
| `runtime-call-graphs`, random | 16 | 2 | 12.4 → 51.1 | 1.55 → 6.39 |
| `runtime-word`, fixed | 16 | 4 | 12.7 → 35.1 | 3.17 → 8.77 |
| `runtime-primitives`, fixed | 81 | 34 | 12.7 → 25.2 | 5.34 → 10.58 |
| `runtime-loops`, fixed | 60 | 10 | 11.6 → 39.1 | 1.93 → 6.51 |
| `runtime-call-graphs`, fixed | 56 | 26 | 12.7 → 23.5 | 5.91 → 10.89 |

A compilation still takes about four seconds. A case that reuses one takes
0.6 to 0.8 seconds: tool identity checks, four short processes and the
imported Hull run. Other work on the machine was heavier during the runs
without sharing (load average 5 to 8 against 3 to 4), so the compilation
counts are the load-independent comparison.

All fourteen pure fixed corpora, 595 cases, gave the same cases, categories,
fingerprints, counts and coverage with and without sharing on O0 and on O2.
So did the `runtime-word`, `runtime-loops`, `runtime-modules` and
`runtime-call-graphs` corpora on Yul: 176 cases with 51 distinct sources, in
546 instead of 1,433 seconds under the same parallel load. Synthetic-adapter
campaigns, which keep every case's archive, replayed all 44 of their archives
exactly, 39 of them reused: eight `runtime-word` and eight `runtime-modules`
cases on O0 and on Yul, and twelve `runtime-primitives` cases on O2. The
recorded O2 `runtime-comptime` crash (derived seed `13439332813997308047`)
crashed all eight inputs of its function again, with the same categories and
fingerprints, after one compilation instead of eight, in 19 instead of 84
seconds. `semantic-fuzz.py`'s crash-site replay named the same call site for
the compiling archive and each reusing one. `check-semantic-findings.py`
passed with the fixed closed case `cases/0006.json`.

Random sources repeat across seeds in three scalar profiles. Of the first 64
functions accepted from seed 1 under revision three with seeded inputs,
`runtime-word` had 12 distinct sources, `runtime-functions` 24 and
`runtime-primitives` 39; every other runtime-input profile had 64. Most repeats
are the identity `f(x) = x`: 51 of the 64 `runtime-word` functions and 26 of
the 64 primitive functions. Over 256 functions per revision, the identity was
71 to 82% of accepted `runtime-word` functions at 32 nodes and 41 to 44% of
`runtime-primitives` functions at 96 nodes under each of the three revisions.
The emitter of `runtime-word`, `runtime-functions` and `runtime-mutation`
rejects the extended operators, which most generated programs contain: they
caused 255 of 262 exclusions for `runtime-word`, 548 of 554 for
`runtime-functions` and 578 of 606 for `runtime-mutation`. A one-leaf program
always becomes the identity and passes; the mutation templates keep that
profile's sources distinct. The primitive profile's exclusions were all
functions whose eight boundary outputs agreed. Sharing compiles each repeat
once, but every repeat still runs all its inputs: a 64-case random
`runtime-word` run had eight functions and two distinct sources. [Revision
four](#revision-four-masks-within-the-emitter) keeps masks within each
emitter's features and removes most of these repeats.

## Check the reducer

The explicit test adapter below perturbs a copied observation only after all
three real executions agree:

```sh
python3 scripts/semantic-campaign.py \
  --seed 78 --nodes 32 --cases 1 --attempts 1 \
  --test-perturb-path rustEvm --shrink-attempts 8 \
  --output .upstream/semantic-reducer-test
```

This command intentionally exits nonzero. Its synthetic findings are marked
and stored separately from genuine findings. The actual execution reports are
unchanged; the changed observation exists only in `analysis.json`. Reproduce
the reduced synthetic finding with `--case` and the same explicit adapter:

```sh
python3 scripts/semantic-campaign.py \
  --case .upstream/semantic-reducer-test/findings/synthetic/0000/reduced/case.json \
  --test-perturb-path rustEvm --shrink-attempts 0 \
  --output .upstream/semantic-reducer-replay
```

Without the adapter, that case's three real results still match. This tests
detection, preservation and reduction of a controlled difference; it is not
evidence of an upstream compiler bug.

Focused campaign tests and independent corpus validation are available with:

```sh
python3 scripts/test-semantic-campaign.py
python3 Tests/scripts/test-semantic-corpus.py
```

The corpus validator checks deterministic materialization, native Core
execution, replay and AST coverage. It does not execute the EVM. The complete
campaign above executes all three paths for every passing corpus case.

## Compare functions with runtime inputs

The `runtime-word` profile is the first M4 extension. It keeps the closed G0
generator and saved cases unchanged. The original Core program applies a checked
Word-to-Word lambda to one recorded Word. Its Solcore source accepts that same
Word through `SynthesizedInput.run(uint256)`, so changing the input does not
change the function's source. Each input is a separate comparison case and
currently has its own compilation and deployment.

```sh
python3 scripts/semantic-campaign.py \
  --profile runtime-word --seed 78 --nodes 32 --cases 8 --attempts 256 \
  --output .upstream/semantic-runtime-inputs
```

Generation abstracts one Word literal from a G0 expression without capturing
local variables. It evaluates the resulting Core function at zero, one, maximum
Word and the high bit, and accepts the function only if all four return and at
least two results differ. One accepted function supplies up to four cases in
that order, followed in random mode by four
[seeded inputs](#seeded-runtime-inputs). `--attempts` counts function candidates; `--cases` counts individual
input comparisons. The final function's inputs may be truncated by that limit;
[`--functions N`](#seeded-runtime-inputs) requests whole functions instead.
Generation fuel failures appear in `generationResourceExclusions` as a subset
of `excluded`, separately from executed-case resource failures.

Native commands are:

```text
semantic-case-tool input-generate SEED NODES COUNT ATTEMPTS FUEL
semantic-case-tool input-emit FUNCTION.json INPUT [FUEL]
```

`FUNCTION.json` is a Core Wire program containing a closed Word-to-Word lambda.
`INPUT` is a canonical unsigned decimal Word. Imported and reduced functions
may be constant; the input-sensitivity requirement is a generation filter.
The existing `observe`, `replay` and `shrink` commands recognize both case
schemas. Replay checks the original Core argument, ABI calldata, function,
source and versioned generation provenance. It recomputes observations rather
than trusting saved results. Generated cases retain their generation validation
fuel independently of a replay's execution budget.

The runtime corpus checks inputs separately from constants in the program:

```sh
python3 Tests/scripts/test-semantic-corpus.py --manifest scripts/semantic-input-corpus.json
python3 scripts/semantic-campaign.py \
  --corpus scripts/semantic-input-corpus.json \
  --output .upstream/semantic-input-ci
python3 scripts/test-source-input-rust.py
```

For runtime manifests, `requiredInputs` is satisfied only by inputs whose three
executions agree. `generatedInputs`, `matchedInputs` and `missingInputs` report
that coverage. `requiredWordLiterals` still measures literal presence in the
Core AST, including an application's argument; it cannot establish input
coverage. The fixed functions cover identity, unsigned boundary branches,
nested local scopes and generated bodies. They do not claim all richer M4
features or measured EVM opcode coverage.

The external input regression executes two unchanged source functions at all
four boundary inputs, checks three-way agreement and varying results, and
replays a saved input-dependent run. The input profile also supports automatic
reduction of its function body and input while retaining the checked application
form. Named functions, private mutable locals, aggregates and bounded loops
extend this workflow below.

## Compare the extended Word primitives

`runtime-primitives` retains the original checked Word-to-Word Core function
and imports raw functions from `std.opcodes`. It adds unsigned and signed
division/remainder, signed greater-than, shifts, byte selection, sign extension,
exponentiation, leading-zero count and modular addition/multiplication.
The [mapping table](../docs/design/next-implementation-roadmap.md#3-missing-runtime-operation-mappings)
records operand order and boundary behavior. Raw division/modular operations
return zero for a zero divisor/modulus; the public convenience wrappers are
not interchangeable with those raw functions.

```sh
python3 scripts/semantic-suite.py --mode fixed --profile runtime-primitives \
  --backend sonatina-o0 --output .upstream/semantic-primitives-fixed
python3 scripts/semantic-suite.py --mode random --profile runtime-primitives \
  --seed 20261026 --cases 16 --attempts 2048 \
  --output .upstream/semantic-primitives-random
```

Repeat with `--backend sonatina-o2` or `--backend yul --solc PATH`. The fixed
manifest contains 81 hand-specified cases and requires all fourteen new AST
operators plus eight input boundaries. This is AST and observed result coverage,
not proof that an optimizer emitted or executed a particular opcode.

Generation uses the unchanged broad Core generator, then abstracts a literal
and requires varied completed results over 0, 1, 2, 255, 256, maximum Word, the
high bit and the high bit minus one. One accepted function produces up to eight
inputs in that order. Default generation uses a 96-node complete applied-program
budget and 512 attempts; the admitted range is 8–512 nodes. The new schema and
versions preserve earlier profile output. Imported boundary cases may be
constant. Typed shrinking can reduce both function bodies and inputs, and
strict replay rederives generation, source, ABI and the original Core result.

Native commands are `primitive-generate SEED NODES COUNT ATTEMPTS FUEL` and
`primitive-emit FUNCTION.json INPUT [FUEL]`; `replay`, `observe` and `shrink`
dispatch the new schema. Use `replay` to authenticate a saved case; `observe`
only executes its admitted Core program and does not authenticate saved source.

## Compare inline Yul

`runtime-assembly` renders the functions of `runtime-primitives` partly or
wholly as inline Yul in `assembly { }` blocks. Every other profile's source is
Solcore expressions and statements only, so this is the profile that reaches
the compiler's inline-assembly path: Yul parsing, Solcore locals inside
`assembly`, builtin resolution and lowering to Hull.

Its Core reference is the primitive profile's original checked Word-to-Word
function for the same seed, budget and revision, generated by the same steps:
the G0 program under the same swarm mask, then the same literal abstraction.
The Core reference and its observations are therefore unchanged, and a Lean
test requires both profiles to accept the same functions with the same
programs, inputs, observations, generation records and exclusions.

A plan has schema `solcore-lean.assembly-plan.v1`, the checked
`functionProgram` and a `form`, drawn from a SplitMix64 hash of the case seed:

- `switch`: the whole body is one `assembly` block assigning the Solcore
  result local `sc_out`. Each Core `if` becomes a Yul `switch` whose `case 0`
  computes the else branch and whose `default` computes the then branch, each
  assigning one Yul local.
- `if`: the whole body as in `switch`, with each Core `if` as a Yul local
  holding the condition and two Yul `if`s, on it and on `iszero` of it.
- `operations`: Solcore `let`, `if`, literals and `!`, as in the primitive
  renderer, with every other operation in its own `assembly` block. The block
  assigns a fresh Solcore Word local from Solcore Word operands, and a
  comparison's Word becomes a Bool through std's `tobool`.

Word literals become decimal Yul literals and Bool literals `1` or `0`; Yul
never reads a Solcore Bool. The builtins are `not`, `clz`, `iszero` for `!`,
`add`, `sub`, `mul`, `div`, `mod`, `and`, `or`, `xor`, `eq`, `gt`, `sgt`,
`shl`, `shr` and `sar` (shift first), `byte`, `exp`, `signextend`, `sdiv`,
`smod`, `addmod` and `mulmod`, so every form renders all 26 G0 features and
revision four equals revision three for this profile. The ABI is
`SynthesizedAssembly.run(uint256)`; no emitter proof covers it.

Before the profile was written, a probe compiled five inline Yul sources with
the pinned compiler and std: every builtin above, Yul `let`, `switch`, `if`,
nested blocks, a `for` loop and a Yul function, assignments of Solcore locals
from Yul in a contract method and a helper, and 256-bit literals. Checked Hull
export, Sonatina O0 and O2, Yul through `export-rust-yul.py`, Anvil and the
Lean Hull runner matched a model of EVM word semantics at ten inputs on every
path, without a change to shared code.

```sh
python3 scripts/semantic-campaign.py \
  --profile runtime-assembly --functions 8 --output .upstream/semantic-assembly
python3 scripts/semantic-campaign.py \
  --corpus scripts/semantic-assembly-corpus.json --output .upstream/semantic-assembly-ci
python3 Tests/scripts/test-semantic-assembly-corpus.py
```

Native commands are `assembly-generate SEED NODES COUNT ATTEMPTS FUEL
[VERSION] [seeded-inputs-v1/splitmix64] [exclude-boundary-identity-v1]` and
`assembly-emit PLAN.json INPUT [FUEL]`; saved cases contain `assemblyPlan` and
the applied original Core `program`, whose exact correspondence native
admission checks for every origin. The generated origin also records the form,
and replay requires it to be the seed's.

- Generation, its eight boundary inputs and its exclusions are those of
  `runtime-primitives`, in its order, with a 96-node default budget; random
  campaigns add four seeded inputs and apply the boundary identity filter,
  since a primitive function can be the identity.
- Reductions are the primitive reductions of the Core function (G0 shrinking
  under the abstraction and smaller inputs), sealed by the full checker and
  strictly smaller, each in the parent's form; a reduced origin records the
  parent's plan.
- `assemblyRequirements` declares the required `forms` and `formFeatures`
  (`form:feature`), and `assemblyCoverage` counts only three-way matches
  toward passing coverage.

The fixed corpus is built from the primitive corpus: its 34 distinct
hand-specified functions, in corpus order, in three consecutive groups of 12,
11 and 11, each group combined by a balanced XOR tree into one function, so
every operation keeps the operands the primitive corpus chose for it. Each
function runs in each form at the eight boundary inputs: 72 cases from nine
plans and eight sources, since one group has no `if` and its `switch` and `if`
forms coincide. Every form covers all 29 AST features, and the functions shift
only by the input or by the literal 1.
`Tests/scripts/test-semantic-assembly-corpus.py` rebuilds the construction,
emits and replays every entry natively, reads the features from the AST and
checks reductions and tampering.

Two other corpora were tried first. The 81 primitive cases in each form, 243
cases from 102 sources, matched on O0 and O2 but needed more than the suite's
900-second profile limit on Yul. Generated functions chosen for coverage from
G0 revision one crashed Sonatina O0 code-image export in four of the 17
whole-body functions tried, each shifting by a constant count of at least
2^64 (recorded locally, not investigated). A fixed corpus that crashes would
track a known upstream defect, so the corpus avoids that construct; random
campaigns still generate it.

Frozen matrices at `33d7c411d`:
- The fixed corpus matched all 72 cases on all three paths with complete
  form, feature and input coverage, compiling 8 sources, in 114 seconds on O0,
  109 on O2 and 135 on Yul.
- Random suites from root seed 1 with eight whole functions took 24
  generation attempts, excluding 9 functions whose boundary outputs agree and
  7 boundary identities. They drew four `switch`, one `if` and three
  `operations` functions: 96 cases from 8 distinct sources.
- All 96 matched on O2 in 127 seconds. On O0 and Yul, 84 matched and the twelve
  inputs of the first `switch` function crashed Sonatina O0 code-image export
  with `Integer overflow when casting to usize`, in 203 and 261 seconds; the
  Yul runs export O0 images too.

The reduction of that function kept the fingerprint with a left shift of the
constant 0 by a constant count far above 256. The crash is retained as a
finding and recorded locally without investigation, so those two random gates
did not pass.

## Raw primitives in aggregate-based step functions

Eleven profiles render their checked aggregate step functions with
`AggregateRenderer`: `runtime-aggregates`, `runtime-loops`,
`runtime-generics`, `runtime-closures`, the step functions of
`runtime-comptime` and `runtime-modules`, and the five stateful profiles
(storage, rollback, parent/child calls, keyed storage and dynamic arrays).
Since emitter version 2 these step functions also render the fourteen raw
primitives: Clz, unsigned and signed division and remainder, signed
greater-than, the three shifts, byte selection, exponentiation, sign
extension, and the ternary `addmod`/`mulmod`. Previously every generated
program containing one of them was an operator exclusion.

The renderer uses the call-graph helpers exactly as the aggregate call-graph
renderer does. Each primitive operand is snapshotted into a fresh local in
Core evaluation order before the alias is called; shifts print
`shl(shift, value)` from those snapshots; signed comparison is converted with
`tobool`; ternary operands are all snapshotted. The original operations
(`+ - * & | ^ == > ! ~`) keep their exact unsnapshotted text, so every program
without a raw primitive emits byte-identical source. The aliases are imported
only when a rendered step uses one: profiles without another opcode import add
the primitive profile's `import { div as sc_div, ... } from std.opcodes;`, and
the stateful profiles append the same aliases to their existing `std.opcodes`
import. Pair, sum, case and private-cell scoping are unchanged.

Every affected emitter version and profile version moved to `v2`, including the
shared aggregate step profile version, because accepted programs changed. Saved
cases of the older versions are rejected by the explicit version check rather
than re-emitted: all 202 legacy cases of the six affected pure profiles fail
with `profileVersion changed`, while all 347 legacy cases of the other eight
pure profiles replay to identical JSON.

Out of scope and unchanged: `ScalarRenderer`, which the priority-5 emitter
proof unfolds, and its users (`closed-g0`, `runtime-word`, `runtime-functions`
and the compile-time constants of `runtime-comptime` and `runtime-modules`);
`MutationRenderer` (`runtime-mutation`, 22 operator exclusions in the recorded
random allocation); and the exclusions for node budgets too small for an
aggregate template.

Operator exclusions for root seed `20261026`, sixteen cases and 2,048 attempts
(the recorded random suite allocation, generation only):

| Profile | Before | After | Attempts before → after |
| --- | ---: | ---: | --- |
| runtime-aggregates | 42 | 0 | 46 → 4 |
| runtime-loops | 23 | 0 | 26 → 3 |
| runtime-generics | 33 | 0 | 37 → 4 |
| runtime-closures | 47 | 0 | 51 → 4 |
| runtime-comptime | 376 | 17 (constants) | 382 → 32 |
| runtime-modules | 574 | 9 (constants) | 636 → 18 |
| stateful-storage | 206 | 0 | 222 → 16 |
| stateful-storage-rollback | 206 | 0 | 222 → 16 |
| stateful-calls | 149 | 0 | 180 → 18 |
| stateful-keyed-storage | 180 | 0 | 196 → 16 |
| stateful-dynamic-array | 163 | 0 | 195 → 17 |

The remaining comptime and module operator exclusions come only from their
`ScalarRenderer` constants. Template-budget exclusions are unchanged in kind
(1 for modules, 2 for calls and 1 for dynamic arrays in this allocation).

Each affected fixed corpus gained generated entries whose step functions cover
all fourteen primitive AST features, and requires them: two or three seeds per
profile at every boundary input for the pure profiles, and two or three
scenarios for the stateful ones. Expected keyed and dynamic-array histories were
computed by an independent Python evaluator with the documented EVM primitive
semantics and matched original Core. The native corpus validators now admit
primitive step features (constants still admit only the original scalar set)
and count ternary nodes like `if` nodes, as the Wire measure does.

| Corpus | v1 cases | v2 cases |
| --- | ---: | ---: |
| aggregates | 32 | 44 |
| loops | 48 | 60 |
| generics | 28 | 36 |
| closures | 24 | 32 |
| comptime | 32 | 40 |
| modules | 32 | 44 |
| storage | 10 | 12 |
| storage rollback | 12 | 14 |
| calls | 14 | 16 |
| keyed storage | 12 | 14 |
| dynamic arrays | 12 | 15 |

Local validation ran on commit `660a2729b` with frozen scripts and native
tools; all 1,358 per-case reports record that commit and a clean tracked tree.
The fixed suites matched all 256 pure cases on O0, O2 and Yul (1,429.9, 1,441.0
and 2,324.3 seconds) and all 71 stateful scenarios and 197 transaction prefixes
on O0 and O2 (416.4 and 423.1 seconds), with complete coverage including every
primitive feature. The random suites (root seed `20261026`, sixteen cases and
2,048 attempts per profile) matched all 96 pure cases on O0, O2 and Yul (556.2,
557.8 and 863.9 seconds) and all 80 stateful scenarios and 240 prefixes on O0
(485.6 seconds); 92 of the 96 accepted pure cases and 73 of the 80 stateful
scenarios call at least one alias. The O2 stateful random suite failed:
storage, rollback, calls and keyed storage matched 16 of 16 each, but dynamic
arrays matched fifteen and one scenario crashed O2 code-image export with the
panic recorded as Q013 (`Integer overflow when casting to usize`). The same
scenario matched on O0. Automatic reduction kept the crash fingerprint through
thirteen accepted candidates before its attempt limit; the reduced case still
shifts left by a large constant count. The crash is retained as a finding and
was neither suppressed nor reclassified, so that O2 gate did not pass.

## Compare directly generated call graphs

`runtime-call-graphs` generates typed Word/Bool expressions with the runtime
parameter already in scope. One to three helpers can call any earlier helper;
the entry and arguments need not follow a fixed chain. Local bindings,
conditionals and all scalar primitives are admitted. The original Core checker
seals the complete graph, and the original Core application supplies the oracle.

```sh
python3 scripts/semantic-suite.py --mode fixed --profile runtime-call-graphs \
  --backend sonatina-o0 --output .upstream/semantic-call-graphs-fixed
python3 scripts/semantic-suite.py --mode random --profile runtime-call-graphs \
  --seed 20261026 --cases 16 --attempts 2048 \
  --output .upstream/semantic-call-graphs-random
```

O2 and Yul use the same cases with their usual backend flags. The fixed corpus
contains 56 cases with hand-specified Core results. It requires helper counts
one through three, eight input boundaries and nine syntactic structures:
skipped helpers, multiple callees, shared callees, nested calls, calls in
branches and local bindings, a diamond, calls in predicates and primitive
operands. `callShapeCoverage` records required, generated, matched and missing
structures. Only completed matches satisfy coverage. The inventory includes
all declared bodies; it does not claim an executed call trace or branch coverage.

The default complete-program budget is 192 nodes, with 1,024 generation
attempts. Explicit attempt limits override this default. The admitted budget
range is 13–512 nodes; small budgets can exhaust generation because a generated
entry must contain a call. Generated functions must also return varying values
over the same eight inputs used by `runtime-primitives`. Imported functions
may be constant. Attempts count graphs, while cases count individual inputs.

`call-graph-generate SEED NODES COUNT ATTEMPTS FUEL` and
`call-graph-emit FUNCTION.json INPUT [FUEL]` produce the new case schema.
Replay regenerates the original graph and body budgets, checks canonical
source, input, versions and structural metadata, and recomputes Core results.
Reduction retains the helper bindings, reseals every candidate and requires a
strictly smaller complete application. Its failure identity and selected
backend follow the ordinary campaign rules. The older chain-based profile
below keeps its existing schema and generator unchanged.

## Compare acyclic named functions

The `runtime-functions` profile adds one to three named Word-to-Word helpers.
Each helper can call earlier helpers; an entry function receives the ABI Word
and returns a Word. The original Core program retains the complete chain of
helper lambdas and applies the resulting entry closure to the recorded input.
Source emission uses top-level named functions and
`SynthesizedFunctions.run(uint256)`. Recursive or escaping function values and
references to host bindings are outside this profile.

```sh
python3 scripts/semantic-campaign.py \
  --profile runtime-functions --seed 31 --nodes 96 --cases 8 --attempts 256 \
  --output .upstream/semantic-functions
python3 scripts/semantic-campaign.py \
  --corpus scripts/semantic-function-corpus.json \
  --output .upstream/semantic-function-ci
python3 scripts/test-source-function-rust.py
```

Native entry points are `function-generate SEED NODES COUNT ATTEMPTS FUEL` and
`function-emit FUNCTION.json INPUT [FUEL]`. Observe, replay and shrink dispatch
by the saved schema. Node limits apply to the entire original Core application,
including all helper definitions. Generation attempts count function graphs;
each accepted graph supplies the same four ordered boundary inputs as the
single-function profile, and in random mode the four
[seeded inputs](#seeded-runtime-inputs) after them. Generated graphs call every earlier helper in a
chain; imported graphs can also share callees, as in the diamond fixture.

The fixed corpus includes chains, a diamond and generated graphs with one,
two and three helpers. It tracks `requiredHelperCounts` separately from input
coverage. `matchedHelperCounts` records declaration counts for cases whose
three results agree. It is not a count of runtime calls or EVM call instructions.
Body feature coverage includes `functionCall`, without counting the compiler's
wrapper lambdas as source function definitions.

Reduction keeps helper declarations in their original order and checks the
complete graph after every candidate body or input change. The first reducer
keeps the number of helpers fixed; it can remove calls or simplify bodies but
does not delete and reindex declarations. Private mutable locals, aggregates
and bounded loops extend this workflow below.

## Compare private mutable locals

The `runtime-mutation` profile keeps the Word-only ABI and one to three acyclic
Word helpers. Each helper may allocate private Word cells, read and update them,
and sequence Unit results through locals and branches. Cell aliases, escaping
cells and non-Word cells are excluded. The original Core graph retains real
allocations, loads and stores; the source uses mutable Word locals in
`SynthesizedMutation.run(uint256)` and its helpers.

```sh
python3 scripts/semantic-campaign.py \
  --profile runtime-mutation --seed 57 --nodes 192 --cases 4 --attempts 256 \
  --output .upstream/semantic-mutation
python3 scripts/semantic-campaign.py \
  --corpus scripts/semantic-mutation-corpus.json \
  --output .upstream/semantic-mutation-ci
python3 scripts/test-source-mutation-rust.py
```

Native commands are `mutation-generate SEED NODES COUNT ATTEMPTS FUEL` and
`mutation-emit FUNCTION.json INPUT [FUEL]`. Replay and shrinking use the saved
case schema. The campaign's default node limit is 192 for this profile; the
512-node hard limit still applies to the complete applied function graph.
Versioned templates combine checked G0 scalar expressions with ordered stores,
Unit branches, two independent cells and a load followed by a later update.
Each accepted graph must return distinct values at two or more boundary inputs.

Every source read is captured before subsequent effects. Unit sequencing
binders remain in the renderer's context even when no source declaration is
needed. Reduction preserves the typed binder inventory and helper declarations,
rechecks the whole graph and requires smaller candidates. It may simplify store
values or replace a store with Unit without deleting its surrounding binder.

The fixed 28-case corpus contains seven graphs at all four boundary inputs. All
cases match across the three actual paths. Coverage includes fourteen AST
feature kinds, helper counts one through three and all four inputs. A separate
`recipeCoverage` section records the four generator templates and update counts
one through four. Matched recipe coverage requires native replay and three-way
agreement; it measures generator metadata, not dynamic branches or instructions.
The fixed manifest's recipe requirements are enforced alongside AST/input/helper
coverage. A separate twelve-case external regression checks read-before-write
snapshots, independent cells and callee isolation, followed by exact replay.

## Compare internal pairs, sums and matches

The `runtime-aggregates` profile admits internal `(word, word)` pairs and
`sum<word, word>` values, projections, and two-way matches. It combines them
with the existing scalar operations, private Word cells and acyclic helpers.
The ABI remains `SynthesizedAggregates.run(uint256)` with Word-only arguments
and results. Nested aggregate types, aggregate cells and escaping cell values
are outside this profile.

```sh
python3 scripts/semantic-campaign.py \
  --profile runtime-aggregates --seed 21 --nodes 256 --cases 4 --attempts 256 \
  --output .upstream/semantic-aggregates
python3 scripts/semantic-campaign.py \
  --corpus scripts/semantic-aggregate-corpus.json \
  --output .upstream/semantic-aggregate-ci
python3 scripts/test-source-aggregate-rust.py
```

Native commands are `aggregate-generate SEED NODES COUNT ATTEMPTS FUEL` and
`aggregate-emit FUNCTION.json INPUT [FUEL]`. The campaign defaults to 256 nodes
for this profile; its hard limit remains 512 nodes for the complete applied
graph. Fixed seeds use individual budgets within that limit. Since emitter
version 2 the raw primitives render as described in
[Raw primitives in aggregate-based step functions](#raw-primitives-in-aggregate-based-step-functions);
integer operations remain explicit exclusions.

Pair operands evaluate left to right and retain their values across later
writes. Projections and sum scrutinees evaluate once. The emitter uses tuple
patterns for projection and sum patterns for branch selection. It retains Core
payload, Unit and local binding positions independently of fresh source names.
Reduction preserves distinct left/right payload markers as well as typed let
bindings. It cannot extract a branch body and silently drop its payload binder.

The fixed 32-case corpus has eight graphs at all four boundary inputs. All
cases agree across the three actual paths. Eighteen AST feature kinds, helper
counts one through three and all four generator templates are covered. Recipe
requirements use `templates: [0, 1, 2, 3]` and `updates: []`; this profile has no
update-count recipe dimension. Coverage is still AST/metadata coverage.
The separate sixteen-case external suite checks retained aggregate snapshots,
single evaluation of projections, nested payload/helper effects and typed
pair/sum branch results, then replays a saved run exactly.

## Compare bounded loops

The `runtime-loops` profile retains a checked aggregate step graph and a mask.
Its source runs `while (limit > counter)` with `limit = input & mask`, updating
an accumulator through the arbitrary step entry on each iteration. The original
Core reference captures that entry closure once and executes a finite sequence
of literal-ordinal guards and accumulator stores. It does not reuse the source
counter implementation. The ABI is `SynthesizedLoops.run(uint256)`.

```sh
python3 scripts/semantic-campaign.py \
  --profile runtime-loops --seed 21 --nodes 384 --cases 6 --attempts 256 \
  --output .upstream/semantic-loops
python3 scripts/semantic-campaign.py \
  --corpus scripts/semantic-loop-corpus.json --seconds 600 \
  --output .upstream/semantic-loop-ci
python3 scripts/test-source-loop-rust.py
```

Native commands are `loop-generate SEED NODES COUNT ATTEMPTS FUEL` and
`loop-emit PLAN.json INPUT [FUEL]`. A plan has schema
`solcore-lean.loop-plan.v1`, a `stepProgram` containing a checked aggregate
function DAG, and an integer `mask` in zero, one, three or seven. Saved cases
contain both `loopPlan` and the actual applied original Core `program`. Native
admission reconstructs and checks their exact correspondence for every origin.
The complete applied reference has a 512-node limit; generation defaults to 384.

Each accepted seed supplies six ordered inputs: zero, one, three, seven,
maximum Word and the high bit. Generation selects masks one, three or seven,
requires an input-sensitive step, and checks that at least one positive-trip
input changes its value. Imported and reduced plans may be identity functions
or use a zero mask. Reduction preserves step binders and helper count, rebuilds
the complete reference, and requires strict decrease of its complexity.

The fixed corpus has eight plans at all six inputs, with all 48 cases matching
across the three actual paths. It covers nineteen step AST features, one to
three step helpers and all four aggregate recipes. `loopRequirements` declares
required `masks` and `iterations`; the fixed values are zero, one, three and
seven for each. `loopCoverage` derives prescribed iterations from the validated
input and mask and counts only three-way matches toward passing coverage. It
does not claim measured execution traces. Helper coverage excludes the emitted
`sc_step` and ABI wrappers. Features describe the step graph; full-program
literal coverage remains separate.

The external 24-case suite checks zero and positive iterations, arbitrary step
entries, pair/sum branches, fresh helper-local cells per iteration and Word
wrap, followed by exact replay.

## Compare bounded loops over call graphs

`runtime-call-graph-loops` uses a directly generated scalar call graph as the
step of the bounded loop above. Its unchanged helpers and arbitrary entry are
resealed by the aggregate DAG checker and then by the existing bounded-loop
plan; the executed step program is the scalar graph's exact declaration chain.
The finite ordinal-guard Core reference and its typing are reused, with no new
evaluator or Core primitive. The source emits the helpers, then the entry as
`sc_step`, with the call-graph renderer and raw `std.opcodes` aliases, inside
the same `while (limit > counter)` wrapper. The older `runtime-loops` emitter
and its narrower renderer are unchanged. The ABI is
`SynthesizedCallGraphLoops.run(uint256)`.

```sh
python3 scripts/semantic-suite.py --mode fixed --profile runtime-call-graph-loops \
  --backend sonatina-o0 --output .upstream/semantic-call-graph-loops-fixed
python3 scripts/semantic-suite.py --mode random --profile runtime-call-graph-loops \
  --seed 20261026 --cases 16 --attempts 2048 \
  --output .upstream/semantic-call-graph-loops-random
```

A plan has schema `solcore-lean.call-graph-loop-plan.v1`, a scalar
`stepProgram` and a `mask` of zero, one, three or seven. Generation first draws
mask one, three or seven, subtracts that mask's measured wrapper overhead from
the complete applied-program budget, generates the step with the
`runtime-call-graphs` grammar and remeasures the complete loop. The default
budget is 256 nodes; the admitted range is 39–512, and the mask-seven wrapper
alone needs 111. An accepted plan needs an entry call, step results that vary
over the eight primitive inputs and a positive-trip loop input whose final
value differs from that input. Imported and reduced plans may be constant or
use mask zero. Each plan yields up to six inputs: zero, one, three, seven,
maximum Word and the high bit, followed in random mode by four
[seeded inputs](#seeded-runtime-inputs). Attempts count plans; cases count inputs.

`call-graph-loop-generate SEED NODES COUNT ATTEMPTS FUEL` and
`call-graph-loop-emit PLAN.json INPUT [FUEL]` produce the case schema
`solcore-lean.semantic-call-graph-loop-case.v1`. Every origin rebuilds the
canonical applied reference from the saved plan. Replay regenerates generated
plans with their step origin and budget, and checks canonical source, ABI,
versions, features, helper count and call shapes. Reduction retains helper
bindings, reseals each candidate as a plan, never raises the mask and requires
a strictly smaller complete application; smaller masks remove whole guards.
A reduced origin names its parent plan and input.

The fixed corpus has eight imported and three generated plans at all six inputs.
Its expected Words were computed outside Lean from EVM Word semantics and the
loop definition; the native corpus test checks each against original Core.
It requires all thirty scalar AST features including calls, one to three
helpers, the nine call shapes, and masks and iterations zero, one, three and
seven. `loopCoverage` and `callShapeCoverage` count only three-way matches.
Neither inventory is an executed trace, call path or opcode measurement.

Native validation confirmed all 66 expected Words and replayed 264 strictly
smaller typed reductions. All 66 fixed cases matched on O0, O2 and Yul; the
first O2 run had stopped on one host adapter error before any execution, and a
fresh run matched all 66. That error was macOS rejecting `killpg` with `EPERM`
for a group holding only an exited, unreaped member; process cleanup now
tolerates it. Random seed `20261026` with sixteen cases and 2,048
attempts matched all sixteen on each backend. A controlled synthetic reduction
accepted four typed reductions per backend, all keeping three helpers, and
original and reduced archives replayed exactly.

## Compare nested bounded loops

`runtime-nested-loops` runs a bounded source `while` loop whose body runs a
second bounded `while` loop around the step. A plan has schema
`solcore-lean.nested-loop-plan.v1`, a checked aggregate `stepProgram`, an
`outerMask` and an `innerMask` in zero, one or three, and an `innerBound` that
reads the `input`, the `counter` or the `accumulator`. With input `x`, the
wrapper sets `acc = x` and runs `x & outerMask` outer iterations; each first
sets the inner bound, `x & innerMask`, `(i + 1) & innerMask` for outer counter
`i`, or `acc & innerMask`, resets the inner counter and then calls
`acc = sc_step(acc)` once per inner iteration. Both counters, the bound and the
accumulator are declared before the outer loop and assigned inside it. A call
therefore runs at most three outer iterations, three inner iterations in each
and nine step calls. The original Core reference unrolls the outer and inner
ordinal guards over one accumulator cell, without a counter cell, and checks
the complete applied program against the 512-node limit. The ABI is
`SynthesizedNestedLoops.run(uint256)`; no emitter proof covers this wrapper.

```sh
python3 scripts/semantic-campaign.py \
  --profile runtime-nested-loops --functions 4 --output .upstream/semantic-nested-loops
python3 scripts/semantic-campaign.py \
  --corpus scripts/semantic-nested-loop-corpus.json --output .upstream/semantic-nested-loop-ci
python3 Tests/scripts/test-semantic-nested-loop-corpus.py
```

Native commands are `nested-loop-generate SEED NODES COUNT ATTEMPTS FUEL
[VERSION] [seeded-inputs-v1/splitmix64]` and `nested-loop-emit PLAN.json INPUT
[FUEL]`; saved cases contain `nestedLoopPlan` and the applied original Core
`program`, whose exact correspondence native admission checks for every
origin. The step is generated as for `runtime-loops`, so the profile is
G0-based and revision four equals revision three for it. Generation draws one
of twelve shapes, both masks from one and three and the bound, from a
SplitMix64 hash of the case seed, and defaults to 384 nodes. Each function
runs at the boundary inputs zero, one, two, three, the maximum Word and the high
bit, which give zero to three outer iterations, and random campaigns add four
seeded inputs. Generation excludes a node budget too small for the shape, the
step's own exclusions, a step whose boundary inputs agree, fuel exhaustion and
a function that returns every boundary input unchanged (`boundary-identity`);
a boundary input without a step call returns itself, so the profile needs no
acceptance filter.

Every case records in `provenance.iterations` the inner trip count of each
outer iteration it runs, specified by the plan, the input and, for the
`accumulator` bound, the step's original Core results evaluated call by call;
it is `null` if a step call does not return within the fuel. It is not a
measured trace. Replay recomputes it, and the Lean test requires that the
unrolled reference returns the accumulator of that call-by-call evaluation.
Reductions keep the step's helper count and binders and may shrink the step,
lower either mask, replace the `counter` or `accumulator` bound by the `input`
bound or move the input to a boundary input; each candidate is sealed by the
full checker and is strictly smaller in nodes, then literal weight.

The fixed corpus has twelve plans, one per shape, at all six inputs: 72 cases
from G0 revision one. `nestedLoopRequirements` requires every shape, outer
iterations zero to three, inner trip counts zero to three within a run outer
iteration and total step calls 0, 1, 2, 3, 4, 6 and 9; the corpus also reaches
5 and 7. It covers all 39 step AST features its cases use, the 37 of the loop
corpus with `and` and `==`, one to three helpers and all four aggregate
templates. `nestedLoopCoverage` in the summary counts only three-way matches
toward passing coverage. `Tests/scripts/test-semantic-nested-loop-corpus.py`
materializes each case twice, recomputes the outer trips and every input or
counter bound and the first accumulator bound, which reads the input, and
checks replay, reductions and tampering natively.

Over the first 256 functions accepted from seed 1 under revision four with
seeded inputs, generation took 1.13 attempts per function, excluding 30
boundary identities and 4 step template budgets. All 256 sources were distinct
and every shape appeared 12 to 29 times. Of the 2,560 cases, 1,134 made no
step call, since inputs zero and the high bit, and any input without a set bit
under the outer mask, skip the outer loop.

Frozen matrices at `01344eea3` matched every case on all three paths. The
fixed corpus matched all 72 cases with complete shape, iteration, feature,
input, helper and template coverage, compiling 12 sources, in 118 seconds on
O0, 114 on O2 and 162 on Yul. Random suites from root seed 1 with four whole
functions matched all 40 cases on each backend in 52, 47 and 65 seconds, with
four distinct sources, shapes `1x1:accumulator`, `1x1:counter`, `1x1:input` and
`3x3:accumulator`, outer iterations zero to three and totals 0, 1, 4 and 9;
generation took five attempts, excluding one boundary identity.

## Compare bounded recursion

`runtime-recursion` calls a recursive source function, or two functions that
call each other, to a depth taken from the input, over an aggregate step. A
plan has schema `solcore-lean.recursion-plan.v1`, a checked aggregate
`stepProgram`, a `depthMask` in zero, one, three or seven and a `form`. With
input `x` and depth `d = x & depthMask`, the contract returns `f(d, x)`, where
`f(0, acc) = acc` and every call with `d > 0` makes one call at depth `d - 1`:

- `tail`: `sc_rec(d, acc) = sc_rec(d - 1, sc_step(acc))`;
- `nontail`: `sc_rec(d, acc) = sc_step(sc_rec(d - 1, acc)) + d`, with each
  frame's work after its call;
- `mutual`: `sc_even(d, acc) = sc_odd(d - 1, sc_step(acc))` and
  `sc_odd(d, acc) = sc_even(d - 1, acc + d)`, entered at `sc_even`.

A call therefore recurses at most seven frames deep. The original Core
reference unrolls the frames into ordinal guards over one accumulator cell,
with no recursion and no counter:

- `tail` steps at ordinals 0 to `d - 1`;
- `nontail` applies `step(acc) + k` for `k` from 1 to `d`, innermost frame
  first;
- `mutual` steps at even ordinals and adds `d - i` at odd ordinal `i`.

The complete applied program is checked against the 512-node limit. The ABI
is `SynthesizedRecursion.run(uint256)`; no emitter proof covers this wrapper.
Before the profile was written, the pinned compiler, std, checked Hull export,
Sonatina O0 and O2, Yul, Anvil and the Lean Hull runner were checked on all
three forms at eight inputs; every path matched a model of the function
without a change to shared code.

```sh
python3 scripts/semantic-campaign.py \
  --profile runtime-recursion --functions 4 --output .upstream/semantic-recursion
python3 scripts/semantic-campaign.py \
  --corpus scripts/semantic-recursion-corpus.json --output .upstream/semantic-recursion-ci
python3 Tests/scripts/test-semantic-recursion-corpus.py
```

Native commands are `recursion-generate SEED NODES COUNT ATTEMPTS FUEL
[VERSION] [seeded-inputs-v1/splitmix64]` and `recursion-emit PLAN.json INPUT
[FUEL]`; saved cases contain `recursionPlan` and the applied original Core
`program`, whose exact correspondence native admission checks for every
origin. The step is generated as for `runtime-loops`, so the profile is
G0-based and revision four equals revision three for it.

Generation:
- Each case draws one of nine shapes, a form with depth mask one, three or
  seven, from a SplitMix64 hash of the case seed. The default budget is 384
  nodes.
- Each function runs at the boundary inputs 0, 1, 2, 3, 7, the maximum Word
  and the high bit, giving depths zero to three and seven, and random
  campaigns add four seeded inputs.
- It excludes:
  - a node budget too small for the shape;
  - the step's own exclusions;
  - a step whose boundary inputs agree;
  - fuel exhaustion;
  - a function that returns every boundary input unchanged
    (`boundary-identity`).

  A depth-zero input returns itself, so the profile needs no acceptance
  filter.

A case's depth is prescribed by the plan and the input.
`recursionRequirements` declares the required `shapes` and `depths`, and
`recursionCoverage` counts only three-way matches toward passing coverage.
Reductions:
- keep the step's helper count and binders and may shrink the step;
- may lower the depth mask, replace `nontail` or `mutual` by `tail`, or move
  the input to a boundary input;
- are each sealed by the full checker and strictly smaller in nodes, then
  literal weight.

The Lean test compares the unrolled reference with a recursive model of the
emitted source, frame by frame over the step's original Core, for 1,023
generated cases.

The fixed corpus has nine plans, one per shape, at all seven inputs: 63 cases
from G0 revision one. It requires:
- every shape and depths 0, 1, 2, 3 and 7;
- all 39 step AST features its cases use, the 37 of the loop corpus with `and`
  and `==`;
- one to three helpers and all four aggregate templates.

`Tests/scripts/test-semantic-recursion-corpus.py` materializes each case
twice, recomputes each depth and checks replay, reductions and tampering
natively. Over the first 256 functions accepted from seed 1 under revision
four with seeded inputs, generation took 1.04 attempts per function,
excluding 11 boundary identities. All 256 sources were distinct, and every
shape appeared 20 to 36 times.

Frozen matrices at `0d5a60935` matched every case on all three paths. The
fixed corpus matched all 63 cases with complete shape, depth, feature, input,
helper and template coverage, compiling 9 sources, in 115 seconds on O0, 105
on O2 and 144 on Yul. Random suites from root seed 1 with four whole
functions matched all 44 cases on each backend in 61, 59 and 77 seconds, with
four distinct sources, shapes `1:nontail`, `3:tail` and `7:mutual`, and depths
0 to 4, 6 and 7, in four generation attempts.

## Compare aggregate compositions with call graphs

`runtime-aggregate-call-graphs` generates typed Word, Bool, Word-pair and
Word-sum expressions directly, with the runtime parameter in scope. One to
three helpers may call any earlier helper. Pairs, sums, projections, let-bound
aggregates, aggregate-valued branches and case expressions compose with those
calls in operands, components, payloads, scrutinees and branches. Helper
arguments and results and the ABI remain Words. Private cells and Unit values,
covered by `runtime-aggregates`, are outside this grammar. The existing
aggregate DAG checker seals each graph; original Core supplies the oracle.

```sh
python3 scripts/semantic-suite.py --mode fixed --profile runtime-aggregate-call-graphs \
  --backend sonatina-o0 --output .upstream/semantic-aggregate-call-graphs-fixed
python3 scripts/semantic-suite.py --mode random --profile runtime-aggregate-call-graphs \
  --seed 20261026 --cases 16 --attempts 2048 \
  --output .upstream/semantic-aggregate-call-graphs-random
```

Source uses the call-graph renderer's scalar, raw-primitive, snapshot and call
formatting, and the aggregate profile's tuple, `sum<word, word>`, `inl`/`inr`
and `match` forms; a test checks scalar bodies render identically to the
call-graph profile. The default budget is 192 complete-program nodes, admitted
13–512. Accepted graphs need an entry call, a call composed with an aggregate
value or payload scope, and varied results over the eight primitive inputs.
Imported graphs may be constant. Each graph yields up to eight inputs, followed
in random mode by four [seeded inputs](#seeded-runtime-inputs).

`aggregate-call-graph-generate SEED NODES COUNT ATTEMPTS FUEL` and
`aggregate-call-graph-emit FUNCTION.json INPUT [FUEL]` produce the case schema
`solcore-lean.semantic-aggregate-call-graph-case.v1`. Replay regenerates the
graph and budgets and checks canonical source, ABI, versions, features, helper
count and composition shapes. Reduction reuses the typed aggregate reductions:
every helper, typed let and case payload scope is retained, candidates stay in
this grammar and must strictly decrease the complete application.

`aggregateShapeCoverage` records nine syntactic structures: calls in pair
components and sum payloads, calls on projections, calls in case scrutinees and
branches, calls on a case payload, let-bound aggregates, aggregate-valued
branches and nested cases. Only completed matches satisfy coverage; this does
not claim that a call, branch or payload executed. The fixed corpus has four
imported and three generated graphs at all eight inputs. Its expected Words
were computed outside Lean, and native validation checks each against original
Core. It requires all 36 scalar and aggregate AST features, one to three helpers
and the nine structures.

Native validation confirmed all 56 expected Words and replayed 224 strictly
smaller typed reductions. All 56 fixed cases matched on O0, O2 and Yul. Random
seed `20261026` with sixteen cases and 2,048 attempts matched all sixteen on O0
and Yul; O2 matched eight and retained eight compiler crashes from one graph,
a recorded upstream finding, so that O2 random run fails. A controlled
synthetic reduction accepted four typed reductions per backend, keeping every
helper and binder, and original and reduced archives replayed exactly.

## Compare ordered storage transactions

The M5a execution connection uses a separate storage case format and runner.
`SynthesizedStorage.run(uint256)` reads slots zero and one, applies a checked
aggregate step to `input + old0`, writes its result to slot zero, increments
slot one, and returns the sum of both reread slots. Each scenario starts with
empty storage. Generated scenarios contain three ordered transactions, or up
to eight in random [storage campaigns](#run-and-reduce-storage-campaigns);
imported scenarios may contain one through three, and reductions keep at
least one.

Build the two native tools and generate a small corpus:

```sh
lake build semanticStorageTool rustHullStorageScenario
mkdir -p .upstream/semantic-storage-cases
.lake/build/bin/semantic-storage-tool generate 0 256 2 64 1000000 \
  > .upstream/semantic-storage-cases/corpus.json
```

Generation arguments are `SEED NODES COUNT ATTEMPTS FUEL`; `COUNT` counts
scenarios. Check that the corpus `status` is `complete` before using it as a
completed batch. Native entry points are:

```text
semantic-storage-tool emit PLAN.json TRANSACTIONS.json [FUEL]
semantic-storage-tool replay CASE.json [FUEL]
semantic-storage-tool observe CASE.json BINDINGS.json [FUEL]
semantic-storage-tool shrink CASE.json LIMIT [FUEL]
```

A plan has schema `solcore-lean.storage-plan.v1` and a `stepProgram` containing
a checked aggregate function DAG. Transactions are an ordered JSON array of
`{id, input, calldata, value}` objects: IDs are distinct bounded identifiers,
inputs are canonical decimal Words, calldata is selector `0xa444f5e9` followed
by that Word's 32-byte encoding, and value is `"0"`. The saved
`solcore-lean.semantic-storage-case.v1` contains one original host-aware Core
contract, its emitted source, plan, transactions and versioned provenance.
It contains no expected execution result. Replay reconstructs the exact
contract, checks emission and metadata, and validates generated or reduced
origins. Shrinking preserves helper/binder scope and transaction ID order while
simplifying the step, inputs or sequence; candidates still need execution to
establish that they preserve a finding.

`observe` executes the original checked contract through `ContractRuntime`.
Bindings have schema `solcore-lean.storage-bindings.v1` with distinct decimal
`caller` and `address` fields. The comparison runner records the actual Anvil
bindings in `bindings.json` and supplies them to both Core paths. Each invocation
uses the same installed code and a fresh local heap; only its terminal
`finalWorld` becomes the next transaction's world.

Extract and compare one scenario, then replay its archive:

```sh
python3 - <<'PY'
import json
from pathlib import Path
root = Path('.upstream/semantic-storage-cases')
corpus = json.loads((root / 'corpus.json').read_text())
assert corpus['status'] == 'complete' and corpus['cases']
(root / 'case.json').write_text(json.dumps(corpus['cases'][0], indent=2) + '\n')
PY
python3 scripts/semantic-storage-differential.py \
  --case .upstream/semantic-storage-cases/case.json \
  --output .upstream/semantic-storage-cases/run
python3 scripts/semantic-storage-differential.py \
  --replay .upstream/semantic-storage-cases/run \
  --output .upstream/semantic-storage-cases/replay
```

Both output directories must be new. The runner compiles checked Rust Hull and
linked Sonatina images at the selected O0/O2 level, verifies the deployed runtime bytes, and sends actual
transactions on its owned local Anvil. Return bytes come from each mined
transaction's trace; slot snapshots come from `eth_getStorageAt` at that
receipt's block. The separate Hull runner reports committed slots explicitly,
including when a receipt has no world, and stops on incomplete execution.
An uncertain transaction submission is never retried automatically.

A pass requires agreement on empty initial storage and on status, return bytes
and committed slots after every transaction, across all three path pairs. The
contract's [whole committed storage](#compare-whole-committed-storage) must
agree too. A later resource failure cannot erase an already observed prefix
mismatch. Exact
replay checks archive members, tool identities and saved budgets, then starts a
fresh deployment and recomputes all observations.

```sh
python3 scripts/test-semantic-storage-differential.py
python3 scripts/test-source-storage-rust.py
```

The 34 protocol regressions pass. The external suite passes six scenarios and
fifteen actual transactions, followed by exact archive replay. It covers
feedback, repeated inputs, single-call sequences, sparse zero storage, clearing
and rewriting a slot, fresh private cells, arbitrary entries and aggregate
branches. Changing the input sequence leaves the original Core contract and
source unchanged. Full repository build/tests and the kernel policy check pass.

This first storage profile admits valid `run(uint256)`
inputs, zero call value, initially empty literal slots zero and one, and
successful Word returns. The rollback profile below extends completion
behavior; bounded external calls use the separate profile below. This scope
does not establish equivalence of arbitrary storage, gas, balances, nonce,
logs, account lifecycle or the source emitter itself.

## Run and reduce storage campaigns

Run the fixed stateful corpus or generate a bounded batch:

```sh
python3 scripts/semantic-storage-campaign.py \
  --corpus scripts/semantic-storage-corpus.json \
  --output .upstream/semantic-storage-ci --seconds 600
python3 scripts/semantic-storage-campaign.py \
  --seed 3 --nodes 384 --cases 4 --attempts 256 \
  --output .upstream/semantic-storage-search --seconds 600
python3 Tests/scripts/test-semantic-storage-corpus.py
python3 scripts/test-semantic-storage-campaign.py
```

All ten fixed scenarios and 27 transaction prefixes match across the actual
three paths. The manifest requires nineteen step AST features, six boundary
inputs, one through three declared helpers and transactions, and all four step
generator templates. Only fully matched scenarios count toward passing
coverage. The native corpus validator checks materialization, strict replay and
repeat observations; it does not execute an EVM.

Random generation draws the checked step with
[G0 revision three](#revision-three-swarm-masks) and passes
`core-g0-v3/lcg64-v1` after `FUEL` to the native `generate` command;
`--g0-version` selects revision one or two instead. Every helper of a
revision-three step uses the scenario seed's swarm mask, which the case
records in `provenance.swarmMask` as the pure profiles do. Replay requires the
mask for revision three, compares a generated case's mask with its seed's and
rejects a mask under the other revisions, so no case tool command accepts a
revision-three case without its mask. A fixed corpus or a saved `--case` uses
the version it records in `generatorVersion`, and a disagreeing
`--g0-version` is refused. Reductions inherit their parent's version and mask.
The summary records `configuration.g0Version` and
`generation.generatorVersions`. The call campaign handles the version the same
way. A suite sample of four random eight-transaction cases for each of the
thirteen stateful profiles recorded revision three and its masks and matched
on O0 and O2, while the fixed corpora kept revision one and their 167
scenarios.

Random generation also requests `--transactions` transactions per scenario,
from one to eight and eight by default, and passes the count after the version
to `generate`. A sequence is the first transactions of consecutive
three-transaction blocks. Block zero is the scenario seed's original three
transactions, so three transactions regenerate the fixed corpora bit for bit;
each later block draws the same choices from a derived seed. A generated origin
records a count other than three as `transactionCount`, and replay
regenerates exactly that length. Call-value and forwarded-value generation send
zero where a value or a forwarded amount would exceed its 2^72 total. A corpus
or a saved case keeps its own sequence, and `--transactions` is refused with
either. The summary records the length in `configuration.transactions` and
`generation.transactions`. Every profile's reductions first remove one
transaction, from the last to the first, so a long sequence loses the tail
beyond a difference before the candidate limit is spent. Sixteen
eight-transaction cases per profile at the 512-node budget matched on O0 and
O2 (208 scenarios and 1,664 prefixes per level); the slowest profile,
nested-array, used 153 of its 900 suite seconds.

The summary counts scenarios separately from transactions observed on any path,
completed on all three paths, and matched ordered prefixes. Shrink executions
are excluded from these transaction counts. The campaign enforces generation,
case, total time, disk and reduction limits. Successful runs retain compact
receipts and input cases; their exports are removed. Use `--case` with a saved
case for a new experiment. Findings retain full original and final archives
for `semantic-storage-differential.py --replay`.

Reduction can simplify the checked step, reduce runtime inputs or remove
transactions. The failure fingerprint uses a stable transaction ID rather than
its sequence index, and preserves the differing fields/slots, disagreeing paths
and outcome/payload forms. Candidate identity includes both the original Core
program and the transaction sequence. Every accepted candidate has been
rechecked and rerun on all three paths.

To exercise reduction deliberately, use an explicit copied-observation adapter:

```sh
python3 scripts/semantic-storage-campaign.py \
  --case .upstream/semantic-storage-cases/case.json \
  --test-perturb-path importedHull --test-transaction-id tx-1 \
  --test-field storage:1 --shrink-attempts 12 \
  --output .upstream/semantic-storage-reducer --seconds 600
```

This changes a copied observation only after actual agreement. Raw reports
remain unchanged, and the command exits nonzero for the synthetic mismatch.
`--test-field` accepts `output`, `storage:0`, `storage:1` or `stray` (see
[whole committed storage](#compare-whole-committed-storage)). A selected transaction
removed by a candidate cannot preserve that synthetic finding. The integrated
check reduced three transactions to only `tx-1`, retained the same fingerprint,
and passed both fresh actual archive replay and synthetic replay. Genuine
findings discovered while shrinking are retained separately.

## Compare rollback after storage writes

The `stateful-storage-rollback` profile keeps the two-slot feedback protocol and
uses `SynthesizedRollback.run(uint256)`. Both writes and the final slot reads
execute before the original ABI input selects completion: an odd input reverts
with the tentative slot sum encoded as exactly 32 bytes; an even input returns
that same Word. A reverted call retains the immediately preceding committed
world, while its output describes the tentative computation. A zero payload
still contains 32 bytes.

The original Core contract uses the existing typed `wordOutcomeV1` convention.
`ContractRuntime` selects the committed or rolled-back world; the Core wrapper
does not restore storage itself. The source emits `mstore(0, result)` followed
by `revert_(0, 32)` in the odd-input branch. The comparison requires matching
status, payload and committed storage at every prefix, and independently checks
that each reverted snapshot equals its predecessor.

Build the new native case tool:

```sh
lake build semanticStorageRollbackTool rustHullStorageScenario
```

`semantic-storage-rollback-tool` provides the same `generate`, `emit`, `replay`,
`observe` and `shrink` commands as the storage tool above. Its plan schema is
`solcore-lean.storage-rollback-plan.v1`, and its case schema is
`solcore-lean.semantic-storage-rollback-case.v1`. Generated scenarios use an
even/odd/even sequence and must complete as return/revert/return under actual
Core execution. Imported and reduced scenarios may have any parity pattern
within the one-to-three transaction limit. Existing successful-storage cases
retain their own schema, source and completion policy.

The same comparison and campaign scripts select the native tool and completion
rules from the saved case or corpus profile. Use
`--profile stateful-storage-rollback` for a seed search. The storage runner enables Anvil's
`--steps-tracing`: a failed receipt counts as an explicit revert only when its
trace confirms terminal `REVERT`, after resource errors have been excluded.
Out-of-gas, fuel exhaustion and exceptional failure never become matching
rollbacks. Archive replay retains the usual tool-hash and budget checks.

```sh
python3 scripts/test-source-storage-rollback-rust.py
python3 Tests/scripts/test-semantic-storage-corpus.py \
  --manifest scripts/semantic-storage-rollback-corpus.json
python3 scripts/semantic-storage-campaign.py \
  --corpus scripts/semantic-storage-rollback-corpus.json \
  --output .upstream/semantic-storage-rollback-ci --seconds 600
```

The external suite passed eight scenarios and 21 actual transactions, including
twelve returns and nine reverts, followed by exact archive replay. Cases cover
success/revert/success, consecutive reverts, an initial all-zero revert payload,
rollback of a tentative slot deletion, fresh private cells, arbitrary entries,
aggregate branches and zero writes. The original Core contract and source stay
fixed when transaction inputs change.

The fixed twelve-scenario corpus passed native materialization, replay and all
33 transactions. It covers twenty step AST features, the six boundary inputs,
one through three declared helpers and transactions, and all four generator
templates. `requiredOutcomes` and `requiredCompletionPatterns` add coverage for
both return/revert and four ordered completion patterns, measured from completed
histories. This native validator does not execute the EVM. The separate actual
campaign also passed all twelve scenarios and 33 prefixes, with complete
coverage. The ten-scenario M5a campaign still passed all 27 prefixes with step
tracing enabled.

A copied reverted-payload difference at `tx-1` accepted nine reductions in
twelve candidate executions, leaving only the same reverting transaction.
Every actual candidate report matched. Exact archive replay and fresh synthetic
replay reproduced actual agreement and the same synthetic failure fingerprint.
For this profile, a reducer cannot preserve a reverted-payload finding by
turning it into a normal return, an empty payload or resource exhaustion.

Full repository build/tests and kernel policy passed, along with forty storage
protocol and 24 campaign regressions. The rollback profile retains the initially
empty two-slot domain, valid Word calldata and zero call value.

## Compare bounded parent/child calls

The `stateful-calls` profile installs `SynthesizedCaller` and
`SynthesizedCallee`. The parent's empty payable constructor receives eight units
of value; the child's deployment receives zero. Both begin with empty storage.
Original Core starts from that declared post-deployment world; it does not
execute the source constructors. Rust EVM and imported Hull execute the actual
deployments, and the runner checks their resulting initial accounts.

Each zero-value transaction, one to three or up to eight in random campaigns,
calls `SynthesizedCaller.run(uint256 target, uint256 input)`, selector
`0x7357f5d2`.
The parent receives 68 bytes including the selector. It calls the payable child
fallback with one raw 32-byte Word. The source reserves scratch memory through
the free-memory pointer and rejects child returndata that is not exactly 32
bytes. The fixed protocol uses the low three input bits:

| Mask | Prescribed behavior |
| --- | --- |
| `1` | Child reverts after its storage writes and topic-two log. |
| `2` | Parent reverts after consuming the child outcome and writing/logging its result. |
| `4` | Parent sends value one to the child; otherwise it sends zero. |

The parent increments slot zero by the input and logs topic one. The child
applies the checked aggregate step to `input + oldChild0`, writes that result
to slot zero, increments slot one, and logs topic two. The parent writes the
child payload to slot one, adding one if the child reverted, then logs topic
three. Its root payload is the sum of both parent slots. Each return/revert
payload is one big-endian Word. Unexpected call failures are exceptional exits.

Build the separate native tools and generate a case:

```sh
lake build semanticCallTool rustHullCallScenario
mkdir -p .upstream/semantic-call-cases
.lake/build/bin/semantic-call-tool generate 1 243 1 1 1000000 \
  > .upstream/semantic-call-cases/corpus.json
python3 - <<'PY'
import json
from pathlib import Path
root = Path('.upstream/semantic-call-cases')
corpus = json.loads((root / 'corpus.json').read_text())
assert corpus['status'] == 'complete' and corpus['cases']
(root / 'case.json').write_text(json.dumps(corpus['cases'][0], indent=2) + '\n')
PY
python3 scripts/semantic-call-differential.py \
  --case .upstream/semantic-call-cases/case.json \
  --output .upstream/semantic-call-cases/run
python3 scripts/semantic-call-differential.py \
  --replay .upstream/semantic-call-cases/run \
  --output .upstream/semantic-call-cases/replay
```

The native tool also provides:

```text
semantic-call-tool emit PLAN.json TRANSACTIONS.json [FUEL]
semantic-call-tool replay CASE.json [FUEL]
semantic-call-tool observe CASE.json BINDINGS.json [FUEL]
semantic-call-tool shrink CASE.json LIMIT [FUEL]
```

Plans use `solcore-lean.call-plan.v1` with a checked aggregate `stepProgram`.
Cases use `solcore-lean.semantic-call-case.v1` and retain both original Core
programs. The combined programs are limited to 512 nodes; the fixed wrappers
add 179 nodes to the step. Transactions contain a stable `id`, decimal `input`,
`value: "0"`, `target: "parent"` and `callee: "child"`. The source and programs
remain fixed across input sequences. Actual decimal caller/parent/child
addresses arrive through `solcore-lean.call-bindings.v1`. They must be distinct;
contract addresses zero through 17 and 256 are excluded at the Osaka boundary.
Cases never embed an invented deployment address or a saved expected result.

Original Core runs through `OneLevelNestedExecution.run`, retaining only the
terminal committed world between transactions and starting fresh private heaps.
The Rust path mines transactions, reads their output from step-enabled traces,
and obtains both accounts' slots zero/one and balances at each receipt block.
Committed logs come from receipts. Imported Hull uses the same actual bindings
and exact linked runtime images. A pass requires matching initial accounts and
every completed prefix: root status/payload, both account snapshots, both
contracts' [whole committed storage](#compare-whole-committed-storage) and
ordered logs. Root rollback must restore both prior snapshots and remove
committed logs; child rollback can leave earlier parent effects intact.
Unknown submission outcomes are not retried. Fuel, gas and process limits
remain distinct.

Exact archive replay checks saved artifact and executable hashes before fresh
execution. Rebuilding a native tool or changing an adapter invalidates an old
exact archive; use its `case.json` with `--case` for a new run under updated tools.

```sh
python3 scripts/test-source-call-rust.py
python3 scripts/test-semantic-call-differential.py
python3 scripts/test-semantic-call-campaign.py
python3 Tests/scripts/test-semantic-call-corpus.py
python3 scripts/semantic-call-campaign.py \
  --corpus scripts/semantic-call-corpus.json \
  --output .upstream/semantic-call-ci --seconds 600
```

The external suite passed ten scenarios and 26 transactions, including nineteen
returns and seven root reverts, followed by exact archive replay. It covers all
eight prescribed modes, Word boundaries, value retained after child success,
both rollback levels, fresh private cells and aggregate branches. Six separate
identity sequences covering fifteen transactions also matched original Core and
imported Hull. Full repository build/tests and kernel policy passed, along with
eleven protocol and thirty campaign regressions.

The fixed manifest contains fourteen scenarios and 38 transactions, nineteen
step AST features, inputs zero through seven/maximum/high-bit, helper and
transaction counts one through three, and four generation templates. Coverage
distinguishes prescribed `input & 7` modes from observed root outcomes and
ordered committed log patterns. Neither is internal opcode trace coverage.
Native materialization, strict replay and repeated observations passed all
fourteen scenarios and 38 transactions, with complete declared coverage and
24 negative checks, including fuel exhaustion. This validator does not execute
the EVM. The actual fixed campaign also passed all fourteen scenarios and 38
prefixes, with complete coverage. A copied log-payload difference at `tx-1`
reduced three transactions to one through three accepted reductions in six
candidate executions. All actual reports matched; exact archive replay and
synthetic same-fingerprint replay passed. Fuel exhaustion remained inconclusive
with prior accounts retained and unknown logs. Both constructor receipts must
verify their exact linked runtime bytes; a fresh run and exact replay also
passed after that check was added.

M5 is complete within its documented profiles. The bounded-call domain is one installed parent and
one child, valid Word calldata, fixed initial balances and slots zero/one.
Gas/nonce equivalence, precompiles, arbitrary accounts and deeper calls remain
outside this profile.

## Compare keyed storage transactions

The `stateful-keyed-storage` profile is the first state/ABI extension. Each
transaction calls `SynthesizedKeyedStorage.run(uint256 key, uint256 input)`,
selector `0x7357f5d2`, with exactly two ABI Words. The key selects an arbitrary
full-width slot. The contract reads `old = sload(key)` and the counter
`count = sload(0)`, computes `step(input + old)` with the checked aggregate
step, then writes, in this order:

| Order | Slot | Value |
| --- | --- | --- |
| 1 | `key` | the step result |
| 2 | `key + 1`, wrapping | `old` |
| 3 | `0` (counter) | `count + 1` |

It rereads all three slots and returns their wrapped sum. An odd input reverts
after those writes and rereads, with the same Word as a 32-byte payload, so the
committed world keeps its predecessor. Later writes win when slots alias: key
zero is the counter, key maximum's successor wraps to the counter, and a
transaction may read another transaction's key or successor slot. The original
Core contract uses `wordOutcomeV1`; `ContractRuntime` commits or rolls back.

Observations are declared by the case, not discovered from one path.
`observedSlots` is the sorted, duplicate-free set containing the counter and
every transaction's key and wrapping successor. All three paths report status,
payload and the committed value of every declared slot after every transaction.
Original Core reads them from the public committed world; the Rust EVM path
uses `eth_getStorageAt` at each receipt block; imported Hull reads its committed
entries. Slots outside the declaration are also checked on the two executable
paths alone: the Hull runner reports every nonzero committed slot outside it,
and the EVM path asks Anvil's `prestateTracer` in diff mode for each mined
transaction's (and the deployment's) changed slots, then rereads those outside
the declaration at the receipt block. A nonzero undeclared slot on either path
is a semantic mismatch (`undeclaredStorage`, with `undeclaredPaths`). A diff
that changes another account's storage fails closed as an adapter error. The
deployment must leave every declared slot zero and no undeclared nonzero slot.
All three paths also compare the contract's
[whole committed storage](#compare-whole-committed-storage), which original
Core now enumerates as well.

Build the native tools and generate a case:

```sh
lake build semanticKeyedStorageTool rustHullKeyedStorageScenario
mkdir -p .upstream/semantic-keyed-storage-cases
.lake/build/bin/semantic-keyed-storage-tool generate 0 384 2 512 1000000 \
  > .upstream/semantic-keyed-storage-cases/corpus.json
```

The tool accepts the same `generate`, `emit`, `replay`, `observe` and `shrink`
commands as the two-slot tools. Plans use `solcore-lean.keyed-storage-plan.v1`
under the case field `keyedStoragePlan`; cases use
`solcore-lean.semantic-keyed-storage-case.v1`. Transactions are
`{id, key, input, calldata, value}` with canonical decimal Words, the selector
followed by both Words, and zero value. Bindings reuse
`solcore-lean.storage-bindings.v1`. Existing storage, rollback and call schemas,
plans and saved cases are unchanged.

Generation reuses the aggregate step generator, so most attempts are ordinary
exclusions of operators the source renderer does not admit; 207 of the first
3,000 seeds at the default 384-node budget were accepted.
Three transactions draw keys from a six-entry bank (zero, one, the high bit, a
full-width pattern, maximum minus one and maximum), inputs from the six storage
boundaries adjusted to a prescribed parity, and one of four completion patterns
(all return, or one revert in the first, second or third position). These
choices use the high halves of draws from a separate stream, so they do not
correlate with the step seed's helper and template digits. Generated scenarios
must complete with exactly the prescribed outcomes under original Core.
Imported scenarios may use any one to three transactions; random scenarios
have up to eight, and reductions keep at least one.

Reduction simplifies the checked step (keeping every helper and binder),
removes transactions while keeping stable IDs, and replaces one input or key by
a bank value. The order is transaction count, complete program complexity, then
the sum of all keys and inputs. Every candidate rederives its observed slots,
so a reduction that drops the slot of a finding cannot preserve that finding.

```sh
python3 scripts/semantic-storage-differential.py \
  --case .upstream/semantic-keyed-storage-cases/case.json \
  --output .upstream/semantic-keyed-storage-cases/run
python3 scripts/semantic-storage-campaign.py \
  --corpus scripts/semantic-keyed-storage-corpus.json \
  --output .upstream/semantic-keyed-storage-ci --seconds 900
python3 scripts/semantic-suite.py --mode random --profile stateful-keyed-storage \
  --seed 20261026 --cases 16 --attempts 2048 --output .upstream/semantic-keyed-random
```

The storage runner and campaign select the keyed native tool, Hull runner and
comparison rules from the case or manifest profile. `--backend sonatina-o2`
works as for the other storage profiles; Yul is rejected. The synthetic
adapter accepts `--test-field storage:SLOT` for any declared decimal slot of
the original scenario; a candidate that no longer declares that slot is an
ordinary, non-preserving analysis. Fingerprints name differing slots and, for
this profile, the paths with undeclared storage.

The fixed corpus has twelve scenarios and 33 transactions: eight imported plans
and four generated seeds. Its expected histories were computed outside Lean by
a separate evaluator of the step programs and a direct model of the protocol;
`Tests/Main.lean` registers a validator that compares every status, payload
and declared committed slot with original Core and rejects tampered entries.
Required coverage is all 21 step AST features in the corpus, the six inputs,
the six bank keys, one to three helpers and transactions, all four generator
templates, both outcomes, six completion patterns and four static alias kinds:
`key-counter`, `successor-counter`, `repeated-key` and `successor-key`. Alias
kinds describe the transaction keys; they do not claim an aliasing write was
committed or that a particular opcode was executed.

Local validation used committed code with frozen scripts and native tools.
The fixed suite matched all twelve scenarios and 33 transaction prefixes on
Sonatina O0 and O2, with complete coverage, in 69.7 and 69.6 seconds. The
recorded random suite (root seed `20261026`, sixteen cases, 2,048 attempts)
accepted sixteen scenarios from 196 attempts, with 180 ordinary generation
exclusions and no resource exclusions. All sixteen scenarios and 48 prefixes
matched on both levels in 92.5 and 92.4 seconds; they covered all four
completion patterns and alias kinds. Neither run produced a finding.

A copied `importedHull` difference in slot one at `tx-1` of the counter-alias
corpus scenario was reduced on each level to that one transaction with key and
input zero: four accepted reductions in five candidate executions, all of whose
actual comparisons matched. The original and reduced archives replayed exactly
with three-way agreement (four replays), and fresh synthetic replays reproduced
the same fingerprint. Core or Hull fuel one was classified as inconclusive. The
two existing storage profiles still matched all 22 fixed scenarios and 60
prefixes on each level with the extended adapter, and the eight existing native
tools kept their hashes. Changing the shared adapter does invalidate exact
replay of earlier storage archives, as for any adapter change.

This profile does not compare gas, balances, nonces, logs or code, nor
malformed calldata, Solidity-style hashed mapping layouts, dynamic ABI values,
multiple callers or nonzero call value. Undeclared-slot containment is checked
on the Hull and EVM paths only. Agreement in these runs is test evidence, not
a preservation proof. After the adapter was generalized for dynamic arrays
below, the keyed fixed and random suites were repeated on both levels with the
same results.

## Compare bounded dynamic arrays

The `stateful-dynamic-array` profile adds one bounded dynamic ABI value. Each
transaction calls `SynthesizedDynamicArray.run(uint256 flags, uint256[] values)`,
selector `0x9a94c44b`, with zero to three elements in the canonical head/tail
encoding: flags, the tail offset 64 relative to the arguments, the length and
the elements. The source parameter is a lazily decoded
`calldata<array<uint256>>`; it reads `values.length()` and `values[uint256(i)]`.
Original Core follows the head offset to the same length word and element Words
with `inputDataWordBE?`, as the ABI does.

The contract reads the accumulator from slot 0. For each present element `i`
(at most three, unrolled in both Core and source) it computes
`acc = step(acc + values[i])` and writes slot `1 + i`. It then writes the
accumulator to slot 0, adds the length to a running element count in slot 4,
and returns the sum of slots 0 and 4. Odd flags revert after those writes with
the same Word. Shorter arrays leave earlier per-element slots untouched, and an
empty array still rewrites the accumulator and count. Observed slots are fixed
at zero through four, and the keyed profile's containment rules apply: the
Hull and EVM paths must show no nonzero committed slot outside them. The
declared-slot Hull runner `rust-hull-keyed-storage-scenario` serves both
profiles because it accepts the declared slots and calldata from the scenario.

```sh
lake build semanticDynamicArrayTool rustHullKeyedStorageScenario
mkdir -p .upstream/semantic-dynamic-array-cases
.lake/build/bin/semantic-dynamic-array-tool generate 0 384 2 512 1000000 \
  > .upstream/semantic-dynamic-array-cases/corpus.json
python3 scripts/semantic-storage-campaign.py \
  --corpus scripts/semantic-dynamic-array-corpus.json \
  --output .upstream/semantic-dynamic-array-ci --seconds 900
```

Plans use `solcore-lean.dynamic-array-plan.v1` under `dynamicArrayPlan`; cases
use `solcore-lean.semantic-dynamic-array-case.v1`. Transactions are
`{id, flags, values, calldata, value}`; the tool and the adapter both reject
calldata that is not the canonical encoding of the saved flags and values,
arrays longer than three elements and noncanonical Words. The calldata of twelve
generated transactions, including empty arrays, matched `cast calldata` from the
pinned Foundry release byte for byte; the Lean tests retain two such vectors.
Non-canonical
offsets, truncated arrays and the Rust decoder's revert paths are outside this
profile: Core reads an absent Word as zero, while the Rust ABI decoder reverts.

Generation reuses the aggregate step generator; 235 of the first 3,000 seeds at
the 384-node default were accepted. Three transactions draw lengths zero to
three, elements and flags from the six storage boundary inputs, and one of the
four completion patterns from a separate high-bit stream. Reductions simplify
the step, remove a transaction, remove one array element, or replace one
element or the flags by a bank value. They are ordered by transaction count,
program complexity, total element count, then the sum of flags and elements.
The campaign records array lengths as a coverage dimension and treats every
element as a runtime input.

The fixed corpus has twelve scenarios (eight imported, four generated) and 33
transactions with independently computed histories, validated against original
Core by a registered Lean test. It requires all 23 step AST features of the
corpus, the six boundary elements, lengths zero through three, one to three
helpers and transactions, all four templates, both outcomes and six completion
patterns.

Local validation used committed code with frozen scripts and native tools. The
fixed suite matched all twelve scenarios and 33 prefixes on Sonatina O0 and O2
with complete coverage, in 94.7 and 94.1 seconds. The recorded random suite
(root seed `20261026`, sixteen cases, 2,048 attempts) accepted sixteen
scenarios from 195 attempts, with 179 ordinary exclusions and no resource
exclusions; all sixteen and 48 prefixes matched on both levels in 109.8 and
108.4 seconds, covering every length and all four generated completion
patterns. Neither run produced a finding. A copied `importedHull` difference in
slot three at `tx-0` of a three-transaction scenario was reduced on each level
to that transaction with an empty array: six accepted reductions in eight
candidate executions, all of whose actual comparisons matched. The original and
reduced archives replayed exactly with three-way agreement (four replays), and
synthetic replays reproduced the fingerprint. Core or Hull fuel one was
inconclusive. The keyed, two-slot storage and rollback fixed corpora still
matched on both levels with the generalized adapter.

This profile compares one dynamic Word array beside one static Word. Nested or
multi-word element types, `bytes` and strings, ABI-encoded return values and
dynamic memory are outside it, as are gas, balances, nonces and logs. Agreement
is test evidence, not a preservation proof.

## Compare committed event logs

The `stateful-logs` profile makes event logs committed observations. Each
transaction calls `SynthesizedLogs.run(uint256 flags, uint256 input)`,
selector `0x7357f5d2`, with exactly two ABI Words. A plan holds the checked
aggregate step and zero to three log sites. A site has a guard bit `g` (one,
two or three, strictly increasing across sites), a topic count `n` from zero
to four and a data length of zero, one or two Words.

The contract reads `old = sload(0)` and `count = sload(1)`, computes
`result = step(input + old)`, then writes `result` to slot 0 and `count + 1`
to slot 1. Each site in order whose guard bit is set in `flags` computes
`value = step(result + g)` and emits one LOGn record:

| Field | Value |
| --- | --- |
| Emitter | the contract address |
| Topics | `value + 1`, ..., `value + n` |
| Data | `value`, then `result`, as big-endian Words; first `w` of them |

The source emits it with the pinned `std.opcodes` wrapper `log0` to `log4`
over a buffer reserved from the free-memory pointer. Odd flags then revert
with `result` as a 32-byte payload; otherwise `run` returns `result`.

### Definitions

These definitions were fixed before any execution.

- **Log observation.** For each transaction, the ordered list of committed
  logs `{address, topics, data}`: the emitter as a decimal address, zero to
  four decimal topic Words and the data as hexadecimal bytes. The Rust EVM
  path reads the `logs` of each mined receipt in log-index order. Imported
  Hull reads the logs of each actual receipt from the declared-slot runner.
  Original Core's host interface has a single log primitive,
  `emitLogWord(topic, payload)`, with one topic Word and one data Word. The
  Core contract therefore writes each site as a frame of `1 + w + n` word
  logs, and the observer decodes the committed journal of the public
  top-level runtime under framing `core-word-log-framing-v1`:

  | Record | Topic Word | Payload Word |
  | --- | --- | --- |
  | Header | `256 + 16 * w + n` | `0` |
  | Data `i`, for `i` = 1..`w` | `512 + i` | data Word `i` |
  | Topic `j`, for `j` = 1..`n` | `768 + j` | topic `j` |

  Every record of a frame must come from the same emitter. A journal that is
  not a sequence of complete frames is an observer failure, never an empty or
  partial log list. The framing is a convention of this profile, not a Core
  LOGn semantics; Core and its host interface are unchanged.
- **Rollback.** A reverted transaction has no committed logs on any path and
  keeps the prior committed slots. Original Core's public runtime selects the
  checkpoint journal and world; Hull receipts of failed calls export no logs;
  EVM receipts of failed transactions carry none. Logs committed by earlier
  transactions stay committed: after the sequence, `eth_getLogs` over the
  whole local chain for the contract must return exactly the concatenation of
  the deployment and per-transaction receipt logs. The Core and Hull histories
  report each transaction's committed logs once and never retract them. An
  out-of-fuel or otherwise incomplete transaction has unknown logs (`null`)
  and ends the sequence.
- **Deployment.** The contract has no constructor and emits no constructor
  logs. The Hull and EVM deployment receipts must contain no logs and leave
  slots 0 and 1 zero, with no nonzero undeclared slot. Original Core starts
  from the declared post-deployment world with no logs. A deployment log on
  any path is a semantic mismatch at the initial stage.
- **Committed comparison.** After every transaction all three paths must agree
  on status, payload, slots 0 and 1, and the ordered committed logs. The keyed
  profile's containment rules apply to slots outside 0 and 1 on the Hull and
  EVM paths. Each path's logs must also have the static shape that the plan
  and flags determine: on return, one log per guarded site, in site order,
  from the contract address, with that site's topic count and 32 times its
  data length bytes of data; on revert, none.
- **Sequence reduction.** Candidates simplify the checked step (keeping every
  helper and binder), remove one transaction with stable IDs, remove one log
  site (the others keep their guards) or drop its last topic or last data
  Word, replace one transaction's input by a storage boundary input, clear
  one of bits zero to three of its flags, or keep only those four bits. They
  are ordered by transaction count, complete program complexity, then the sum
  of all flags and inputs. A candidate that no longer emits the log of a
  finding cannot preserve that finding.

Coverage adds four dimensions to the storage step dimensions: committed log
counts per transaction, committed topic arities, committed data lengths in
bytes, and the number of guarded sites of each reverted transaction, whose
logs rollback must discard. Generated coverage derives them from the plan and
flags; matched coverage uses the actual original-Core histories.

### Running and validation

```sh
lake build semanticEventLogTool rustHullKeyedStorageScenario
mkdir -p .upstream/semantic-log-cases
.lake/build/bin/semantic-log-tool generate 0 384 2 512 1000000 \
  > .upstream/semantic-log-cases/corpus.json
python3 scripts/semantic-storage-campaign.py \
  --corpus scripts/semantic-log-corpus.json \
  --output .upstream/semantic-log-ci --seconds 900
python3 scripts/semantic-suite.py --mode random --profile stateful-logs \
  --seed 20261026 --cases 16 --attempts 2048 --output .upstream/semantic-log-random
```

The tool accepts the same `generate`, `emit`, `replay`, `observe` and `shrink`
commands as the other storage tools. Plans use `solcore-lean.log-plan.v1`
under the case field `logPlan`, with the step program and its `sites`; cases
use `solcore-lean.semantic-log-case.v1` and record `framingVersion` in their
provenance. Transactions are `{id, flags, input, calldata, value}`.
Histories use `solcore-lean.log-history.v2`: the storage history fields plus
`initialLogs`, the per-transaction `logs` (`null` when unknown) and, on the
EVM path only, `chainLogs`. The declared-slot Hull runner
`rust-hull-keyed-storage-scenario` already exported every receipt's logs, so
it serves this profile unchanged. The storage runner and campaign select the
native tool and comparison rules from the case or manifest profile.
`--backend sonatina-o2` works as for the other storage profiles; Yul is
rejected.

Generation measures the wrapper of the chosen sites and gives the remaining
node budget to the aggregate step generator. A separate high-bit stream
chooses one to three sites (guards, topic counts and data lengths), three
boundary inputs, the guard bits of each transaction's flags, whether its flags
also set the high bits `2^255 + 16`, and one of the four completion patterns.
Of the first 300 seeds at the 384-node default, 283 were accepted; the others
left too few nodes for the selected step template. Generated scenarios must
complete with the prescribed outcomes, and their decoded logs must have the
static site shapes under original Core.

The synthetic adapter accepts `--test-field log`: it flips the low bit of the
first committed log's first topic, or of its last data byte when it has no
topic, in a copied history. A transaction without such a log cannot carry the
synthetic finding. Fingerprints name `logPaths` for deployment and chain-log
differences.

The fixed corpus has twelve scenarios and 33 transactions that commit 27 logs:
eight imported plans, which reuse the dynamic-array corpus steps with new site
layouts and flags, and four generated seeds. Its expected histories, including
every topic and data byte, were computed outside Lean by a separate evaluator
of the step programs and a direct model of the protocol. `Tests/Main.lean`
registers a validator that compares every status, payload, slot and log with
original Core and rejects tampered topics, data, emitters and log order.
Required coverage is all 39 step AST features in the corpus, the six inputs,
one to three helpers and transactions, all four templates, both outcomes, six
completion patterns, committed log counts zero to three, topic arities zero to
four, data lengths of 0, 32 and 64 bytes, and reverted transactions with zero
to three guarded sites.

Local validation used committed code with frozen scripts and native tools; the
eleven existing native tools kept their hashes. The fixed suite matched all
twelve scenarios and 33 prefixes on Sonatina O0 and O2, with complete coverage,
in 68.3 and 68.1 seconds. The recorded random suite (root seed `20261026`,
sixteen cases, 2,048 attempts) accepted sixteen scenarios from eighteen
attempts, with two ordinary exclusions and no resource exclusions. Its 37 sites
took all fifteen combinations of topic count and data length. O0 matched all
sixteen scenarios and 48 prefixes in 92.7 seconds, committing 49 logs on each
path and covering every log count, topic arity and data length, four
completion patterns and discarded counts zero to two.

The O2 random gate failed. Fifteen scenarios and 45 prefixes matched; scenario
`generated-14` (seed `11810673490881475037`) crashed the compiler during O2
code-image export with a host `arithmetic operation overflow` panic in
`primitive-types`. Checked Hull export succeeded, and the same scenario matched
on O0. The panic message differs from the earlier `Integer overflow when
casting to usize` shift-count crashes. Automatic reduction accepted three of
sixteen candidates before its attempt limit and kept the crash fingerprint;
the reduced step's only remaining raw opcode call is `signextend` with index
31. The finding is retained, and the symptom is recorded without upstream
investigation.

A copied `importedHull` log difference at `tx-2` of the three-site,
three-transaction `identity-full-frames` scenario was reduced on each level to
that transaction with flags 2, input zero and one site with one data Word and
no topic: twelve accepted reductions in 28 candidate executions, all of whose
actual comparisons matched. The original and reduced archives replayed exactly
with three-way agreement (four replays), and synthetic replays reproduced the
fingerprint. Core or Hull fuel one was classified as inconclusive. With the
extended adapter, the two-slot storage, rollback, call, keyed and
dynamic-array fixed corpora still matched all 71 scenarios and 197 prefixes on
each level. Changing the shared adapter invalidates exact replay of earlier
storage archives, as for any adapter change.

This profile does not compare gas, balances, nonces or code, `LOG` from
constructors or from more than one contract, memory-dependent data lengths
other than whole Words, or ABI event signatures and indexing. Agreement is
test evidence, not a preservation proof.

## Compare nonzero call value

The `stateful-call-value` profile sends value with each transaction and makes
the contract's own balance a committed observation. Each transaction calls the
payable `SynthesizedCallValue.run(uint256 flags, uint256 input)`, selector
`0x7357f5d2`, with exactly two ABI Words and a call value from a fixed bank:
0, 1, 7, 2^64 - 1, 2^64 and 2^70. The source reads the value with the pinned
`std.opcodes` `callvalue` wrapper; original Core reads it with the
`callValue` host function.

The contract reads `old = sload(0)` and `total = sload(1)`, computes
`result = step(input + value + old)` with the checked aggregate step, writes
`result` to slot 0 and `total + value` to slot 1, then reverts with `result`
as a 32-byte payload if `flags` is odd and returns it otherwise. Slot 1 is the
committed value the contract has accepted, so after every committed
transaction the balance must equal the deployment value plus slot 1.

### Definitions

These definitions were fixed before any execution.

- **Value observation.** After deployment and after every transaction, all
  three paths report status, payload, slots 0 and 1, and the contract's
  committed balance as a decimal Word. The keyed profile's containment rules
  apply to other slots on the Hull and EVM paths. The sender's balance is
  never observed: on the EVM path it also pays gas. Original Core reads the
  contract account's balance in the committed world of
  `BalancedTopLevelExecution`, which transfers the call value from the caller
  to the contract before the root runs. The imported-Hull runner performs the
  same top-level transfer in its checked ledger, as the call runner does for
  its funded constructor, passes the value and entry balance to the Hull
  context, and commits the receipt ledger only on return. The EVM path reads
  `eth_getBalance` at each receipt block.
- **Funds.** A scenario sends at most 2^72 in total. The local Anvil sender
  holds its default funds; original Core and imported Hull fund the caller
  with 2^80. A transfer that original Core or Hull rejects is an execution
  error, never a revert.
- **Rollback.** A reverted transaction refunds its value: the contract keeps
  its prior committed balance and slots on every path. Original Core's
  balanced root runs on the post-transfer world with the pre-transfer world as
  its checkpoint; Hull keeps its prior ledger; the EVM reverts the transfer.
  An out-of-fuel or otherwise incomplete transaction has an unknown balance
  and ends the sequence.
- **Deployment.** The contract has an empty payable constructor and is
  deployed with a value of 0 or 5 recorded in the case. Every path starts with
  that balance, zero slots, no constructor logs and, on Hull and EVM, no
  nonzero undeclared slot. Original Core starts from the declared
  post-deployment world: the contract holds the deployment value and the
  caller 2^80.
- **Committed comparison.** After every transaction all three paths must agree
  on status, payload, slots 0 and 1 and the committed balance. Each path must
  also follow the fixed protocol: the flags parity selects the completion, the
  payload is one Word, a revert keeps the prior slots and balance, and every
  committed balance equals the deployment value plus slot 1.
- **Sequence reduction.** Candidates simplify the checked step (keeping every
  helper and binder), remove one transaction with stable IDs, replace one
  input by a storage boundary input or one value by a smaller bank value,
  reduce one transaction's flags to their parity or clear its revert bit, or
  lower the deployment value to zero. They are ordered by transaction count,
  complete program complexity, then the sum of all flags, inputs and values
  and the deployment value.

Coverage adds three dimensions to the storage step dimensions: the call
values, the values of reverted transactions, whose refunds rollback must
perform, and the deployment values.

### Running and validation

```sh
lake build semanticCallValueTool rustHullValueScenario
mkdir -p .upstream/semantic-call-value-cases
.lake/build/bin/semantic-call-value-tool generate 0 384 2 512 1000000 \
  > .upstream/semantic-call-value-cases/corpus.json
python3 scripts/semantic-storage-campaign.py \
  --corpus scripts/semantic-call-value-corpus.json \
  --output .upstream/semantic-call-value-ci --seconds 900
python3 scripts/semantic-suite.py --mode random --profile stateful-call-value \
  --seed 20261026 --cases 16 --attempts 2048 --output .upstream/semantic-call-value-random
```

The tool accepts the same `generate`, `emit`, `replay`, `observe` and `shrink`
commands as the other storage tools. Plans use `solcore-lean.call-value-plan.v1`
under the case field `callValuePlan`, with the step program and the
`deploymentValue`; cases use `solcore-lean.semantic-call-value-case.v1`.
Transactions are `{id, flags, input, value, calldata}`, where `value` is the
call value. Histories use `solcore-lean.call-value-history.v2`: the storage
history fields plus `initialBalance`, the per-transaction `committedBalance`,
`finalBalance` and the deployment `initialLogs`. The keyed-storage runner
rejects nonzero value, so the new runner `rust-hull-value-scenario` accepts
`callerFunds`, a constructor value and per-call values in its
`solcore-lean.value-contract-scenario.v1` scenarios and reports a rejected
transfer as `transfer-rejected`. Every value is at most 2^70, so a scenario of
at most four values, including the deployment value, sends at most 2^72.

Generation uses a separate high-bit stream for three boundary inputs, three
bank values, the deployment value and one of the four completion patterns;
flags are just the parity. All of the first 300 seeds at the 384-node default
were accepted. Generated scenarios must complete with the prescribed outcomes,
and their committed balances must equal the deployment value plus slot 1 under
original Core. The campaign's candidate identity includes the deployment value,
so a candidate that only lowers it is executed rather than skipped.

The synthetic adapter accepts `--test-field balance`: it flips the low bit of
the selected transaction's committed balance in a copied history.

The fixed corpus has twelve scenarios and 33 transactions: eight imported
plans, which reuse the dynamic-array corpus steps with new values, flags and
deployment values, and four generated seeds. Its expected histories, including
every committed balance, were computed outside Lean by a separate evaluator of
the step programs and a direct model of the protocol. `Tests/Main.lean`
registers a validator that compares every status, payload, slot and balance
with original Core and rejects tampered balances, values, deployment values and
committed refunds. Required coverage is all 39 step AST features in the
corpus, the six inputs, one to three helpers and transactions, all four
templates, both outcomes, six completion patterns, all six bank values, refunds
of 0, 1, 2^64 and 2^70, and both deployment values.

Local validation used committed code with frozen scripts and native tools; the
twelve existing native tools kept their hashes. The fixed suite matched all
twelve scenarios and 33 prefixes on Sonatina O0 and O2, with complete coverage,
in 66.8 and 66.5 seconds. The recorded random suite (root seed `20261026`,
sixteen cases, 2,048 attempts) accepted sixteen scenarios from sixteen
attempts without exclusions. All sixteen scenarios and 48 prefixes matched on
both levels in 94.9 and 93.5 seconds; they refunded every bank value and
covered both deployment values and the four generated completion patterns.
Neither run produced a finding.

A copied `importedHull` balance difference at `tx-2` of the funded
`identity-funded-refund` scenario was reduced on each level to that
transaction with zero flags, input, value and deployment value: six accepted
reductions in six candidate executions, all of whose actual comparisons
matched. The original and reduced archives replayed exactly with three-way
agreement (four replays), and synthetic replays reproduced the fingerprint.
Core or Hull fuel one was classified as inconclusive. With the extended
adapter, the two-slot storage, rollback, call, keyed, dynamic-array and log
fixed corpora still matched all 83 scenarios and 230 prefixes on each level.

This profile does not compare the sender's balance, gas, nonces or code, value
sent by contracts, values above the local sender's funds, or non-payable
methods, whose dispatcher rejects value with a 4-byte selector payload that
the Word outcome convention cannot express. Agreement is test evidence, not a
preservation proof.


## Compare bounded dynamic bytes

The `stateful-bytes` profile adds one bounded dynamic `bytes` value. Each
transaction calls `SynthesizedBytes.run(uint256 flags, bytes payload)`,
selector `0x220eb9b6`, with a payload of 0 to 64 bytes in the canonical
head/tail encoding: flags, the tail offset 64 relative to the arguments, the
length, the payload bytes and zero padding to a multiple of 32 bytes. The
calldata is therefore 100, 132 or 164 bytes long. The pinned dialect decodes
`bytes` only into memory, so the source parameter is `payload: memory<bytes>`
(`data` is a keyword). Its decoder follows the head offset, checks the range,
copies the length Word and the payload into fresh memory with `calldatacopy`
and zeroes the padding. Original Core reads calldata directly.

The contract reads `acc = sload(0)`. For each present 32-byte chunk `k`
(chunk 0 when the length exceeds 0, chunk 1 when it exceeds 32) it computes
`acc = step(acc + chunk_k)` with the checked aggregate step and writes slot
`1 + k`; in a chunk, payload bytes at or past the length read as zero. It then
writes `acc` to slot 0, adds the payload length to a running byte count in
slot 3 and writes the last payload byte, or zero for an empty payload, to
slot 4. The result is `sload(0) + sload(3) + sload(4) + calldatasize()`. Odd
flags revert with it as a 32-byte payload after the writes; other flags
return it. Shorter payloads leave slot 2, or slots 1 and 2, untouched.

### Definitions

These definitions were fixed before any execution.

- **Payload scope.** A payload has 0 to 64 bytes, including lengths that are
  not multiples of 32, and its calldata is exactly the canonical encoding
  above. Non-canonical offsets, truncated or longer payloads and nonzero
  padding are outside the profile. On truncated input the Rust decoder reverts
  with a 4-byte error that the Word outcome convention cannot express, while
  Core reads an absent Word or byte as zero.
- **Reading.** Original Core follows the head offset to the length with
  `inputDataWordBE?`. It reads each chunk Word the same way and masks it to
  the payload length, so padding never contributes. It reads the last payload
  byte with `inputDataByte?` and the calldata size with `inputDataSize`. Core
  and its host interface are unchanged. The source reads the decoded copy:
  the length as `mload(data)` and chunk `k` as `mload(data + 32 + 32k)`, which
  the decoder zero-padded. It reads the last byte as `mload(data + length) &
  255`, an unaligned load of the Word that ends at that byte; for an empty
  payload that Word is the zero length itself.
- **Committed observation.** After every transaction all three paths report
  status, payload and slots 0 through 4. The keyed profile's containment rules
  apply: the Hull and EVM paths must show no nonzero committed slot outside
  them. Memory is per call and not observed.
- **Committed comparison.** All three paths must agree on every observed field
  after every transaction. Each path must also follow the fixed protocol: the
  flags parity selects the completion and the payload is one Word. A revert
  keeps the prior slots. A returned transaction adds its payload length to
  slot 3, leaves its last payload byte (zero when empty) in slot 4 and returns
  the sum of the committed slots 0, 3 and 4 plus its calldata size.
- **Rollback.** A revert keeps the prior committed slots on every path, chosen
  by `ContractRuntime` for original Core. An incomplete transaction ends the
  sequence.
- **Deployment.** The constructor is empty and receives zero value. Every
  declared slot is zero afterwards, and no undeclared slot is nonzero on the
  Hull and EVM paths. Original Core starts from the declared post-deployment
  world.
- **Sequence reduction.** Candidates simplify the checked step (keeping every
  helper and binder), remove one transaction with stable IDs, truncate one
  payload to a shorter length from the generation bank, set every byte of one
  payload to zero, or reduce one transaction's flags to their parity or clear
  its revert bit. They are ordered by transaction count, complete program
  complexity, total payload length, then the sum of all flags and payload
  bytes.

Generation draws three payload lengths from the bank 0, 1, 17, 31, 32, 33,
48, 63 and 64, a byte pattern for each (zeros, `0xff`, the ramp 1, 2, 3, ...
or seeded bytes) and one of four completion patterns from a separate high-bit
stream; flags are just the parity. Coverage adds two dimensions: the payload
lengths, and the payload lengths of reverted transactions, whose slot writes
rollback must discard. The chunk Words are the runtime inputs.

### Running and validation

```sh
lake build semanticBytesTool rustHullKeyedStorageScenario
mkdir -p .upstream/semantic-bytes-cases
.lake/build/bin/semantic-bytes-tool generate 0 384 2 512 1000000 \
  > .upstream/semantic-bytes-cases/corpus.json
python3 scripts/semantic-storage-campaign.py \
  --corpus scripts/semantic-bytes-corpus.json \
  --output .upstream/semantic-bytes-ci --seconds 900
python3 scripts/semantic-suite.py --mode random --profile stateful-bytes \
  --seed 20261026 --cases 16 --attempts 2048 --output .upstream/semantic-bytes-random
```

The tool accepts the same `generate`, `emit`, `replay`, `observe` and `shrink`
commands as the other storage tools. Plans use `solcore-lean.bytes-plan.v1`
under the case field `bytesPlan`; cases use
`solcore-lean.semantic-bytes-case.v1`. Transactions are
`{id, flags, payload, calldata, value}`: `payload` is `0x` followed by two
lowercase hexadecimal digits per byte, and `value` is always zero. The tool
and the adapter both reject a payload longer than 64 bytes, a noncanonical
spelling and calldata that is not the canonical zero-padded encoding of the
saved flags and payload. The calldata of 26 generated transactions covering
every bank length matched `cast calldata "run(uint256,bytes)"` from the pinned
Foundry release byte for byte; the Lean tests retain two such vectors.
Histories use `solcore-lean.bytes-history.v2` with the dynamic-array history
fields, and the declared-slot Hull runner `rust-hull-keyed-storage-scenario`
serves the profile unchanged.

Generation reserves the measured 176-node wrapper before generating the step,
so the 384-node default leaves 208 nodes for it. 275 of the first 300 seeds
were accepted; the others drew a step template that does not fit. Generated
scenarios must complete with the prescribed outcomes and follow the length,
last-byte and sum protocol under original Core.

The fixed corpus has twelve scenarios and 33 transactions: eight imported
plans, which reuse the dynamic-array corpus steps with new payloads and flags,
and four generated seeds. Its expected histories were computed outside Lean by
a separate evaluator of the step programs and a direct model of the protocol.
`Tests/Main.lean` registers a validator that compares every status, payload
and slot with original Core. It rejects tampered outputs, byte counts and last
bytes, committed writes of a reverted transaction, and consistently re-encoded
payloads with a changed or appended byte. Required coverage is all 39 step AST
features in the corpus, the six storage boundary Words as chunks, one to three
helpers and transactions, all four templates, both outcomes, six completion
patterns, all nine bank lengths and reverted payloads of 0, 17, 32, 33 and 64
bytes.

Local validation used committed code with frozen scripts and native tools; the
fourteen existing native tools kept their hashes. The fixed suite matched all
twelve scenarios and 33 prefixes on Sonatina O0 and O2, with complete
coverage, in 73.5 and 73.4 seconds. The recorded random suite (root seed
`20261026`, sixteen cases, 2,048 attempts) accepted sixteen scenarios from
eighteen attempts; its two exclusions drew a step template that does not fit.
All sixteen scenarios and 48 prefixes matched on both levels in 101.5 and
100.5 seconds. They covered every bank length, reverted payloads of 0, 1, 17,
31, 32 and 64 bytes and the four generated completion patterns. Neither run
produced a finding.

A copied `importedHull` difference in slot 2 at `tx-2` of the
`aggregate-pair-full-words` scenario was reduced on each level to that
transaction with zero flags, an empty payload and a reduced step: nine
accepted reductions in nine candidate executions, all of whose actual
comparisons matched. The original and reduced archives replayed exactly with
three-way agreement (four replays), and synthetic replays reproduced the
fingerprint. Core or Hull fuel one was classified as inconclusive. With the
extended adapter, the two-slot storage, rollback, call, keyed, dynamic-array,
log and call-value fixed corpora still matched all 95 scenarios and 263
prefixes on each level.

This profile does not compare gas, balances, nonces, code or memory, payloads
longer than 64 bytes, non-canonical offsets or padding, truncated input and
the decoder's revert paths, strings, `bytes` return values or nested dynamic
values. Agreement is test evidence, not a preservation proof.

## Compare value forwarded by contracts

The `stateful-forwarded-value` profile has one contract send value to another.
It installs `SynthesizedForwarder` and `SynthesizedRecipient`. Each transaction
calls the payable `SynthesizedForwarder.run(uint256 target, uint256 input,
uint256 amount)`, selector `0x24b912e5`, with a call value. The target Word is
the bound child address. The parent forwards `amount` to the child's payable
fallback through the pinned raw `call` wrapper; original Core's parent calls
`callContractWordWithValue` with the same value. The `stateful-calls` profile
already forwards zero or one unit from a fixed eight-unit endowment in
zero-value transactions. Here the sender funds the parent, and both the call
value and the amount come from the bank 0, 1, 7, 2^64 - 1, 2^64 and 2^70.

The parent adds the input and its call value to slot 0. It then calls the
child with the input as one raw 32-byte Word and value `amount`. The child
reads `old0` and `old1`, computes `step(input + callvalue + old0)` with the
checked aggregate step and writes it to slot 0, and adds its call value to
slot 1. An odd input makes it revert with that Word after both writes;
otherwise it returns it. The parent writes the child's payload to slot 1,
adding one if the child reverted, and returns `sload(0) + sload(1)`. Inputs
with bit two set make the parent revert with that Word after both writes. No
logs are emitted. Call modes are therefore `input & 3`: both return, the child
reverts, the root reverts, or both revert.

### Definitions

These definitions were fixed before any execution.

- **Value observation.** After deployment and after every transaction, all
  three paths report the root status and payload, and both contracts'
  balances and slots 0 and 1. Committed logs must be empty. The sender's
  balance is never observed: on the EVM path it also pays gas. Original Core
  runs each transaction through `BalancedTopLevelExecution`, which transfers
  the call value to the parent before the root runs, while the nested runtime
  transfers `amount` at the child call boundary. The imported-Hull runner
  performs the same top-level transfer in its checked ledger, and Hull's own
  call semantics move the forwarded value. The EVM path reads `eth_getBalance`
  for both contracts at each receipt block.
- **Funds.** The parent's empty payable constructor receives 2^72; the child
  deploys with zero value. Every call value and amount is at most 2^70, so the
  parent can always pay three forwards, and the local Anvil sender can pay
  the deployment and three call values. Original Core and imported Hull fund
  the caller with 2^80. A top-level transfer that original Core or Hull
  rejects is an execution error, never a revert.
- **Rollback and refunds.** A child revert discards the child's writes and the
  forwarded value: the child's committed account stays as it was, and the
  amount stays with the parent. A root revert, with or without a child revert,
  keeps both prior committed accounts and returns the call value to the
  sender. An out-of-fuel or otherwise incomplete transaction has unknown
  accounts and ends the sequence.
- **Deployment.** Both constructors are empty. Every path starts with the
  parent holding 2^72, the child holding zero, empty storage and no
  constructor logs. Original Core starts from that declared post-deployment
  world.
- **Committed comparison.** All three paths must agree on every observed field
  after every transaction. Each path must also follow the fixed protocol: bit
  two of the input selects the root completion and the payload is one Word. A
  root revert keeps both accounts, and a child revert under a committed root
  keeps the child's account. In every committed state the child's balance
  equals its slot 1, and the two balances sum to 2^72 plus the call values of
  every committed transaction so far.
- **Sequence reduction.** Candidates simplify the checked step (keeping every
  helper and binder), remove one transaction with stable IDs, replace one
  input by a bank input, clear its child or root revert bit, or lower one call
  value or amount to a smaller bank value. They are ordered by transaction
  count, complete program complexity, then the sum of all inputs, call values
  and amounts.

Generation draws, from a separate high-bit stream, three inputs from the
call profile's ten boundary inputs with their low two bits replaced by one of
the four call modes, and three call values and three amounts from the bank.
Coverage adds the call modes and four value dimensions: call values, forwarded
amounts, amounts a child revert returns to the parent, and call values a root
revert returns to the sender.

### Running and validation

```sh
lake build semanticForwardTool rustHullForwardScenario
mkdir -p .upstream/semantic-forward-cases
.lake/build/bin/semantic-forward-tool generate 0 384 2 512 1000000 \
  > .upstream/semantic-forward-cases/corpus.json
python3 scripts/semantic-call-campaign.py --profile stateful-forwarded-value \
  --corpus scripts/semantic-forward-corpus.json \
  --output .upstream/semantic-forward-ci --seconds 900
python3 scripts/semantic-suite.py --mode random --profile stateful-forwarded-value \
  --seed 20261026 --cases 16 --attempts 2048 --output .upstream/semantic-forward-random
```

The tool accepts the same `generate`, `emit`, `replay`, `observe` and `shrink`
commands as `semantic-call-tool`, with the same call bindings. Plans use
`solcore-lean.forward-plan.v1` under the case field `forwardPlan`; cases use
`solcore-lean.semantic-forward-case.v1`. Transactions are
`{id, input, value, amount, target, callee}`: `value` is the call value the
sender pays and `amount` the value the parent forwards, both at most 2^70.
Histories use `solcore-lean.forward-history.v2` with the call history's
fields. The call runner fixes the eight-unit endowment and zero top-level
value, so the new runner `rust-hull-forward-scenario` accepts `callerFunds`,
the fixed 2^72 endowment and per-call values and amounts in its
`solcore-lean.forward-contract-scenario.v1` scenarios. It reports a rejected
transfer as `transfer-rejected`. `semantic-call-differential.py` and
`semantic-call-campaign.py` select the profile by case schema or `--profile`.
Without explicit tools they use the profile's native tool and runner, and
`stateful-calls` keeps its schemas and rules. The calldata of 24 generated
transactions matched `cast calldata "run(uint256,uint256,uint256)"` from the
pinned Foundry release byte for byte; the Lean tests retain one such vector.

Generation reserves the measured 169-node wrappers before generating the step,
so the 384-node default leaves 215 nodes for it. 275 of the first 300 seeds
were accepted; the others drew a step template that does not fit. Generated
scenarios must complete with the prescribed root outcomes and satisfy the
refund and balance rules under original Core.

The fixed corpus has twelve scenarios and 33 transactions: eight imported
plans, which reuse the dynamic-array corpus steps with new inputs, call values
and amounts, and four generated seeds. Its expected histories, including both
accounts after every transaction, were computed outside Lean by a separate
evaluator of the step programs and a direct model of the protocol.
`Tests/Main.lean` registers a validator that compares every status, payload,
account and empty log list with original Core. It rejects tampered outputs,
balances and logs, a forward committed after a child revert, and changed call
values and amounts. Required coverage is all 39 step AST features in the
corpus, the ten boundary inputs, the four call modes, one to three helpers
and transactions, all four templates, both outcomes, every bank value as a
call value and as an amount, forwards of 1, 2^64 and 2^70 kept by child
reverts, and call values of 0, 7, 2^64 - 1 and 2^70 returned by root reverts.

Local validation used committed code with frozen scripts and native tools; the
fifteen existing native tools kept their hashes. The fixed suite matched all
twelve scenarios and 33 prefixes on Sonatina O0 and O2, with complete
coverage, in 71.2 and 77.4 seconds. The recorded random suite (root seed
`20261026`, sixteen cases, 2,048 attempts) accepted sixteen scenarios from
seventeen attempts; its one exclusion drew a step template that does not fit.
On O0 all sixteen scenarios and 48 prefixes matched in 98.1 seconds. They
covered every bank value as a call value and as an amount, child-revert and
root-revert refunds of every bank value, and all four call modes. On O2
fourteen scenarios and 42 prefixes matched. The other two, `generated-12` and
`generated-14`, crashed the compiler during O2 code-image export with
`Integer overflow when casting to usize`. Checked Hull export succeeded, and
both matched on O0. The O2 random gate therefore failed. Its findings are
recorded in the local `questions.md` without upstream investigation;
automatic reduction of the first kept the crash fingerprint within its attempt
limit.

A copied `importedHull` child-balance difference at `tx-2` of the
`three-helper-forwards` scenario was reduced on each level to that transaction
with zero input, call value and amount and a reduced step: nine accepted
reductions in nine candidate executions, all of whose actual comparisons
matched. The original and reduced archives replayed exactly with three-way
agreement (four replays), and synthetic replays reproduced the fingerprint.
Core or Hull fuel one was classified as inconclusive. With the extended call
and suite scripts, the two-slot storage, rollback, call, keyed, dynamic-array,
log, call-value and bytes fixed corpora still matched all 107 scenarios and
296 prefixes on each level. `scripts/test-source-call-rust.py`, run with the
cloned upstream, still matched all ten parent/child scenarios and 26
transactions.

This profile does not compare the sender's balance, gas, nonces or code,
forwards the parent cannot pay, value sent by the child, deeper or repeated
calls, or logs. Agreement is test evidence, not a preservation proof.

## Compare Keccak-addressed storage mappings

The `stateful-mapping` profile stores through a mapping whose entries live at
Keccak-256 slots. It installs `SynthesizedMapping` with two contract fields:
`counter: word` at slot 0 and `entries: mapping(word => word)` at base slot 1.
The second is the dialect's form of `mapping(uint256 => uint256)`. Each
transaction calls `SynthesizedMapping.run(uint256 flags, uint256 key, uint256
input)`, selector `0x24b912e5`, with exactly three ABI Words and zero value.

The pinned std indexes a mapping through `hash2(p, k)`, which stores the
base slot `p` at memory 0 and the key `k` at memory 32 and hashes those 64
bytes. An entry therefore lives at `keccak256(p ++ k)`. That is the reverse of
Solidity's `keccak256(k ++ p)`, although the std comment cites Solidity's
layout. A probe contract confirmed this order on Sonatina O0 and O2, and the
profile follows the pinned dialect.

The contract reads `old = entries[key]` and writes `entries[key] =
step(input + old)` with the checked aggregate step. It then writes
`entries[key + 1] = old + 1`, where the key wraps at the maximum, and
increments the counter. The result rereads `entries[key] + entries[key + 1] +
counter`; odd flags revert with it as a 32-byte payload after the writes, and
other flags return it.

### Definitions

These definitions were fixed before any execution.

- **Slot derivation.** Original Core derives `keccak256(1 ++ key)` and
  `keccak256(1 ++ (key + 1))` itself, without a Core or host change. It reads
  the key Word with `inputDataWordBE?`, splits the two big-endian Words into
  the eight 64-bit lanes of one 136-byte block, adds Ethereum's `0x01` domain
  byte and the final `0x80`, and applies the Core Keccak-f[1600] permutation
  and digest builders of the Hull import path, converted to Wire with
  `Wire.Expr.ofCore?`. The Hull path lowers the source's `keccak256` builtin
  through the same builders. The reference stays trustworthy for three
  reasons. Both builders are proved against the independent `KeccakSemantics`
  specification (`permute_evaluates`, `digest_evaluates`). The EVM path
  computes Keccak in the EVM, independent of any Lean code. The fixed
  corpus's slots and histories come from Foundry's `cast keccak`. Only the
  absorption of two Words is new; tests check it against `cast keccak` and
  the separate `Solcore.Abi.V1.Keccak256`. The fixed Keccak closure is
  outside the step's node budget.
- **Committed observation.** After every transaction all three paths report
  status, payload and the committed values of the declared slots. These are
  slot 0 plus `keccak256(1 ++ k)` and `keccak256(1 ++ (k + 1))` for every
  transaction key `k`, as decimal Words in ascending order. The keyed profile's
  containment rules apply: the Hull and EVM paths must show no nonzero
  committed slot outside the declaration. A path that derived a slot
  differently therefore differs even where the values agree.
- **Committed comparison.** All three paths must agree on every observed field
  after every transaction. The flags parity selects the completion, the
  payload is one Word, and a revert keeps the prior slots.
- **Rollback.** A revert keeps the prior committed slots on every path, chosen
  by `ContractRuntime` for original Core. An incomplete transaction ends the
  sequence.
- **Deployment.** The constructor is empty and receives zero value. Every
  declared slot is zero afterwards, and no undeclared slot is nonzero on the
  Hull and EVM paths. Original Core starts from the declared post-deployment
  world.
- **Sequence reduction.** Candidates simplify the checked step (keeping every
  helper and binder), remove one transaction with stable IDs, replace one key
  or input by a bank value, or reduce one transaction's flags to their parity
  or clear its revert bit. They are ordered by transaction count, complete
  program complexity, then the sum of all flags, keys and inputs. A candidate
  rederives its declared slots, so one that no longer declares a finding's
  slot cannot keep the finding.

Generation draws three keys from a bank that contains successor pairs and the
maximum, three inputs from the storage boundary inputs and one of four
completion patterns from a separate high-bit stream; flags are just the
parity. Coverage adds the keys and three static alias kinds: a repeated key,
a key that is another key's successor, and the maximum key, whose successor
wraps to zero.

### Running and validation

```sh
lake build semanticMappingTool rustHullKeyedStorageScenario
mkdir -p .upstream/semantic-mapping-cases
.lake/build/bin/semantic-mapping-tool generate 0 384 2 512 1000000 \
  > .upstream/semantic-mapping-cases/corpus.json
python3 scripts/semantic-storage-campaign.py \
  --corpus scripts/semantic-mapping-corpus.json \
  --output .upstream/semantic-mapping-ci --seconds 900
python3 scripts/semantic-suite.py --mode random --profile stateful-mapping \
  --seed 20261026 --cases 16 --attempts 2048 --output .upstream/semantic-mapping-random
```

The tool accepts the same `generate`, `emit`, `replay`, `observe` and `shrink`
commands as the other storage tools. Plans use `solcore-lean.mapping-plan.v1`
under the case field `mappingPlan`; cases use
`solcore-lean.semantic-mapping-case.v1`. Transactions are
`{id, flags, key, input, calldata, value}`, and `value` is always zero. The
tool and the adapter both reject calldata that is not the selector followed
by the saved flags, key and input as three Words. A case's `observedSlots`
must equal the slots the profile derives from its keys. The tool derives them
with `Solcore.Abi.V1.Keccak256` and the adapter with its own Keccak-256, which
the Python tests check against `cast keccak`. The calldata of all 33 fixed and
48 random transactions matched `cast calldata "run(uint256,uint256,uint256)"`
from the pinned Foundry release byte for byte; the Lean tests retain one such
vector. Histories use `solcore-lean.mapping-history.v2` with the keyed history
fields, and the declared-slot Hull runner `rust-hull-keyed-storage-scenario`
serves the profile unchanged.

The Keccak closure converted from the Core builders has 2,654 Wire nodes. A
Lean test checks it, the ABI Keccak and the observer's slots against `cast
keccak` for six keys and two further 64-byte inputs. The closure lies outside
the node budget, so generation reserves only the measured 93-node wrapper and
the 384-node default leaves 291 nodes for the step. All 300 of the first 300
seeds were accepted. Generated scenarios must complete with the prescribed
outcomes, and each returned transaction must increment the counter and return
the sum of the two entries and the counter. One original Core transaction
needs about 164,000 fuel units, within the default 1,000,000. Because a case
embeds the closure (about 120 to 160 KB), a native shrink response for this
profile carries at most 16 candidates, the profile's `shrinkBatch`, to stay
within the campaign's 4 MiB bound on tool output. Other profiles keep
`--shrink-candidates`.

The fixed corpus has twelve scenarios and 33 transactions: eight imported
plans, which reuse the dynamic-array corpus steps with new keys, inputs and
flags, and four generated seeds. Its expected slots and histories were
computed outside Lean, with slots from `cast keccak`, by a separate evaluator
of the step programs and a direct model of the protocol. `Tests/Main.lean`
registers a validator that compares every status, payload and declared slot
with original Core and every declared slot list with the independent one. It
rejects tampered outputs, counters and entries, a declared or committed slot
in Solidity's order, a missing or extra declared slot, and a consistently
re-encoded key change. Required coverage is all 39 step AST features in the
corpus, the six storage boundary inputs, the whole key bank (0, 1, 6, 7,
2^255 and 2^256 - 1), the three alias kinds, one to three helpers and
transactions, all four templates, both outcomes and six completion patterns.

Local validation used committed code with frozen scripts and native tools; the
seventeen existing native tools are byte-identical to main's. The fixed suite
matched all twelve scenarios and 33 prefixes on Sonatina O0 and O2, with
complete coverage, in 75.3 and 75.0 seconds. The recorded random suite (root
seed `20261026`, sixteen cases, 2,048 attempts) accepted sixteen scenarios
from sixteen attempts with no exclusions. All sixteen scenarios and 48
prefixes matched on both levels in 105.1 and 102.7 seconds. They covered the
whole key bank, all three alias kinds and the four generated completion
patterns. Neither run produced a finding.

A copied `importedHull` difference in the entry slot of key 7 at `tx-2` of
the `fresh-cell-high-key` scenario was reduced on each level to that
transaction with key 6, zero input and flags and a reduced step: seven
accepted reductions in eleven candidate executions, all of whose actual
comparisons matched. Key 6 keeps the slot as its successor's entry. The four
rejected candidates lowered the key to 0 or 1, whose declared slots exclude
it, and matched as ordinary executions. A copied counter difference at the
reverted `tx-2` of the `generated-15` scenario was reduced on each level to
that transaction with key and input zero and a reduced step: 37 accepted
reductions in 38 candidate executions. It still reverts, because clearing its
revert bit changed the completion and was rejected. Early native shrink
responses of both reductions reached the sixteen-candidate bound, and each
such batch still held an accepted candidate. The original and reduced
archives replayed exactly with three-way agreement (eight replays), and
synthetic replays reproduced the fingerprints. Core or Hull fuel one was
classified as inconclusive. With the extended adapter, campaign and suite, the
two-slot storage, rollback, call, keyed, dynamic-array, log, call-value, bytes
and forwarded-value fixed corpora still matched all 119 scenarios and 329
prefixes on each level.

This profile does not compare gas, balances, nonces, code or memory, other key
or value types, other base slots, nested mappings or Solidity's slot order.
Agreement is test evidence, not a preservation proof.

## Compare a sender-keyed mapping ledger

The `stateful-ledger` profile keys the mapping profile's Keccak-addressed
entries by the transaction's sender. It installs `SynthesizedLedger` with the
same two fields: `counter: word` at slot 0 and `entries: mapping(word =>
word)` at base slot 1. Each transaction calls `SynthesizedLedger.run(uint256
flags, uint256 recipient, uint256 amount, uint256 input)`, selector
`0x15509d2b`, with exactly four ABI Words and zero value, from one of three
fixed senders. These are Anvil's first three default accounts, in this order:
`0xf39Fd6e51aad88F6F4ce6aB8827279cffFb92266`,
`0x70997970C51812dc3A010C7d01b50e0d17dc79C8` and
`0x3C44CdDdB6a900fa2b585dd299e03d12FA4293BC`. The first one deploys the
contract. The contract reads the sender with `caller()` from `std.opcodes`
and uses its zero-extended Word as the key.

The contract credits `B = entries[sender] + step(input)` with the checked
aggregate step. If `amount > B`, it stores `B` at memory zero and reverts with
those 32 bytes without writing. Otherwise it writes
`entries[sender] = B - amount` and then
`entries[recipient] = entries[recipient] + amount`, increments the counter,
and rereads the sender's entry, the recipient's entry and the counter. Odd
flags revert with their sum after the writes; other flags return it.

### Definitions

These definitions were fixed before any execution.

- **Senders.** Each transaction names one of the three senders. Original Core
  invokes it through `TopLevelExecution` with that `caller`, over a world that
  holds an empty account for each sender, and Core's `callerAddress` host
  request reads it. A new Hull runner, `rust-hull-ledger-scenario`, accepts a
  declared sender set and uses each call's sender as the call context's
  caller; the keyed runner, which requires the constructor's caller, is
  unchanged. The EVM path checks that `eth_accounts` contains every sender
  and sends each transaction from its sender's unlocked account, which Anvil
  funds with 10,000 ether. Balances, nonces and gas are not observed.
- **Slot derivation.** As for the mapping: original Core hashes `1 ++ k` with
  the fixed Keccak closure for the sender's and the recipient's keys, without
  a Core or host change.
- **Committed observation.** After every transaction all three paths report
  status, payload and the committed values of the declared slots. These are
  slot 0 plus `keccak256(1 ++ k)` for every transaction's sender and recipient
  `k`, as decimal Words in ascending order. The keyed profile's containment
  rules apply.
- **Committed comparison and ledger protocol.** All three paths must agree on
  every observed field after every transaction. Each completed row must also
  follow the protocol, checked from its transaction and the prior committed
  slots. Odd flags revert. An even-flag revert is an insufficient balance, so
  its payload is below the amount. A revert keeps every declared slot. A
  returned row increments the counter, changes no declared slot other than
  the counter and the two entries, and returns the sum of the sender's entry,
  the recipient's entry and the counter. For a recipient other than the
  sender, the recipient's entry gains exactly the amount modulo 2^256, and the
  sender's entry plus the amount does not exceed the largest Word. A
  self-transfer leaves an entry of at least the amount.
- **Rollback.** A revert keeps the prior committed slots on every path, chosen
  by `ContractRuntime` for original Core. An incomplete transaction ends the
  sequence.
- **Deployment.** The first sender deploys with zero value and an empty
  constructor. Every declared slot is zero afterwards, and no undeclared slot
  is nonzero on the Hull and EVM paths. Original Core starts from the
  declared post-deployment world.
- **Sequence reduction.** Candidates simplify the checked step (keeping every
  helper and binder), remove one transaction with stable IDs, give one
  transaction an earlier sender in the fixed order, replace one recipient,
  amount or input by a bank value, or reduce one transaction's flags to their
  parity or clear its revert bit. They are ordered by transaction count, the
  number of distinct senders, complete program complexity, then the sum of
  sender positions, flags, recipients, amounts and inputs. A candidate
  rederives its declared slots, so one that no longer declares a finding's
  slot cannot keep the finding.

For each block of three transactions, generation draws each transaction's
sender, recipient, amount and input, and one of four flags patterns, from a
separate high-bit stream.
Recipients come from a bank of the three senders, 0, 2^160 - 1 and 2^256 - 1;
amounts from 0, 1, 7, 2^64 - 1, 2^64 and 2^70; inputs from the storage
boundary inputs. Coverage adds the senders, recipients and amounts, one to
three distinct senders, both revert causes (odd flags and an even-flag
insufficient balance) and three static alias kinds: a self-transfer, a sender
that an earlier transaction paid, and a repeated sender.

### Running and validation

```sh
lake build semanticLedgerTool rustHullLedgerScenario
mkdir -p .upstream/semantic-ledger-cases
.lake/build/bin/semantic-ledger-tool generate 0 384 2 512 1000000 \
  > .upstream/semantic-ledger-cases/corpus.json
python3 scripts/semantic-storage-campaign.py \
  --corpus scripts/semantic-ledger-corpus.json \
  --output .upstream/semantic-ledger-ci --seconds 900
python3 scripts/semantic-suite.py --mode random --profile stateful-ledger \
  --seed 20261026 --cases 16 --attempts 2048 --output .upstream/semantic-ledger-random
```

The tool accepts the same `generate`, `emit`, `replay`, `observe` and `shrink`
commands as the other storage tools; `observe` also rejects bindings whose
contract address is a sender. Plans use `solcore-lean.ledger-plan.v1` under
the case field `ledgerPlan`; cases use `solcore-lean.semantic-ledger-case.v1`.
Transactions are `{id, sender, flags, recipient, amount, input, calldata,
value}`. `sender` is the decimal address of one of the three senders, the
calldata holds the selector and the other four fields as Words, and `value`
is always zero. The tool and the adapter both reject any other sender and
calldata that does not hold the saved Words. A case's `observedSlots` must
equal the slots derived from its senders and recipients. The calldata of all
32 fixed and 48 random transactions matched `cast calldata
"run(uint256,uint256,uint256,uint256)"` from the pinned Foundry release byte
for byte; the Lean tests retain one such vector. Histories use
`solcore-lean.ledger-history.v2` with the keyed history fields.

The new Hull runner `rust-hull-ledger-scenario` takes
`solcore-lean.ledger-contract-scenario.v1` scenarios: the keyed scenario
fields plus `senders`, one to eight distinct addresses other than the
contract, which must include the constructor's caller. Each call's context
names its own caller, which must be a declared sender. The adapter declares
the three senders and uses each transaction's sender as its call's caller. On
the EVM path it first checks that Anvil's first account is the first sender
and that `eth_accounts` unlocks all three, then sends each transaction from
its own sender.

The adapter cannot evaluate the step, so it checks the ledger protocol from
each row and the prior committed slots. Odd flags revert, and a revert keeps
the slots. An even-flag revert reports a credited balance below the amount. A
returned row increments the counter, changes only the counter and the two
entries, and returns their sum. It credits another recipient with exactly the
amount without wrapping the sender's entry; a self-transfer keeps at least the
amount. All three paths agreeing on a row that breaks the protocol is still a
mismatch. Before execution, the campaign plans even flags as returns, so only
matched histories can cover an insufficient balance.

Generation reserves the measured 115-node wrapper, so the 384-node default
leaves 269 nodes for the step; the 2,654-node Keccak closure lies outside the
budget. All 300 of the first 300 seeds were accepted. Their 900 transactions
returned 612 times, reverted on odd flags 217 times and reverted for an
insufficient balance 71 times. Generated scenarios must complete and follow
the ledger protocol under original Core. As for the mapping, a native shrink
response carries at most 16 candidates.

The fixed corpus has twelve scenarios and 32 transactions: eight imported
plans, which reuse the dynamic-array corpus steps with new senders,
recipients, amounts, inputs and flags, and four generated seeds. Its expected
slots and histories were computed outside Lean, with slots from `cast
keccak`, by a separate evaluator of the step programs and a direct model of
the protocol. `Tests/Main.lean` registers a validator that compares every
status, payload and declared slot with original Core and every declared slot
list with the independent one. It rejects tampered outputs, counters and
entries, a sender slot in Solidity's order, a missing or extra declared slot,
another sender and a consistently re-encoded recipient change. Required
coverage is all 33 step AST features in the corpus, the six storage boundary
inputs, all three senders, the whole recipient and amount banks, one to three
distinct senders, both revert causes, the three alias kinds, one to three
helpers and transactions, all four templates, both outcomes and seven
completion patterns.

Local validation used committed code with frozen scripts and native tools; the
eighteen existing native tools are byte-identical to main's. The fixed suite
matched all twelve scenarios and 32 prefixes on Sonatina O0 and O2, with
complete coverage, in 76.2 and 75.6 seconds. The recorded random suite (root
seed `20261026`, sixteen cases, 2,048 attempts) accepted sixteen scenarios
from sixteen attempts with no exclusions. All sixteen scenarios and 48
prefixes matched on both levels in 109.8 and 128.5 seconds. They covered all
senders, recipients and amounts, one to three distinct senders, both revert
causes and all three alias kinds. Neither run produced a finding.

A copied `importedHull` counter difference at `tx-2` of the
`identity-three-senders` scenario, an insufficient-balance revert after two
transfers from the two other senders, was reduced on each level to that
transaction from the first sender with recipient zero, amount one, input zero
and a reduced step: nine accepted reductions in eleven candidate executions,
all of whose actual comparisons matched. The two rejected candidates lowered
the amount to zero, which would have let the transfer through and changed the
completion. A copied difference in the third sender's entry slot at the same
transaction was reduced on each level to that transaction from the first
sender, paying amount one to the third sender, with input zero and a reduced
step: eight accepted reductions in seventeen candidate executions, all of
whose actual comparisons matched. An earlier sender was rejected while it
removed the third sender's slot from the declaration, and accepted once the
transaction paid the third sender, which keeps the slot declared. Recipients
that dropped the slot and an amount of zero were rejected.

On the `generated-8` scenario, whose three-helper step has many reductions, a
difference in its third sender's slot reached the 64-attempt limit on each
level with eleven accepted step reductions in 64 candidate executions. Every
sixteen-candidate batch began with step candidates, and most of them made the
last transfer insufficient, so the transaction candidates were not reached.
The original and reduced archives of all three reductions replayed exactly
with three-way agreement (twelve replays), and synthetic replays reproduced
the fingerprints. Core or Hull fuel one was classified as inconclusive.

With the extended adapter, campaign and suite, the two-slot storage, rollback,
call, keyed, dynamic-array, log, call-value, bytes, forwarded-value and
mapping fixed corpora still matched all 131 scenarios and 362 prefixes on each
level.

This profile does not compare gas, balances, nonces, code or memory, other
senders, value-bearing transfers, contract callers, other key or value types
or Solidity's slot order. Agreement is test evidence, not a preservation
proof.

## Compare `bytes` payloads beyond 64 bytes

The `stateful-long-bytes` profile extends the bytes profile to payloads of up
to 256 bytes. It was built as the fallback for ABI-encoded multi-word return
values: original Core's contract entry conventions return exactly one Word,
and no host request writes return data, so a tuple or `bytes` return would
need a new entry convention in the shared contract runtime. Each transaction
calls `SynthesizedLongBytes.run(uint256 flags, bytes payload)`, selector
`0x220eb9b6`, with the bytes profile's canonical head/tail encoding and a
payload of 0 to 256 bytes. The calldata is therefore 100 to 356 bytes long.
The source parameter is again `payload: memory<bytes>`, so the pinned decoder
copies the length Word and up to eight payload Words into fresh memory and
zeroes the padding.

The contract reads `acc = sload(0)`. For each present 32-byte chunk `k` from 0
to 7 (present when the length exceeds `32k`) it computes `acc = step(acc +
chunk_k)` with the checked aggregate step and writes slot `1 + k`; in a chunk,
payload bytes at or past the length read as zero. It then writes `acc` to slot
0, adds the payload length to a running byte count in slot 9 and writes the
last payload byte, or zero for an empty payload, to slot 10. The result is
`sload(0) + sload(9) + sload(10) + calldatasize()`. Odd flags revert with it
as a 32-byte payload after the writes; other flags return it. With two chunks
and slots 3 and 4 for the count and the last byte, this is exactly the bytes
profile.

### Definitions

These definitions were fixed before any execution.

- **Payload scope.** A payload has 0 to 256 bytes, including lengths that are
  not multiples of 32, and its calldata is exactly the canonical encoding.
  Non-canonical offsets, truncated or longer payloads and nonzero padding are
  outside the profile, as for the bytes profile.
- **Reading.** As for the bytes profile. Original Core follows the head offset
  to the length and reads each chunk Word with `inputDataWordBE?`, masked to
  the payload length, the last payload byte with `inputDataByte?` and the
  calldata size with `inputDataSize`. Core and its host interface are
  unchanged. The source reads chunk `k` of the decoded copy as `mload(data +
  32 + 32k)` and the last byte as `mload(data + length) & 255`.
- **Committed observation.** After every transaction all three paths report
  status, payload and slots 0 through 10. The keyed profile's containment
  rules apply: the Hull and EVM paths must show no nonzero committed slot
  outside them. Memory is per call and not observed.
- **Committed comparison.** All three paths must agree on every observed field
  after every transaction. Each path must also follow the fixed protocol: the
  flags parity selects the completion and the payload is one Word. A revert
  keeps the prior slots. A returned transaction adds its payload length to
  slot 9, leaves its last payload byte (zero when empty) in slot 10 and
  returns the sum of the committed slots 0, 9 and 10 plus its calldata size.
- **Rollback.** A revert keeps the prior committed slots on every path, chosen
  by `ContractRuntime` for original Core. An incomplete transaction ends the
  sequence.
- **Deployment.** The constructor is empty and receives zero value. Every
  declared slot is zero afterwards, and no undeclared slot is nonzero on the
  Hull and EVM paths. Original Core starts from the declared post-deployment
  world.
- **Sequence reduction.** As for the bytes profile: candidates simplify the
  checked step (keeping every helper and binder), remove one transaction with
  stable IDs, truncate one payload to a shorter length from the generation
  bank, set every byte of one payload to zero, or reduce one transaction's
  flags to their parity or clear its revert bit. They are ordered by
  transaction count, complete program complexity, total payload length, then
  the sum of all flags and payload bytes.
- **Node budget.** The eight chunk guards are a fixed part of the wrapper and
  lie outside the step's node budget, as the mapping's Keccak closure does;
  the complete contract may exceed the requested budget by exactly their size.

Generation draws three payload lengths from the bank 0, 1, 64, 65, 96, 97,
128, 129, 192, 223, 255 and 256, a byte pattern for each (zeros, `0xff`, the
ramp 1, 2, 3, ... or seeded bytes) and one of four completion patterns from a
separate high-bit stream; flags are just the parity. Coverage adds the payload
lengths and the payload lengths of reverted transactions, as for the bytes
profile. The chunk Words are the runtime inputs.

### Running and validation

```sh
lake build semanticLongBytesTool rustHullKeyedStorageScenario
mkdir -p .upstream/semantic-long-bytes-cases
.lake/build/bin/semantic-long-bytes-tool generate 0 384 2 512 1000000 \
  > .upstream/semantic-long-bytes-cases/corpus.json
python3 scripts/semantic-storage-campaign.py \
  --corpus scripts/semantic-long-bytes-corpus.json \
  --output .upstream/semantic-long-bytes-ci --seconds 900
python3 scripts/semantic-suite.py --mode random --profile stateful-long-bytes \
  --seed 20261026 --cases 16 --attempts 2048 --output .upstream/semantic-long-bytes-random
```

The tool accepts the same `generate`, `emit`, `replay`, `observe` and `shrink`
commands as the other storage tools. Plans use `solcore-lean.long-bytes-plan.v1`
under the case field `longBytesPlan`; cases use
`solcore-lean.semantic-long-bytes-case.v1`. Transactions are the bytes
profile's `{id, flags, payload, calldata, value}`, with payloads of up to 256
bytes. The adapter treats the profile as a bytes profile with its own payload
bound, observed slots and count and last-byte slots (`maxPayload`, `slots`,
`countSlot` and `tailSlot` in its profile entry). The bytes profile keeps its
64-byte bound and slots 0 to 4. The calldata of all 33 fixed and 48 random
transactions matched `cast calldata "run(uint256,bytes)"` from the pinned
Foundry release byte for byte; the Lean tests retain a 65-byte vector.
Histories use `solcore-lean.long-bytes-history.v2` with the bytes history
fields, and the declared-slot Hull runner `rust-hull-keyed-storage-scenario`
serves the profile unchanged.

The eight chunk guards take 296 Core nodes. They lie outside the node budget,
so generation reserves only the measured 102-node wrapper and the 384-node
default leaves 282 nodes for the step. All 300 of the first 300 seeds were
accepted, and their 900 transactions used every bank length. Generated
scenarios must complete with the prescribed outcomes and follow the length,
last-byte and sum protocol under original Core. A case reaches about 75 KB. At
the 512-node budget, 32 candidates of an eight-transaction case reached
4.13 MB, so a native shrink response carries at most 16 candidates, the
profile's `shrinkBatch`, within the campaign's 4 MiB bound on tool output.

The fixed corpus has twelve scenarios and 33 transactions: eight imported
plans, which reuse the dynamic-array corpus steps with payloads of 0 to 256
bytes, and four generated seeds. Its expected histories were computed outside
Lean by a separate evaluator of the step programs and a direct model of the
protocol. `Tests/Main.lean` registers a validator that compares every status,
payload and slot with original Core. It rejects tampered outputs, byte counts,
last bytes and chunk results, committed writes of a reverted transaction, and
consistently re-encoded payloads with a changed or appended byte. Required
coverage is all 31 step AST features in the corpus, the six storage boundary
Words as chunks, one to three helpers and transactions, all four templates,
both outcomes, six completion patterns, all twelve bank lengths and reverted
payloads of 0, 65, 97, 128, 223, 255 and 256 bytes.

Local validation used committed code with frozen scripts and native tools; the
twenty existing native tools are byte-identical to main's. The fixed suite
matched all twelve scenarios and 33 prefixes on Sonatina O0 and O2, with
complete coverage, in 76.7 and 76.5 seconds. The recorded random suite (root
seed `20261026`, sixteen cases, 2,048 attempts) accepted sixteen scenarios
from sixteen attempts with no exclusions. All sixteen scenarios and 48
prefixes matched on both levels in 107.5 and 105.6 seconds. They covered all
twelve bank lengths and reverted payloads of 64, 96, 97, 128, 192, 223, 255 and
256 bytes. Neither run produced a finding.

A copied `importedHull` difference in slot 8, the slot that only payloads of
more than 224 bytes write, at `tx-0` of the `increment-all-ones` scenario
(256, 128 and 97 bytes of `0xff`) was reduced on each level to that
transaction with an empty payload and a reduced step: five accepted reductions
in seven candidate executions, all of whose actual comparisons matched. The
two rejected candidates removed `tx-0` itself. Truncating its payload kept the
finding because every declared slot is observed whether or not a transaction
writes it. The original and reduced archives replayed exactly with three-way
agreement (four replays), and synthetic replays reproduced the fingerprint.
Core or Hull fuel one was classified as inconclusive. With the extended
adapter, campaign and suite, the two-slot storage, rollback, call, keyed,
dynamic-array, log, call-value, bytes, forwarded-value, mapping and ledger
fixed corpora still matched all 143 scenarios and 394 prefixes on each level.

This profile does not compare gas, balances, nonces, code or memory, payloads
longer than 256 bytes, non-canonical offsets or padding, truncated input and
the decoder's revert paths, strings, or return values longer than one Word.
Agreement is test evidence, not a preservation proof.

## Compare nested dynamic arrays

The `stateful-nested-array` profile adds one nested dynamic ABI input. Each
transaction calls `SynthesizedNestedArray.run(uint256 flags, uint256[][]
values)`, selector `0x7095aff8`, with at most three rows of at most two
elements each in the canonical nested head/tail encoding. That is the flags
and the head offset 64, then at the offset the outer length and one offset per
row, measured from the start of that offset table, and then each row's length
and elements. The calldata is therefore 100 to 484 bytes long. The source
parameter is the lazily decoded `calldata<array<calldata<array<uint256>>>>`;
it reads `values.length()`, the row `values[uint256(i)]`, its `length()` and
the element `row[uint256(j)]`. Original Core follows the head offset, the
outer length, each row's offset and each row's length to the same Words with
`inputDataWordBE?`, as the ABI does.

The contract reads the accumulator from slot 0. For each present row `i` (at
most three) and each present element `j` of it (at most two), unrolled in both
Core and source, it computes `acc = step(acc + values[i][j])` and writes slot
`1 + 2i + j`. It then writes the accumulator to slot 0, adds the outer length
to a running row count in slot 7 and the number of elements to a running
element count in slot 8, and returns the sum of slots 0, 7 and 8. Odd flags
revert after those writes with the same Word. Absent rows and elements leave
their slots untouched.

### Definitions

These definitions were fixed before any execution.

- **Input scope.** A value has at most three rows of at most two elements,
  including empty rows and an empty outer array, and its calldata is exactly
  the canonical encoding. Non-canonical offsets, longer values, truncated
  input and the decoder's revert paths are outside the profile.
- **Reading.** Original Core reads the head offset `o` at byte 36, the outer
  length at `4 + o`, row `i`'s offset `r_i` at `4 + o + 32 + 32i`, that row's
  length at `4 + o + 32 + r_i` and element `j` one Word per index after it.
  Core and its host interface are unchanged. The source reads the same Words
  through the lazy calldata view, whose indexing checks each index against its
  length.
- **Committed observation.** After every transaction all three paths report
  status, payload and slots 0 through 8. The keyed profile's containment rules
  apply: the Hull and EVM paths must show no nonzero committed slot outside
  them. Memory is per call and not observed.
- **Committed comparison.** All three paths must agree on every observed field
  after every transaction. Each path must also follow the fixed protocol: the
  flags parity selects the completion and the payload is one Word. A revert
  keeps the prior slots. A returned transaction adds its row count to slot 7
  and its element count to slot 8 and returns the sum of the committed slots
  0, 7 and 8.
- **Rollback.** A revert keeps the prior committed slots on every path, chosen
  by `ContractRuntime` for original Core. An incomplete transaction ends the
  sequence.
- **Deployment.** The constructor is empty and receives zero value. Every
  declared slot is zero afterwards, and no undeclared slot is nonzero on the
  Hull and EVM paths. Original Core starts from the declared post-deployment
  world.
- **Sequence reduction.** Candidates simplify the checked step (keeping every
  helper and binder), remove one transaction with stable IDs, remove one row
  of one value, remove the last element of one row, set every element of one
  value to zero, or reduce one transaction's flags to their parity or clear
  its revert bit. They are ordered by transaction count, complete program
  complexity, the total number of rows and elements, then the sum of all flags
  and elements.
- **Node budget.** The row and element guards are a fixed part of the wrapper
  and lie outside the step's node budget, as the long-bytes chunk guards do;
  the complete contract may exceed the requested budget by exactly their size.

Generation draws, for each transaction of a three-transaction block, an outer
length from 0 to 3, a length from 0 to 2 for each present row and each element
from the storage boundary inputs, and for the block one of four completion
patterns, from a separate high-bit stream; flags are just the parity. Coverage adds two dimensions: the outer
lengths 0 to 3 and the row lengths 0 to 2. The elements are the runtime
inputs.

### Running and validation

```sh
lake build semanticNestedArrayTool rustHullKeyedStorageScenario
mkdir -p .upstream/semantic-nested-array-cases
.lake/build/bin/semantic-nested-array-tool generate 0 384 2 512 1000000 \
  > .upstream/semantic-nested-array-cases/corpus.json
python3 scripts/semantic-storage-campaign.py \
  --corpus scripts/semantic-nested-array-corpus.json \
  --output .upstream/semantic-nested-array-ci --seconds 900
python3 scripts/semantic-suite.py --mode random --profile stateful-nested-array \
  --seed 20261026 --cases 16 --attempts 2048 --output .upstream/semantic-nested-array-random
```

The tool accepts the same `generate`, `emit`, `replay`, `observe` and `shrink`
commands as the other storage tools. Plans use
`solcore-lean.nested-array-plan.v1` under the case field `nestedArrayPlan`;
cases use `solcore-lean.semantic-nested-array-case.v1`. Transactions are
`{id, flags, values, calldata, value}`, where `values` lists the rows, each a
list of canonical decimal Words. The adapter checks the calldata with its own
encoder of the nested head/tail encoding, and checks every returned row's row
count in slot 7, element count in slot 8 and committed sum. The calldata of
all 33 fixed and 48 random transactions matched `cast calldata
"run(uint256,uint256[][])"` from the pinned Foundry release byte for byte. The
Lean tests retain four of its vectors, among them an empty outer array, an
empty first row and three full rows, and the Python tests three. Histories use
`solcore-lean.nested-array-history.v2`, and the declared-slot Hull runner
`rust-hull-keyed-storage-scenario` serves the profile unchanged.

The three row guards and their six element guards take 270 Core nodes. They
lie outside the node budget, so generation reserves only the measured 86-node
wrapper and the 384-node default leaves 298 nodes for the step. All 300 of the
first 300 seeds were accepted; their 900 transactions used every outer length
223 to 227 times and every row length 418 to 485 times. Generated scenarios
must complete with the prescribed outcomes and follow the row-count,
element-count and sum protocol under original Core. A case reaches about 73
KB. At the 512-node budget, 32 candidates of an eight-transaction case reached
3.35 MB, so a native shrink response carries at most 16 candidates, the
profile's `shrinkBatch`, within the campaign's 4 MiB bound on tool output.

The fixed corpus has twelve scenarios and 33 transactions: eight imported
plans, which reuse the dynamic-array corpus steps with values of up to three
rows of two elements, and four generated seeds. Its expected histories were
computed outside Lean by a separate evaluator of the step programs and a
direct model of the protocol. `Tests/Main.lean` registers a validator that
compares every status, payload and slot with original Core. It rejects
tampered outputs, row counts, element counts and element results, a written
slot of an absent element, committed writes of a reverted transaction, and
consistently re-encoded values with a changed element, an empty row in place
of a row or a dropped row. Required coverage is all 32 step AST features in
the corpus, the six storage boundary Words as elements, one to three helpers
and transactions, all four templates, both outcomes, six completion patterns,
outer lengths 0 to 3 and row lengths 0 to 2. Its reverted transactions have
outer lengths 0 to 3.

Local validation used committed code with frozen scripts and native tools; the
twenty-one existing native tools are byte-identical to main's. The fixed suite
matched all twelve scenarios and 33 prefixes on Sonatina O0 and O2, with
complete coverage, in 93.8 and 91.0 seconds. The recorded random suite (root
seed `20261026`, sixteen cases, 2,048 attempts) accepted sixteen scenarios
from sixteen attempts with no exclusions. All sixteen scenarios and 48
prefixes matched on both levels in 166.1 and 163.6 seconds. They covered every
outer and row length, four completion patterns and 39 step AST features, and
their reverted transactions had outer lengths 0 to 3. Neither run produced a
finding.

A copied `importedHull` difference in slot 6, the slot that only a third row
with two elements writes, at `tx-0` of the `increment-full-values` scenario
(three full rows, then a reverted full value, then three empty rows) was
reduced on each level to that transaction with an empty outer array and a
reduced step: seven accepted reductions in nine candidate executions, all of
whose actual comparisons matched. The two rejected candidates removed `tx-0`
itself. Removing its rows kept the finding because every declared slot is
observed whether or not a transaction writes it. Both levels took the same
path to the same reduced case. The original and reduced archives replayed
exactly with three-way agreement (four replays), and synthetic replays
reproduced the fingerprint. Core or Hull fuel one was classified as
inconclusive. With the extended adapter, campaign and suite, the two-slot
storage, rollback, call, keyed, dynamic-array, log, call-value, bytes,
forwarded-value, mapping, ledger and long-bytes fixed corpora still matched all
155 scenarios and 427 prefixes on each level.

This profile does not compare gas, balances, nonces, code or memory, deeper
nesting, static or multi-word elements, more than three rows or two elements
per row, non-canonical offsets, truncated input and the decoder's revert
paths, or return values longer than one Word. Agreement is test evidence, not
a preservation proof.

## Compare malformed calldata

Every other profile sends canonical calldata. `stateful-malformed-calldata`
sends the dynamic-array contract, `run(uint256 flags, uint256[] values)`,
calldata with one malformation per transaction and compares the three paths
against the pinned std's dispatcher (`std/dispatch.sol`) and decoder
(`std/std.sol`). The compiled contract is the dynamic-array one, emitted from
the same step, and the declared-slot Hull runner serves it unchanged.

### Definitions

The original Core contract `core-malformed-calldata-contract-v1` evaluates
std's checks on the actual calldata, in std's order, through `inputDataSize`,
`inputDataByte?` and `inputDataWordBE?`:

1. Fewer than 4 bytes, or a selector other than `0x9a94c44b`, reaches the
   default fallback, which reverts with `0x4924aef0`
   (`NoSelectorMatchedWithoutFallback()`).
2. Fewer than 68 bytes reverts with `0x08638556` (`ABIInputTruncated()`,
   `do_exec`'s head check).
3. With head offset `o` at byte 36: `o > size - 4`, fewer than 32 bytes at
   `4 + o`, a length above `2^251 - 1` or `32 * length > size - (36 + o)`
   reverts with `0x08638556` (`CalldataWordReader`, `checkArrayHead`).
4. Otherwise the dynamic-array protocol runs on the Word at 4 (flags), the Word
   at `4 + o` (length) and the Word at `36 + o + 32i` (element `i`). Overlaps
   are not checked and trailing bytes are ignored.

A std rejection reverts with exactly its four selector bytes and keeps every
slot. `ArrayOutOfBounds()` cannot arise, since the protocol guards every index
by the length, nor can `NonPayableReceivedValue()`, since no transaction
carries value. Core contracts return or revert one Word, so the wrapper
reverts with the selector as its Word payload.

Each transaction records `{id, flags, values, malformation, calldata,
stdRejection, value}`. The malformation is one of `none`, `short` (0 to 3
selector bytes), `selector` (xor 1, 2^31 or 2^32 − 1), `truncate` (inside the
head or the tail), `trailing` (1, 31, 32, 33 or 64 bytes of zeros, ones or a
ramp), `offset` (out of range: size − 3, size − 35, 2^255; wrapping: 2^256 − 4,
2^256 − 2, 2^256 − 1; overlapping: 0 and 32) or `length` (one too long, 2^251,
2^251 + 1, 2^256 − 1, one shorter, zero). Calldata is at most 1 KiB.
`stdRejection` is the rejecting selector or `null`, from a second std model
written over the bytes (`stdRejection?`); generation and replay require
original Core to give that outcome, and the adapter checks calldata and
outcome with its own encoder and model.

The selector rule: when original Core reverts with exactly one of std's error
selectors as a Word and the transaction's `stdRejection` is that selector, Rust
EVM and imported Hull must each revert with exactly those four bytes, and the
row's Core output is compared as the selector. Every other row is compared
exactly, including a body revert whose 32-byte result equals a selector, and
Hull against EVM is byte-for-byte in every row. Each comparison and analysis
lists the rows compared by selector in `selectorRows`. A false agreement would
need the wrapper's std branch and `stdRejection?` to both reject a transaction
std accepts while both compiled paths reject it with the same selector; the
golden cases guard against that.

Reductions remove transactions first, then reduce the step, then for each
transaction replace its malformation with `none`, try simpler malformations of
its kind, and finally reduce elements and flags. The order counts
transactions, program size, a malformation weight, elements and values.
Gas, value-bearing malformations, malformed constructor calldata and calldata
over 1 KiB are out of scope; every length is checked against the calldata size
before any loop or copy, so a huge length reverts instead of running out of
gas.

### Running and validation

```sh
lake build semanticMalformedCalldataTool rustHullKeyedStorageScenario
mkdir -p .upstream/semantic-malformed-calldata-cases
.lake/build/bin/semantic-malformed-calldata-tool generate 1 448 4 64 1000000 core-g0-v3/lcg64-v1 8 \
  > .upstream/semantic-malformed-calldata-cases/corpus.json
python3 scripts/semantic-storage-campaign.py \
  --corpus scripts/semantic-malformed-calldata-corpus.json \
  --output .upstream/semantic-malformed-calldata-ci --seconds 900
python3 scripts/semantic-suite.py --mode random --profile stateful-malformed-calldata \
  --cases 16 --output .upstream/semantic-malformed-calldata-random
```

Plans use `solcore-lean.malformed-calldata-plan.v1` under
`malformedCalldataPlan`; cases use
`solcore-lean.semantic-malformed-calldata-case.v1` and histories
`solcore-lean.malformed-calldata-history.v1`. The std checks take 273 Core
nodes against the dynamic-array wrapper's 162, so the suite's default budget
for this profile is 448 nodes, leaving 175 for the step.
`Solcore/Test/SourceMalformedCalldataGolden.lean` checks the wrapper and
`stdRejection?` against 35 golden cases written out from the std reading: every
malformation kind, wrapping offsets and lengths, overlap, and the decode order
(a wrong selector on short or truncated calldata, a truncated head with a bad
offset, a wrapping offset with a wrapping length). Each accepted case must
behave exactly like the canonical dynamic-array contract on the decoded words.

The fixed corpus has thirteen scenarios and 36 transactions: eight imported
plans, which reuse the dynamic-array corpus steps with malformed transactions,
and five generated seeds. Its expected histories were computed without the
std wrapper: a prescribed rejection reverts with its selector Word and keeps the
slots, and an accepted transaction is the canonical dynamic-array contract on
the words std decodes. Required coverage is every malformation kind, both std
selectors and acceptance, lengths 0 to 3, one to three helpers and
transactions, all four templates, both outcomes and eight completion patterns.

Local validation used committed code with frozen scripts and native tools. The
fixed suite matched all thirteen scenarios and 36 prefixes on Sonatina O0 and
O2 with complete coverage. Its 22 std rejections reverted on Hull and EVM with
exactly the selector std prescribes, while the thirteen existing stateful
corpora kept their 167 scenarios and 460 prefixes. Random suites of sixteen
eight-transaction cases (seed `20261030`) matched all 16 scenarios and 128
prefixes on both levels, at 448 nodes and at 512:
- 448 nodes: 81 rows were compared by selector and 47 transactions were
  accepted;
- 512 nodes: 82 rows were compared by selector and 46 transactions were
  accepted.
A case took about 7 seconds. Neither run produced a finding.

## Compare malformed nested arrays

`stateful-malformed-nested-array` sends the nested-array contract,
`run(uint256 flags, uint256[][] values)`, calldata with one malformation per
transaction and compares the three paths against the pinned std's dispatcher
and lazy decoder. The compiled contract is the nested-array one, emitted from
the same step, and the declared-slot Hull runner serves it unchanged. The
selector rule, its narrowing and `selectorRows` are exactly those of
`stateful-malformed-calldata`.

### Definitions

The original Core contract `core-malformed-nested-array-contract-v1` evaluates
std's checks on the actual calldata through the same input host functions:

1. Dispatch and the outer array are checked as for malformed calldata, with
   the selector `0x7095aff8`. With head offset `o` and outer length `n`,
   `32n > size - (36 + o)` reverts with `0x08638556`. The offset table at
   `T = 36 + o` is therefore checked whole, including entries for rows the
   body never reads.
2. The protocol reads `values.length()` and then, for each row `i < min(n, 3)`
   in order, `values[i]` (`abiArrayGet` and the lazy calldata array decode).
   With `r` the table Word at `T + 32i`, row `i` reverts with `0x08638556`
   when `r > size - T`, when fewer than 32 bytes remain at `T + r`, when its
   length `m` (the Word at `T + r`) exceeds `2^251 - 1`, or when
   `32m > size - (T + r + 32)`. Its element `j` is the Word at
   `T + r + 32 + 32j`. The protocol folds `j < min(m, 2)` and counts `m`.
3. Rows past the third are never decoded. Row `i` is checked after the
   earlier rows have been folded and written, but a revert commits nothing,
   so only its selector is observable. A read row's whole element region is
   checked, including elements the protocol skips.
4. Overlaps between table entries, rows and the head are not checked, and
   trailing bytes are ignored.

`ArrayOutOfBounds()` cannot arise, since the protocol guards every row index
by the outer length and every element index by the row length.
`NonPayableReceivedValue()` cannot arise either, since no transaction carries
value. Canonical values have up to four rows of up to three elements, one row
and one element more than the protocol reads. The shared modules
`Solcore/Synthesis/Core/StdDispatch.lean` (std's dispatch and head checks in
Core) and `Solcore/Synthesis/Stateful/StdCalldata.lean` (the byte-level model
and the malformation changes) hold what the profiles share.

Each transaction records `{id, flags, values, malformation, calldata,
stdRejection, value}`. The malformation is one of the malformed-calldata kinds
on the outer array (`none`, `short`, `selector`, `truncate`, `trailing`,
`offset`, `length`), `row-offset` or `row-length`. A row malformation names a
present row `row` and replaces its table Word or its length Word with
`value`. The generation banks are:
- `row-offset`:
  - out of range: `size - T - 31`, `size - T`, `size - T + 1`, `2^255`;
  - wrapping onto the outer head: `2^256 - 32` and `2^256 - 1`;
  - overlapping the table: `0`;
  - overlapping another row: that row's offset, or that offset plus 32;
- `row-length`: one too long, the most that fits, one more than fits,
  `2^251`, `2^251 + 1`, `2^256 - 1`, one shorter, and zero.

Banks leave out changes that keep the canonical calldata as it is, and a row
kind drawn for a value without rows sends the canonical calldata.
`stdRejection` comes from a second std model written over the bytes
(`stdDecode`). The adapter checks the calldata and the outcome with its own
encoder and a third model, `nested_std_decode`. A returned row must also
follow the nested-array protocol on the decoded Words: the decoded outer
length goes to slot 7, the read rows' lengths to slot 8, and the row returns
the committed sum.

Reductions remove transactions first and then reduce the step. For each
transaction they then replace the malformation with `none`, try simpler
malformations of the same kind and row, and finally reduce rows, elements and
flags as for nested arrays. Gas, value-bearing malformations, malformed
constructor calldata, calldata over 1 KiB and memory are out of scope.

### Running and validation

```sh
lake build semanticMalformedNestedArrayTool rustHullKeyedStorageScenario
python3 scripts/semantic-storage-campaign.py \
  --corpus scripts/semantic-malformed-nested-array-corpus.json \
  --output .upstream/semantic-malformed-nested-array-ci --seconds 900
python3 scripts/semantic-suite.py --mode random --profile stateful-malformed-nested-array \
  --cases 16 --output .upstream/semantic-malformed-nested-array-random
```

Plans use `solcore-lean.malformed-nested-array-plan.v1` under
`malformedNestedArrayPlan`. Cases use
`solcore-lean.semantic-malformed-nested-array-case.v1` and histories
`solcore-lean.malformed-nested-array-history.v1`. The wrapper keeps 197 Core
nodes inside the step budget. Its 483 nodes of row checks and guards lie
outside it, as the nested-array guards do. The suite's default budget is 448
nodes, which leaves 251 for the step.

`Solcore/Test/SourceMalformedNestedArrayGolden.lean` checks the wrapper and
`stdDecode` against 64 golden cases written out from the std reading: 57
malformations and seven decode-order cases. They cover every malformation kind
and wrapping offsets and lengths. They also cover overlaps that std accepts,
such as a row on its own table Word, a row aliasing another and a row inside
another row's elements, and overlaps it rejects. The lazy checks are covered:
- a malformed or cut fourth row is accepted;
- a cut in the table is rejected;
- a cut in a read row's skipped element is rejected;
- a bad second row is rejected after the first is folded.

So is the decode order: dispatch before decoding, the outer array before
rows, an outer length that leaves a malformed row unread, and an accepted row
before a rejected one. Each accepted case must behave exactly like the
canonical nested-array contract on the decoded Words, with unread rows empty.

The fixed corpus has thirteen scenarios and 36 transactions: eight imported
plans, which reuse the nested-array corpus steps with malformed transactions,
and five generated seeds. Its expected histories were computed without the
std wrapper, from `stdDecode` and the canonical nested-array contract.
Required coverage:
- every malformation kind, both std selectors and acceptance;
- zero to four rows of zero to three elements, and row malformations of rows
  0 to 3;
- one to three helpers and transactions, all four templates, both outcomes
  and eight completion patterns.

Local validation used committed code with frozen scripts and native tools. The
fixed suite matched all thirteen scenarios and 36 prefixes on Sonatina O0 and
O2 with complete coverage. Its 20 std rejections reverted on Hull and EVM with
exactly the selector std prescribes, while the fourteen other stateful corpora
kept their 180 scenarios and 496 prefixes. Random suites of sixteen
eight-transaction cases (seed `20261031`) matched all 16 scenarios and 128
prefixes on both levels, at 448 nodes and at 512. Both budgets draw the same
transactions, and the step differs in 15 of the 16 cases. 67 rows were
compared by selector, 61 transactions were accepted, and no seed was
excluded. A case took about 8.5
seconds. Neither run produced a finding.

## Compare malformed bytes

`stateful-malformed-bytes` sends the long-bytes contract,
`run(uint256 flags, bytes payload)`, calldata with one malformation per
transaction and compares the three paths against the pinned std's dispatcher
and `bytes` decoder. The compiled contract is the long-bytes one, emitted from
the same step, and the declared-slot Hull runner serves it unchanged. The
selector rule, its narrowing and `selectorRows` are exactly those of
`stateful-malformed-calldata`.

### Definitions

The original Core contract `core-malformed-bytes-contract-v1` evaluates std's
checks on the actual calldata through the same input host functions:

1. Dispatch and the head are checked as for malformed calldata, with the
   selector `0x220eb9b6`: with tail offset `o`, `o > size - 4` or fewer than
   32 bytes at `4 + o` reverts with `0x08638556`.
2. With payload length `L`, the Word at `4 + o`, `L > size - (36 + o)`
   reverts with `0x08638556` (`decodeBytesLike`'s advance over the payload).
   std's later `require(length <= ~0 - 63)` can then no longer fail, so a
   length above `~0 - 63` is rejected by the first check with the same
   selector.
3. std copies the length Word and the payload into memory and zeroes the
   padding there, so the calldata padding is neither required nor read: a cut
   inside it is accepted and nonzero padding is ignored.
4. The body reads memory only. It folds chunk `k < 8` when `L > 32k`, writes
   the last payload byte and the running length, and returns or reverts with
   the slots' sum plus the actual calldata size.

Core reads chunk `k` as the aligned calldata Word at `36 + o + 32k`, masked to
the payload. When a cut inside the padding leaves that Word incomplete, it
reads the Word that ends at the last payload byte instead, shifted left to the
chunk's start; that Word exists once std's check has passed.
`NonPayableReceivedValue()` cannot arise, since no transaction carries value.

Each transaction records `{id, flags, payload, malformation, calldata,
stdRejection, value}`. The malformation is one of the malformed-calldata kinds
(`none`, `short`, `selector`, `truncate`, `trailing`, `offset`, `length`) or
`padding`. The banks are:
- `truncate`: cuts inside the head, the length Word, the last payload byte,
  the padding, the last Word or the last byte;
- `length`: one too long, the most that fits, one more than fits,
  `2^256 - 63`, `2^256 - 1`, `2^255`, one shorter, and zero;
- `padding`: `ones`, `ramp` or `last-byte`, for a payload that does not fill
  its last Word.

A kind whose bank is empty for a payload sends the canonical calldata. The
adapter checks the calldata and the outcome with its own encoder and a third
model, `bytes_std_decode`. A returned row must also follow the long-bytes
protocol on the decoded payload: its length goes to slot 9 and its last byte
to slot 10, and the row returns the committed sum plus the actual calldata
size.

Reductions remove transactions first and then reduce the step. For each
transaction they then replace the malformation with `none`, try simpler
malformations of the same kind, and finally shorten the payload to a bank
length, zero it and reduce the flags. Gas, value-bearing malformations,
malformed constructor calldata, calldata over 1 KiB and memory are out of
scope.

### Running and validation

```sh
lake build semanticMalformedBytesTool rustHullKeyedStorageScenario
python3 scripts/semantic-storage-campaign.py \
  --corpus scripts/semantic-malformed-bytes-corpus.json \
  --output .upstream/semantic-malformed-bytes-ci --seconds 900
python3 scripts/semantic-suite.py --mode random --profile stateful-malformed-bytes \
  --cases 16 --output .upstream/semantic-malformed-bytes-random
```

Plans use `solcore-lean.malformed-bytes-plan.v1` under `malformedBytesPlan`.
Cases use `solcore-lean.semantic-malformed-bytes-case.v1` and histories
`solcore-lean.malformed-bytes-history.v1`. The wrapper keeps 211 Core nodes
inside the step budget. Its 416 nodes of chunk guards lie outside it, as the
long-bytes guards do. The suite's default budget is 448 nodes, which leaves 237
for the step.

`Solcore/Test/SourceMalformedBytesGolden.lean` checks the wrapper and
`stdDecode` against 40 golden cases written out from the std reading: 34
malformations and six decode-order cases. They cover every malformation kind
and std's padding rules: cuts inside the padding and nonzero padding are
accepted, a cut inside the payload is rejected, and lengths may run into the
padding. The offset overlaps differ from the array's: offset 0 decodes the
flags as a two-byte length, and offset 32 decodes the original length Word as
a 32-byte payload. Each accepted case must behave exactly like the canonical
long-bytes contract on the decoded payload, except that its result counts the
actual calldata size.

The fixed corpus has thirteen scenarios and 36 transactions: eight imported
scenarios, which reuse the long-bytes corpus steps and payloads with one
malformation per transaction, and five generated seeds. Its expected histories
were computed without the std wrapper, from `stdDecode` and the canonical
long-bytes contract. Required coverage:
- every malformation kind, both std selectors and acceptance;
- all twelve bank payload lengths and the six boundary Words as chunks;
- one to three helpers and transactions, all four templates, both outcomes
  and eight completion patterns.

Local validation used committed code with frozen scripts and native tools. The
fixed suite matched all thirteen scenarios and 36 prefixes on Sonatina O0 and
O2 with complete coverage. Its 14 std rejections reverted on Hull and EVM with
exactly the selector std prescribes, and its 22 accepted transactions,
including cut and nonzero padding, matched exactly. The fifteen other stateful
corpora kept their 193 scenarios and 532 prefixes. Random suites of sixteen
eight-transaction cases (seed `20261031`) matched all 16 scenarios and 128
prefixes on both levels, at 448 nodes and at 512. Both budgets draw the same
transactions, and the step differs in 14 of the 16 cases. 75 rows were
compared by selector, 53 transactions were accepted, and no seed was
excluded. A case took about 6.5
seconds. Neither run produced a finding.

## Compare several methods

`stateful-methods` gives one contract, `SynthesizedMethods`, two to four
external methods over shared declared slots and compares the three paths
against the pinned std's dispatcher. Every other stateful contract has one
method, `run(...)`. The compiler builds std's method tuple from the public
functions in declaration order, std runs the first method whose selector
matches, and a missing selector reaches the default fallback. A duplicate
signature or a selector collision does not compile. The declared-slot Hull
runner serves the contract unchanged, and the selector rule and `selectorRows`
are exactly those of `stateful-malformed-calldata`.

### Definitions

Method `i` of `n` is named `m_` and eight hex digits drawn from the scenario
seed, takes `k` uint256 arguments with `k` from 0 to 2 and returns one uint256.
Its selector is the first four bytes of the Keccak-256 of
`name(uint256,...)`. Names are distinct and selectors do not collide. Each
case records the names, signatures, selectors, arities and the selector order
in declaration order: `ascending`, `descending` or `mixed`, which needs three
methods.

The declared slots are 0 to 5: slot 0 is a shared accumulator, slot 1 a
shared call count and slot `2 + i` method `i`'s last result. Each method has
its own checked aggregate step. With input `x`, the wrapping sum of its
arguments or 0 without arguments, method `i` sets slot 0 to
`step_i(x + slot 0)`, adds one to slot 1 and copies the new slot 0 to slot
`2 + i`. Its result is the sum of slots 0, 1 and `2 + i`. An odd `x` reverts
with that Word; otherwise the method returns it.

The original Core contract `core-methods-contract-v1` dispatches as std does,
through `StdDispatch` and the input host functions:
1. calldata shorter than 4 bytes reverts with `0x4924aef0`;
2. the selector Word is compared with each method's selector in declaration
   order, and no match reverts with `0x4924aef0`;
3. the matched method checks its head size, reverting with `0x08638556`, then
   reads its arguments and runs its protocol.

Each transaction records `{id, method, selector, inputs, calldata,
stdRejection, value}`. It calls one method with its arguments in canonical
calldata, or it sends the missing selector, that of one more drawn name, with
one Word. std rejects the missing selector with `0x4924aef0`. All
transactions are zero-value. The adapter recomputes every selector with its
own Keccak, checks the calldata with its own encoder and the outcome with a
third model, `methods_dispatch`. A returned row must also follow the
shared-slot protocol: slot one counts the call, the called method's slot holds
the new slot zero, every other method's slot keeps its value and the output is
the sum of slots 0, 1 and `2 + i`.

Generation draws the method count, names, arities and the missing selector
from one stream of the scenario seed. The steps share the step budget
equally. Each method's step comes from the first of eight seeds of its own
stream whose step fits its share, under the case's one swarm mask. Each
transaction draws a target from another stream: a method, or about one time
in `2n + 1` the missing selector. Inputs come from the boundary bank.
Reductions remove transactions first, then each method that no remaining
transaction calls, then reduce the steps method by method, and finally
simplify inputs. Gas, value-bearing and payable methods, fallbacks, overloaded
names, calldata that is neither canonical nor a missing selector, and return
values other than one Word are out of scope.

### Running and validation

```sh
lake build semanticMethodsTool rustHullKeyedStorageScenario
python3 scripts/semantic-storage-campaign.py \
  --corpus scripts/semantic-methods-corpus.json \
  --output .upstream/semantic-methods-ci --seconds 900
python3 scripts/semantic-suite.py --mode random --profile stateful-methods \
  --cases 16 --output .upstream/semantic-methods-random
```

Plans use `solcore-lean.methods-plan.v1` under `methodsPlan`. Cases use
`solcore-lean.semantic-methods-case.v1` and histories
`solcore-lean.methods-history.v1`. The dispatch shell keeps 58 Core nodes
inside the budget. Each method's selector comparison, head check and protocol,
72 to 86 nodes by arity, lie outside it. The suite's default budget is 448
nodes, which leaves 390 for the steps: 195 nodes per method with two methods
and 97 with four.

`Solcore/Test/SourceMethodsGolden.lean` checks the wrapper and `stdDispatch`
against golden cases written out from the std reading. Eight contracts declare
two, three and four methods with ascending, descending and mixed selectors.
Their steps add a known constant, so every row follows by hand. The 110
single calls cover:
- each method with an even input and, if it takes arguments, an odd one;
- each method with arguments, called without them;
- each method with an extra Word, which std accepts;
- a missing selector, short calldata and empty calldata.

One five-transaction sequence on four methods checks that the slots are
shared and that rejections and odd inputs commit nothing. The selectors match
`cast sig`.

The fixed corpus has twelve scenarios and 33 transactions: eight imported
scenarios, which reuse six storage corpus steps as methods, and four
generated seeds. Its expected histories were computed without the dispatch
wrapper, from `stdDispatch`, each step run alone and the protocol's slot
arithmetic. Required coverage:
- two to four methods, calls at every method position, all three selector
  orders, arities zero to two, the missing selector and acceptance;
- the six boundary Words as inputs;
- one to three helpers and transactions, all four templates, both outcomes
  and ten completion patterns.

Local validation used committed code with frozen scripts and native tools. The
fixed suite matched all twelve scenarios and 33 prefixes on Sonatina O0 and
O2 with complete coverage. Its five missing-selector transactions reverted on
Hull and EVM with exactly `0x4924aef0`, and its 28 method calls, eleven of
them reverting on an odd input, matched exactly. The sixteen other stateful
corpora kept their 206 scenarios and 568 prefixes. Random suites of sixteen
eight-transaction cases (seed `20261031`) matched all 16 scenarios and 128
prefixes on both levels, at 448 nodes and at 512. They drew two methods in two
cases, three in seven and four in seven, and twelve contracts had mixed
selectors. Both budgets draw the same contracts and transactions, and a step
differs in every case. 19 rows were compared by selector, 109 method calls
were accepted, and no seed was excluded. A case took about seven seconds.
Neither run produced a finding.

## Compare whole committed storage

Every stateful profile compares the declared slots on all three paths. The thirteen
declared-slot profiles also require the Hull and EVM paths to hold no nonzero
slot outside the declaration. A stray write by original Core itself, or any
stray write in the two-slot, rollback and two call profiles, was invisible. All
seventeen stateful profiles now also compare the observed contracts' whole
committed storage after deployment and after every transaction. The
[roadmap](../docs/design/next-implementation-roadmap.md) fixes the definitions;
this section describes how the paths observe it.

### Observation

Each history carries `initialAccountStorage`, an `accountStorage` list on every
row and `finalAccountStorage`. Each lists the observed accounts in role order:
`contract` for the fifteen storage-family profiles, `parent` and `child` for
`stateful-calls` and `stateful-forwarded-value`. Every account names its role,
its bound decimal address and its nonzero entries `{slot, value}` in strictly
increasing slot order. Zero is never listed, so a cleared slot and a slot never
written are the same observation. An incomplete transaction reports the prior
committed storage, as its declared slots do.

- Original Core reads the committed world through `Account.storageEntries`.
  `ContractRuntime`'s account keeps the strictly increasing list of exactly
  its present slots beside its storage function, and every write maintains it.
  `Account.mem_storageEntries_iff` proves that an entry is listed exactly when
  `storageValue?` returns it, and `Account.ext` still holds. The shared module
  `Solcore.Synthesis.Stateful.AccountStorage` renders the observation for the
  observers.
- Imported Hull reports each observed account's committed entries, which a
  revert or incomplete call leaves unchanged. `AccountStorage.canonicalEntries`
  keeps every distinct key with the value its first entry gives, as
  `WordMapping.lookupEntries` does, and drops zero values.
  `mem_canonicalEntries_iff` and `canonicalEntries_sorted` prove that.
- The EVM path calls `debug_traceTransaction` with `prestateTracer` in diff
  mode for every deployment and mined transaction, in every profile. It
  accumulates the observed accounts' reported storage keys and rereads them all
  with `eth_getStorageAt` at each receipt block, dropping zero values. A
  storage change at another account fails closed as an adapter error. The
  report keeps every diff (`storageDiff`).

The diff mode reports exactly the slots whose committed value a transaction
changes. A hand-assembled probe on Anvil 1.5.1 checked this against
`eth_getStorageAt` at the parent and receipt blocks for every slot its calldata
could write, and against the opcode trace's `SSTORE`s. It covered:

- constructor writes;
- fresh, changed and cleared slots, and slots 0, 2^255 and 2^256 - 1;
- a value restored by a later transaction;
- a reverted transaction;
- child calls that returned or reverted under a returned or reverted parent.

A write that leaves a value unchanged inside one transaction is not reported: 0
to 5 to 0, 3 to 4 to 3, a same-value write, or a write rolled back with its
frame. The opcode trace shows that these writes ran, but committed storage
cannot observe them. A contract starts empty, so a slot is nonzero after a
block only if some transaction up to that block changed it, and the union of
reported keys covers the whole storage. The final `anvil_dumpState` of the
probe matched that union. Anvil 1.5.1 has no `debug_storageRangeAt`. A first
matrix also required `anvil_dumpState` to agree after every mined transaction,
but with `--steps-tracing` the dump embeds every step trace. On the
nested-array corpus it outgrew its 64 MiB bound within two transactions, so
that run-time cross-check was dropped. Rerun the probe after any Anvil change;
it starts its own local Anvil with the adapters' flags and exits nonzero on any
discrepancy:

```sh
python3 scripts/check-evm-storage-diff.py
```

### Comparison, rollback and fingerprints

After deployment, every path's observed storage must be empty; every profile
has an empty constructor. After every transaction the three observations must
be equal. A difference is a `semantic-mismatch` at the existing stage with the
field `accountStorage` and the classification `accountStorageDifferences`: the
sorted, unique list of `{account, slot, zeroPaths}` records. They give the
role, the slot as a decimal Word if the case declares it and `undeclared`
otherwise, and the paths at which the slot is zero. A reverted transaction must
leave each path's whole storage equal to its prior observation. In the call
profiles, a child revert (odd input) under a returned root must leave the
child's whole storage unchanged. A path that breaks either rule is listed in
`accountStorageRollbackPaths`. The declared-slot, containment, balance and log
comparisons are unchanged, so a stray Hull write in a declared-slot profile now
reports both `undeclaredStorage` and `accountStorage`.

The storage and call campaigns copy both lists into every fingerprint, empty
when there is no difference. Undeclared slots are fingerprinted only as
`undeclared`, so a reduction may move a stray write to another undeclared slot,
but not to a declared slot, another account or another set of paths that lack
it. Candidates are rerun on all three paths, and `same_failure` requires the
whole fingerprint.

Histories now use the `.v2` schemas of the thirteen profiles that existed
then; the later profiles start at
`solcore-lean.malformed-calldata-history.v1`,
`solcore-lean.malformed-nested-array-history.v1`,
`solcore-lean.malformed-bytes-history.v1` and
`solcore-lean.methods-history.v1`, whole storage included. Reports use
`solcore-lean.semantic-storage-differential.v2` and
`solcore-lean.semantic-call-differential.v2`, and campaign analyses use
`solcore-lean.semantic-storage-analysis.v2` and
`solcore-lean.semantic-call-analysis.v2`. Cases, plans, corpora, Hull scenario
inputs and campaign summaries keep their schemas. The account representation
changed, so every native tool was rebuilt and older archives cannot be replayed
exactly; rerun their `case.json` with `--case`.

### Running and validation

Build and prepare the tools as usual, then run any stateful corpus or suite. To
check detection, reduction and replay of a stray write, add a copied undeclared
slot after actual agreement:

```sh
python3 scripts/semantic-storage-campaign.py \
  --case .upstream/semantic-storage-cases/case.json \
  --test-perturb-path importedHull --test-transaction-id tx-2 \
  --test-field stray --shrink-attempts 24 \
  --output .upstream/semantic-stray-reducer --seconds 900
python3 scripts/semantic-call-campaign.py --profile stateful-calls \
  --case .upstream/semantic-call-cases/case.json \
  --test-perturb-path rustEvm --test-transaction-id tx-1 \
  --test-field child:stray --shrink-attempts 24 \
  --output .upstream/semantic-call-stray-reducer --seconds 900
```

`stray` (storage profiles) and `parent:stray` or `child:stray` (call profiles)
XOR one into the implicit zero Word of slot 2^256 - 2 in one path's copied
whole storage at the selected transaction. A scenario that declares that slot
is rejected before execution. A candidate that removes the transaction,
declares the slot or already holds it there cannot keep the synthetic finding.

### Results

The account change rebuilt every native tool; Core's semantics and every
existing storage law are unchanged. Before each commit the full Lean build and
tests, kernel policy and 572 Python policy tests passed, and the three corpus
validators passed on the final code. With frozen scripts and native tools at
the final commit, all thirteen stateful fixed corpora matched on Sonatina O0
and O2: 167 scenarios and 460 prefixes on each level, in 1,004 and 1,011
seconds, with no finding.

| Profile | Scenarios | Prefixes | O0 seconds | O2 seconds |
| --- | ---: | ---: | ---: | ---: |
| `stateful-storage` | 12 | 33 | 62.2 | 62.2 |
| `stateful-storage-rollback` | 14 | 39 | 72.9 | 73.2 |
| `stateful-calls` | 16 | 44 | 92.3 | 101.2 |
| `stateful-keyed-storage` | 14 | 39 | 76.5 | 76.3 |
| `stateful-dynamic-array` | 15 | 42 | 101.1 | 99.0 |
| `stateful-logs` | 12 | 33 | 66.6 | 66.2 |
| `stateful-call-value` | 12 | 33 | 65.7 | 64.9 |
| `stateful-bytes` | 12 | 33 | 73.5 | 73.3 |
| `stateful-forwarded-value` | 12 | 33 | 71.0 | 76.9 |
| `stateful-mapping` | 12 | 33 | 75.8 | 75.0 |
| `stateful-ledger` | 12 | 32 | 75.7 | 74.6 |
| `stateful-long-bytes` | 12 | 33 | 77.7 | 77.6 |
| `stateful-nested-array` | 12 | 33 | 93.3 | 90.1 |

The synthetic checks used the commands above with the fixed `generated-21`
storage scenario and the `child-rollback-then-value` call scenario, at both
levels. The stray Hull write at `tx-2`, which no earlier observation of the
two-slot profile could see, was classified as an undeclared slot absent on Core
and the EVM. It was reduced to `tx-2` alone with input zero and a smaller step:
sixteen accepted reductions in sixteen candidate executions. The stray EVM
child write at the child-reverting `tx-1` was classified as an undeclared child
slot and as a child-rollback violation on the EVM path. It was reduced to
`tx-1` alone with input one: four accepted reductions in seven executions. The
rejected candidates removed `tx-1` or made the child return, which drops the
rollback classification. Every candidate's actual comparison matched. The
original and reduced archives replayed exactly with agreement (eight replays),
and each replay reproduced the synthetic fingerprint.

This observation does not cover accounts other than the deployed contracts,
transient storage, gas, nonces or code. Agreement is test evidence, not a
preservation proof.

## Compare storage-family contracts on Yul

The fifteen storage-family profiles also run with `--backend yul --solc PATH`.
They compile as the pure profiles do: the checked Rust driver's Yul goes
through solc `0.8.35+commit.47b9dedd` with optimization and Osaka. The two
call profiles stay on Sonatina, because each of their sources compiles a parent
and a child contract. The
[roadmap](../docs/design/next-implementation-roadmap.md) fixes the observation
boundary; this section describes how to run it.

### Definitions

- **Paths:** original Core, the Yul EVM, and imported Hull linked with
  Sonatina O0 images. `pathBackends` records them as `original-core`, `yul` and
  `sonatina-o0`. Hull is an additional reference, not Yul-linked execution.
- **Compilation:** each scenario compiles its own Yul after native replay and
  the O0 Hull and image exports. The EVM deploys the creation bytes, checks the
  installed runtime against the same compilation's deployed bytes, and mines
  every transaction.
- **Observations:** the same as on Sonatina:
  - completion and the returned or reverted bytes, with std's error selectors
    under the selector rule;
  - the declared slots and their containment;
  - the whole committed storage;
  - ordered logs;
  - call value and the contract's balance;
  - the ledger's senders.
- **No layout dependence:** the wrappers' runtime code reads no code, and
  their creation code reads only its own runtime object. Gas, layout, code
  size and optimizer internals are not compared.
- **Admission:** `export-rust-yul.py` admits the sixteen pure and the twelve
  storage-family wrappers, taken from the adapters' profile tables; the three
  malformed profiles reuse wrappers. Each must compile to one creation object
  with one runtime sub-object and no link or immutable references.

### Running and validation

```sh
python3 scripts/semantic-storage-campaign.py --backend yul \
  --corpus scripts/semantic-ledger-corpus.json \
  --output .upstream/semantic-ledger-yul --seconds 900
python3 scripts/semantic-suite.py --mode fixed --backend yul \
  --profile stateful-storage --profile stateful-methods \
  --output .upstream/semantic-storage-yul-fixed
```

Reports keep `backend` `yul` and the same Yul evidence as the pure profiles:
- the checked Yul;
- the exact solc request and response;
- the compiler's digest and full version;
- the main and the Yul Hull artifacts.

Exact replay inherits the backend and rejects a conflicting `--backend`. It
fails if the exporter, the transport or solc's digest or version changed.
`--solc` may name the same executable at another path. Reductions and their
archives keep the backend; a Yul finding is a different identity from the same
difference on Sonatina.

The suite runs a storage-family profile on Yul when `--profile` selects it.
Its default Yul selection stays the sixteen pure profiles. `--backend yul`
with `stateful-calls` or `stateful-forwarded-value` is refused before
execution.

### Results

A feasibility probe preceded the code. It ran the unchanged storage adapter on
the first four scenarios of each fixed corpus, with the EVM deploying solc's
bytes. All 60 scenarios and 173 transactions matched, and every wrapper
compiled to one creation/runtime pair.

The matrices then ran on the committed code with scripts, native tools, solc,
Anvil, and the Rust driver and code-image exporter frozen. Each table entry
gives scenarios and prefixes, all matched:
- **Fixed corpora:** complete coverage.
- **Random suites:** root seed `20261028`, sixteen eight-transaction scenarios
  per profile, G0 revision three, the suite's default budgets.

| Profile | Fixed | Seconds | Random | Seconds |
| --- | ---: | ---: | ---: | ---: |
| `stateful-storage` | 12 / 33 | 95.6 | 16 / 128 | 133.5 |
| `stateful-storage-rollback` | 14 / 39 | 129.6 | 16 / 128 | 135.3 |
| `stateful-keyed-storage` | 14 / 39 | 118.5 | 16 / 128 | 142.9 |
| `stateful-dynamic-array` | 15 / 42 | 155.0 | 16 / 128 | 173.4 |
| `stateful-logs` | 12 / 33 | 102.4 | 16 / 128 | 144.2 |
| `stateful-call-value` | 12 / 33 | 100.6 | 16 / 128 | 144.1 |
| `stateful-bytes` | 12 / 33 | 110.1 | 16 / 128 | 151.7 |
| `stateful-long-bytes` | 12 / 33 | 116.2 | 16 / 128 | 168.9 |
| `stateful-mapping` | 12 / 33 | 110.4 | 16 / 128 | 169.3 |
| `stateful-ledger` | 12 / 32 | 112.5 | 16 / 128 | 172.5 |
| `stateful-nested-array` | 12 / 33 | 137.9 | 16 / 128 | 203.5 |
| `stateful-malformed-calldata` | 13 / 36 | 129.3 | 16 / 128 | 166.4 |
| `stateful-malformed-nested-array` | 13 / 36 | 147.9 | 16 / 128 | 197.6 |
| `stateful-malformed-bytes` | 13 / 36 | 124.7 | 16 / 128 | 166.0 |
| `stateful-methods` | 12 / 33 | 113.3 | 16 / 128 | 163.8 |
| Total | 190 / 524 | 1,804 | 240 / 1,920 | 2,433 |

Selector-rule rows, logs and deployment values on the two suites:

| | Fixed | Random |
| --- | ---: | ---: |
| Rows compared by std's error selector | 61 | 257 |
| Logs | 27 | 83 |
| Nonzero deployment values | 5 | 8 |

Every report recorded the Yul export and `pathBackends`, and every
deployment's prestate diff was empty. Random generation took 248 attempts,
with eight ordinary budget exclusions and no resource exclusion. On the same
code, Sonatina O0 still matched the storage, call-value and several-methods
corpora, in 60.0, 63.1 and 71.6 seconds against 95.6, 100.6 and 113.3 on Yul.
Neither suite produced a finding. Agreement is test evidence, not a
preservation proof.

## Compare generic selection

The `runtime-generics` profile uses a genuinely polymorphic source function
`sc_select<a>(flag, left, right)` at Word, `(word, word)` or `sum<word, word>`.
Each plan contains an independently checked aggregate step graph. The wrapper
computes `left = step(input)` and `right = step(input + 1)` in order before
selection. Odd input selects the left candidate; even input selects the right.
Pair candidates include the original or incremented input as their second
field, and the result sums both fields. Sum candidates use distinct
constructors, and the right branch adds one to its payload. Each selected
value therefore contributes to the returned ABI Word.

The original Core reference contains a monomorphic curried selector closure
and the complete applied step graph. It does not import Rust's specialized
program or computed result. The full program passes the Core checker; the
source emitter's meaning preservation remains unproved.

```sh
lake build semanticCaseTool rustHullScenario
python3 scripts/semantic-campaign.py \
  --profile runtime-generics --seed 1 --nodes 384 --cases 12 --attempts 256 \
  --output .upstream/semantic-generics
python3 scripts/semantic-campaign.py \
  --corpus scripts/semantic-generic-corpus.json --seconds 600 \
  --output .upstream/semantic-generic-ci
python3 Tests/scripts/test-semantic-generic-corpus.py
```

Native commands are `generic-generate SEED NODES COUNT ATTEMPTS FUEL` and
`generic-emit PLAN.json INPUT [FUEL]`. A plan has schema
`solcore-lean.generic-plan.v1`, a canonical checked `stepProgram`, and `variant`
equal to `word`, `pair` or `sum`. The case contains both `genericPlan` and its
complete applied original Core `program`. `observe`, `replay` and `shrink` use
the same commands as earlier pure profiles. The 512-node limit includes all
selector and ABI-input reference syntax; the step alone cannot exhaust that
budget and then hide additional wrapper nodes.

Generated plans use the four boundary inputs zero, one, maximum Word and the
high bit. Both the step and full reference must return at least two distinct
boundary results. Imported and reduced constant computations remain valid.
Seeded provenance is regenerated; every saved program, source, type variant,
input and ABI is reconstructed. Reduction preserves the type variant, helper
count and typed binder inventory while strictly decreasing the complete
reference. A reduced case records its canonical parent plan and input; replay
checks the claimed decrease instead of trusting a `reduced` label.

The corpus's `genericRequirements.instantiations` contains the six combinations
`word:even`, `word:odd`, `pair:even`, `pair:odd`, `sum:even` and `sum:odd`.
`genericCoverage` records these prescribed combinations only after real
three-way agreement. They are not measured specialization or opcode coverage.
The step AST feature inventory and declared helper count exclude the selector
and ABI wrapper. Rejection, resource exhaustion and missing paths cannot meet
coverage requirements. The common campaign's archive replay, explicit synthetic
mismatch adapter and reduction checks apply unchanged.

The fixed corpus contains 28 cases across seven plans. All passed the actual
three-path comparison, covering nineteen step AST features, all four step
recipes, one through three helpers and every required variant/parity pair.
Native validation also checks twelve strictly smaller candidates and fifteen
negative cases. A separate generated pair case reduced its high-bit input to
zero in eight accepted candidate executions while preserving the synthetic
failure fingerprint and type. Original/reduced archive replay and synthetic
replay passed. A fuel-one run remained inconclusive. Capturing closures,
comptime and module combinations use the separate profiles below.


## Compare captured closures

The `runtime-closures` profile exercises runtime Word captures through actual
source lambdas and a generic higher-order `sc_apply<a>`. Both variants compute
an initial outer local with the original aggregate step, create a closure,
increment the outer local, and then increment it again after choosing the
second callable. `snapshot` reuses the first closure twice. `independent`
creates a second closure after the first increment. The first call receives
the original input, the second receives input plus one. The ABI result is
three times the first result plus the second result plus the current outer
local, so all captures, calls and outer assignments contribute.

The Core reference loads each captured Word before constructing its lambda.
The body uses that snapshot rather than reading the mutable outer cell. It
executes one direct closure application and one application through a checked
higher-order function. The entire original program passes the Core checker.
The pinned Rust implementation supplies the capture semantics being tested;
this profile does not claim equivalence with the separate native Lean source
frontend or prove source-emitter correctness.

```sh
lake build semanticCaseTool rustHullScenario
python3 scripts/semantic-campaign.py \
  --profile runtime-closures --seed 1 --nodes 384 --cases 12 --attempts 256 \
  --output .upstream/semantic-closures
python3 scripts/semantic-campaign.py \
  --corpus scripts/semantic-closure-corpus.json --seconds 600 \
  --output .upstream/semantic-closure-ci
python3 Tests/scripts/test-semantic-closure-corpus.py
```

Native commands are `closure-generate SEED NODES COUNT ATTEMPTS FUEL` and
`closure-emit PLAN.json INPUT [FUEL]`. Schema `solcore-lean.closure-plan.v1`
retains a checked aggregate `stepProgram` and `variant` equal to `snapshot` or
`independent`. Cases contain both `closurePlan` and the complete applied
original Core `program`, with a full-program 512-node limit. Generation uses
zero, one, maximum Word and high-bit inputs and rejects constant generated
steps/references. Imported and reduced constant cases remain admissible.

Replay reconstructs the plan, source, input, original program, ABI and origin.
Shrinking preserves the capture recipe, step helper count and typed binders,
strictly decreases the full reference, and records a canonical parent witness.
The common campaign compares all three actual paths before accepting a
reduction. `closureRequirements.variants` and `closureCoverage` track the two
prescribed capture recipes only after matched execution; they are not measured
closure or opcode coverage. The AST feature/helper inventory describes the
original step and excludes the fixed capture/apply/ABI wrapper.

This profile is limited to fixed callable identities and Word snapshots.
Writes through captures, aggregate captures, escaped closure factories and
dynamic selection between different callable identities are separate scopes.
Comptime and source-module bundles use the separate profiles below.

The fixed closure corpus contains 24 cases across six plans. All matched across
the three real execution paths, covering nineteen step AST features, four Word
boundaries, all four aggregate recipes, one through three helpers and both
capture variants. Native validation also checked eight smaller candidates and
fifteen negative cases. A generated independent-capture case reduced in eight
accepted executions while retaining its maximum-Word input and failure
fingerprint. Original/reduced actual archive replay and synthetic replay passed;
an actual fuel-one run remained inconclusive. The attempt limit was recorded,
so reduction does not claim a globally minimal counterexample.


## Compare comptime expressions

The `runtime-comptime` profile retains two original Core ASTs: a closed G0 Word
expression and an aggregate step graph. Source renders the complete closed
expression inside `sc_constant`, which returns `comptime<word>`. Its result
passes through `sc_static(comptime value: word)`, also returning
`comptime<word>`, before use with runtime input. The emitter never evaluates
that expression itself or substitutes a Rust-computed result.

The independent Core reference evaluates the original closed expression once
to obtain `k`, then calls the runtime step once. The `offset` variant returns
`step(input + k) + k`; `scale` returns `step(input) * (k | 1) + k`. The odd
multiplier prevents a zero multiplier from discarding the step. All arithmetic
uses Word wrap. Both retained ASTs and the wrapper count toward the full
512-node limit and the whole-program typing check.

```sh
lake build semanticCaseTool rustHullScenario
python3 scripts/semantic-campaign.py \
  --profile runtime-comptime --seed 1 --nodes 384 --cases 12 --attempts 256 \
  --output .upstream/semantic-comptime
python3 scripts/semantic-campaign.py \
  --corpus scripts/semantic-comptime-corpus.json --seconds 600 \
  --output .upstream/semantic-comptime-ci
python3 Tests/scripts/test-semantic-comptime-corpus.py
```

Native commands are `comptime-generate SEED NODES COUNT ATTEMPTS FUEL` and
`comptime-emit PLAN.json INPUT [FUEL]`. Schema `solcore-lean.comptime-plan.v1`
contains `constantProgram`, `stepProgram` and `variant` (`offset` or `scale`).
The case carries `comptimePlan` and the full applied Core reference. Generation
records both seeds and node allocations, reserves at most eight nodes for the
generated constant, requires an actual operation in that AST, and uses the
four standard boundary inputs. Random comptime campaigns default to 512
generation attempts; other profiles retain 256. Larger imported constants
remain supported within the full-program budget. Constants still render only
the original scalar operations, so other constant operations and fuel
exhaustion remain explicit exclusions; step functions render the raw
primitives. Imported and
reduced constants may be literals.

Replay reconstructs both ASTs, source and wrapper, independently of any saved
observation. Shrinking may reduce the closed constant, step or runtime input;
every candidate is rechecked, keeps its variant and step binder inventory,
and strictly decreases the full reference. A canonical parent witness supports
replay of each reduced case. Actual three-way execution determines whether a
candidate retains an observed failure.

`provenance.features` describes the original step AST;
`provenance.constantFeatures` describes the original closed expression. Fixed
corpora specify `requiredConstantFeatures` and each entry's
`expectedConstantFeatures` separately. `constantCoverage` counts only completed
three-way agreement. `comptimeRequirements.variants` and `comptimeCoverage`
require both composition recipes. These inventories describe source inputs,
not measured backend opcodes. Passing a runtime value to a comptime parameter
is outside this profile; an actual negative probe is rejected during Rust's
comptime evaluation with `SC0409`.

Comptime source-emitter correctness is tested, not formally proved. This
profile does not unify the native Lean frontend's own staging evaluator or
claim unrestricted cross-stage persistence. The module profile below combines
this staging boundary with imported generics and captured closures.

All 32 fixed comptime cases across eight plans match the three real execution
paths. Coverage includes all fifteen enabled constant AST features, 21 step AST
features, both variants, four boundary inputs, one through three helpers and
all four step recipes. Native validation checks eleven smaller candidates and
twenty negative cases. A scale case reduced both retained ASTs in twelve
accepted executions while keeping its maximum-Word input and synthetic
fingerprint. Original/reduced archive replay and synthetic replay passed;
actual fuel-one execution remained inconclusive. All 64 saved cases from the
eight earlier pure profiles retained identical native artifacts and results.


## Compare module bundles and mixed features

The `runtime-modules` profile emits four flat files with explicit imports and
exports. Every provider contributes to the returned Word:

| File | Role |
| --- | --- |
| `case.sol` | ABI entry, staged constant, ordered provider calls and generic selection. |
| `common.sol` | Original closed constant expression, comptime parameter/return, generic apply and select. |
| `left.sol` | Original aggregate step, a Word snapshot closure and mutation of its outer local. |
| `right.sol` | A distinct Word snapshot closure, input-dependent capture and outer mutation. |

Let `k` be the original closed constant, and `x` the runtime input. The left
provider captures `step(x + k)`, increments its outer local, and combines a
closure call with that current local. The right provider captures `x ^ k`,
increments its outer local by two, and likewise combines its closure result
with the current local. Both providers pass a closure through the imported
generic apply function. After both return, an imported generic selector chooses
left for odd input and right for even input. The final Word is selected plus
left plus three times right plus `k`. Both captures and every provider therefore
remain observable even when one selector branch is not taken.

The Core reference retains both original ASTs, creates actual snapshot lambdas,
and evaluates the corresponding fixed composition. It does not parse the
emitted files or reuse Rust's specialized constants, closures or function IDs.
The full program is checker-sealed; the module emitter's meaning preservation
remains unproved.

```sh
lake build semanticCaseTool rustHullScenario
python3 scripts/semantic-campaign.py \
  --profile runtime-modules --seed 1 --nodes 384 --cases 16 --attempts 512 \
  --output .upstream/semantic-modules
python3 scripts/semantic-campaign.py \
  --corpus scripts/semantic-module-corpus.json --seconds 900 \
  --output .upstream/semantic-module-ci
python3 Tests/scripts/test-semantic-module-corpus.py
python3 scripts/test-semantic-source-bundle.py
```

Native commands are `module-generate SEED NODES COUNT ATTEMPTS FUEL` and
`module-emit PLAN.json INPUT [FUEL]`. A `solcore-lean.module-plan.v1` plan retains
`constantProgram` and `stepProgram`; the composition is fixed and has no
variant field. All 512 permitted nodes include both ASTs and the composition.
Random generation reserves at most eight nodes for the constant and defaults
to a 512-attempt campaign limit. All four boundary inputs are emitted per
accepted plan. Constant/step/input shrinking retains typed step binders,
strictly decreases the full original program, and regenerates all four files.

Each `solcore-lean.semantic-module-case.v1` case has `modulePlan`, the applied
Core `program`, the usual input/ABI/provenance fields, and `sourceBundle`:

```json
{
  "schema": "solcore-lean.source-bundle.v1",
  "entry": "case.sol",
  "files": [
    {"path": "case.sol", "source": "..."},
    {"path": "common.sol", "source": "..."},
    {"path": "left.sol", "source": "..."},
    {"path": "right.sol", "source": "..."}
  ]
}
```

The names and ordering are fixed, and `source` is a byte-identical alias of the
entry text. Native replay reconstructs every file and its import/export graph.
Changed providers, missing/extra files, noncanonical names and mismatched entry
aliases cannot pass replay.

Hull's span-derived source inventory may omit a loaded provider after staging
or optimization. The adapter therefore saves and hashes all four generated
files independently before and after both exports. It also checks the complete
tracked pinned standard-library source inventory. The fresh source root is
flat; extra source files, directories and symlinks are rejected. A generated
source URI is recognized only by its exact recorded URI, never by basename or
suffix. Library URIs and hashes remain separate.

`sourceBundleReceipt` retains all relative file hashes, their original URIs and
the pinned library inventory. Replay verifies every archived provider even if
it is absent from Hull spans, then compares generated hashes by canonical
relative name. It does not read the former source directory. An archive can
therefore be moved before replay, while the pinned library/tool identities must
remain unchanged:

```sh
python3 scripts/semantic-differential.py --case CASE.json --output .upstream/module-run
mv .upstream/module-run .upstream/module-archive
python3 scripts/semantic-differential.py --replay .upstream/module-archive \
  --output .upstream/module-replay
```

The fixed corpus requires both prescribed selection branches through
`moduleRequirements.branches` and `moduleCoverage`. Step and original constant
features remain separate inventories, as in the comptime profile. These are
source recipe inventories, not measured import, specialization or opcode
coverage. The scope is this fixed four-file graph, Word captures and ABI Word
results; arbitrary module graphs, cyclic imports, dynamic ABI and native Lean
frontend equivalence are outside it.

All 32 fixed module cases across eight plans match the three actual execution
paths, with no errors, rejections or inconclusive cases. Coverage includes 21
step AST features, all fifteen closed-constant features, one through three
helpers, four boundary inputs, four generation recipes and both prescribed
selection branches. Native validation checks eleven smaller candidates and 31
negative, tamper, path and fuel cases. All 72 saved cases from the nine earlier
pure profiles retain identical native artifacts and observations.

Exact archive replay passed after relocation to a path containing spaces and
removal of the old directory. A synthetic mismatch accepted twelve reductions
in twelve executions, reducing both constant and step while retaining its
maximum-Word input and fingerprint. Actual reduced archive replay matched;
synthetic replay preserved the finding. This bounded search makes no global
minimality claim. Fuel-one execution was inconclusive. Missing archived
provider inventory and an extra `foreign.sol` were rejected before processes
started.

The full repository build (9,900 jobs), tests and semantic-kernel check passed,
as did 33 protocol, 61 campaign and ten source-bundle regressions. M6 is complete
for its bounded generic, closure, comptime and module profiles. These results
do not prove source-emitter preservation or language-wide compiler correctness.
