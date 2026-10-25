# Generated semantic comparisons

The implementation plan and completion criteria are in
[Semantic differential testing milestones](../docs/design/semantic-differential-testing.md).
The reference Rust revision remains `2a745e12974c373c3799fec81b48a53c7dce2ab4`.

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
The emitter's meaning preservation has not been formally proved. Core typing
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
