# Development guide

This guide describes the required local checks and the workflows for extending
the executable semantics or canonical source frontend.

## Build and test

Use the checked-in Lean toolchain:

    lake build
    lake test
    node scripts/verify-metadata.mjs
    node scripts/check-kernel.mjs

The metadata check protects profile digests, schemas, standard-library hashes,
and golden bytes. The kernel-policy check scans semantic roots for disallowed
escape hatches.

To verify canonical standard-library bytes against an upstream checkout:

    node scripts/verify-metadata.mjs --canonical-source-root <solcore-checkout>/std

## Run the Oracle

    lake exe solcoreOracle --help
    lake exe solcoreOracle --version
    lake exe solcoreOracle capabilities-v3
    lake exe solcoreOracle capabilities-v4
    lake exe solcoreOracle capabilities-v5

With no command, the Oracle consumes and produces one NDJSON object per line.
The request schema selects the protocol. Do not infer a protocol from request
shape or internal implementation details.

## Semantic feature workflow

Before implementation:

1. identify a small vertical feature;
2. accept an ADR fixing observable choices;
3. list every affected syntax, typing, evaluation, machine, checker, safety,
   wire-isolation, and test obligation.

During implementation:

Keep each commit at roughly 300 changed lines or fewer. Split larger features
at independently buildable and testable boundaries.

1. extend the internal Core algebra;
2. extend declarative typing and evaluation;
3. extend total executable inference and evaluation;
4. extend detailed diagnostics;
5. extend the CEK machine;
6. re-establish static and dynamic correspondence;
7. re-establish value, environment, frame, and state safety;
8. make old wire projections reject the new constructors;
9. add focused positive, negative, order, and resource tests.

After implementation:

1. build changed modules with warnings as errors;
2. run the full test suite;
3. run metadata and kernel-policy checks;
4. inspect critical theorem axiom reports;
5. run trust-zero checks for new audit roots where appropriate;
6. update Current status and the feature matrix.

## Completion standard

A feature is not complete merely because evaluation returns the expected value.
Reviewers should be able to locate:

- the independent rule;
- the executable implementation;
- soundness and completeness;
- dynamic correspondence;
- safety preservation;
- resource behavior;
- diagnostic behavior; and
- version-isolation tests.

If a proof direction is intentionally delayed, the status must say partial and
name the missing direction.

## Published compatibility

Do not add new constructors to Semantic Core wire v1, v2, or v3. Conversion
from a later internal Core is intentionally a partial projection. New internal
constructs must produce no representation in an older closed wire.

Similarly, do not reinterpret Surface v1 or any published Oracle v1-v5
contract. Publication of different behavior requires a new additive version
and a separate decision.

The following files are compatibility artifacts and change only as part of an
explicit publication:

- profiles and their manifest;
- JSON schemas;
- capability documents and digests;
- existing golden streams and their manifest;
- published feature arrays and limits.

## Repository locations

| Change | Primary location | Also inspect |
| --- | --- | --- |
| Core algebra and rules | Solcore/Core | all Core proofs and frozen wire projections |
| Checked-contract runtime | Solcore/ContractRuntime | world/frame transitions, observation and verdict decisions |
| Public protocol | Solcore/Oracle | schemas, profiles, golden cases |
| Canonical standard-library bytes | Solcore/Standard | source identity, byte-count and hash pins; canonical workspace consumers |
| Workspace identity | Solcore/Workspace | workspace ADR and tests |
| Canonical source syntax | Solcore/Syntax | ADR-0153 and canonical syntax plan |
| Historical parser maintenance | Solcore/Surface | Surface publication decisions |
| Historical Multi reference | Solcore/Surface/Multi | ADR-0015 and ADR-0018 |

## Canonical frontend replacement

Place new source syntax only under `Solcore/Syntax`. Do not extend the Surface
v1 or Multi grammars, and do not add an adapter merely to reuse their ASTs.
They remain historical compatibility boundaries.

For an upstream syntax change:

1. update the pinned upstream revision;
2. classify its token, grammar, recovery, AST, and diagnostic impact;
3. update the corresponding fixtures; and
4. run the focused frontend and complete repository checks.

Keep syntax and semantic changes independently reviewable. The canonical
parser reaches checked Core only through explicit resolution, source typing,
and elaboration stages. A public source result requires a new additive Oracle
version.

## Kernel policy

scripts/check-kernel.mjs scans Core, Foundation, Semantics, Resolved,
SourceSemantics, TypeSystem, Frontend, Standard, Syntax, Surface, and Workspace
Lean sources. It rejects the language escape hatches named in that script,
including appearances in comments.

This policy is separate from Lean's foundations. Critical theorem axiom reports
may contain propext, Quot.sound, or Classical.choice and should report the
actual result.

## Documentation policy

- README contains only purpose and usage.
- Current status is the only revision-local implementation ledger.
- Architecture describes stable responsibilities.
- ADRs contain durable decisions and rationale.
- Plans contain implementation order and exit conditions.
- Matrices summarize feature and external-evidence coverage.

Do not duplicate long proof inventories or performance diaries across several
documents.
