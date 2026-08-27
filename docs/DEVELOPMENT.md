# Development guide

This guide describes the required local checks and the workflow for extending
the executable semantics.

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

With no command, the Oracle consumes and produces one NDJSON object per line.
The request schema selects the protocol. Do not infer a protocol from the
newest internal implementation.

## Semantic feature workflow

Before implementation:

1. identify a small vertical feature;
2. accept an ADR fixing observable choices;
3. list every affected syntax, typing, evaluation, machine, checker, safety,
   wire-isolation, and test obligation.

During implementation:

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

Do not add new constructors to Semantic Core wire v1 or v2. Their conversion
from the internal Core is intentionally a projection. New internal constructs
must produce no old-wire representation.

Similarly, do not reinterpret Surface v1 or Oracle v4. Publication requires a
new version and a separate decision.

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
| Runtime semantics | Solcore/Semantics | observation and verdict decisions |
| Public protocol | Solcore/Oracle | schemas, profiles, golden cases |
| Workspace identity | Solcore/Workspace | workspace ADR and tests |
| Frozen parser maintenance | Solcore/Surface | Surface publication decisions |
| Frozen Multi reference | Solcore/Surface/Multi | ADR-0015 and frontend freeze plan |

## Frontend freeze

Do not expand the current Multi grammar or its proof inventory during the
semantics-first phase. A necessary maintenance fix must:

- preserve the current grammar version;
- avoid mixing with Core commits;
- state whether it affects only an incomplete experiment or the frozen
  reference;
- run the relevant parser and full repository checks.

Any restored parser experiment remains outside the stable parser baseline.
Stage semantic changes explicitly so unrelated frontend work is not committed
by accident.

## Kernel policy

scripts/check-kernel.mjs scans Core, Semantics, Standard, Surface, and Workspace
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
