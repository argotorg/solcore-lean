# ADR-0008: Semantic observations and EVM revisions

- Status: Accepted
- Decision date: 2026-07-23
- Scope: dynamic semantics, differential oracle

## Reader summary / Current implementation

- **Decision:** Contract observations require an explicit EVM revision and
  compare semantic state effects rather than compiler artifacts.
- **Current implementation:** Current profiles intentionally omit an EVM
  revision and publish only Core evaluation or parse observations. No contract
  EVM execution profile is implemented.
- **Boundary:** Gas belongs only to a separately versioned observation profile;
  it is not part of the current gas-free Core observations.
- **Suggested reading:** Read “Decision” for the observation envelope and
  “Conformance requirements” for deterministic-host requirements.

## Context

The Haskell and Rust EVM test environments do not implicitly use the same
revision. Executing bytecode on different forks can cause differences in opcode
availability, gas, and other host behavior to be misidentified as differences in
compiler semantics.

Comparing bytecode, generated names, internal map order, or even diagnostic prose
also produces many differences unrelated to source-language meaning.

## Decision

Every contract-execution profile specifies an EVM revision explicitly. There is no
implicit default. All compiler outputs under comparison and the Lean evaluator use
the same revision, deterministic host, initial state, and transaction sequence. If
the revision is absent or inconsistent with the profile, execution does not begin.

For each transaction, the standard contract observation includes:

- Halt status: return, revert, or a trap defined by the specification
- Returndata or revertdata
- Storage delta
- Balance delta
- Logs
- External-call trace
- Addresses and code of created contracts

State updates made by a reverted frame are rolled back, while call traces and
revertdata that normatively survive remain in the observation.

The standard `evmStateV1` observation excludes gas, wall-clock time,
compiler-generated names, Hull/Yul ordering, and optimizer traces. Gas comparisons
use a dedicated `evmStateWithGasV1` profile with both the EVM revision and gas
schedule fixed.

Words, addresses, and byte strings use lowercase fixed-width hexadecimal;
integers use decimal strings. Map-like outputs and diagnostics are normalized to
the key order defined by the specification.

## Consequences

- Tests for the Haskell environment's Prague-equivalent revision are not compared
  directly with Rust's Osaka target unless both environments are configured
  explicitly.
- Agreement of source semantics can be assessed independently of byte identity
  between backend artifacts.
- Gas-optimization differences are not standard semantic divergences.
- Comparing canonical deltas instead of entire states omits unrelated initial
  state from the output.
- Host nondeterminism is fixed by the request, making executions reproducible.

## Conformance requirements

- Reject a missing EVM revision or an inconsistent profile before execution.
- Verify that different map insertion orders for the same observation canonicalize
  to the same byte sequence.
- Include tests that distinguish return, revert, and trap.
- Include tests that verify storage and balance rollback after a revert.
- Include observation tests for logs, nested external calls, and contract
  creation.
- Use a golden test to verify that no gas field appears in the standard profile.
- A gas profile remains `unsupported` until its revision and schedule are fully
  specified.
