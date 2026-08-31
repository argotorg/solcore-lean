# Semantic Core implementation policy

This file retains its historical name so existing links remain valid. It now
describes the current implementation policy and the boundary that has been
completed. It is not a chronological ledger, a commit plan, or a promise that
every possible next feature will be implemented.

For the concise revision-local result, see [Current status](CURRENT_STATUS.md).
For public data shapes, see [Core Wire v3](CORE_WIRE_V3.md) and
[Oracle v5](ORACLE_V5_WIRE.md).

## Current objective and boundary

The checked Semantic Core and contract runtime are the completed executable
semantic boundary. They have three connected public parts:

1. Semantic Core v3 represents the checked language independently of source
   spelling.
2. The checked-contract runtime executes Core against an explicit world and
   environment.
3. Oracle v5 validates public JSON, checks Core, runs a scenario, and returns a
   total semantic observation.

The canonical PR #20 syntax is implemented as an independent source layer, and
its formal parser proof boundary remains active. The parser produces source
syntax; it does not bypass resolution, source typing, or elaboration into
checked Core.

## Why Core remains separate from source syntax

Runtime meaning does not depend on source spelling. Semantic Core gives typing
and execution a small, explicit input while the canonical frontend retains
tokens, comments, grouping, and source spans in its own representation.

The separation is:

```text
canonical source frontend
  → resolved and typed source
  → Semantic Core v3
  → checked-contract runtime
  → Oracle v5 observation
```

The canonical source frontend and the last three stages are implemented as
separate boundaries. The resolved-and-typed source stage does not yet exist;
accepting Core JSON does not simulate source resolution or elaboration.

## Core v3 policy

Semantic Core v3 is a closed public algebra. It contains the currently
supported value, type, control-flow, local-cell, named-data, and Word-operation
forms, plus a frozen contract host context.

The following rules protect that boundary:

- public tags and fields are changed only by a new additive wire version;
- exact encoders emit one canonical representation;
- strict decoders reject missing, unknown, and malformed fields;
- Core depth and node limits are measured before unbounded construction;
- old Core wires continue to reject forms outside their own closed languages;
- internal runtime values, stores, closures, and proof witnesses are not wire
  values; and
- Core-to-wire projection remains explicitly partial for any later internal
  form outside v3.

Well-typedness is mandatory. A decoded program is checked against the frozen
host context before contract admission. The public executor never treats an
unchecked term as an executable contract.

## Executable contract policy

Execution begins from caller-supplied, finite values rather than ambient host
state. A scenario supplies:

- a package of Core contracts;
- accounts with balance, nonce, sparse storage, and optional code;
- nested-call bindings and creation templates;
- a deterministic creation-address policy;
- target, caller, call value, and calldata;
- evaluator fuel; and
- a finite set of state probes.

The implemented runtime includes a top-level call, depth-one checked child
calls, value transfer, checked initialization and runtime installation, ordered
Word logs, and a static `uint256 -> uint256` ABI.

State and effects follow one checkpoint discipline:

- top-level return commits the working world and journal;
- top-level preflight rejection, revert, or trap selects the root checkpoint;
- child return contributes its working changes to the parent;
- child revert or trap restores the child checkpoint;
- initializer failure removes provisional creation effects; and
- internal fuel-resumption laws prove that completed transfers, creations, and
  logs are not replayed. Oracle v5 exposes exhaustion only as `inconclusive`
  and publishes no resume token.

Oracle observations expose only caller-requested state endpoints plus terminal
data and the committed journal. This keeps results finite while allowing tests
to compare account presence, storage, balance, nonce, code, logs, and created
addresses.

Evaluator fuel is a totality and resource boundary. It is not an EVM gas price,
fee schedule, or claim about wall-clock cost. Exhaustion is `inconclusive`, not
a semantic rejection and not a fabricated terminal execution.

## Oracle v5 policy

Oracle v5 is the public composition point. It performs operations in a fixed
order so malformed input, resource exhaustion, typing failure, admission
failure, scenario failure, and execution remain distinct.

Its three queries are:

- `capabilities`, for exact version, profile, feature, and limit discovery;
- `coreCheck`, for one Core v3 program; and
- `execute`, for one complete checked-contract scenario.

Request and response unions are query-specific. A Core-check response cannot
carry an execution observation, and an execution rejection identifies the
phase that rejected it. Protocol errors remain separate from language and
runtime verdicts.

Oracle v1 through v4 remain frozen. V5 dispatch is additive and must not change
their decoding, capability reports, result shapes, or command-line behavior.

## Parser policy

ADR-0153 ended the parser pause. The active target is the pinned PR #20 syntax,
implemented afresh under `Solcore.Syntax` without Surface v1 or Multi
compatibility constraints. Executable lexer and parser coverage is complete;
resource, span, provenance, and grammar-soundness proofs now follow it.

Surface v1 and Oracle v4 remain frozen historical interfaces and are not
reinterpreted. Any public result for the canonical frontend requires a new
additive version.

## Work outside the current boundary

The following areas are not implemented by the current executable path:

- unbounded or recursively nested contract execution;
- a general ABI with dynamic values, fallback, receive, and broader call kinds;
- a complete source pipeline for resolution, source typing, elaboration, and
  execution;
- generation or synthesis of arbitrary well-typed Core or Solcore programs;
  and
- an automated semantic differential-testing harness against independent
  implementations.

Other EVM-adjacent concerns such as gas schedules, block context, memory,
bytecode execution, and full EVM equivalence are also outside the present
claim.

These are candidate directions, not a scheduled roadmap. Starting any one of
them requires an explicit choice of observable behavior, prerequisites, public
versioning, and validation cost. Completing the current executable semantics
does not by itself authorize or commit the project to a particular next area.

## Change discipline

Changes inside the current boundary should preserve these checks:

- declarative and executable typing agree for the published Core;
- evaluator and state transitions retain their stated safety properties;
- commit and rollback select the exact proved endpoints;
- resource limits produce deterministic protocol or inconclusive results;
- encoders and decoders retain canonical round trips and exact failure order;
- old public versions remain unchanged; and
- full build, tests, metadata validation, and kernel trust checks pass.

A new public feature should be small enough to specify, execute, test, and
review as one coherent behavior. Historical decision records explain why past
choices were made; this document and Current status define the active policy.
