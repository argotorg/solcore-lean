# Semantic Core implementation policy

This file retains its historical name so existing links remain valid. It now
describes the current implementation policy and the boundary that has been
completed. It is not a chronological ledger, a commit plan, or a promise that
every possible next feature will be implemented.

For the concise revision-local result, see [Current status](CURRENT_STATUS.md).
For public data shapes, see [Core Wire v3](CORE_WIRE_V3.md) and
[Oracle v5](ORACLE_V5_WIRE.md).

## Current objective and boundary

The current objective is a syntax-independent executable formal specification.
That objective has three connected public parts:

1. Semantic Core v3 represents the checked language independently of source
   spelling.
2. The checked-contract runtime executes Core against an explicit world and
   environment.
3. Oracle v5 validates public JSON, checks Core, runs a scenario, and returns a
   total semantic observation.

This is the present completion boundary. Work within it should close defects,
keep the public codecs and semantics aligned, strengthen proofs and tests where
they protect observable behavior, and keep documentation accurate. Expansion
beyond it requires a separate decision about scope and priority.

## Why Core comes before source syntax

Concrete Solcore syntax may change substantially. Encoding runtime meaning in
the current parser or AST would make semantic work depend on unstable spelling.
Semantic Core instead gives typing and execution a small, explicit input that a
future frontend can target.

The separation is:

```text
future source frontend
  → resolved and typed source
  → Semantic Core v3
  → checked-contract runtime
  → Oracle v5 observation
```

Only the last three stages are part of the current executable path. No source
frontend is implicitly simulated by accepting Core JSON.

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
- fuel resumption does not replay already completed transfers, creations, or
  logs.

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

Surface v1 and Oracle v4 remain supported. New concrete grammar work and
parser-specific proof expansion are paused until Solcore syntax stabilizes.

Parser work may resume only when there is an explicit source-language target
and a clear adapter boundary into checked Core. Resumption should preserve old
Surface and Oracle versions and publish a new version when observable syntax or
results change.

The parser is therefore neither deleted nor the current implementation target.
Its frozen tests remain useful regression evidence, but they do not define the
shape of a future Solcore frontend.

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
