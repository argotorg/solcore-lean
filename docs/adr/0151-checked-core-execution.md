# ADR-0151: Checked-Core Execution

- Status: Accepted
- Decision date: 2026-08-30
- Scope: Core Wire admission, checked contract execution, and Static Word ABI
- Implementation: Complete

## Context

ADR-0145 through ADR-0149 establish the executable contract lifecycle from an
explicit `WorldState`: root commit and rollback, checked nested calls, checked
balance transfer, checked creation, rollback-aware logs, exact state queries,
and fuel-only resumption. ADR-0150 adds the Static Word ABI and routes raw
calldata through the same lifecycle.

These components require a precise boundary between untrusted Core-shaped
input and executable checked contracts. They also require explicit ownership of
world construction, immutable environment data, contract admission, execution
fuel, and committed observations. None of those concerns should introduce a
second evaluator, ABI dispatcher, state transition, or rollback policy.

## Decision

Use Semantic Core Wire as the closed representation of the current Core
algebra, and use the existing checker and `ContractRuntime` APIs as the sole
admission and execution path.

The direct Lean workflow is:

1. construct or decode a finite Wire Program;
2. convert it to ordinary Core;
3. check it against the Wire host context;
4. admit it into an explicit checked-contract profile;
5. construct a finite `WorldState` and `ExecutionEnvironment`; and
6. invoke `BalancedTopLevelExecution.runWithEnvironment`.

Every result is the existing total runtime result. This decision adds no
parallel evaluator or runtime semantics.

## Semantic Core Wire

Core Wire is a closed algebra covering the current internal:

- primitive, product, function, sum, cell, and named-data types;
- data definitions and constructor identities;
- literals, variables, products, functions, sums, cells, named data, binding,
  conditionals, and primitive-operation expressions; and
- the supported unary, binary, and ternary operators.

The complete field and operator catalog is recorded in
[Core Wire](../CORE_WIRE.md). Wire-to-Core conversion is total.
Core-to-wire conversion returns `Option`, so an unassigned future constructor
or operator is rejected until the current Wire boundary explicitly supports it.

Canonical scalar encoding uses exact lowercase hexadecimal forms for Word,
Address, and byte values. Natural numbers encode as integers. Structural
decoding rejects unknown or missing fields, invalid tags, invalid scalars, and
values beyond explicit depth and node budgets.

## Frozen host context and checker promotion

Core Wire fixes the host-function order and each function's parameter and result
types. Admission checks against that frozen context rather than the append-only
current host table. A later host-table extension therefore cannot silently make
a previously invalid Wire free variable valid.

The detailed context-parameterized checker preserves paths and rejection
reasons. Successful checking promotes to the current
`CheckedHostCoreProgram` evidence used by `ContractRuntime`. No caller may
assert checked status or construct the proof-bearing runtime value directly.

## Checked contract profiles

Contract admission is explicit and closed:

- `returnWord` admits a checked Program returning `word`;
- `wordOutcomeV1` admits a checked Program returning
  `sum(word, sum(word, word))`; and
- the Static Word ABI admits a nonempty table of `uint256 -> uint256`
  implementations through ADR-0150.

Static Word method input consists of a validated method name and checked
implementation. Input type, output type, canonical signature, and selector are
derived rather than accepted redundantly. Admission rejects unsupported result
types, ill-typed implementations, nonempty method data definitions, empty
tables, duplicate signatures, and selector collisions before any runnable
contract is produced.

## Finite world and immutable environment

Execution starts from an explicit finite `WorldState`. Each account contains an
Address, Word balance and nonce, sparse nonzero storage, and optional checked
code. Construction uses the ordinary account and world operations, preserving
exact lookup, balance, nonce, storage, and code provenance.

`ExecutionEnvironment` supplies finite checked-call bindings, checked creation
templates, and a total creation-address policy consisting of explicit routes
plus a default Address. Resolution still verifies that selected code is
installed in the current world.

The root contract is selected from the target account. Root installation
requires the target account and checked code to be present before execution.
Raw calldata is passed directly to the selected checked contract, including to
the Static Word ABI dispatcher when that contract profile owns the entry.

## Bounded execution and rollback

`BalancedTopLevelExecution.runWithEnvironment` is invoked exactly once for a
top-level run. Its supplied step budget is the execution-fuel boundary.

- A root balance-preflight failure is a terminal result with identity committed
  state.
- Return commits the runtime-selected state and journal.
- Revert and trap use the existing rollback rules.
- Fuel exhaustion is a nonterminal bounded result and does not fabricate a
  committed state.

Internal resumption laws remain specification evidence. This decision does not
introduce a serialized continuation or a second replay mechanism.

## Results and finite state observation

Terminal results distinguish preflight rejection, return bytes, revert bytes,
and trap reasons. Committed logs and created Addresses retain chronological
order and preserve duplicates where the runtime does.

`WorldState` is function-valued, so consumers observe exact requested points
rather than an asserted global enumeration. `WorldStateDelta` provides exact
initial and committed endpoints for account presence, storage, balance, nonce,
and checked code. These projections are views of the existing runtime state,
not an independently computed transition.

## Required proofs and executable regressions

Implementation is complete when tests and proofs cover:

- complete Core Wire conversion and codec round trips;
- every closed tag, scalar, depth, node, and collection boundary;
- frozen-host checker acceptance and rejection with detailed diagnostics;
- checked Core and Static Word contract admission;
- exact finite `WorldState` and `ExecutionEnvironment` construction;
- root installation success and every rejection class;
- ABI return, short-input revert, and unknown-selector revert;
- storage, balance, nested call, creation, logs, returndata, and exact observed
  endpoints on commit and rollback;
- preflight rejection and zero or mid-execution fuel exhaustion;
- deterministic repeated execution from equal inputs; and
- the aggregate build, tests, semantic-kernel checks, and axiom checks.

## Exclusions

This decision does not add dynamic ABI types, fallback or receive methods, ABI
events, unrestricted call depth, delegate or static calls, gas accounting, EVM
bytecode, an EVM-specific creation-address formula, or serialized resumption.
Source parsing, resolution, typing, and lowering are separate frontend stages.

Publishing the complete current Core algebra is deliberate: it permits direct
checking of arbitrary Core candidates, while execution remains restricted to
explicit admitted contract profiles.
