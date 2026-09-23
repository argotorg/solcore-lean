# Semantic Core implementation policy

This document records the sequencing and completion policy for Semantic Core,
checked-contract execution, ABI support, and reproducible Core synthesis. For
implemented coverage, see [Current status](CURRENT_STATUS.md).

## Objective and boundary

Semantic Core is the small, syntax-independent executable language between
source compilation and effectful contract execution. It owns local values and
stores, typing, evaluation, checking, machines, primitives, and safety. It does
not own source parsing, inference, world-state accounts, transaction rollback,
or ABI encoding.

The surrounding retained boundaries are:

```text
Frontend elaboration --> checked Core --> ContractRuntime
                              ^                 ^
                              |                 |
                          Synthesis            Abi
```

Every arrow is an explicit typed adapter.

## Core language policy

A Core feature is complete only when the affected obligations are addressed:

1. data and syntax representation;
2. declarative typing and evaluation;
3. executable inference/checking and evaluation;
4. deterministic diagnostic behavior;
5. machine execution where applicable;
6. correspondence, progress, and preservation at the changed boundary;
7. fuel and resumption behavior; and
8. explicit representation or rejection in each retained wire encoding.

Core values and stores remain separate from source heaps and contract world
state. New source concepts enter Core only through an explicit lowering with a
stated proof boundary.

## Retained wire encodings

Core Wire v1, v2, and v3 are closed representations. Their modules may decode,
encode, or project only the constructors assigned to that version. Adding an
internal Core constructor must not change the meaning of existing encoded
values.

- [ADR-0010](adr/0010-m1b-core-wire-v1.md) records the v1 boundary.
- [Core Wire v3](CORE_WIRE_V3.md) catalogs the current encoding.
- [ADR-0151](adr/0151-versioned-checked-core-execution.md) records how checked
  Core v3 enters the retained execution stack.

Strict decoding should reject missing or unknown fields, invalid tags,
noncanonical scalar encodings, duplicate keys, and configured resource-limit
violations deterministically.

## Primitive policy

Primitive operations must define:

- operand and result types;
- left-to-right evaluation order;
- exact Word-width behavior;
- exceptional cases such as zero divisors or oversized shifts;
- executable and declarative agreement; and
- machine and renaming support.

Dedicated modules own coherent families such as arithmetic, division,
remainder, shifts, sign extension, byte selection, modular operations,
bitwise logic, conversions, and comparisons.

## Checked-contract execution policy

`Solcore.ContractRuntime` accepts only admitted checked programs. Its inputs
make the finite world, code registry, creation templates, call environment,
invocation, and resource bounds explicit.

Each runtime feature must state:

- its preflight conditions;
- which state belongs to the transaction checkpoint and working view;
- which child effects are committed or rolled back;
- the order of logs and created addresses;
- the fuel charged before and after host transitions; and
- the typed observation returned for every modeled outcome.

A top-level return commits the modeled working state. Revert, trap, and
specified preflight failures select the corresponding checkpoint. Nested-call
and creation failures resolve local state before returning to their parent.

Contract execution is not an EVM model. EVM gas, fees, blocks, bytecode,
memory, and fork equivalence require separate future definitions.

## ABI policy

ABI support lives under `Solcore.Abi`. A callable boundary is admitted only
when its metadata, signature, decoding, and encoding obligations are explicit.
The current implementation covers Keccak-256 and the modeled static-word
boundary; general dynamic/composite ABI support remains outside the completed
scope.

## Synthesis policy

[ADR-0152](adr/0152-reproducible-checked-core-case-synthesis.md) governs the
pure Core v3 generator and shrinker. Reproducibility requires an explicit seed,
versioned fragment assumptions, deterministic generation, checker-sealed
output, and a returned final seed state.

A shrink candidate must:

- remain inside the declared fragment;
- preserve binder scope;
- pass the Core checker; and
- be strictly smaller under the documented measure.

Expansion beyond Word/Boolean terms should proceed one feature family at a
time: functions and recursion, algebraic data, cells, then host effects. Each
step needs generation coverage, shrinking invariants, and regression seeds.

## Work order

For a vertical Core/runtime increment:

1. settle the declarative rule and observable edge cases;
2. implement the checker/evaluator path;
3. establish machine and safety results;
4. update retained encoding isolation;
5. add contract-runtime or ABI adapters only when required;
6. extend synthesis only after the checker boundary is stable; and
7. update status, feature, and compatibility documentation.

## Exit conditions

A change may be marked complete when:

- all changed Lean modules build with warnings as errors;
- focused and full tests pass;
- repository-data and kernel-policy checks pass;
- retained encodings either represent or reject the form explicitly;
- resource and rollback behavior are tested at their boundaries; and
- open proof or interoperability work is named without broadening the claim.
