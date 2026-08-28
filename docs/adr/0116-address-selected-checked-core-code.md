# ADR-0116: Address-selected checked Core code

- Status: Accepted
- Decision date: 2026-08-29
- Scope: checked code association, address selection, and pure Core execution
- Implementation: Planned

## Context

ADR-0056 made `Account` and `WorldState` the explicit rollback-visible runtime
state, but deliberately limited an Account to sparse storage. ADR-0099 through
ADR-0115 then completed the storage path from parent-indexed initialization to
proven-present total reads and writes. More storage wrappers would no longer
advance executable contract semantics.

The next missing input has a concrete consumer. `Core.Program.runStateful`
already executes a closed Core program from an empty lexical environment and
empty Core-local store. The checker already proves when such a program is
well-typed, and the safety layer proves that checked execution cannot produce
a machine fault. What is missing is rollback-visible association of that code,
selection by an Address, and one honest execution operation.

The current Core is still pure with respect to `WorldState`: it cannot read
calldata, caller, value, or contract storage. It also returns `Core.Value`, not
contract return bytes. This slice must not disguise either limitation.

## Decision

Treat `Core.Program` as the contract Core that will gain explicit effects in
later, separate slices. Do not introduce a second contract-body IR now. Store
only programs accepted by the existing checker:

```lean
structure CheckedCoreProgram where
  program : Core.Program
  checked : program.check = true

namespace CheckedCoreProgram

def ofProgram? (program : Core.Program) : Option CheckedCoreProgram

def runStateful
    (code : CheckedCoreProgram)
    (fuel : Nat) : Core.StatefulRunResult

end CheckedCoreProgram
```

`ofProgram?` is the executable admission boundary. It returns `some` with the
exact checker equation when `program.check = true`, and `none` otherwise.
`runStateful` delegates to the retained program. It preserves the Core-local
final store because erasing that store would make the first contract consumer
less informative than the existing Core API.

Extend `Account` with a private optional `CheckedCoreProgram`. `Account.empty`
has no code. Add exactly these Account operations:

```lean
def Account.code? (account : Account) : Option CheckedCoreProgram

def Account.withCode
    (account : Account)
    (code : CheckedCoreProgram) : Account
```

`withCode` replaces code while preserving sparse storage. `storageWrite`
preserves code. Code belongs to the Account rather than a parallel registry so
ordinary `WorldState` checkpointing and rollback also cover code identity.

Add address-selected lookup and execution:

```lean
def WorldState.code?
    (state : WorldState)
    (codeAddress : Address) : Option CheckedCoreProgram

def WorldState.runCode?
    (state : WorldState)
    (codeAddress : Address)
    (fuel : Nat) : Option Core.StatefulRunResult
```

`code?` binds `account?` to `Account.code?`. `runCode?` maps the selected code
to `CheckedCoreProgram.runStateful`. The argument is named `codeAddress`; this
is its complete role. It is not implicitly the existing `storageAddress`, a
callee identity, an authorization principal, or a frame field.

## Required proof interface

The checked-code layer publishes direct accepted/rejected constructor laws, an
existential sufficient-fuel completion threshold, and a no-machine-fault
theorem for every fuel value. These delegate to existing checked Core safety;
`outOfFuel` remains possible when a run is below the threshold.

The Account layer publishes observations sufficient to prevent hidden state
loss:

- `Account.code?_empty` returns `none`;
- `Account.code?_withCode` returns the exact checked code;
- `Account.storageValue?_withCode` preserves every slot;
- `Account.code?_storageWrite` preserves the optional code.

`Account.ext` must now require both storage observation equality and code
observation equality. The old storage-only theorem becomes false once code is
part of Account identity and must not survive under another name. Existing
storage-write algebra proofs must supply code preservation explicitly.

The WorldState layer publishes explicit absent/no-code/present selection laws
and matching execution laws. A present code law reduces `runCode?` to the exact
retained checked program run. A checked selected run cannot be a machine fault.
No theorem converts `outOfFuel` to a semantic trap or claims sufficient fuel
was supplied by a caller.

Every new declaration must pass trust-zero checking. Exact axiom reports are
limited to `[propext]` or `[propext, Quot.sound]` inherited from existing proof
and finite-word infrastructure.
Simp rules are limited to constructor or explicitly selected lookup branches
whose right side removes the new operation. No broad execution simp rule may
hide address selection.

## Required regressions

Add focused runtime checks for:

- admission of a valid closed program and rejection of an invalid one;
- an empty Account and a present Account with no code;
- exact address selection in a two-Account WorldState;
- execution to the expected `Core.StatefulRunResult`;
- preservation of selected code across a storage write;
- fuel exhaustion remaining `Core.StatefulRunResult.outOfFuel`.

Add compile-only regressions that name the constructor laws, storage/code
preservation, address selection, exact execution, and selected-run no-fault
theorem directly. They must not prove those goals solely by unfolding or broad
simplification.

## Dependency boundary

Keep checked code construction independent of contract state. Its definition
module imports only the Core checker layer; its execution module imports the
Core machine. Safety properties import the existing Core safety layer.

`WorldState.lean` may depend on the checked-code carrier but not on the Core
machine or safety proof. Address-selected execution belongs in a later module
that imports both `WorldState` and checked-code execution. This prevents every
state-only consumer from acquiring an execution dependency.

Place the new semantic modules after the current WorldState storage foundation
and before frame-specific refinements. Keep public Wire schemas, Oracle paths,
and the frozen frontend dependency graph unchanged.

## What this slice does not decide

This is selected pure Core execution, not a complete contract-frame evaluator.
It does not expose WorldState to Core evaluation, commit the Core-local store to
contract storage, or produce `FrameRunResult` or `FrameOutcome`.

There is no conversion from `Core.Value` to `Bytes`; no return, revert, trap,
fallback, receive, constructor, or ABI rule; and no policy that treats
`outOfFuel` as a contract result. There is no caller, callee, calldata,
transferred value, call kind, balance, nonce, creation, self-destruction, log,
external call, scheduling, reentrancy, gas, transaction, or publication rule.

Future Core effects must be added through explicit syntax-independent
operations and re-prove checking, execution correspondence, and safety. If a
future requirement proves that `Core.Program` cannot carry those effects, a
new ADR may replace the stored code type; this decision does not freeze a
published representation.

## Staged implementation plan

Keep every commit below 300 changed lines:

1. accept this ADR and update targeted internal status documents;
2. add checked-code admission and execution definitions with focused laws;
3. extend Account and migrate extensionality/storage algebra;
4. add address-selected WorldState code lookup and execution;
5. add safety and preservation properties;
6. add focused runtime and compile regressions;
7. run independent audit and record completion evidence.

## Publication and consequences

This slice is internal. It gives one Address a real code-selection role and
connects rollback-visible Account state to an executable checked Core consumer
without pretending that pure Core execution is already contract execution.
