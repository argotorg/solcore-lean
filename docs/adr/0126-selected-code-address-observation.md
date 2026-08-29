# ADR-0126: Selected code-address observation

- Status: Accepted
- Decision date: 2026-08-29
- Scope: expose the existing code selector to host-aware Core execution
- Implementation: Not started

## Context

Address-selected execution already receives a `codeAddress` and uses it to
look up checked code in the working WorldState. The same execution separately
retains a `storageAddress` for working-storage access. ADR-0121 lets Core
observe the storage selector, but Core cannot observe the Address that selected
its code.

Unlike a new caller, current-contract, call-value, calldata, or call-kind
input, the code selector already has an exact producer and lifetime. It is an
argument of the selected entry point, it determines the checked program being
run, and it is fixed for that run. Existing regressions deliberately use
different code and storage Addresses.

The next safe input observation is therefore the existing code selector. It
does not require inventing a caller identity, a call frame, or an input carrier
whose ownership rules are not yet defined.

## Decision

Append one internal host capability named `codeAddress`, with exact type
`unit -> word` at index 3. Calling it returns the Address used as the run's code
selector, widened losslessly to a Core Word.

The name means only "the Address supplied to select this checked code". It is
not defined as a current contract, `self`, callee, caller, owner, authority, or
storage target. In particular, it remains independent of `storageAddress`.

The operation takes Unit because Core host functions use unary application.
No nullary Core form is introduced.

## Exact Core contract

Extend the append-only host capability universe:

```lean
inductive HostFunction where
  | storageRead
  | storageWrite
  | storageAddress
  | codeAddress

HostFunction.storageRead.index = 0
HostFunction.storageWrite.index = 1
HostFunction.storageAddress.index = 2
HostFunction.codeAddress.index = 3
```

`codeAddress` has parameter type `.unit` and result type `.word`. The fixed
host context and runtime environment append the new function without moving
the first three entries; both lengths become 4.

Extend the first-order request protocol:

```lean
inductive HostRequest where
  | storageRead (slot : Word)
  | storageWrite (slot value : Word)
  | storageAddress
  | codeAddress

HostRequest.Response .codeAddress = Word
HostRequest.responseType .codeAddress = .word
HostRequest.responseValue .codeAddress response = .word response
```

Applying `.codeAddress` to Unit emits exactly the corresponding request. Any
other runtime argument produces the existing `invalidHostArgument` fault.
Checked host programs cannot reach that fault. Resumption injects the Word and
preserves the saved CEK continuation and Core-local store exactly.

## Static execution parameter

Parameterize the combined handler by the code selector:

```lean
def HostStorageDriver.handleRequest
    (codeAddress : Address)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (request : Core.HostRequest) :
    HostStorageDriver.Context RollbackState TraceState × request.Response

def HostStorageDriver.handler
    (codeAddress : Address) :
    HostHandler (HostStorageDriver.Context RollbackState TraceState)
```

The new branch is exact:

```lean
HostStorageDriver.handleRequest codeAddress context .codeAddress =
  (context, addressToWord codeAddress)
```

The code selector is a static parameter of one driver run, not mutable
working storage. It is deliberately not copied into the storage context. This
avoids duplicating the selector and then needing an invariant saying the
stored copy agrees with the Address used for code lookup.

The specialized low-level operations consequently receive the selector:

```lean
HostStorageDriver.run context codeAddress fuel state
code.runWithStorage context codeAddress fuel
```

`HostStorageDriver.HandledSteps` and `HostStorageDriver.FuelSound` are indexed
by the same selector. Exact execution evidence therefore cannot silently
switch the response Address while replaying a run.

The address-selected public entry point keeps its existing shape:

```lean
context.runCodeWithStorage? codeAddress fuel
```

Internally, that one `codeAddress` is used both for the working-WorldState code
lookup and for `code.runWithStorage context codeAddress fuel`. Thus selected
code and the observable code selector agree by construction. ADR-0124 and
ADR-0125 retain their existing high-level argument and nested-option shapes.

## Handler behavior

The storage read, storage write, and storage-address branches retain their
existing meanings. The added static parameter is ignored by those branches.
The code-address branch:

- leaves the complete storage handler context unchanged;
- performs no WorldState lookup or update;
- returns `addressToWord codeAddress` exactly;
- preserves the saved continuation and Core-local store; and
- strictly narrows back through `wordToAddress?` to the same Address.

The lossless widening is the existing ADR-0053 bridge. No truncation,
normalization, or new representation is added.

## Fuel behavior

The existing host-runner accounting applies:

1. evaluating Unit uses ordinary Core transitions;
2. emitting the code-address request consumes one Core fuel unit;
3. handling and resuming consume no additional Core fuel; and
4. execution continues with exactly the remaining fuel reported by Core.

The minimal observation is request-ready out of fuel at budget 4 and completes
at budget 5. Completed and raw-fault results remain exact with more fuel.
Out-of-fuel remains budget-relative and receives no stability law.

## Required proof interface

Core must expose and verify:

- exact parameter, result, index, table lookup, and table-length laws;
- exact application, emission, suspension, invalid-argument, response, and
  resume laws;
- executable/declarative request correspondence and determinism;
- response and suspension typing, typed progress, preservation, and no-fault;
- unchanged generic runner soundness, completeness, and terminal stability;
  and
- frozen Wire v1 and v2 rejection of the internal host-function value.

Semantics must expose and verify:

- the exact context-preserving handler equation;
- the exact widened response and strict recovery of `codeAddress`;
- continuation and Core-local store preservation;
- request resumption with exact remaining fuel;
- storage selector, checkpoint, working-effect, code, and non-selected Account
  preservation under the parameterized handler;
- code-address-indexed fuel soundness, completeness, and terminal stability;
- selected execution using one Address for lookup and observation; and
- unchanged selected no-fault and optional-branch results.

## Required regressions

Add focused tests for:

- fixed host indices 0 through 3 and all four table entries;
- host-check acceptance and closed-check rejection of `unit -> word` code
  observation;
- static rejection and raw-machine faulting for a non-Unit argument;
- exact emission, Word resumption, continuation, and local-store reuse;
- direct frozen Wire v1 and v2 rejection;
- exact handler response and lossless narrowing;
- request-ready exhaustion at fuel 4 and completion at fuel 5;
- a selected fixture with `codeAddress != storageAddress` returning the code
  selector and explicitly not the storage selector;
- exact completed value, local Store, and storage context at a larger budget;
- a compile consumer of the parameterized fuel specification and stability;
  and
- all existing storage, continuation, and parent-indexed regressions.

## Compatibility and dependency boundary

This is an append-only extension of the unpublished Core host protocol. The
first three capability positions and their behavior do not move. Exhaustive
internal matches on `HostFunction` and `HostRequest` must add one branch, and
low-level storage-driver calls must supply a code selector.

Core owns only the typed `unit -> word` capability and request protocol; it
imports no Address or WorldState meaning. Semantics owns the Address response
and the invariant that the selected entry point uses one selector for lookup
and execution.

No parser, Surface, ABI, Oracle, schema, profile, gas, or public runtime module
changes. Frozen Wire projections continue to reject every host function. The
root README does not change.

## Non-goals

This ADR does not define a current contract, `self`, callee, caller, origin,
owner, authority, Account presence at the code selector, or equality with the
storage selector.

It adds no caller address, call value, calldata, call kind, balance, nonce,
transfer, external call, creation, recursion, reentrancy, stack, depth,
scheduler, transaction, commit, rollback, ABI, gas, refund, log, or EVM
revision policy.

The selector does not grant storage authority or prove that the code Account
remains present after arbitrary future mutations. It is fixed only for the
specific handled run parameterized by it.

## Implementation sequence

Keep each green commit below roughly 300 changed lines:

1. record and activate this exact selector observation;
2. append the Core capability, request, machine, and safety branches;
3. parameterize the storage handler and driver, preserving existing behavior;
4. lift fuel soundness, completeness, and stability through the selector;
5. update selected execution and continuation proofs without changing their
   high-level optional shapes;
6. add Core, handler, selected runtime, and compile-only regressions; and
7. run full validation and independent audit, then synchronize acceptance
   evidence and current-facing internal documents.

## Consequences

Host-aware Core code can now distinguish the Address selecting its checked
code from the separately retained working-storage selector. The selected entry
point makes that observation coherent with actual code lookup by construction.

This still does not define a complete call frame. The next input role must be
selected only after its producer, lifetime, and relationship to parent and
child execution are specified.
