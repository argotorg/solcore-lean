# ADR-0126: Selected code-address observation

- Status: Accepted
- Decision date: 2026-08-29
- Scope: expose the existing code selector to host-aware Core execution
- Implementation: Complete

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

The low-level `runWithStorage` accepts a caller-supplied selector and makes no
WorldState lookup claim. Lookup provenance is guaranteed only by the
address-selected `runCodeWithStorage?` composition below.

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
at budget 5. The specialized storage interface preserves completed results
with more fuel; generic `HostDriver` metatheory separately preserves raw
faults. Out-of-fuel remains budget-relative and receives no stability law.

## Required proof interface

Core must expose and verify:

- exact parameter, result, index, table lookup, and table-length laws;
- exact application, emission, suspension, invalid-argument, response, and
  resume laws;
- executable/declarative request correspondence and determinism;
- response and suspension typing, typed progress, preservation, and no-fault;
- unchanged generic runner soundness, completeness, and terminal stability.

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

No parser, source syntax, ABI, gas, or public runtime module changes. The root
README does not change.

## Non-goals

This ADR does not define a current contract, `self`, callee, caller, origin,
owner, authority, or equality with the storage selector. The observation adds
no retained Account-presence evidence beyond the existing selected lookup.

It adds no caller address, call value, calldata, call kind, balance, nonce,
transfer, external call, creation, recursion, reentrancy, stack, depth,
scheduler, transaction, commit, rollback, ABI, gas, refund, log, or EVM
revision policy.

The selector does not grant storage authority or prove that the code Account
remains present after arbitrary future mutations. It is fixed only for the
specific handled run parameterized by it.

## Implemented sequence

The work was completed in this order:

1. recorded and activated the exact selector observation;
2. parameterized the storage handler and driver while preserving behavior;
3. appended the Core capability, request, machine, and safety branches;
4. lifted fuel soundness, completeness, and stability through the selector;
5. updated selected execution and continuation proofs without changing their
   high-level optional shapes;
6. added Core, handler, selected runtime, and compile-only regressions; and
7. ran full validation and independent audit, then synchronized acceptance
   evidence and current-facing internal documents.

## Implementation record

The combined storage runner now receives one explicit code selector. The
address-selected entry point passes the same value to both checked-code lookup
and the handler, while its public argument and nested optional result shapes
remain unchanged.

Core appends `codeAddress` as capability index 3 and as a first-order host
request. Its Unit argument, Word response, suspension, resumption, progress,
preservation, and checked no-fault path use the same machinery as the existing
host capabilities.

Semantics returns `addressToWord codeAddress` without changing the handler
context. Public laws expose the exact resumed control, continuation, local
store, strict Address recovery, remaining fuel, fuel specification, and
completed-result stability.

Focused regressions separate code address `0x10` from storage address `0x20`.
They stop exactly before the request at fuel 4, complete at fuel 5, reject the
storage selector as the result, and retain the same completed context, value,
and local store at fuel 32.

## Acceptance evidence

- the full build completed 627 jobs;
- the complete test suite completed 1,142 jobs and all runtime checks passed;
- all changed Lean modules compiled with trust zero and warnings as errors;
- the semantic-kernel policy check passed;
- the public selector laws use only the repository's permitted logical
  foundations; and
- independent implementation and regression audits found no correctness gap.

The parser, source syntax, ABI, public formats, and root README did not
change. Implementation was split into small green commits; the one larger
cross-layer signature migration changed every caller atomically so no
temporary default selector entered the semantics.

## Consequences

Host-aware Core code can now distinguish the Address selecting its checked
code from the separately retained working-storage selector. The selected entry
point makes that observation coherent with actual code lookup by construction.

This still does not define a complete call frame. The next input role must be
selected only after its producer, lifetime, and relationship to parent and
child execution are specified.
