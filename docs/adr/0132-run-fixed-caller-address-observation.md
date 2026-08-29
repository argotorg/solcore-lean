# ADR-0132: Run-fixed caller-address observation

- Status: Accepted
- Decision date: 2026-08-29
- Scope: expose one explicitly supplied run-fixed Address to internal Core code
- Implementation: Not started

## Context

ADR-0131 places the selected code Address and one invocation-value Word in a
single immutable `HostStorageDriver.ExecutionInputs`. The same input is passed
through request handling, recursive driving, fuel evidence, selected code
execution, completion, and parent-indexed continuation construction. Mutable
working storage remains a separate handler context.

Core can already observe the retained storage selector, selected code selector,
and invocation-value Word. The next roadmap family permits another contract
entry input only when it has an identified Core consumer and an exact lifetime.
A caller-address observation has both if its meaning is deliberately limited to
one Address explicitly placed in `ExecutionInputs` for one handled run.

The repository still has no active parent machine, call stack, call kind,
nested invocation transition, authenticated sender, or transaction origin.
Consequently, no existing value can derive or validate this Address. In
particular, a parent-indexed continuation relates checkpoints and traces to a
parent working state; it does not contain an executing parent's Address.

## Decision

Append one field to the existing immutable carrier:

```lean
namespace Solcore.Semantics.HostStorageDriver

structure ExecutionInputs where
  codeAddress : Address
  callValue : Core.Word
  callerAddress : Address

end Solcore.Semantics.HostStorageDriver
```

For a run parameterized by `inputs`, `inputs.callerAddress` means exactly the
Address supplied in that field by the API constructing the run. It remains
fixed because every recursive driver call receives the same complete `inputs`.
The semantics supplies no evidence about where the Address came from, who
selected it, or whether any runtime entity controls it.

Do not add a default, optional value, zero compatibility path, fallback field,
or constructor that infers this Address from another role. Every construction
of `ExecutionInputs` must state it explicitly.

## Address-role separation

The four current inputs and selectors keep distinct meanings:

| Value | Owner | Exact operational use |
| --- | --- | --- |
| storage address | mutable storage context | selects the Account used by storage reads and writes |
| `inputs.codeAddress` | immutable execution input | selects checked code and answers `codeAddress` |
| `inputs.callValue` | immutable execution input | answers `callValue` as an uninterpreted Word |
| `inputs.callerAddress` | immutable execution input | answers `callerAddress` after lossless widening |

No inequality or equality is required between the three Addresses. The caller
Address may be zero, may name no WorldState Account, and may equal either
selector. None of those cases changes its meaning or causes lookup failure.

Adding this field does not rename `codeAddress` or the storage selector as a
callee, current contract, `self`, or active frame Address. It also creates no
relationship between `callerAddress` and `callValue`.

## Core host capability

Append one internal capability after the five existing entries:

```lean
inductive HostFunction where
  | storageRead
  | storageWrite
  | storageAddress
  | codeAddress
  | callValue
  | callerAddress
```

`HostFunction.callerAddress` has parameter type Unit, result type Word, and
stable index 5. Existing indexes 0 through 4 do not move. `hostContext` and
`hostEnvironment` append its function type and runtime value, so both have
length 6.

Append the matching request:

```lean
inductive HostRequest where
  | storageRead (slot : Word)
  | storageWrite (slot value : Word)
  | storageAddress
  | codeAddress
  | callValue
  | callerAddress
```

`HostRequest.callerAddress.Response` is Word. Its response type is Core Word,
and injecting a response produces `.word response`. Applying the capability to
Unit emits exactly this request. Any other argument produces the existing
`invalidHostArgument` fault. Resumption injects the exact Word while preserving
the saved continuation and Core-local Store.

Core owns only the typed capability and first-order request. It does not import
Address, WorldState, frames, the storage handler, or caller provenance.

## Handler and driver meaning

Semantics interprets the request using the existing strict Address bridge:

```lean
handleRequest inputs context .callerAddress =
  (context, addressToWord inputs.callerAddress)
```

The request is read-only. It performs no Account or code lookup and leaves the
complete mutable storage context unchanged. Strict narrowing of the response
must recover `some inputs.callerAddress`.

`handler`, `handleSuspension`, `HostStorageDriver.run`, and every fuel-indexed
relation continue to receive the same whole `ExecutionInputs`. Selected code
lookup remains solely `code? inputs.codeAddress`. The selected-execution,
completion, and parent-continuation operations pass the same input unchanged
without adding caller information to their result carriers.

## Parent and nested-invocation boundary

This ADR does not derive `callerAddress` from `parentWorking`,
`ParentIndexedFrameInitialization`, a checkpoint, a trace, or a completed
parent-indexed continuation. Those values establish state/effect relationships,
not an executing parent identity.

A future nested-invocation operation may construct a child's `ExecutionInputs`
and impose a caller relationship appropriate to its separately accepted call
kind. That future theorem is neither assumed nor approximated here. Until such
an operation exists, `callerAddress` remains only the explicit run input above.

## Exact proof obligations

Expose focused exact laws for:

- all `ExecutionInputs` constructor projections, including `callerAddress`;
- capability parameter type, result type, and append-only index 5;
- host-context and host-environment lookup and length 6;
- request response type, response value, and exact suspension resumption;
- begin application, Unit request emission, and invalid-argument behavior;
- executable/declarative transition and emission correspondence;
- typed request emission, response typing, preservation, and no-fault safety;
- exact handler response and unchanged mutable context;
- exact resumed control, continuation, and Core-local Store;
- strict recovery through `wordToAddress?`;
- recursive driver handling with the same complete input and remaining fuel;
- driver type safety, completeness, fuel soundness, and terminal stability;
- selected failure and success continuing to depend on `inputs.codeAddress`;
- unchanged storage-absence, code-absence, out-of-fuel, and completion layers;
  and
- unchanged parent-context coherence and completed larger-fuel stability.

No theorem may identify the caller Address with a parent, code selector,
storage selector, Account owner, signer, authority, transaction origin, or
entity that supplied `callValue`.

## Required regressions

Low-level Core tests must cover:

- fixed indexes 0 through 5, both table lookups, and table length 6;
- the first unbound host-capability index at 6;
- host-check acceptance of `callerAddress Unit` and closed-check rejection;
- static rejection and exact raw fault for a non-Unit argument;
- exact request emission, response injection, continuation, and Store reuse;
- request-ready exhaustion at measured fuel 4 and completion at fuel 5; and
- direct rejection of `.hostFunction .callerAddress` by Wire v1 and v2.

End-to-end regressions must:

- use distinct nonzero storage, code, and caller Addresses plus a numerically
  distinct call-value Word, so projection swaps are observable;
- return the exact widened caller Address at fuel 5 and the identical completed
  result and context with larger fuel;
- succeed when the caller Address has no WorldState Account;
- vary only `callerAddress` while retaining the same code selector, storage
  selector, and call value, and observe only the caller-dependent result change;
- observe the caller Address, write that exact Word to working storage, observe
  it again, and obtain the same Word twice around the mutation;
- carry a caller-derived result through the existing three optional
  parent-continuation boundaries and consume it through ADR-0129's fold; and
- retain all existing storage-address, code-address, call-value, safety, fuel,
  and larger-budget regressions.

The measured resource boundary, not an assumed index-independent cost, is the
acceptance result. If the implementation changes the 4/5 boundary, the ADR must
be revisited rather than silently changing the expected test.

## Dependency and publication boundary

Semantics owns `callerAddress : Address`, lossless Address-to-Word widening,
strict recovery, and request interpretation. Core sees only a Unit-to-Word
internal capability. Generic HostDriver and continuation layers remain
parameterized and must not import Address-specific meaning.

Frozen Core Wire v1 and v2 continue to reject every host-function value. Add no
Wire tag, Oracle command, external runtime request, schema, profile, metadata
capability, ABI rule, Surface form, parser rule, or source elaboration in this
slice. The root README does not change. Publication requires a separate ADR.

## Non-goals

This ADR does not define or prove:

- an authenticated sender, signer, owner, beneficiary, authority, or access
  control decision;
- an immediate parent caller, active parent frame, transaction origin, EOA,
  contract identity, or provenance chain;
- current contract, `self`, callee, target, delegate, library, or equality
  between any Address roles;
- caller Account presence, code presence, balance, nonce, storage, liveness, or
  control of a private key;
- balance debit or credit, value transfer, affordability, denomination,
  conservation, refund, payability, or a relationship to `callValue`;
- nested invocation, call stack, call depth, recursion, reentrancy, scheduling,
  external calls, creation, callbacks, or parent resumption;
- call kind, static-call restriction, delegate-call behavior, fallback,
  constructor, receive, or dispatch policy;
- calldata, return-data decoding, ABI, selector, storage layout, or source
  declaration meaning;
- checkpoint capture time, Account lifetime, rollback application, commit,
  transaction finalization, or persistence;
- gas, fork rules, diagnostics, tracing provenance, events, or logs; or
- a public representation, compatibility promise, parser change, or Oracle
  behavior.

## Implementation sequence

Keep each green commit at roughly 300 changed lines or fewer:

1. record and activate this exact weak contract;
2. append the input field and projection law, then migrate explicit record
   constructions without a default;
3. append the Core capability and request, add the handler branch, and close
   machine, correspondence, progress, typing, preservation, runner,
   request-exhaustive, and no-fault cases;
4. add exact suspension laws, strict recovery, and the driver
   request-resumption law;
5. repair custom test handlers and compile consumers;
6. add focused Core admission, fault, layout, fuel, and Wire regressions;
7. add direct selected-execution, absent-caller-Account, role-separation, and
   larger-fuel regressions;
8. add observe-write-observe, parent-continuation, and fold regressions;
9. run trust, axiom, dependency, build, test, metadata, kernel, compatibility,
   and independent audits; and
10. synchronize completion evidence in current-facing internal documents.

Temporary migration names must be removed before completion. No transitional
API may infer `callerAddress` from another field or manufacture a default.

## Consequences

Internal checked Core code can observe one exact run-fixed caller-address Word
without giving that Address identity provenance, authority, Account existence,
or parent-frame meaning. Storage mutation cannot change the observation because
the value lives in the immutable execution input.

Defining an actual nested caller relationship remains a future lifecycle
decision. The explicit field can later be populated by such a transition, but
this ADR neither constrains nor anticipates that transition's call-kind rules.
