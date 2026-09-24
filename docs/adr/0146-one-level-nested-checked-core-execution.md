# ADR-0146: One-level nested checked-Core execution

- Status: Accepted
- Decision date: 2026-08-30
- Scope: execute depth-one checked-contract calls inside the top-level lifecycle
- Implementation: Complete

## Context

ADR-0145 executes one installed checked Core contract from an explicit
`WorldState`. It owns the root checkpoint, commits only a returned result,
rolls revert and trap back to that checkpoint, retains out-of-fuel for exact
resumption, and exposes a total terminal result.

That runner still treats every host request synchronously. A nested contract
call cannot be implemented as an ordinary total handler callback: the child
may exhaust the remaining budget, and out-of-fuel is an inconclusive resumable
state rather than a call failure. Giving the child a separate hidden budget or
mapping its exhaustion to a response would break ADR-0145's fuel meaning.

Nested execution can also change an Account other than the direct root target.
The single-target `TopLevelStorageDelta` is therefore not a complete observation
of a nested run. The nested boundary needs an address-generic query without
claiming that function-valued worlds can be enumerated.

Concrete syntax remains intentionally outside this milestone. The operation
starts from checked Core contracts and an explicit initial world.

## Decision

Add one depth-one nested checked-Core execution milestone above ADR-0145. A
root contract may issue any number of sequential child calls. Each child is a
leaf: a call request made by that child receives an explicit depth-limit
failure and does not start a grandchild.

The public runner receives:

- the explicit root `WorldState`, checked root contract, installation witness,
  and direct invocation from ADR-0145;
- a checked-contract registry used to resolve child targets; and
- one shared natural-number fuel budget.

Its result is total: either the root has completed with a selected final world,
or an exact root-or-child scheduler configuration is retained for resumption.
Checked execution exposes no raw machine-fault branch.

## Implemented result

The completed implementation provides one typed Word-call capability, resolves
checked child code against the current working world, and runs the root and its
active child under one shared fuel budget. Exhaustion retains the exact active
machine and its registry for later resumption. A `Reachable` seal records that
the retained mode came from an installed root through scheduler transitions,
so callers cannot manufacture a resumable frame or swap registries.

Child return rebases the parent's speculative working world; child revert and
trap restore the call checkpoint. The later root result still owns the
transaction decision: root return commits all accumulated changes, while root
revert or trap restores the original world. Terminal results expose exact
state-delta queries for any Address and storage slot.

## Typed call capability

Extend the append-only Core host capability list with a final capability:

```text
callContractWord : Word × Word ->
  Word + (Word + (Word + Word))
```

The request arguments are a target word and one input word. Its indexed host
response is a semantic sum, not an untyped status/data pair:

```text
left returnWord
right (left revertWord)
right (right (left trapReason))
right (right (right dispatchFailureReason))
```

Use a dedicated `ContractCallWordResult` carrier with `returned`, `reverted`,
`trapped`, and `failed` constructors, together with a total injection into the
fixed Core sum type. Existing host capability indices remain unchanged.

`failed` is only a pre-execution dispatch result, or the response to a child
attempting to exceed depth one. In particular, child revert and trap retain
their own constructors, and child out-of-fuel is never converted to `failed`.

Decode child completion directly from the typed Core result and the child's
`CoreContractEntryProfile`. The decoder returns the exact Word disposition.
It must not round-trip through return bytes, truncate data, or use a fallback
value for an impossible shape.

## Dynamic checked-contract resolution

Define a registry whose lookup returns only `CheckedCoreContract` values. At
each root call request:

1. narrow the target Word with the strict `wordToAddress?` bridge;
2. query the registry at that Address;
3. query the current root working world, not the transaction's initial world;
4. require a present Account whose installed code is exactly the registered
   contract's checked code; and
5. retain the resulting `InstalledCheckedCoreContract` witness in child mode.

An out-of-range target, missing registry entry, missing Account, missing code,
or code mismatch produces a distinct internal dispatch-failure reason and
leaves the current working world unchanged. These reason codes are internal
semantic values, not a public Wire or serialization commitment.

For this Word-call profile, derive the child invocation as follows:

```text
target         = strictly narrowed requested target
caller         = parent's currentAddress
callValue      = 0
inputData      = exactly 32-byte big-endian encoding of the input Word
codeAddress    = target
currentAddress = target
storageAddress = target
```

Value transfer and general byte-array call data are later milestones.

## Shared-fuel two-mode scheduler

Do not run a child atomically inside `HostHandler.handle`. Introduce an
explicit scheduler with two active modes:

```text
runningRoot:
  root storage context + root Core state

runningChild:
  suspended root call request and continuation
  parent context at the call checkpoint
  resolved checked child contract and installation witness
  child storage context + child Core state
```

One budget is threaded through both modes. Every ordinary Core transition and
every host-request boundary consumes fuel according to the existing
`Core.hostRun` convention, whether it belongs to the root or child. Starting a
child and delivering its completed typed response are administrative mode
changes and do not create a hidden second budget. Termination uses the shared
fuel together with a finite administrative-mode rank where necessary.

If fuel expires in root mode, retain the exact root context and state. If it
expires in child mode, retain the exact child context and state plus the
suspended parent continuation and call checkpoint. Resumption continues that
exact active mode. It must not rerun target resolution, restart the child,
repeat a preceding host update, or deliver the parent response twice.

Each retained result also carries the registry used by the run and a
`Reachable` proof generated from the installed root and the scheduler's own
transitions. Resumption therefore cannot accept an unrelated registry or an
arbitrarily assembled root or child frame.

ADR-0148 strengthens this retained capability boundary to the complete fixed
`ExecutionEnvironment`. Call resolution still uses its `callRegistry`
projection, while exhaustion also retains the creation-template registry and
address policy. Resumption accepts no replacement environment.

The implementation proves the split-budget law against a one-shot scheduler
run:

```text
resumeWithFuel (run fuel initialConfiguration) additional =
  run (fuel + additional) initialConfiguration
```

This equality covers root exhaustion, child exhaustion, child completion and
parent resumption, and every root terminal branch. Completed results remain
terminal under additional fuel.

## Child checkpoint and parent rebase

The child's initial world is the root working world at its call site. This is
the child checkpoint. Child finalization is fixed:

```text
child return -> select child terminal working world
child revert -> select child call checkpoint
child trap   -> select child call checkpoint
```

After child finalization, inject the exact typed call result into the suspended
root continuation. Rebuild the root storage context over the selected child
world while preserving the root checkpoint and effect components. If the call
target equals the root storage Address, refresh the cached root storage
Account from the selected world; this is required for self-call coherence.
For a different target, prove that the cached root Account is unchanged.

A returned child world becomes only the root's new speculative working world.
It is not yet a transaction commit. When the root later completes:

```text
root return -> commit the accumulated root-and-child working world
root revert -> restore the original ADR-0145 root checkpoint
root trap   -> restore the original ADR-0145 root checkpoint
```

Thus a successful child write is visible to the resumed root, while a later
root revert or trap rolls it back together with every earlier root write.

## Global queryable state delta

Add an exact delta indexed by arbitrary initial and final `WorldState` values.
It exposes, for every Address and slot:

- the exact initial and final Account lookup endpoints;
- the exact initial and final `readStorage?` endpoints; and
- `slotChange? address slot`, returning the old/new optional Words exactly
  when those endpoints differ and `none` when they agree.

Using optional Word endpoints preserves the difference between an absent
Account and a present Account whose slot reads as zero. The terminal nested
result carries this delta from the explicit root initial world to its selected
final world. Root revert and trap therefore have an identity committed delta.

The function-valued world representation still cannot enumerate all changed
Addresses or slots. No finite change list, completeness claim about such a
list, or public serialization is introduced.

## Implemented laws and regressions

The proof interface establishes:

- append-only host capability indices and exact request/response typing;
- total, injective classification of the four nested response dispositions;
- typed child Word decoding for every supported entry profile;
- dynamic resolution against the exact call-site working world and code;
- exact derivation of child caller, input, value, and all address roles;
- exact shared-fuel accounting across both scheduler modes;
- retention and exact resumption of child out-of-fuel;
- at-most-once child start, host update, and parent response delivery;
- child-return propagation and child-revert/trap call-checkpoint rollback;
- correct parent storage-context rebasing, including a self-call;
- root return commit and root revert/trap rollback to the original world;
- absence of raw faults for every checked root and resolved checked child; and
- exact arbitrary-address/slot delta query laws.

Executable tests use actual checker-accepted root and child programs. They
cover:

- child return after a storage write, observed by the resumed root;
- child revert and trap after a write, with no child state committed;
- a child return followed by root revert and by root trap;
- out-of-fuel before dispatch, during child execution, and after returning to
  the root, followed by exact resumption and one-shot equality;
- two sequential child calls under the same shared budget;
- self-call rebasing and a call to a different Account;
- invalid target, missing registry/Account/code, and code mismatch failures;
- a child call attempt receiving the depth-one failure without a grandchild;
- exact returned, reverted, trapped, and failed Core sum branches; and
- global slot queries for the root target, child target, untouched Address,
  and identity rollback.

The public theorems have external compile consumers. Focused and full builds,
the executable suite, trust-zero and warning-as-error checks, semantic-kernel
checks, diff hygiene, axiom reports, and independent contract
and coverage audits complete the acceptance boundary.

## Non-goals and following milestones

This ADR does not add:

- recursive depth greater than one, delegate call, static call, or reentrancy;
- nonzero call value, balance checks or transfer;
- Account creation, contract creation, deletion, or nonce policy;
- logs or a concrete event journal;
- general byte-array calldata, Solidity ABI, or storage layout;
- gas prices, refunds, or consumed-gas reporting;
- an enumerable whole-world diff;
- source syntax, grammar, parser proofs, or elaboration; or
- a Wire tag, schema, external serialized command, or compatibility promise.

The next implementation is balance semantics: checked balance availability and
transfer for value-bearing calls. Creation, logs, and ABI follow as later
vertical slices. Parser-related proofs remain paused until the Solcore syntax
direction stabilizes.

## Consequences

Nested calls become part of one total, fuel-resumable transaction lifecycle
without weakening the meaning of exhaustion. A single budget measures actual
Core work across the root and active child, call-local rollback composes with
root rollback, and terminal state changes can be queried at any Address and
slot. The depth-one limit keeps this milestone finite while establishing the
scheduler and checkpoint structure needed by later recursive execution.
