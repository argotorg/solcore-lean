# ADR-0145: Executable checked-Core top-level lifecycle

- Status: Accepted
- Decision date: 2026-08-30
- Scope: execute one installed checked Core contract from an explicit state
- Implementation: Complete

## Context

The internal semantics can already check Core programs, execute storage-backed
host requests with bounded fuel, retain exhaustion for resumption, and build a
canonical returned parent continuation. Those parts do not yet form one
top-level operation. In particular, callers can still supply an arbitrary
completion policy, trap rollback is not selected as a final state, and no
single total result joins terminal data to the committed or rolled-back world.

Concrete Solcore syntax may change, so this milestone must not depend on the
parser or source AST. It starts at the checked Core boundary.

## Decision

Implement one vertical top-level lifecycle. Its public inputs are:

- an explicit initial `WorldState`;
- a checked Core contract installed at one target Account;
- a direct invocation containing target, caller, call value, and input bytes;
- a bounded execution fuel budget.

Its executable result is total. It is either a resumable out-of-fuel state or a
terminal return, revert, or trap with the selected final world and an exact
state observation. Checked execution must not expose the raw machine-fault
branch.

This is one ADR and one milestone even though implementation is split into
small commits. Proof-only adapters on the ADR-0144 path are not separate
milestones.

## Checked contract entry profiles

Core currently finishes with a typed `Core.Value`; it has no dedicated return,
revert, or trap expression. The meaning of that value belongs to the checked
contract, not to an arbitrary callback supplied when it runs.

Define two initial entry profiles:

```lean
inductive CoreContractEntryProfile where
  | returnWord
  | wordOutcomeV1

def CoreContractEntryProfile.resultType :
    CoreContractEntryProfile -> Core.Ty
  | .returnWord => .word
  | .wordOutcomeV1 => .sum .word (.sum .word .word)
```

`returnWord` preserves the existing canonical convention: the completed Word
is returned as exactly 32 big-endian bytes.

`wordOutcomeV1` is a typed, syntax-independent halt convention:

```text
left word                  -> return(canonical word bytes)
right (left word)          -> revert(canonical word bytes)
right (right trapCodeWord) -> trap(trapCodeWord)
```

The contract binds checked code to exactly one profile:

```lean
structure CheckedCoreContract where
  code : CheckedHostCoreProgram
  entryProfile : CoreContractEntryProfile
  resultType_eq :
    code.program.resultType = entryProfile.resultType
```

Provide a checked factory that recognizes only these two result types. A
contract with any other result type is rejected before execution. The profile
decoder consumes a runtime typing proof. Malformed values are not silently
turned into traps; they are unreachable for checker-accepted execution.

## Installation and direct invocation

The state and the supplied contract must not become competing sources of code.
Require an installation witness:

```lean
structure InstalledCheckedCoreContract
    (initialWorld : WorldState)
    (target : Address)
    (contract : CheckedCoreContract) where
  account : Account
  account_present : initialWorld.account? target = some account
  code_present : account.code? = some contract.code
```

The direct invocation supplies:

```lean
structure TopLevelInvocation where
  target : Address
  caller : Address
  callValue : Core.Word
  inputData : HostStorageDriver.InputData
```

The runner derives all address roles for this initial direct-call profile:

```text
codeAddress    = target
currentAddress = target
storageAddress = target
callerAddress  = caller
callValue      = invocation.callValue
inputData      = invocation.inputData
```

Delegate-call and child-call address rules belong to nested invocation, not to
this profile.

## Root checkpoint

Construct the storage driver context internally. Both the checkpoint and the
working world start as the explicit `initialWorld`. Root rollback and trace
payloads are unit values until their concrete transaction forms are added:

```text
checkpoint world   = initialWorld
working world      = initialWorld
checkpoint effects = (unit, unit)
working effects    = (unit, unit)
storage address    = target
```

The installation witness supplies the required present storage Account. The
runner executes `contract.code` directly; it does not perform a second code
selection after installation has fixed the exact code.

## Total bounded result

Define one branch-complete result, indexed by the fixed initial state, contract,
and invocation:

```text
outOfFuel:
  retained storage context
  retained Core state and typing evidence

completed:
  terminal storage context
  exact Core value and Store
  decoded FrameOutcome
  selected final WorldState
  exact single-Account storage delta
```

Out of fuel is inconclusive and resumable. It is not a trap and does not have a
committed state delta. Additional fuel continues from the retained context and
Core state under the same contract and invocation inputs.

The raw driver fault constructor is eliminated using checked-state safety.
Successful completion retains the raw value and Core-local Store for auditing;
the decoded `FrameOutcome` is the contract-level meaning.

## Commit and rollback

Finalization is fixed and has no caller-supplied policy:

```text
returned -> finalWorld = terminal working WorldState
reverted -> finalWorld = initialWorld
trapped  -> finalWorld = initialWorld
```

The semantics is pure. “Commit” means selecting the terminal working state as
the result; “rollback” means selecting the immutable initial checkpoint. The
specification does not mutate the input value in place.

Return data and revert data remain distinct constructors of `FrameOutcome`.
A trap retains its explicit Word reason. All terminal branches retain the
speculative terminal context so tests and later proofs can observe that writes
occurred before rollback.

## Exact state observation

`WorldState` and Account storage are lookup functions, not enumerable finite
maps. Therefore this milestone must not claim to compute a canonical finite
list of every changed Account and slot.

Instead expose an exact single-Account storage delta for the target. It carries:

- the target Account before and after finalization;
- proofs that both Accounts are present;
- preservation of the target code;
- preservation of every non-target Account; and
- an executable `slotChange?` query returning the exact old/new Word pair when
  the selected slot differs, and `none` when it does not.

The current storage handler changes only its selected Account, so these claims
are exact. Return observes changes between the initial and terminal working
world. Revert and trap compare the initial world with itself, so every slot
query reports no committed change.

A later observation milestone may add a finite write journal or finite-map
world representation. That is required before a direct Lean API can return an
enumerable whole-world delta.

## Required laws and regressions

The proof interface must establish:

- profile recognition, uniqueness, and typed decoding for every halt branch;
- exact installed Account and code provenance;
- exact derivation of every direct-invocation input and root checkpoint field;
- checked execution cannot produce a raw machine fault;
- return selects the terminal working world;
- revert and trap select the initial world;
- code and every non-target Account are preserved;
- slot queries report exact initial/final storage values;
- fixed-input resumption agrees with one-shot execution at summed fuel; and
- completed results remain terminal under further fuel.

Executable tests must use actual checker-accepted Core programs, not injected
completion policies. At minimum they cover:

- write then dynamically return a Word;
- write then dynamically revert a Word;
- write then dynamically trap with a Word code;
- no-write return;
- pre-write and post-write exhaustion followed by successful resumption;
- return commit and nonempty target delta;
- revert/trap rollback and empty committed target delta;
- exact return/revert bytes and trap code;
- preservation of target code and a distinct Account; and
- caller, call value, input bytes, and target-derived address observations.

All public theorems require external compile consumers. Acceptance also
requires focused and full builds, the executable suite, trust-zero and
warning-as-error checks for every changed Lean root, semantic-kernel checks,
diff hygiene, axiom reports, and independent contract and
coverage audits.

## Non-goals

This ADR does not add:

- concrete syntax, parser proofs, source elaboration, or Wire changes;
- nested calls, delegate calls, a scheduler, call depth, or reentrancy;
- balance transfer, nonce policy, Account creation or deletion;
- logs or a concrete transaction event journal;
- gas prices, refunds, or consumed-gas accounting;
- Solidity ABI or storage layout;
- an enumerable whole-world delta; or
- an external serialized command or compatibility promise.

After this lifecycle is complete, nested calls, balance, creation, logs, and
ABI can connect to one executable transaction boundary in that order or in
smaller vertical slices chosen at that time.

## Implementation result

The accepted lifecycle is implemented as a pure, syntax-independent API. A
checked contract owns its completion decoder, an installation witness ties its
exact code to the initial world, and the runner constructs the root checkpoint
internally. The total result has only `completed` and `outOfFuel` branches; raw
machine faults are excluded by checked execution.

Return selects the terminal working world. Revert and trap select the original
world while retaining the speculative terminal context. Both speculative and
committed target-storage deltas remain queryable by slot, and code plus every
non-target Account are preserved.

Fuel resumption reuses one validated raw-result classifier. It is proved equal
to a one-shot run at the summed budget, including the complete dependent result
and state delta. Runtime fixtures exercise write/return, write/revert,
write/trap, pre-write and post-write exhaustion, terminal stability, and a
read-only program that observes caller, input size and byte, and all three
direct target address roles.

All 45 theorem contracts introduced by this milestone have external compile
consumers. Full build and runtime tests, trust-zero compilation, kernel-policy
checks, diff hygiene, and axiom reports pass. The only reported
Lean axioms are the repository-accepted `propext` and `Quot.sound`.

## Consequences

The semantics gains its first direct end-to-end operation from explicit state
and checked code to a total, state-resolved result. Return/revert/trap behavior
comes from the executed checked program and cannot be reinterpreted by its
caller. Parser evolution remains isolated from this work.
