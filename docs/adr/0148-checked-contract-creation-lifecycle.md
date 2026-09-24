# ADR-0148: Checked contract creation lifecycle

- Status: Accepted
- Decision date: 2026-08-30
- Scope: create and initialize checked contracts inside the executable lifecycle
- Implementation: Complete

## Context

ADR-0147 supplies explicit accounts, checked value transfer, transaction and
call checkpoints, shared fuel, sealed resumption, and arbitrary-address delta
queries. It still cannot create an account, run initializer code, or install a
new checked runtime contract. Creation must use that lifecycle: exhaustion is
resumable, initializer failure has a defined rollback point, and root failure
still restores the transaction's original world.

The repository does not yet define a revision-pinned CREATE address algorithm
or a public execution schema. Freezing an arbitrary arithmetic substitute for
Keccak and RLP would make that placeholder part of the language. This decision
therefore makes address derivation an explicit run-fixed semantic input.

## Decision

Add a depth-one checked creation operation to the existing root scheduler. A
root may request creation and may continue after the initializer finishes. The
initializer occupies the scheduler's one child slot, so calls and creations
requested by the initializer receive the existing depth-limit failure.

The operation receives a checked creation template, derives a fresh address
from the creator and its old nonce, prepares a provisional account, transfers
the requested value, and runs checked initializer code. Normal initializer
return installs the template's checked runtime code. Revert or trap removes the
provisional account and its effects while retaining the nonce consumed by an
initializer that actually started.

All behavior remains syntax independent. Inputs are checked Core programs,
explicit world state, and an explicit execution environment.

## Scope

This milestone adds non-wrapping Account nonces, explicit policy-relative
address derivation, checked initializer/runtime templates, a typed root host
capability, shared-fuel initializer execution, call-site and transaction
rollback, sealed resumption, and queryable creation-state endpoints.

## Non-goals

This milestone does not define:

- concrete Solcore creation syntax or parser behavior;
- a canonical Keccak/RLP, CREATE2, salt, or EVM-revision address algorithm;
- recursive call depth or initializer-created grandchildren;
- destructors, committed-account deletion, gas, warmth, refunds, or logs;
- ABI encoding, constructor arguments, storage layout, or ordered traces; or
- an external serialized request or enumerable state-diff schema.

Those choices remain separate milestones.

## Account nonce

Every present Account owns one `Core.Word` nonce. `Account.empty` has nonce
zero. Storage writes, balance replacement, and code replacement preserve the
nonce. Nonce replacement preserves storage, code, and balance.

World lookup distinguishes `none` for an absent account from `some 0` for a
present zero-nonce account.

Increment is mathematical and checked. It succeeds only when `nonce + 1` is
strictly below `2^256`; it never wraps from the maximum Word to zero. A nonce
overflow rejects creation before initializer code starts.

## Explicit address policy

Creation receives a run-fixed `CreationAddressPolicy` whose total operation is
`derive : Address -> Word -> Address`.

The arguments are the creator Address and its nonce before increment. Retaining
the policy across exhaustion makes execution pure, total, and deterministic
without prematurely selecting a public chain-specific algorithm.

The derived Address must be absent in the current working world. Collision is
an explicit failure; creation never replaces an existing Account. A later
public execution profile must pin a concrete derivation policy or provide an
equally explicit finite representation.

## Checked creation templates

A `CheckedCreationTemplate` contains two checker-accepted contracts:

- the initializer contract executed during creation; and
- the runtime contract installed after normal initializer return.

A creation-template registry resolves the request's Word template identifier.
The normal checked-contract registry must already contain the exact runtime
contract at the derived Address. Preflight verifies that registration before
starting the initializer.

Pre-registration keeps the environment immutable. After creation, a later call
in the same root can combine that entry with the installed world code. No
resumable result mutates or replaces its registry.

## Fixed execution environment

One `ExecutionEnvironment` fixes the checked-contract registry, creation
template registry, and address policy for the whole run.

The environment is retained by every out-of-fuel result. Compatibility runners
construct a calls-only environment from the existing checked-contract registry
and an empty creation registry. Programs that use only the pre-existing call
and storage capabilities therefore keep their behavior. The newly introduced
creation host capability is deliberately disabled at this boundary: every root
creation request fails as `unavailable` (stable code 1). The earlier flat
handler's depth-limit response was an integration scaffold, not a compatibility
contract for the new host capability.

## Append-only host capability

Keep host indexes 0 through 11 unchanged. Append at index 12:

```text
createContractWord : Word x (Word x Word) ->
  Word + (Word + (Word + Word))
```

Parameters are template identifier, transferred value, and initializer input.
The reused `ContractCallWordResult` reports a created Address, revert data, trap
reason, or preflight/depth failure respectively.

The canonical host table length becomes 13 while all older indexes retain
their meaning.

## Preflight and initializer start

A root creation request performs these checks and transformations in order:

1. resolve the checked creation template;
2. read the creator Account and its old nonce;
3. derive the candidate Address from the fixed policy and old nonce;
4. verify that nonce increment does not overflow;
5. verify that the candidate Address is absent;
6. verify exact runtime pre-registration at that Address;
7. verify that the creator can transfer the requested value;
8. create the post-nonce parent world;
9. insert a provisional zero-nonce Account carrying initializer code;
10. transfer value into that provisional Account; and
11. start the initializer with the resulting world.

A failure in steps 1 through 7 returns a typed failure response, leaves the
parent context exactly unchanged, and does not start Core initializer code.
The provisional transformations do not escape unless all preflight checks
succeed.

The initializer observes the created Address as storage, current, and code
Address; the creator as caller; the requested value; and the exact big-endian
bytes of the input Word.

The provisional initializer code is an internal working-state device used to
reuse checked installation and storage-context invariants. It is never present
in a committed successful result.

## Completion and rollback

Once initializer execution starts, the incremented creator nonce represents a
consumed creation attempt.

Normal return preserves the transferred balance and initializer storage,
replaces initializer code with runtime code without changing the new Account's
nonce, storage, or balance, and resumes the root with the created Address.

Revert or trap selects the post-nonce parent world. This removes the provisional
Account, refunds its value, discards initialization effects, and resumes the
root with the exact revert data or trap reason.

Thus preflight rejection consumes no nonce, while an initializer that starts
consumes exactly one nonce even when it reverts or traps. A later successful
root return commits that call-site decision.

The root transaction checkpoint remains the original explicit WorldState. If
the root later reverts or traps, every creation effect, including a consumed
nonce, runtime installation, balance movement, and initializer storage, rolls
back to that original world.

## Shared fuel, resumption, and sealing

Creation receives no private initializer budget. Root execution, preparation,
initializer execution, completion delivery, and later root execution use the
same scheduler fuel. Out-of-fuel retains the exact active root or initializer,
working worlds, fixed execution environment, and reachability evidence.

Resumption supplies only additional fuel. It does not repeat template lookup,
address derivation, nonce increment, provisional insertion, or value transfer.
The one-shot and split-fuel executions must be equal.

Result constructors and resumable scheduler provenance remain sealed. Public
views may inspect completion or exhaustion, but callers cannot manufacture a
completed creation, substitute an environment, or attach an unrelated world to
a retained machine state.

Initializer mode is defined in `OneLevelNestedExecutionMode`, separate from the
base state carriers, to keep the creation-state import graph acyclic. Semantic
names, high-level run APIs, and the `Solcore.Semantics` umbrella remain stable.
Direct imports of the internal `OneLevelNestedExecutionState` module are not a
published compatibility boundary; internal users that need active scheduler
modes import `OneLevelNestedExecutionMode`.

## Failures and stable codes

Creation preserves the existing call failure codes and appends new ones:

```text
0 invalid target address
1 unavailable checked contract or creation template
2 depth limit exceeded
3 insufficient balance
4 recipient balance overflow
5 creation nonce overflow
6 creation address collision
```

Codes 0 through 4 keep their existing meanings. A missing template, missing
creator, or runtime registration mismatch maps to unavailable. Credit overflow
cannot occur for a fresh zero-balance Account receiving one Word value, but code
4 remains reserved and unchanged for value calls.

## State delta

Extend `WorldStateDelta` with exact queryable nonce and code endpoints, a nonce
change query, and a created-account query that distinguishes initial absence
from a present empty Account. Existing account, storage, and balance queries
remain unchanged.

WorldState is function-valued, so this milestone does not claim to enumerate
all changed addresses. The returned created Address and fixed derivation inputs
identify the new Account for exact delta queries. Enumerable transaction-wide
creation observations are now supplied by the rollback-aware transaction
journal completed in
[ADR-0149](0149-rollback-aware-logs-and-transaction-observations.md).

## Acceptance boundary

Implementation is complete when proofs and executable checked-program tests
cover:

- nonce zero, successful increment, maximum overflow, and payload preservation;
- exact old-nonce address derivation and fixed-policy determinism;
- template absence, runtime mismatch, insufficient funds, overflow, and
  collision as no-start identity failures;
- fresh-account insertion without overwriting any unrelated Account;
- initializer observation of caller, value, input, and all three Addresses;
- return-time runtime installation with initializer storage and balance kept;
- initializer revert/trap rollback with value refund and nonce retention;
- successful creation followed by root revert/trap global rollback;
- a later same-root call resolving and executing the deployed runtime;
- root, pre-initializer, initializer, and post-initializer exhaustion;
- exact split-fuel equality without double derivation, increment, or transfer;
- creator, created, and untouched account/nonce/code/storage/balance deltas;
- stable host indexes, result injection, and depth failure;
- private result construction and fixed-environment reachability sealing; and
- full build, runtime suite, trust-zero, kernel-policy, and axiom
  audits for the new semantic roots.

The executable lifecycle now covers these acceptance cases with checked Core
programs and proof consumers. Initializer return installs the checked runtime;
initializer revert and trap restore the call-site state while retaining the
consumed nonce; a later root revert or trap restores the original world.
Creation exhaustion resumes under the same fixed environment and agrees with a
one-shot run, including creation followed by a same-root runtime call.

The full 836-job build, 1,556-job test build, and runtime suite pass. All 80
changed Lean roots pass warnings-as-errors and trust-zero validation.
Semantic-kernel and diff checks pass. Axiom reports contain only `propext`,
`Quot.sound`, and, for some execution and resumption proofs,
`Classical.choice`; there is no `sorry`, `admit`, or `unsafe` declaration.
