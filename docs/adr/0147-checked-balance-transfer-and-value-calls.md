# ADR-0147: Checked balance transfer and value-bearing calls

- Status: Accepted
- Decision date: 2026-08-30
- Scope: add non-wrapping balances to the executable checked-Core lifecycle
- Implementation: In progress

## Context

ADR-0146 completes a depth-one checked-Core scheduler. It can run a root
contract, suspend it for a checked child, commit child returns, roll child
revert or trap back to the call site, and finally commit or roll back the whole
root invocation. Calls currently carry no value: the child always observes a
zero `callValue`, and `WorldState` has no account balance.

The next vertical slice must make value transfer part of that same lifecycle.
It must not introduce wrapping arithmetic, implicit account creation, a hidden
child fuel budget, or a second transaction boundary. Existing checked Core
programs and host capability indexes must remain valid.

Concrete Solcore syntax remains outside this milestone. The boundary starts
from an explicit `WorldState`, an installed checked root contract, a checked
contract registry, and a direct invocation.

## Decision

Add an exact unsigned 256-bit balance to each present `Account`. Add a checked,
atomic transfer operation, then connect it to both direct invocation value and
a new value-bearing nested-call capability.

The existing zero-value execution APIs remain available for compatibility.
The canonical balance-aware runner performs transfer preflight once and then
uses the sealed shared-fuel scheduler. A successful root return commits the
transfer and all later effects. Root revert or trap restores the original
world. Out-of-fuel retains the already prepared state and never repeats a
debit or credit during resumption.

## Account and world model

Every explicitly present account owns:

- sparse Word storage;
- optional checker-accepted Core code; and
- one `Core.Word` balance.

`Account.empty` has zero balance. Replacing code or writing storage preserves
the balance. Replacing a balance preserves code and every storage lookup.

The public world operations distinguish absence from a present zero-balance
account:

```text
balance? absentAddress       = none
balance? presentZeroAccount  = some 0
```

Balance writes do not create accounts. Account and contract creation remain a
later milestone with their own policy.

## Checked atomic transfer

`WorldState.transferBalance` receives a sender, recipient, and Word amount. It
returns either a new immutable world or one explicit failure:

```text
senderAbsent
recipientAbsent
insufficientBalance
recipientOverflow
```

Arithmetic is mathematical, not modular:

- debit succeeds only when `amount <= senderBalance`;
- credit succeeds only when `recipientBalance + amount < 2^256`;
- underflow and overflow never wrap;
- no failure returns a partially updated world.

A zero transfer between present accounts is exact identity. A self-transfer
still checks that the account holds the requested amount; when sufficient it
is exact identity and does not run a separate credit overflow check.

The generic transfer primitive requires both accounts to be present, including
for zero. The direct balance-aware runner preserves legacy zero-value behavior
by skipping transfer entirely when top-level `callValue` is zero. Consequently
an explicitly absent external caller can still invoke an installed root with
zero value.

Successful cross-account transfer preserves both accounts' storage and code,
preserves every unrelated account, and conserves the two balances as natural
numbers. Installation evidence for any checked contract can therefore be
transported from the input world to the successful output world.

## Append-only value-call capability

Keep `callContractWord` unchanged at host index 10. Append:

```text
callContractWordWithValue : Word × (Word × Word) ->
  Word + (Word + (Word + Word))
```

The parameter order is target, value, input. Its result reuses the existing
typed `ContractCallWordResult` branches:

```text
returned Word
reverted Word
trapped Word
failed Word
```

All earlier host indexes and types remain unchanged. The existing call remains
the canonical zero-value operation, so old checked programs do not need to be
rewritten.

The stable dispatch failure codes extend without changing codes 0 through 2:

```text
0 invalid target address
1 unavailable checked target
2 depth limit exceeded
3 insufficient balance
4 recipient balance overflow
```

Missing accounts or code discovered while resolving the checked target remain
`unavailable`; account creation is not attempted.

## Nested value-call lifecycle

A root value call is processed in this order:

1. strictly convert the requested target Word to an Address;
2. resolve its checked contract against the current pre-call working world;
3. atomically transfer from the parent's current Address to that target;
4. transport the checked installation into the post-transfer world;
5. start the child with the post-transfer world as its working state.

The child invocation has:

```text
target         = requested checked target
caller         = parent's currentAddress
callValue      = requested value
inputData      = exact 32-byte big-endian input Word
codeAddress    = target
currentAddress = target
storageAddress = target
```

Resolution precedes transfer so invalid or unavailable calls remain exact
no-ops. Insufficient funds or recipient overflow also returns a typed `failed`
response without starting child code.

The suspended parent retains its pre-transfer context as the call checkpoint.
The child runs over the post-transfer world. On completion:

```text
child return -> retain transfer and child effects
child revert -> restore pre-transfer call checkpoint
child trap   -> restore pre-transfer call checkpoint
```

For cross-account calls, the parent's cached Account is refreshed from the
post-transfer world because its balance was debited. Self-calls also use the
current Account witness. A child attempting either nested-call capability
receives the same depth-limit failure and performs no transfer.

## Top-level value lifecycle

The balance-aware root boundary receives the original installed root contract
and invocation. Zero value starts from the original world. Nonzero value first
transfers from `invocation.caller` to `invocation.target`.

On preflight failure, Core does not start. The total result reports the exact
failure, the original final world, and an identity committed delta.

On success, the root context has two distinct endpoints:

```text
checkpoint world = original explicit WorldState
working world    = post-transfer WorldState
```

The root observes the requested `callValue`. A returned root commits its
working world. A reverted or trapped root restores the original checkpoint,
including the top-level value transfer.

Transfer preflight does not consume a Core transition. It is performed once
before the sealed scheduler result is created. A zero-fuel result therefore
retains the post-transfer root state, and later resumption does not transfer a
second time.

## Result and resumption boundary

Balance-aware results use a private constructor and a public observation view.
The view distinguishes preflight rejection from the sealed ADR-0146 execution
result. Callers cannot manufacture a completed result, replace the registry of
an out-of-fuel result, or supply an unrelated prepared frame.

Rejected results are stable under additional fuel. Successful runs reuse the
shared root/child budget and satisfy the same split law:

```text
resume (runBalanced fuel) additional =
  runBalanced (fuel + additional)
```

The equality includes the transfer endpoints and proves that preflight, child
start, updates, and parent response delivery are not replayed.

## Balance delta

Extend the exact arbitrary-address `WorldStateDelta` with:

```text
balanceEndpoints address
balanceChange? address
```

Optional endpoints preserve the difference between absence and present zero.
Working deltas expose speculative transfers. Returned roots expose committed
transfers. Child rollback, root rollback, and preflight rejection expose the
appropriate identity committed endpoints.

## Acceptance boundary

The implementation is complete when executable checked-program regressions and
proof consumers cover:

- underflow, overflow, zero, self, and cross-account transfer;
- storage/code preservation, unrelated accounts, and balance conservation;
- append-only host layout and exact typed result injection;
- child observation of the requested `callValue`;
- child return commit and child revert/trap transfer rollback;
- successful child followed by root revert/trap global rollback;
- top-level rejection without executing Core;
- root, child, and post-child out-of-fuel resumption without double transfer;
- arbitrary root, child, and untouched balance-delta queries; and
- coherence of the legacy zero-value call with ADR-0146.

Full build and executable tests, warning-as-error, trust-zero checks, metadata,
semantic-kernel policy, diff hygiene, and independent acceptance audit must
pass.

## Non-goals and following milestones

This ADR does not add account or contract creation, nonce policy, deletion,
logs, ABI encoding, general byte-array calls, recursive depth, balance-reading
host capabilities, gas pricing, Surface syntax, parser proofs, or a public
Oracle schema.

After this slice, implementation proceeds to creation, logs, ABI, and the
public Oracle. Parser-related proofs remain paused until Solcore syntax
stabilizes.

## Consequences

Value transfer becomes an executable part of the same transaction lifecycle as
checked contract execution. Rollback and fuel resumption cover balances rather
than treating them as an external precondition. The append-only host boundary
keeps all existing checked Core programs compatible, and account creation stays
separate instead of being hidden inside a transfer failure branch.
