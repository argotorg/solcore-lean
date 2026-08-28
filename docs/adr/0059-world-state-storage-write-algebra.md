# ADR-0059: WorldState storage-write algebra

- Status: Accepted
- Decision date: 2026-08-28
- Scope: proof-only sequential algebra for `WorldState.writeStorage?`
- Implementation: Complete

## Context

ADR-0056 fixes conditional storage writes: a present Account is updated, while
an absent Account produces `none`. ADR-0058 proves the underlying Account and
WorldState overwrite and commutation algebra. Their consequences for the
partial WorldState-level operation are not yet available as named laws.

This slice derives those consequences without choosing an execution, rollback,
or trap policy.

## Decision

Add no public executable API, carrier, or instance. Add exactly one private
helper to package the existing successful-write shape. Publish exactly these
four laws:

```lean
@[simp] theorem WorldState.writeStorage?_overwrite
    (state : WorldState) (address : Address)
    (slot first second : Core.Word) :
    (state.writeStorage? address slot first).bind
        (fun next => next.writeStorage? address slot second) =
      state.writeStorage? address slot second

theorem WorldState.writeStorage?_commute_slots
    (state : WorldState) (address : Address)
    (leftSlot leftValue rightSlot rightValue : Core.Word)
    (different : leftSlot ≠ rightSlot) :
    (state.writeStorage? address leftSlot leftValue).bind
        (fun next => next.writeStorage? address rightSlot rightValue) =
      (state.writeStorage? address rightSlot rightValue).bind
        (fun next => next.writeStorage? address leftSlot leftValue)

theorem WorldState.writeStorage?_commute_addresses
    (state : WorldState)
    (leftAddress rightAddress : Address)
    (leftSlot leftValue rightSlot rightValue : Core.Word)
    (different : leftAddress ≠ rightAddress) :
    (state.writeStorage? leftAddress leftSlot leftValue).bind
        (fun next =>
          next.writeStorage? rightAddress rightSlot rightValue) =
      (state.writeStorage? rightAddress rightSlot rightValue).bind
        (fun next =>
          next.writeStorage? leftAddress leftSlot leftValue)

theorem WorldState.writeStorage?_zero_deletes
    (state : WorldState) (address : Address)
    (account : Account) (slot : Core.Word)
    (present : state.account? address = some account) :
    ∃ next,
      state.writeStorage? address slot Core.Word.zero = some next ∧
      next.account? address =
        some (account.storageWrite slot Core.Word.zero) ∧
      (account.storageWrite slot Core.Word.zero).storageValue? slot = none
```

The first law makes a repeated write use the final value. The next two laws
exchange independent slot or address updates. The last law records successful
zero deletion without deleting the Account itself.

The overwrite law alone is a simp rule. Both commutation laws remain non-simp
because exchanging symmetric update orders has no canonical rewrite direction.
No `putAccount` same-address or other-address theorem is added to the public
interface.

The `none` produced by `writeStorage?` continues to mean only that its addressed
Account was absent. This proof layer does not reinterpret it as halt, trap,
revert, rollback, deletion, or inconclusive execution.

## Required tests

Add exactly four runtime assertions:

1. overwrite at a present Account and the absent-Account `none` boundary;
2. distinct-slot commutation;
3. distinct-address commutation, including an absent-address case; and
4. zero deletion, checking Account presence, selected-slot absence, read-zero,
   and preservation of another slot.

Tests use only public state construction and lookup operations. They do not
invoke the proof laws or compare whole private carriers.

## Proof and validation expectations

Completion measures the axiom sets. The first three laws are expected to report
`[propext, Quot.sound]`; the zero-deletion law is expected to report
`[propext]`. No custom axiom, `Classical.choice`, `sorryAx`, or unchecked
declaration is permitted.

## Staged implementation plan

Keep every commit below 300 changed lines:

1. accept this ADR and mark only this proof slice active;
2. add the one private helper and the overwrite and slot-commutation laws;
3. add address commutation and zero deletion;
4. add the exact four runtime assertions; and
5. independently audit and record completion evidence.

## Publication and exclusions

This layer is internal and not published. It adds no parser, source form, Wire
field or tag, Profile, Oracle behavior, or frozen artifact.

It fixes no trap disposition, nested frame or checkpoint rule, surviving logs,
calls, or creations, transaction atomicity, Account creation, deletion, or
other lifecycle rule, state delta, iteration or comparison order,
serialization, ABI, Core-result adapter, EVM revision, opcode, gas schedule, or
resource-limit rule.

## Consequences

Future transitions can compose conditional storage writes without unfolding
their implementation. No new operational slice or semantic decision follows
from these derived laws.

## Implementation record

The proof-only slice is complete with exactly zero public executable API,
carrier, or instance additions. One private helper supports exactly four public
laws in a 189-line properties module with one umbrella import. Only overwrite
is `@[simp]`; both commutation laws and zero deletion remain non-simp.

The overwrite and two commutation laws report exactly
`[propext, Quot.sound]`. Zero deletion reports exactly `[propext]`. There is no
`Classical.choice`, custom axiom, `sorryAx`, or unchecked declaration. Exactly
four runtime assertions live in a 94-line definition-only test module with two
runner lines.

The implementation commits are `c09942c` (166 changed lines), `0fa26af` (80),
`104d3aa` (110), and `bb63ed1` (96). Each remains below 300 changed lines.
Focused and full builds, tests, trust-zero, semantic-kernel, metadata,
forbidden-declaration, document-link, diff, and independent audits pass.
