# ADR-0056: Minimal world-state identity and storage values

- Status: Accepted
- Decision date: 2026-08-28
- Scope: first explicit world-state carrier slice
- Implementation: In progress

## Context

The completed runtime foundation provides canonical addresses, words, frame
halt outcomes, and coherent scalar representations. It still has no explicit
world state. The local cell store in Semantic Core belongs to one Core
execution and does not represent persistent accounts or storage.

[ADR-0008](0008-observation-and-evm-revision.md) requires future contract
execution to receive explicit initial state, but its rollback, calls, balances,
logs, and revision-sensitive behavior are not yet decided. This slice therefore
introduces only account identity, explicit account absence, and word-valued
storage. It does not pretend to be a transaction or execution model.

## Decision

Add exactly two public carriers:

```text
Account
WorldState
```

Their representation is private. Both use finite extensional maps backed by
`Std.ExtTreeMap`, so observable equality is independent of insertion order.
Account storage maps `Core.Word` keys to a private nonzero-Word subtype. A zero
storage entry is therefore unrepresentable. WorldState maps `Address` to
Account and preserves absence explicitly as `none`.

An empty Account is different from an absent Account. Writing zero deletes only
the selected storage entry and leaves the Account present. Writing storage at
an absent address fails; it never creates an Account implicitly. `putAccount`
is the only operation in this slice that can make an absent address present;
`writeStorage?` only replaces an Account already present at that address.

Add exactly eight named public executable definitions:

```text
Account.empty
Account.storageValue?
Account.storageRead
Account.storageWrite
WorldState.empty
WorldState.account?
WorldState.putAccount
WorldState.writeStorage?
```

`storageValue?` exposes entry presence. `storageRead` returns `Core.Word.zero`
when a key is absent. `storageWrite` erases the key for zero and inserts the
nonzero value otherwise. `writeStorage?` returns `none` for an absent Account;
for a present Account it returns an updated WorldState containing the updated
Account.

There is intentionally no WorldState-level read from an absent Account. A
caller must first use `account?`, preserving the distinction between absence
and a present empty Account.

## Required proof interface

Publish exactly twelve focused laws:

1. `WorldState.account?_empty` returns `none`.
2. `WorldState.account?_putAccount_same` returns the inserted Account.
3. `WorldState.account?_putAccount_other` preserves every different address.
4. `Account.storageValue?_empty` returns `none`.
5. `Account.storageRead_empty` returns `Core.Word.zero`.
6. `Account.storageRead_storageWrite_same` returns the written value, including
   zero.
7. `Account.storageValue?_storageWrite_zero` returns `none`, proving canonical
   deletion.
8. `Account.storageValue?_storageWrite_nonzero` returns `some value` when
   `value ≠ Core.Word.zero`.
9. `Account.storageRead_storageWrite_other` preserves every different key.
10. `WorldState.writeStorage?_of_absent` returns `none` when `account?` does.
11. `WorldState.account?_writeStorage?_same` proves that a successful write
    returns the same Account identity with exactly `Account.storageWrite`
    applied.
12. `WorldState.account?_writeStorage?_other` proves that a successful write
    preserves every different address.

Private map and nonzero-subtype helpers do not add to the twelve-law public
interface. The implementation uses no custom axioms or unchecked declarations;
standard Lean dependencies are audited and recorded.

## Required tests

Provide exactly twelve executable runtime assertions, corresponding to the
twelve public laws:

1. empty world lookup is absent;
2. putting an Account makes that address present;
3. putting one address preserves another;
4. empty Account storage has no entry;
5. empty Account storage reads as zero;
6. reading a written nonzero value returns it;
7. writing zero removes entry presence;
8. writing a nonzero value creates entry presence;
9. writing one key preserves another key;
10. storage write at an absent address fails;
11. storage write at a present address updates that Account and keeps it
    present; and
12. storage write at one address preserves another Account.

Fixtures use distinct addresses and storage keys. Tests query the public
operations directly and do not depend on private map iteration or ordering.

## Staged implementation plan

Keep every commit below 300 changed lines and leave the tree green:

1. accept this ADR and mark the state-carrier slice active in documentation;
2. add the two carriers and exact eight executable definitions;
3. add the exact twelve focused laws;
4. add the exact twelve executable runtime assertions; and
5. independently audit the slice and update completion documentation.

## Publication and exclusions

This slice adds no rollback, checkpoint, transaction, frame context, ABI,
contract entry, Core-result adapter, trap taxonomy, balance, nonce, code,
codehash, log, external call, or contract creation rule. It chooses no EVM
revision, gas schedule, host behavior, or resource-limit meaning.

It adds no storage layout, source key derivation, address derivation, Account
deletion, automatic empty-Account pruning, or read rule for a nonexistent
Account. It exposes no map iteration, insertion order, comparison order,
serialization, canonical state delta, or observation schema.

It adds no source form, Core type or expression, Wire tag, JSON schema,
profile, Oracle query, verdict, protocol field, or published observation.
Frozen public formats and metadata remain unchanged.

## Consequences

Later transition rules can receive and return an explicit finite WorldState
without hidden host mutation. Account absence, missing storage, and zero-value
deletion are fixed independently of transaction rollback, calls, ABI behavior,
and serialization.
