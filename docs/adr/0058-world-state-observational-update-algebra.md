# ADR-0058: WorldState observational update algebra

- Status: Accepted
- Decision date: 2026-08-28
- Scope: extensional equality and update algebra for ADR-0056
- Implementation: Complete

## Context

ADR-0056 represents Account and WorldState by private semantic lookup
functions. Its public queries and single-update laws fix observable behavior,
but clients still lack named extensionality, overwrite, and independent-update
commutation laws. These are consequences of the accepted representation, not
new state semantics.

## Decision

Add no public executable operation, carrier, or instance. Publish exactly six
laws:

1. `Account.ext`: Accounts with pointwise-equal `storageValue?` are equal;
2. `WorldState.ext`: WorldStates with pointwise-equal `account?` are equal;
3. `Account.storageWrite_overwrite`: a second write to the same slot supersedes
   the first;
4. `Account.storageWrite_commute`: writes to distinct slots commute;
5. `WorldState.putAccount_overwrite`: a second put at the same address
   supersedes the first; and
6. `WorldState.putAccount_commute`: puts at distinct addresses commute.

Mark the two extensionality laws `@[ext]` and the two overwrite laws `@[simp]`.
Do not mark either commutation law `@[simp]`: their symmetric orientation has
no canonical simplification direction.

The commutation laws quantify an explicit inequality between slots or
addresses. Equality is observational and independent of the private function
field or its proof terms.

## Required tests

Add exactly two compile-time theorem-use examples, one exercising `Account.ext`
and one exercising `WorldState.ext`. Add exactly four runtime assertions:
Account overwrite, Account commutation at distinct slots, WorldState overwrite,
and WorldState commutation at distinct addresses.

Runtime tests distinguish results through existing public lookup operations.
They do not compare whole states or inspect private representation.

## Proof and validation expectations

The six laws are expected to report `[propext, Quot.sound]`; completion records
the measured result. No custom axiom or unchecked declaration is permitted.
Public executable API, carrier, and instance counts remain exactly zero.

## Staged implementation plan

Keep each commit below 300 changed lines:

1. accept this ADR and mark only this proof slice active;
2. add the exact two extensionality laws;
3. add the exact four overwrite and commutation laws;
4. add the exact two compile-time examples and four runtime assertions; and
5. independently audit and record completion evidence.

## Publication and exclusions

This proof-only slice is internal and not published. It adds no parser, source
syntax, Wire field or tag, Profile, or frozen artifact.

It fixes no trap policy, nested frame or checkpoint rule, surviving log, call,
or creation effect, Account lifecycle, transaction atomicity, state delta,
iteration or comparison order, serialization, ABI, Core-result adapter, EVM
revision, opcode, gas, or resource-limit rule.

## Consequences

Later state transitions can reason about replacement and independent updates
without unfolding private carriers. No operational slice is selected by this
decision.

## Implementation record

The proof-only slice is complete with exactly zero executable API, carrier, or
instance additions. It publishes exactly six laws: two extensionality laws in
a 31-line module and four update-algebra laws in a 66-line module, with one
umbrella import for each. Exactly two compile-time theorem-use examples and
four runtime assertions live in a 76-line test module with two runner lines.

Both extensionality laws carry `@[ext]`. Only the two overwrite laws carry
`@[simp]`; the two commutation laws remain outside the simp set. All six laws
report exactly `[propext, Quot.sound]`. There is no `Classical.choice`, custom
axiom, `sorryAx`, or unchecked declaration.

The implementation commits are `a3bfd88` (123 changed lines), `7ae4bb0` (32),
`64590b0` (67), and `05e5f5d` (78). Each is below 300 changed lines. Focused and
full builds, tests, trust-zero, semantic-kernel, metadata, forbidden-declaration,
document-link, diff, and independent audits pass.
