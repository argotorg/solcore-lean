# ADR-0266: Extending worlds at actual computation checkpoints

- Status: Accepted for implementation
- Decision date: 2026-09-10
- Scope: Preserve the supplied store world through genuine saved states

## Context and evidence

The canonical reference remains argotorg/solcore-rs at
`18fd9f75d290df0070e21ee56e0a5691f232596f`. This is a proof-only extension;
no syntax, lowering, executable entry or Rust correspondence changes.
ADR-0263 proves safe actual computation checkpoints using Core.StateHasType,
whose store world is existential. It does not expose an extension of the
original supplied world at a saved checkpoint. ADR-0264 and ADR-0265 separately
provide executable construction and same-world input premises.

Core.StoreHasTypes fixes the world uniquely from every actual stored value's
type and the exact world/store length. The Core transition relation changes
stores only at applyNewCell and applyStoreCell. Existing state preservation
already maintains all actual controls, captured values and pending frames.
Allocation extends a world by the allocated payload type; a typed write keeps
all locations' types while permitting actual values to change.

## Decision

Add one public shared frontend theorem,
ComputationReturnTreeElaborates.runtime_checkpoint_world_extension, in one
small module. Use the same childCoreType, original elaboration, actual runtime
environment/store and typed pending-continuation premises as ADR-0263's state
kernel, together with an actual runStateful outOfFuel equation.

The conclusion exposes a saved world extending the original supplied world,
with StoreHasTypes for the literal checkpoint store. It also states that every
finite Core.Steps path starting at that exact checkpoint has a store typed in
a further extension of that saved world. Actual resumed outOfFuel equations
supply such paths through the existing runner soundness theorem. The extension
is not merely an existential unrelated world or a store-length inequality.

Do not add a public state-at-world relation, record, runner, validator, helper
family or per-profile theorem. Keep the original checkpoint safety theorem and
all earlier contracts unchanged; callers may consume its no-fault and state
typing conclusions separately. No source-ID alignment, fragment membership,
child execution/cost law, source-only bound or independently chosen checkpoint
is required. Pending frames and actual stores are not reconstructed or erased.

## Private proof structure

First show that StoreHasTypes determines the world as the actual store's type
list. Use this to identify a StateHasType witness world with the supplied world.
For a typed single transition, all store-preserving cases retain that world.
Only allocation and write invert the existing typed frame/value and reuse
StoreHasTypes.allocate or StoreHasTypes.write. For arbitrary private nominal
definitions, rebase allowed payload structural evidence to the store's existing
empty-definition contract exactly as existing Core safety does.

Compose these extensions along actual Steps while reusing the existing
transition_preserves_state_type theorem. Recover the genuine initial-to-saved
path from runStateful_outOfFuel_sound and then reuse the same private Steps
result for every subsequent path. Do not duplicate the full Core preservation
proof or alter any executable definition.

## Consumers and verification

Check original parsed effectful bodies and actual pending continuations, with
multiple allocations separated by genuine checkpoints, typed writes that alter
values without changing cell types, retained references and nested captures.
Use independent preparation/elaboration and literal Core paths before applying
the new theorem. Check all sampled fuels and genuine resumed states as well as
symbolic arbitrary allocation/path lengths. A counterexample must retain why
separately typed stores or length monotonicity alone do not justify extension:
an untyped write can change the type at an existing location.

Keep parser and diagnostic work paused and scratch repository-local. Use small
proof/consumer/publication commits, independent reviews, focused/aggregate/full
tests and complete standard-axiom, dependency, kernel/metadata/EOF/whitespace
audits. New Lean files stay below 300 lines.
