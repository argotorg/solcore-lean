# ADR-0052: Internal contract frame halt outcomes

- Status: Accepted
- Decision date: 2026-08-27
- Scope: second internal contract-runtime foundation slice
- Implementation: In progress

## Context

[ADR-0003](0003-verdicts-and-resource-exhaustion.md) separates language
verdicts from runtime halts. A completed contract execution may return, revert,
or reach a trap defined by the language, while an implementation limit is
`inconclusive` rather than a trap. Protocol failures and oracle defects are
separate again.

[ADR-0008](0008-observation-and-evm-revision.md) requires contract observations
to distinguish return data from revert data. It also requires future execution
profiles to fix an EVM revision, initial state, host, and transaction sequence,
but none of those profiles or state transitions exists yet.

[ADR-0051](0051-canonical-runtime-scalars.md) now supplies the internal `Bytes`
type needed for return and revert payloads. It deliberately does not define
contract state, rollback, calls, ABI conversion, or a published observation.
The next safe step is therefore the halt carrier itself, without pretending
that the surrounding evaluator or world state is already known.

The Core machine result is not that carrier. Core completion returns a
`Core.Value`, fuel exhaustion is an implementation limit, and a raw
`Core.MachineFault` is not automatically a specification-defined contract
trap. Turning a Core value into return bytes also requires a later entry and
ABI decision.

## Decision

Add an internal, syntax-independent halt kind with three cases:

```text
FrameHaltKind = returned | reverted | trapped
```

Add a halt outcome parameterized by the future trap-reason type:

```text
FrameOutcome TrapReason
  = returned(returndata : Bytes)
  | reverted(revertdata : Bytes)
  | trapped(reason : TrapReason)
```

The Lean constructors use the spellings `returned`, `reverted`, and `trapped`.
`TrapReason` remains a type parameter: this slice does not invent a trap
taxonomy or collapse all future traps into one concrete reason.

Provide these total observations:

- `kind : FrameOutcome TrapReason → FrameHaltKind`;
- `returndata? : FrameOutcome TrapReason → Option Bytes`;
- `revertdata? : FrameOutcome TrapReason → Option Bytes`; and
- `trapReason? : FrameOutcome TrapReason → Option TrapReason`.

Each projection returns `some` exactly for its matching constructor and `none`
for the other two. Empty bytes remain a present payload: a returned empty byte
string projects to `some ByteArray.empty`, never to `none`. The same rule
applies to empty revert data. Thus absence records a constructor mismatch, not
an empty runtime value.

`FrameOutcome` contains only specification-level frame halts. It has no
constructor for fuel exhaustion, unsupported behavior, inconclusive execution,
an internal error, a protocol error, or a raw Core machine fault. Those remain
at their existing implementation or oracle boundaries.

## Required proof interface

Publish exactly six focused laws:

- the kind of `returned` is `returned`;
- the kind of `reverted` is `reverted`;
- the kind of `trapped` is `trapped`;
- `returndata? outcome = some data` exactly when
  `outcome = .returned data`;
- `revertdata? outcome = some data` exactly when
  `outcome = .reverted data`; and
- `trapReason? outcome = some reason` exactly when
  `outcome = .trapped reason`.

Other definitional reduction equations and private helper lemmas do not add to
the six-law public interface.

## Required tests

Executable regressions cover:

- returned empty and nonempty bytes;
- reverted empty and nonempty bytes;
- at least two distinct test trap reasons, proving that the parameter is
  preserved rather than erased;
- all three kind results;
- the matching projection for every constructor;
- absence from both nonmatching projections; and
- the distinction between `some` empty bytes and an absent projection.

The tests exercise the executable definitions directly. They do not count a
proof term being elaborated again as runtime coverage.

## Staged implementation plan

Keep every commit below 300 changed lines and leave the tree green:

1. accept this ADR and mark the internal slice active in documentation;
2. add the halt kind, parametric outcome, and four projections;
3. add the exact six focused laws;
4. add executable boundary and projection tests; and
5. independently audit the slice and update completion documentation.

## Publication and exclusions

This slice is internal and adds no source form, Core type or expression, frame
evaluator, contract entry rule, `main` return rule, ABI conversion, world
state, storage, balance, log, call, creation, checkpoint, rollback rule, or
trap taxonomy. It chooses no EVM revision, gas schedule, host behavior, or
resource-limit accounting.

It adds no JSON schema, Wire tag, profile, Oracle query, verdict, protocol
field, or published observation. In particular, `FrameOutcome` is not an
`executed` verdict envelope, and its `trapped` constructor is not a replacement
for `inconclusive` or `internalError`.

Address-to-Word conversion, address truncation, map ordering, state deltas,
trace survival, and the mapping from Core completion or fault to a frame halt
remain separate decisions.

## Consequences

Later state-transition and observation rules can refer to return, revert, and
trap without depending on concrete syntax, ABI layout, compiler artifacts, or
a prematurely chosen trap enumeration. Return and revert payloads already use
the canonical byte vocabulary. Concrete state and rollback can be added only
after their own invariants and survival rules are decided.
