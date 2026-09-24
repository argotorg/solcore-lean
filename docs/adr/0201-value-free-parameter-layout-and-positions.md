# ADR-0201: Value-free parameter layout and positions

- Status: Accepted
- Decision date: 2026-09-08
- Scope: Static parameter rows, generated identities and exact reference lowering

## Decision

Prove the ordered layout of `RuntimeParametersDeclareFrom` directly from its
annotation-only rules. Existing runtime layout and position laws require actual
typed arguments and cannot establish these facts for arbitrary nominal types.
Introduce independent single-row and ordered-row judgments pairing each original
typed, non-comptime parameter with its exact spelling, annotation meaning and
type-only row. The row judgment leaves the generated ID unconstrained; a separate
declaration-layout theorem fixes allocation and must not be replaced by row
membership or type agreement.

For arbitrary initial static inputs, retain those rows as a suffix after the
new rows in reverse source order. Prove the exact length and generated ID list.
New binder indices start at the existing owner-relative fresh index, not zero
or the initial table length. Other owners and sparse same-owner indices must
be handled by the existing allocator. Preserve distinct source spellings when
the initial name list is distinct; keep that premise on the general theorem.
The empty-start specializations require no additional name-distinctness premise.

From one actual source lookup `parameters[k]? = some parameter` in a successful
empty-start declaration, derive `k < parameters.length`, the annotation's type,
the exact reversed row at `parameters.length - 1 - k`, first-match name and
context lookups, and the exact Core positional index. The generated local ID is
`(owner, k)`. Do not infer position from equal types, mere membership, or natural
subtraction without the real lookup bound. Same-type parameters remain distinct.

Expose source reference resolution, exact checked reference elaboration and
independent singleton-return elaboration at that position. To specify a desired
type, consume its annotation meaning and use type uniqueness, never a runtime
inhabitant. Reference and wrapper spans remain arbitrary. Existing terminal
bodies can embed singleton evidence without another lowering or cost layer.

## Boundaries and validation

This is a proof interface over unchanged static declarations, allocation and
compilation. No executable adapter, source binding/header/body profile, runtime
argument semantics, Core definition, parser or published interface changes.
No arbitrary nonempty-input source-position formula is inferred from the
empty-start result. General layouts retain their actual fresh starting index.

Independent consumers cover arbitrary and nominal types, sparse/mixed-owner
initial inputs, repeated initial spellings with the necessary distinctness
boundary, source order, exact lookup and out-of-range counterexamples. Parsed
consumers use real parameter lookup witnesses at every tested position, including
same-type distinct parameters and nominal inputs without runtime values. Combine
owner transport with position preservation and retain whole-compilation failure
when a valid parameter list is followed by an invalid body or return contract.

Audit public declarations and consumers with standard axioms only; run focused,
aggregate and full tests, kernel-policy and whitespace checks, keep proof files
below 300 lines and commits small. Leave diagnostics paused and place scratch
files inside the repository.
