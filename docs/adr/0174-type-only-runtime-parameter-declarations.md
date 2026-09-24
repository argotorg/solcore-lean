# ADR-0174: Type-only runtime parameter declarations

- Status: Accepted
- Decision date: 2026-09-08
- Scope: explicit canonical parameter annotations without supplied values

## Decision

Separate the static meaning of a restricted runtime parameter list from the
existence and choice of runtime arguments. Introduce ordered `LocalTypeBinding`
rows containing only a spelling, assigned local identity, and Core type, and a
`LocalTypeInputs` bundle requiring unique identities. Derive the existing name
table and resolved typing context from the same rows. Empty inputs and fresh
prepend binding reuse the existing owner-relative allocator.

Interpret canonical explicitly annotated, non-comptime parameters using the
caller-supplied type-name table. Start the public entry from empty static inputs,
process parameters in written order, reject repeated spellings, and retain the
existing reversed storage order and fresh binder indices. Define an independent
`RuntimeParametersDeclareFrom` relation with empty and annotated-cons cases;
the executable `declareRuntimeParameters?` must agree exactly with its
empty-start specialization. Unsupported annotations or parameter forms mean
outside this adapter profile, not a new language-wide diagnostic.

## Relationship to runtime binding

Erase only runtime values and their structural typing evidence from existing
`LocalInputs`. The erasure preserves exact identities, names, and context and
commutes with fresh binding. Every independent runtime parameter binding must
erase to an independent static declaration.

Conversely, a static declaration and an actual supplied list of structurally
typed arguments with exactly the same source-order type list reconstruct a
runtime binding whose erasure is the original static bundle. The type-list
equality includes arity and order: the expected list is the reverse of the
empty-start static context's values. Use the supplied argument values and their
proofs in the reconstruction; do not fabricate values or assume that every
Core type is inhabited.

Consequently, static declaration may succeed while runtime binding rejects
missing, extra, or wrongly typed arguments. Arbitrary explicit Core types,
including nominal data types, remain valid static annotation meanings even
when no runtime value has been supplied. This layer introduces no execution,
allocation, source call, whole-program declaration collector, inference for
unannotated parameters, generic instantiation, or mutable-local policy.

## Subsequent integration

A following unit may combine these static inputs with the existing restricted
function header and exact return-body elaboration. Its output will be an open
Core expression in the parameter context, not a closed source function or a
new call machine. Relating that compiler to existing runtime preparation must
retain an explicit ordered argument-type guard. Static compilation alone will
not assert runtime argument existence or execution success.

## Validation

Audit all new public declarations and exact executable/relation bridges. Use
independent consumers for arbitrary annotation types, source order, fresh
identities, erasure, reconstruction, and static/runtime rejection boundaries.
Exercise complete, diagnostic-free parsed parameter lists and signatures,
including qualified aliases, duplicate names, unsupported annotations, and
argument mismatch. Run focused and aggregate builds, full tests, kernel,
forbidden-proof-token, and whitespace checks. Keep new proof files
below 300 lines and leave diagnostic proofs untouched.
