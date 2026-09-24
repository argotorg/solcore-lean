# ADR-0006: External ABI admissibility and collisions

- Status: Accepted
- Decision date: 2026-07-23
- Scope: ABI, contract dispatch

## Reader summary / Current implementation

- **Decision:** A public ABI type is supported only when metadata, signature,
  decoding, and encoding are all defined consistently; duplicate signatures and
  selector collisions are rejected before generation.
- **Current implementation:** ADR-0150 completes an internal Static Word ABI
  profile for `uint256 -> uint256`, including its collision checker and checked
  Core dispatcher. Unsupported source shapes are recorded in the feature
  matrix.
- **Boundary:** The current direct Lean ABI API covers only the explicitly
  checked static-word profile; it does not claim general source dispatch.
- **Suggested reading:** Read “Decision” for admissibility and
  “Conformance requirements” for the future totality and collision checks.

## Context

Existing implementations generate ABI metadata, spell selectors, decode calldata,
and encode results in separate subsystems. Some types can be named in metadata but
cannot actually be called because runtime dispatch evidence is missing.

The Haskell emitter admits unknown nullary type names and can reach a partial
function for a parameterized ADT. The Rust compiler rejects user ADTs with a
structured diagnostic and detects duplicate signatures and four-byte selector
collisions before code generation.

## Decision

A public source type is supported only when all four of the following are defined
and mutually consistent for the selected ABI profile.

1. ABI metadata representation
2. Canonical input-signature spelling
3. Decoding from calldata to a source value
4. Encoding from a source result to returndata

If any condition is undefined, the result is `unsupported`; the implementation
must neither infer a type name nor execute a partial function. In particular, the
following remain unsupported in the current version.

- User ADTs without a canonical layout and codec
- `bool` without input-side signature and decoding evidence
- The primitive `word` without complete dispatch evidence
- Nested tuples whose wire mapping does not yet preserve source nesting boundaries

Duplicate canonical signatures, and collisions in which distinct signatures
produce the same four-byte selector, are `rejected` before code generation.

The ABI renderer, selector computation, decoder, and encoder must be total
functions that return structured results. They must not crash on unsupported
shapes.

## Consequences

- A type is not described as "ABI-supported" merely because metadata can be
  generated for it.
- Output-only encoding evidence does not establish support for an input parameter.
- The external representation of a user ADT is not inferred from its source type
  name without a subsequent ADR.
- Safe rejection by the current Rust implementation is desirable implementation
  behavior, but the Lean specification keeps implementation rejection separate
  from an undefined or unsupported language feature.
- Adding standard-library evidence requires conformance tests for all four paths
  at the same time.

## Conformance requirements

- For every supported type, provide an argument/result matrix test that exercises
  metadata, signature spelling, decoding, and encoding.
- Test that `word`, a `bool` input, a user ADT, and an unresolved nested tuple
  produce `unsupported`.
- Verify that duplicate signatures and selector collisions are rejected before
  code generation.
- Verify that an unsupported type produces neither a crash nor an unstructured
  internal failure.
- Provide a round-trip theorem for every covered type for which
  `decode (encode v) = v`.
- If any tuple component is unsupported, the tuple as a whole must not be
  supported.
