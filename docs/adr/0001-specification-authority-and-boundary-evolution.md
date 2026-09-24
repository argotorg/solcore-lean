# ADR-0001: Specification Authority and Boundary Evolution

- Status: Accepted
- Decision date: 2026-07-23
- Scope: specification authority and evolving public boundaries
- Current applicability: The authority ordering remains in effect. Standalone
  language/profile/baseline metadata and external JSON schema publication are
  retired while the implementation boundaries continue to evolve.

## Reader summary / Current implementation

- **Decision:** Declarative Lean rules outrank executors, tests, and comparison
  compilers. Serialized boundaries use one explicit current Lean type and
  codec while the language is evolving.
- **Current implementation:** Public boundaries are the Lean modules and codecs
  themselves. The repository does not maintain separate machine-readable
  profile, feature, baseline, digest, or external JSON-schema mirrors.
- **Boundary:** Acceptance of this ADR does not promote an incomplete language
  feature or make an existing compiler normative.
- **Suggested reading:** Read “Decision” for the authority order, then
  “Conformance Requirements” for the checks that make it operational.

## Context

Solcore has a Haskell implementation, a Rust implementation, language
documentation, a standard library, and multiple test corpora. These sources
contain differences caused by solver modes and compiler phases, undefined ABI
behavior, and implementation defects. Treating any existing implementation as
unconditionally correct would freeze accidental behavior into the formal
specification.

Conversely, treating the Lean executor alone as the specification would make
implementation errors indistinguishable from the intended semantics.

## Decision

The following precedence defines the semantic authority for Solcore:

1. The declarative Lean specification
2. Accepted ADRs
3. Lean executors whose correspondence with the declarative specification has
   been proved
4. Normative conformance tests
5. Existing documentation, the Haskell and Rust implementations, the standard
   library, and existing corpora

Agreement between the two existing implementations, or a majority decision,
does not by itself constitute a normative decision. Differences are recorded
as evidence, and any required semantic choice is decided by an ADR.

Serialized data has one canonical current boundary. In particular,
`Solcore.Core.Wire` owns the current Core representation and codec; historical
variants are not retained as parallel APIs. A change to that boundary is an
ordinary reviewed specification change, not an implicit compatibility promise.
A source or runtime fragment outside the current boundary remains explicitly
partial or unsupported.

Compiler commits, solver modes, dispatch settings, backends, and resource
limits belong in the comparison document or experiment that uses them. They do
not define the language.

## Consequences

- A disagreement between the declarative specification and an executor is
  treated as a defect in the executor or its proof.
- Updating an upstream compiler alone does not change the specification.
- An observable semantic change requires updating the affected Lean definition,
  its tests and proofs, and any governing ADR.
- Undecided behavior may be exposed as `unsupported` instead of imitating an
  existing implementation.
- A conformance corpus is evidence for the specification, but is not by itself
  a specification authority.

## Conformance Requirements

- Compatibility results must record the compiler revision and execution
  settings.
- Changing an expected result in a normative test must be accompanied by a
  corresponding specification change or ADR.
- A serialized boundary must have an explicit current type and codec, with
  tests that reject malformed or unsupported values. A breaking format change
  must update its code, tests, catalog, and governing ADR together.
