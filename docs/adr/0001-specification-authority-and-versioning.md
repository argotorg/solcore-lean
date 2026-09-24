# ADR-0001: Specification Authority and Versioning

- Status: Accepted
- Decision date: 2026-07-23
- Scope: `solcore/0.1.0-draft.1`

## Reader summary / Current implementation

- **Decision:** Versioned declarative Lean rules outrank executors, tests, and
  comparison compilers; every published boundary is identified by explicit
  language, profile, and implementation metadata.
- **Current implementation:** Drafts 1 through 3 and draft 5, the surviving
  profiles and Core schemas, their digests, pinned baselines, and metadata
  checks are present. Later
  ADRs expose only the Core, contract-runtime, and source-semantics fragments
  whose proof boundaries are complete.
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

1. The versioned declarative Lean specification
2. Accepted ADRs and version manifests
3. Lean executors whose correspondence with the declarative specification has
   been proved
4. Normative conformance tests
5. Existing documentation, the Haskell and Rust implementations, the standard
   library, and existing corpora

Agreement between the two existing implementations, or a majority decision,
does not by itself constitute a normative decision. Differences are recorded
as evidence, and any required semantic choice is decided by an ADR.

`LanguageVersion` identifies the grammar, static semantics, dynamic semantics,
ABI, storage layout, and known feature set. A component version whose normative
rules are incomplete is `none`. An EVM revision is specified by a
contract-scope runtime profile, not by the pure Core.

Compiler commits, solver modes, dispatch settings, backends, and resource
limits are recorded in `ImplementationBaseline` and kept separate from the
language version.

## Consequences

- A disagreement between the declarative specification and an executor is
  treated as a defect in the executor or its proof.
- Updating an upstream compiler alone does not change the language version.
- An observable semantic change requires updating the affected component
  version and its ADR.
- Undecided behavior may be exposed as `unsupported` instead of imitating an
  existing implementation.
- A conformance corpus is evidence for the specification, but is not by itself
  a specification authority.

## Conformance Requirements

- Every versioned profile must identify its language version and profile ID.
- Compatibility results must record the compiler revision and execution
  settings.
- Changing an expected result in a normative test must be accompanied by a
  corresponding specification change or ADR.
- After changing an implementation baseline, known differences must be
  revalidated with the same settings.
