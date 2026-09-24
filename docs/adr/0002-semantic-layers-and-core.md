# ADR-0002: Semantic Layers and the Semantic Core

- Status: Accepted
- Decision date: 2026-07-23
- Scope: semantic-layer architecture and Core boundaries

## Reader summary / Current implementation

- **Decision:** Keep source-preserving `Syntax`, name-resolved `Resolved`,
  source typing and execution in `SourceSemantics`, and the typed executable
  `Core` as explicit semantic boundaries.
- **Current implementation:** All four boundaries are represented by Lean
  modules. The parser and frontend connect `Syntax` to `Resolved`; source
  typing and dynamic judgments live under `SourceSemantics`; Core remains a
  separately executable target with its own declarative and machine semantics.
- **Boundary:** Hull, Yul, EVM bytecode, and compiler lowering behavior do not
  define Core semantics.
- **Suggested reading:** Read “Decision” for the layer contract and
  “Conformance Requirements” for the required cross-layer proofs.

## Context

The Haskell and Rust compilers perform specialization, closure conversion,
dispatch generation, and Hull/Yul lowering. If Lean used the same lowering
pipeline and returned only EVM results, it could share the same class of
transformation defects as the existing compilers and would not be an
independent reference implementation.

Furthermore, combining source syntax, name-resolved programs, and typed
semantics in a single AST would obscure the responsibilities and proof
obligations of each phase.

## Decision

The specification is divided into the following explicit layers:

1. `Syntax` preserves source order, UTF-8 byte spans, and explicit syntactic
   boundaries.
2. `Resolved` resolves references to structured identifiers based on module
   paths and source-declaration indices.
3. `SourceSemantics` gives source-level typing and dynamic judgments over the
   resolved language.
4. `Core` represents typed execution semantics and makes lexical
   closures, direct pattern matching, type application, class evidence,
   comptime/runtime stages, and primitive effects explicit.

Hull, Yul, and EVM bytecode are not definitions of the Semantic Core. They are
outputs of lowering passes that may be proved correct in the future.

The semantic kernel is constructed from pure, total functions and does not
depend on `partial`, `unsafe`, or actual IO. External environments and state
are explicit inputs.

## Consequences

- Lambda expressions are evaluated directly as closures in Lean, and `match`
  expressions are evaluated directly as pattern matching.
- An IR produced after erasing type-class dictionaries or polymorphism is not
  the sole representation of the specification.
- The parser, resolver, checker, elaborator, and evaluator have distinct
  failure phases.
- Source spans are used for diagnostics and do not affect dynamic semantics.
- Identical backend output is not a requirement for semantic conformance.

## Conformance Requirements

- The uniqueness and non-dangling property of references returned by the
  resolver must be checked or proved.
- A declarative typing judgment must be constructible from every successful
  checker result.
- Elaboration must be proved to preserve types and effects/stages.
- The evaluator must be proved sound with respect to the dynamic relation.
- The semantic kernel must contain no `sorry`, `admit`, `partial`, or `unsafe`.
- Closures, ADTs, and pattern matching must be evaluable without invoking a
  backend.
