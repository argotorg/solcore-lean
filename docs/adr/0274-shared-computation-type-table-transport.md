# ADR-0274: Meaning-preserving type tables for shared computations

- Status: Accepted for implementation
- Decision date: 2026-09-10
- Scope: Additive body and function transport proofs, without admission changes

## Existing semantic boundary

TypeNameTable.Extends preserves every existing first-match named meaning,
not merely row membership. Appending entries is safe; a fresh-key prepend is
sufficiently safe. A meaning-changing prefix is not an extension. One-way
extension can resolve a formerly unknown type, so it cannot preserve rejection.
Mutual extension preserves the complete lookup result, including absence.

The structural annotation layer already transports its independent meanings
through this relation, including nested unary function types and ordered tuple
types (ADR-0272). Header, static parameter declarations and actual parameter
bindings also have exact-record transport proofs. Earlier restricted body and
runtime endpoints consume them, but the shared computation-body and function
interfaces do not yet expose the corresponding laws.

No new Rust behavior, syntax, operator resolution or runtime policy is chosen
here. This unit proves consequences of those existing Lean definitions.
ADR-0273's conservative terminal-if name-protection boundary remains unchanged.

## Independent body evidence first

Add ComputationReturnTreeHasType.extend_types and
ComputationReturnTreeElaborates.extend_types for an arbitrary fixed child
judgment. Transport by induction on original independent evidence. Only a
typed let's structural annotation meaning needs a new proof; inferred lets,
original initializer scopes, exact fresh tail inputs, name protection, source
spans, match classifications/order/coverage/defaults and generated Core remain
identical. All original branches are retained, including unreachable branches.

Add executable successful-result preservation and whole-Option equality under
mutual extension for an arbitrary fixed checkChild. No childCorrect hypothesis
is needed: inside the executable proof only, instantiate the existing generic
checker correspondence with the checker's success graph and Iff.rfl.
This is the same proof device as ComputationFunctionFactorizationProperties;
it is not a new source semantics or a replacement for independent typing and
elaboration. Never switch between a family of child checkers that themselves
close over different type tables. The operation is the same on both sides.

## Exact function and actual-result transport

Add independent Compiles and Prepares transport using the original header,
parameter and new body laws. Preserve the same declaration, owner, parameter
order, LocalIds, compiled Core/result type, actual arguments and complete
prepared record. Do not identify actual records merely through toCompiled,
types or erased layouts, or reconstruct different inhabitants.

Add compile, prepare and run successful-result preservation under one-way
extension, plus complete Option equality under mutual extension. Run equality
uses the exact same fuel, store and actual inputs: returned values, faults and
genuine out-of-fuel states are all retained. No execution-cost bound, runtime
world inference, automatic validation or arbitrary-store safety follows.
Raw/cost judgments do not mention the type-name table and need no new rules.

Keep the public surface minimal: four body laws and eight function laws in two
new proof files. Existing shared12, recursive14 and entry4 signatures, all
executable definitions and previous proof bodies remain byte-identical.
Import existing structural/header/parameter transport modules directly; do not
pull in older body or runtime-entry proofs just to reuse their special cases.

## Consumers and verification

Independent symbolic consumers cover arbitrary original inputs/types, repeated
shadowing, nested structural annotations and match/conditional evidence.
Executable equations also cover deliberately arbitrary fixed child operations,
without silently adding child typing or correctness. Parsed whole declarations
retain original spans/parameters/header/body and actual captured values.

Exercise safe append and fresh prepend, hidden conflicting duplicate rows and
mutual lookup preservation. Keep explicit counterexamples for changed first
matches and one-way repair of an unknown annotation in an unselected branch:
raw selected success must not imply old whole-body acceptance. Wrong actual
arguments remain rejected. Use separately written Core paths and exact source
costs before comparing transported preparations, all-fuel results and genuine
checkpoints; include effects and corrupt/missing-reference faults where useful.

Commit decision, body proofs, function proofs, consumers and publication in
small reviewed chunks. All proof files stay below 300 lines. Run focused,
aggregate and full tests, public and consumer exact-name standard-axiom audits,
and original-contract, import, kernel-policy, EOF, whitespace, and hash checks.
Diagnostic/parser proof work stays paused; scratch stays inside the repository.
