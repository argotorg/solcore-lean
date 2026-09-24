# ADR-0267: Terminal single-Word literal matches

- Status: Accepted for implementation
- Decision date: 2026-09-10
- Scope: Original ordered literal cases and required default in shared computation bodies

## Canonical evidence

The reference is argotorg/solcore-rs at
`18fd9f75d290df0070e21ee56e0a5691f232596f`.
The parser retains ordered cases and appends an optional default as a wildcard
(`crates/parser/src/parse/stmt.rs:153–173,200–264`); lowering retains original
patterns, bodies and spans (`crates/parser/src/lower/body.rs:471–505`).
Inference checks every arm against the scrutinee and a common result type,
with separate arm scopes (`crates/hir-ty/src/infer/stmt.rs:203–215,269–291`).
Its sequence rules reject a direct non-final return (`:4–41`); this decision
does not generalize early return effects or insert implicit returns.

Known-match specialization processes scrutinees before selecting the first
matching arm (`crates/specialize/src/evaluate/core.rs:549–577`,
`crates/specialize/src/evaluate/known.rs:127–145,170–182`).
Hull materializes nontrivial scrutinees once and preserves row order and leaf
bodies (`crates/hull/src/emit/match_compile.rs:123–150,202–278,637–638,1032–1060`).
Explicit returns remain returns (`crates/hull/src/emit/emitter.rs:251–259`).

Numeric patterns have contextual Word/Integer inference
(`crates/hir-ty/src/infer/pattern.rs:88–146`). Coverage and Hull normalize
Word literals modulo the Word range (`infer/coverage_adapter.rs:584–667`,
`crates/hull/src/emit/match_compile.rs:1154–1165`), whereas known numeric
matching compares BigInts (`crates/specialize/src/evaluate/known.rs:230–246`).
Keep the existing strict in-range Word literal meaning; do not claim overflow
agreement. Unreachable arms are warnings, not rejection gates
(`crates/hir-ty/src/infer/diagnostics.rs:847–858`).

## Source contract and independent rules

Extend the shared ComputationReturnTree checker, typing, elaboration, raw
evaluation and cost relations, without adding another body or runner family.
Accept a terminal original match with exactly one statically Word scrutinee,
zero or more literal cases, and a required default. Every case/default body
is an existing complete computation return tree with the same caller inputs
and result type. Preserve original source spans, list order and duplicates.
Do not accept binders, wildcard case syntax, grouped patterns, constructors,
multiple scrutinees, missing default or general numeric/class resolution.

A small WordMatchPatternDenotes relation reuses WordLiteralDenotes and the
original literal pattern shape. A separate WordMatchChooses relation selects
an original body and counts visited tests. Empty cases choose default for any
actual scrutinee value. Hit requires the actual matching Word; miss requires
an actual unequal Word and recurses on the remaining cases only. Scrutinee
evaluation occurs once outside selection, before the selected body, retaining
its actual effects. Neither raw nor cost rules invoke the checker.

Typing checks all original cases. Elaboration uses an ordered list of original
case/Word/Core entries whose first projection is the exact source case list;
pattern meanings and recursive branch elaborations are separate premises.
No fabricated source binding, LocalId, source rewrite into if, fresh-name gate,
or duplicate rejection is introduced.

## Fixed Core lowering and generic laws

Always lower to one hidden Core let of the scrutinee. In its body, fold the
original entries rightward into ifs with guard
`binary wordEq (var 0) (word literal)`, selected branch `branchCore.weakenAt 0`,
and final `defaultCore.weakenAt 0`. Only the Core environment receives the
actual hidden value. Existing insertion laws bridge every original branch.

Add one generated wordTest constructor with an arbitrary variable index to
ComputationBodyFragment and extend its existing weakening, raw insertion and
exact insertion-path laws. Core.LocalFragment supplies those guard laws;
there is no new child-fragment premise. Keep the old shared 12, recursive
expression 14 and function-entry 4 theorem signatures unchanged.

Independent source cost is scrutinee cost plus selected body cost plus
`2 + 7 * visitedTests`: outer let costs two; each WordEq costs five and if
selection costs two. This is the fixed Core cost, not a Rust/Hull instruction
cost claim. Default-only still evaluates the scrutinee but performs no guard:
a raw non-Word value may succeed there. Nonempty cases with a raw non-Word
fault at the first comparison after preserving scrutinee effects.

## Staging and verification

First commit the small generated fragment extension, then source definitions,
proofs and consumers separately. Check exact checker correspondence, independent
typing, raw equivalence, selected cost, all continuations, fuel thresholds and
genuine checkpoint resumption through existing shared kernels. Reuse actual
runtime input, no-fault and world-extension contracts without new wrappers.

Consumers retain independently prepared original source, literal Core paths,
actual captures/stores, duplicate first-match and decimal/hex equality,
default-only non-Word success versus nonempty comparison fault, effects before
selection, untouched unselected bodies at runtime but all-body static rejection,
nested matches, named/discard scopes, branch type mismatch and excluded shapes.
Migrate only existing rejection fixtures newly admitted by this exact shared
profile; do not change older local-only body/entry interfaces.

Keep diagnostic/parser work paused, scratch repository-local, files and commits
small, and run independent review, focused/aggregate/full tests, all-public and
all-consumer standard-axiom audits, dependency, kernel, EOF and whitespace
checks before publication.
