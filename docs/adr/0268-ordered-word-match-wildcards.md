# ADR-0268: Ordered wildcard cases in terminal Word matches

- Status: Accepted for implementation
- Decision date: 2026-09-10
- Scope: Original wildcard cases in the existing shared Word-match profile

## Canonical evidence

Use argotorg/solcore-rs at
`18fd9f75d290df0070e21ee56e0a5691f232596f`.
The dedicated underscore pattern is Wildcard, not an identifier or binder
(`crates/parser/src/parse/expr_pat.rs:390–393`). Match parsing preserves case
order and places a default after the cases
(`crates/parser/src/parse/stmt.rs:200–264`).
Inference checks every original arm at a common result type and separate scope
(`crates/hir-ty/src/infer/stmt.rs:203–215,269–291`); an unreachable arm is a
warning, not a reason to skip its typing
(`crates/hir-ty/src/infer/diagnostics.rs:854–858`).

Known matching uses the first matching original arm, and wildcard returns the
unchanged environment without testing the value
(`crates/specialize/src/evaluate/known.rs:127–145,170–182`).
Hull first materializes nontrivial scrutinees, preserves row order, and turns a
leading wildcard row directly into a leaf without adding a variable binding
(`crates/hull/src/emit/match_compile.rs:123–150,202–278,295–296`).
These facts support ordered selection and effects, not an identical Rust/Core
representation or transition count.

## Minimal extension of the existing profile

Retain a terminal match with one statically Word scrutinee, the existing strict
in-range Word literal meaning, and a required default. Additionally accept
original `case _` rows, including repeated wildcards and rows following them.
Preserve every original span, case, default and body during static checking.
Do not implement binders, grouped patterns, constructors, multiple scrutinees,
optional-default exhaustiveness, overflow agreement or non-Word static matches.

Keep WordMatchPatternDenotes literal-only. Extend WordMatchChooses with one
wildcard rule: a leading original wildcard chooses its original body for any
actual Core value and performs zero literal comparisons. It ignores later rows
only during dynamic selection. Existing fallback, hit and miss rules remain.
A non-Word actual value reaching an earlier literal comparison still faults;
a later wildcard must not turn that fault into a miss.

The elaboration entries become original case / Option Word / Core triples.
A present Word denotes a strict literal; an absent Word denotes the exact
wildcard shape. The outer checker failure remains distinct from this successful
absent tag. Pattern evidence stays separate from recursive branch evidence to
preserve positivity and the existing branch induction hypotheses. All original
case bodies and the required default are checked at the same result type before
lowering, even after an unconditional wildcard.

The existing wildcard payload contains its own marker span: use an existential
original marker with the exact wildcard constructor, without adding an equality
between that marker and the enclosing pattern span.

## Fixed lowering and proof contracts

Keep the outer hidden Core let, so scrutinee effects occur exactly once even
when the first case is wildcard. Fold a literal entry into the existing WordEq
if; fold a wildcard entry directly into its branch weakened under the saved
actual scrutinee. The latter discards the already-checked Core tail, not the
original static obligations. No source name, LocalId, binding or extra runtime
environment slot is introduced beyond the existing hidden scrutinee slot.

The source cost stays `S + B + 2 + 7 * tests`. Here tests counts executed
literal comparisons, not all visited rows: wildcard contributes zero.
Do not add a child-fragment assumption, generated fragment constructor,
evaluation relation, checker wrapper or runner family. Retain the shared 12,
recursive-expression 14 and entry 4 theorem signatures and all runtime safety,
input construction/validation and saved-world contracts.

The two static wordMatch constructors necessarily adopt the tagged entries or
wildcard/literal pattern alternatives; literal-only consumers are migrated
mechanically without weakening their original conclusions. Existing raw/cost
wordMatch constructors need no signature change. Keep static proof files small
through local proof simplification first; a support module is justified only
if necessary, with no incidental public helper API.

## Staging and verification

Commit this decision before definitions; then separate independent selection,
static, raw/cost proofs, consumer migration/new consumers and publication.
Read-only reviews must check first-match choice/count determinism and original
all-body typing independently of executable acceptance.

Consumers must cover arbitrary literal prefixes before wildcard, wildcard
priority over duplicate/later literal/wildcard rows, malformed unselected body
rejection despite raw first-hit success, and malformed preceding patterns that
cannot be skipped. Retain actual called bodies/captures/stores, scrutinee effects,
selected-only effects, literal Core paths, exact costs, arbitrary continuations
and genuine fuel/checkpoint resumption. Include leading wildcard raw non-Word
success versus a preceding literal fault, named/discarded/nested scope retention,
and direct reuse of runtime input/safety/world premises where applicable.

Migrate only the prior wildcard rejection newly admitted by this exact profile;
keep old local-only interfaces and all other rejection gates unchanged.
Run focused, aggregate and full tests, all-public/all-consumer standard-axiom
audits, old-contract and dependency checks, kernel, EOF and whitespace
checks. Keep diagnostic/parser proof work paused and scratch repository-local.
