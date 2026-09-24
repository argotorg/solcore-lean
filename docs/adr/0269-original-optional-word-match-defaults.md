# ADR-0269: Original optional defaults in exhaustive Word matches

- Status: Accepted for implementation
- Decision date: 2026-09-10
- Scope: Wildcard-covered terminal Word matches without a default

## Canonical evidence

Use argotorg/solcore-rs at
`18fd9f75d290df0070e21ee56e0a5691f232596f`.
The parser accepts an optional default, preserves original case order, and
rejects an entirely empty arm collection
(`crates/parser/src/parse/stmt.rs:200–264`).
Inference checks every arm at a common result type in its original arm scope
(`crates/hir-ty/src/infer/stmt.rs:203–215,269–291`).
Coverage reports non-exhaustiveness separately from unreachable-arm warnings
(`crates/hir-ty/src/infer/coverage_adapter.rs:70–142`,
`crates/hir-ty/src/infer/diagnostics.rs:847–858`).
Its Word constructor space is explicitly open, not a finite enumeration of
all 256-bit values (`infer/coverage_adapter.rs:676–708`).

The existing first-match and once-only scrutinee evidence remains applicable:
`crates/specialize/src/evaluate/known.rs:127–145,170–182` and
`crates/hull/src/emit/match_compile.rs:123–150,202–296`.
Do not infer agreement on overflow, general pattern coverage or instruction
counts from these facts.

## Preserve the original absence

Generalize the existing terminal single-Word match profile to accept either
an original default or an original wildcard case. Keep strict in-range literal
patterns, exact wildcard markers, original order, duplicate priority, all-body
typing and one common result type. Missing default without a wildcard remains
outside static acceptance, including a literal-only arm that happens to match
the supplied runtime value. Empty cases without default are rejected.

Carry the optional default through syntax, selection, typing, elaboration and
raw/cost evaluation. Do not fabricate a source default, reuse an arm body as an
invented default, or add a Unit/error Core fallback. WordMatchChooses takes an
Option source block; fallback exists only for a present original default.
Hit, miss and wildcard preserve the supplied optional default. Dynamic rules
do not gain a static coverage assumption: raw literal-hit success without
default is still meaningful even when the complete source fails typing.

Static coverage is original-default presence or an exact original wildcard
among the cases. Check every original case and any original default, including
unreachable bodies. With a default, preserve its existing role as the common
type anchor. Without one, use the first original case body as the anchor.
Never infer the branch result type from the scrutinee's Word type, a fabricated
body, or an enclosing function annotation.

## Partial lowering, total accepted bodies

The branch fold now returns Option Core.Expr. Its initial tail is the original
optional default Core weakened under the saved scrutinee. A literal maps its
existing WordEq if over the optional tail. A wildcard returns its weakened
original branch as some Core, regardless of the optional tail.

In particular, an original wildcard followed by a literal with no default is
accepted when all bodies type-check: the wildcard covers a suffix whose fold
alone is none. Do not bind the tail monadically before inspecting the current
tag. Static failures in any later pattern/body are never recovered this way;
only lowering of an already-checked unreachable suffix can be discarded.

Represent optional default elaboration with an Option pair of the original
block and its Core, its exact source projection, and a separate pure forall
recursive body premise. Keep case pattern meanings, recursive branches and
the final fold-equals-some-Core evidence separate for positivity and induction.
The outer hidden let is unchanged, so every accepted match evaluates the
original scrutinee once before selecting a body.

Private execution and cost fold proofs must require that same successful
lowering evidence. Choice alone cannot imply it: a sole literal case may hit
raw even though its missing else leaves the complete fold undefined.
Elaboration supplies this evidence to the old public kernels, without adding
a child-fragment or coverage premise to those kernels. Source cost remains
`S + B + 2 + 7 * literalComparisons`, preserving actual captures, stores,
arbitrary continuations and genuine checkpoint resumption.

## Explicit interface changes

Retain the shared 12, recursive-expression 14 and entry 4 theorem signatures,
all runtime input/safety/world contracts, and literal pattern meaning with its
value-uniqueness theorem. No new runner or expression family is introduced.

WordMatchChooses, its constructors and its determinism theorem intentionally
generalize their default argument to Option. The static and raw/cost wordMatch
constructors also reflect the original optional default. This is not a claim
that every public signature remains byte-identical. Migrate required-default
consumers with explicit some values where needed, preserving their original
source, Core, result, store, cost and checkpoint conclusions.

## Verification and staging

Commit the decision, then definitions, independent selection/static/execution/
cost proofs, consumer migrations, new consumers and publication separately.
Keep proof files small with local simplification and narrowly justified support
boundaries if needed, without adding semantic premises to make proofs easier.

The checker proof uses one such boundary: ComputationReturnTreeCheckingProperties
exports ComputationReturnTreeChecking.match_iff, the exact decomposition of
checking an original terminal optional-default match. Its private helpers cover
pattern checking, ordered rows, optional defaults and the first-body type anchor.
The existing soundness/completeness kernel consumes that decomposition without
changing its public signature or assuming static coverage separately.

Move the existing parsed no-default wildcard rejection to an independent
success using the same original source/header/owner/types/arguments. Retain
literal-only no-default rejection. Cover leading and later wildcard, a typed
literal suffix after wildcard with no default, arbitrary literal prefixes,
non-Word branch result types, and unselected bad bodies that still reject.
Keep raw non-exhaustive literal-hit success distinct from whole-source typing.
Reuse independent source costs and literal Core paths, actual effects/captures,
all fuels and genuine saved-state/world resumption. Preserve old default-only
and required-default behavior.

Run independent reviews, focused, aggregate, and full tests, all-public and all-consumer
standard-axiom audits, exact old-kernel contracts, dependency and kernel-policy,
EOF and whitespace checks. Diagnostic/parser work stays paused and scratch
files remain repository-local.
