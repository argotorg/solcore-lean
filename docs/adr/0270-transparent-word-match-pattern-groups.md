# ADR-0270: Transparent groups in original Word match patterns

- Status: Accepted for implementation
- Decision date: 2026-09-10
- Scope: Arbitrarily grouped strict literal and wildcard Word cases

## Canonical evidence and representation boundary

Use argotorg/solcore-rs at
`18fd9f75d290df0070e21ee56e0a5691f232596f`.
Its pattern parser returns the sole inner pattern unchanged for a singleton
parenthesized list, including a trailing comma
(`crates/parser/src/parse/expr_pat.rs:414–426`). Empty and multiple-element
lists remain tuple patterns. Thus parentheses do not add a pattern test or
binding. Lowering retains that leaf kind
(`crates/parser/src/lower/body.rs:596–612`); first-match selection and wildcard
no-binding behavior remain unchanged
(`crates/specialize/src/evaluate/known.rs:127–145,163–182`).

Lean intentionally retains a `PatternValue.group` node and its outer span,
while retaining the original inner pattern and marker/literal spans
(`Solcore/Syntax/Parser/Pattern.lean:75–85,91–111,121–139`).
Do not mutate either parser or pretend their intermediate spans are identical.
This decision supplies transparent semantics for Lean's original group nodes.

Binder-shaped patterns remain excluded. Canonical name resolution prioritizes
Boolean and user constructors before ordinary bindings
(`crates/hir/src/nameres/body_resolver.rs:241–270`).
The current local structural profile does not supply that constructor scope.
Do not silently classify a binder, grouped binder, Boolean or constructor as
a wildcard. Constructor/name-resolution expansion is separate work.

## Independent classification, unchanged lowering

Keep the existing strict `WordMatchPatternDenotes` definition and its public
value-uniqueness theorem unchanged. Add an independent
`WordMatchPatternClassifies : Syntax.Pattern → Option Core.Word → Prop`:
a strict literal denotes a some-Word tag, an exact original wildcard marker
denotes none, and an original group inherits its inner pattern's tag.
Group nesting is arbitrary; no parser success, span-validity, typing, checker,
runtime or coverage premise belongs in this relation.

Add a total `interpretWordMatchPattern?` returning `Option (Option Core.Word)`.
It recursively interprets only group nodes, uses the existing strict literal
interpreter at literal leaves, and returns successful none at wildcard leaves.
All other forms fail, including empty/multiple-element tuples and grouped
unsupported leaves. Prove exact success iff independent classification, and
classification tag uniqueness, with standard axioms only.

Use this one classification in ordered source choice, independent body typing,
elaboration and the checker. A none classification is exactly the catch-all
coverage witness, even under groups. A some classification is still exactly
one Word comparison; groups contribute no comparisons or bindings.
Keep all original cases, bodies, optional defaults, spans and order unchanged.
Later unsupported patterns or ill-typed bodies still reject after a catch-all.

The checker checks each original pattern and body once. The default/first-body
common-result-type anchor and arbitrary branch result type remain unchanged.
The existing Option Core fold, hidden scrutinee let, recursive source evaluation
and cost constructors do not change. In particular, a grouped wildcard can
recover an unlowerable literal-only suffix without a fabricated fallback.
Scrutinee evaluation remains once-only, with actual effects retained.

Costs remain `S + B + 2 + 7 * literalComparisons`, independently of group depth.
Do not claim equality to Rust instruction counts. A leading grouped wildcard
can select on an arbitrary raw actual value; a preceding grouped literal on a
non-Word still faults rather than missing. Static Word typing and optional
runtime-input validation remain separate from raw source execution.

## Explicit interface changes

The hit, miss and wildcard premises of `WordMatchChooses` intentionally use
classification. Its type, fallback and public determinism signature stay the
same. Static and elaboration match-pattern and coverage premises, and the
checker decomposition's pattern premise, intentionally generalize likewise.
Keep the shared 12, recursive-expression 14 and entry 4 theorem signatures,
raw/cost evaluation signatures, runtime contracts and all executable Core
definitions unchanged. No new runner, source expression family, normalization
pass, semantic assumption or generated-fragment constructor is introduced.

Migrate leaf consumers with explicit literal/wildcard classification evidence.
Preserve original accepted source/Core/owner/types/actual arguments/stores,
costs and checkpoint conclusions. Move any old grouped-pattern rejection to
independent success without changing its original source context; retain
grouped unsupported-leaf rejection and strict overflow boundaries.

## Verification and staging

Commit the decision, definitions, independent pattern laws, static/execution/
cost proof migrations, consumer migrations, new consumers and publication in
small reviewable stages. Keep new proof files below 300 lines.

New consumers cover arbitrary nesting depth and original spans; leading and
later grouped wildcard; ordered duplicate/grouped literal cases; original
missing and present defaults; arbitrary branch result types; unsupported
unreachable grouped patterns/bodies; and empty/multiple-element tuple rejection.
Real parsed examples include singleton trailing commas. Reuse independent
source costs and literal Core paths to check effectful calls, captures, nested
local scopes, all fuel boundaries and genuine saved-state/world resumption.
Do not count parser acceptance alone as frontend acceptance.

Run focused/aggregate/full tests, independent reviews, exact old theorem
contracts, published-catalog and all-consumer standard-axiom audits, import
closure/kernel/metadata and EOF/whitespace checks. Diagnostic/parser proofs
stay paused; all scratch files remain repository-local.
