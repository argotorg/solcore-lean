# ADR-0271: Type-general catch-all matches

- Status: Accepted for implementation
- Decision date: 2026-09-10
- Scope: Arbitrarily typed scrutinees when every original case is a wildcard

## Canonical evidence

Use argotorg/solcore-rs at
`18fd9f75d290df0070e21ee56e0a5691f232596f`.
A wildcard accepts its expected scrutinee type unchanged
(`crates/hir-ty/src/infer/pattern.rs:4–12,68–77`).
Match inference checks every original arm and unifies their result types at a
fresh result type independent of the scrutinee
(`crates/hir-ty/src/infer/stmt.rs:203–215,269–291`).
Numeric literal patterns still constrain their expected type; unreachable
literals are not exempt from checking
(`infer/pattern.rs:80–123,132–145`). Rust's Integer support is not evidence
that Lean's selected strict Word-literal profile supports other numeric types.

Coverage treats a wildcard as a catch-all, including abstract types with hidden
constructors (`infer/coverage_adapter.rs:5–39,68–140,152–168`).
The fixture `crates/hir-ty/tests/fixtures/ok/typeck/abstract_data_wildcard_match/main.sol:1–9`
uses a default-only match over Opaque. The parser accepts default-only but
rejects cases=[] with no default (`crates/parser/src/parse/stmt.rs:216–258`).
Original singleton groups remain transparent as specified in ADR-0270.

Hull materializes effectful scrutinees before selecting the first catch-all,
without introducing a wildcard binding
(`crates/hull/src/emit/match_compile.rs:123–150,202–229,272–298`).
Preserve those observations without claiming equality to its instruction counts.

## Static compatibility, not runtime normalization

Extend the existing single-scrutinee terminal match interface in one place:
accept its old Word-scrutinee profile, or accept any existing child-profile
scrutinee type when every original case classifies as none. Each such case
must be an original bare/grouped wildcard; a binder, Boolean or constructor
pattern is not reinterpreted as one.

Keep scrutinee and branch result types independent. "Any type" quantifies over
Core.Ty supported by existing child elaboration and the supplied input context.
It does not add source forms, global/constructor resolution, nominal value
construction, generic polymorphism, or relaxed runtime-world evidence.

Check every original pattern and body, including unreachable cases and default.
A non-Word scrutinee followed by any original Word-literal case is rejected,
even if an earlier wildcard would select immediately. Grouping and actual raw
success do not repair this incompatibility. Preserve strict literal decoding.

The checker retains the inferred scrutinee type, checks original optional
default and case rows once, and then requires either that type to be Word or
all checked tags to be none. The original default/first-original-body result
anchor, common-type checks, coverage and successful Option fold remain intact.
Do not accept an empty/no-default match by vacuous compatibility. Do not
fabricate a default, normalize source patterns, or delete unreachable rows.

Independent HasType compatibility is Word or every original arm classifying
none. Elaboration compatibility is Word or every original row tag equaling
none, with the existing exact source projection and independent classifications.
Prove their equivalence using classification tag uniqueness, not a runtime or
checker assumption. Keep compatibility separate from coverage and recursive
body premises so induction remains structural.

## Unchanged actual execution and cost

Keep original raw choice, raw/cost evaluation, optional defaults and Core fold
unchanged. The hidden let evaluates the original scrutinee once even when its
value is ignored. Wildcard/default branches still weaken under that saved
actual value, preserving captures, stores and original local-ID scopes.

Generalize only the inserted type in the private Core fold typing proof.
Default and wildcard branches use arbitrary-type weakening. Literal branches
recover Word from static compatibility; an all-none row cannot supply a literal
test. No generated-fragment constructor or Core executable change is needed.

Costs remain S+B+2 with no executed literal comparisons, and S+B+2+7*tests for
the existing Word profile. Actual non-Word success is still distinct from static
acceptance: an incompatible unreachable literal may coexist with a raw leading
wildcard selection. Runtime safety still requires the original explicit actual
inputs/store world and typed pending frames.

## Explicit interfaces and staged verification

Generalize the existing wordMatch constructors of HasType and Elaborates with
a scrutinee type and compatibility premise. Keep their single constructor
rather than adding overlapping catch-all-only rules. The exact public checker
decomposition reflects that type and compatibility. Those signatures
intentionally change; retain shared12, recursive14, entry4, runtime contracts,
all raw/cost/choice signatures and strict/grouped pattern laws unchanged.

Migrate old Word consumers with explicit Word compatibility evidence, preserving
their original AST/Core, owners, types, actual arguments, effects, costs and
checkpoints. Move any old wildcard-only Bool rejection to independent success
with its exact original source context. Keep literal-bearing Bool rejections.

New consumers must cover arbitrary and distinct scrutinee/result types;
default-only and nonempty wildcard-only cases with original present/absent
defaults; grouped markers and all unselected obligations; empty/no-default
rejection; and non-Word scrutinees with unreachable literal rejection despite
raw success. Real parsed tests retain effectful evaluation, actual captures,
whole fuel outcomes and genuine checkpoints. Do not infer runtime inhabitants
or a shared world from structural type evidence alone.

Commit decision, definitions, proof migrations, old consumers, new consumers
and publication separately in small chunks; keep proof files below 300 lines.
Require independent reviews, focused/aggregate/full tests, exact old contracts,
published-catalog/all-consumer standard-axiom audits, dependency/kernel/metadata
and EOF/whitespace checks. Diagnostic/parser proofs remain paused; scratch files
stay inside the repository.
