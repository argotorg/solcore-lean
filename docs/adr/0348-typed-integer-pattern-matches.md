# ADR-0348: Typed integer-pattern matches in whole-program execution

## Status

Implemented as an executable vertical slice for terminal, single-scrutinee
matches with decimal or hexadecimal integer patterns, bare or grouped
wildcards, and an optional default body.  The broader pattern language remains
staged as described below.

## Context

ADR-0267 through ADR-0271 established ordered Word-literal and wildcard match
semantics in the earlier shared computation-body engine.  ADR-0347 later gave
expression-position integer literals an explicit builtin-`Int` carrier in the
whole-program inference, specialization, linking, and execution pipeline, but
left pattern literals outside that carrier.

The pinned reference revision
`argotorg/solcore@18fd9f75d290df0070e21ee56e0a5691f232596f`
gives every numeric pattern its own fresh builtin-`Int` obligation, unifies that
target with the scrutinee's expected numeric type, and defaults only pattern
targets which are still open after body inference to Word.  Wildcards preserve
the expected type and do not cause numeric defaulting.  Match inference checks
every written arm in an isolated scope, including arms which are unreachable
after an earlier wildcard.

## Decision

### Retain a pattern-owned builtin Int plan

For each decimal or hexadecimal pattern, inference allocates a fresh target
`alpha`, immediately allocates one builtin `Int<alpha>` requirement, decodes the
complete spelling to `Nat`, and records all three facts in a typed pattern
carrier.  The carrier also preserves the supported source projection, including
every singleton group and source span.  Wildcards carry no requirement.

The fresh pattern target may unify only with an open scrutinee target, Word, or
the staged `integer` type in this initial slice.  Bool, nominal, product,
function, proxy, mapping, and rigid generic scrutinees reject a numeric pattern.
After every arm and default body has been inferred, finalization defaults each
still-open numeric-pattern target to Word.  This ordering allows a branch to
close the shared scrutinee type first.  It also lets a numeric pattern close an
otherwise open expression-literal scrutinee without restoring general
expression-literal Word defaulting.  A wildcard-only match therefore leaves an
unconstrained expression literal unresolved.

### Restrict the first whole-program match profile explicitly

The supported statement has exactly one scrutinee and must be the final
statement in its containing list.  Every explicit arm and the optional default
body must return.  A default body or at least one wildcard supplies coverage.
Every branch is inferred in a fresh lexical view of the same outer scope;
substitutions, occurrence IDs, requirement IDs, and the monotone local-ID
allocator remain declaration-wide, while source bindings never leak between
arms.

Bare and grouped wildcards plus bare and grouped decimal or hexadecimal
patterns are supported.  String, binder, constructor, comptime, tuple, recovery,
and other pattern forms reject explicitly.  Multiple scrutinees, nonterminal
matches, uncovered literal-only matches, and falling-through branches also
reject instead of receiving an invented meaning.

### Preserve identities through specialization and lowering

The typed match stores its scrutinee occurrence, ordered cases, optional
default body, exact pattern-requirement list, and a declaration-owned hidden
local identity.  Flexible final substitution and rigid generic specialization
close both the pattern type and the integer carrier target without changing
source structure, child occurrence IDs, the hidden local, or requirement IDs.
The specialization residual-type audit includes both stored type positions.

Source Core lowering validates the hidden local's owner and separation from the
source scope, exact match-level and per-pattern requirement ownership, source
spelling and decoded value, target equality, the unique solved row, predicate
and evidence goal, exact builtin `intWord` implementation, and its empty premise
list.  A validated numeric pattern becomes `Word.ofNatModulo rawValue`.
`Int<integer>` remains staged because runtime Core still rejects `integer`.

Lowering checks and lowers every written arm and default under the original
source scope before runtime selection is built.  It reconciles every consumed
requirement even when an early wildcard makes a later branch unreachable.  The
runtime term evaluates the scrutinee exactly once in a hidden `let`, then folds
the ordered cases into Word equality tests; the first matching literal or
wildcard wins.  The hidden identity is included in the direct linker's occupied
local set so generated call, method, and coercion temporaries cannot capture it.

## Deferred boundaries

- Multiple scrutinees and tuple-pattern decomposition remain unsupported.
- Binder, constructor, comptime, string, and general nested patterns remain
  unsupported; wildcard groups are transparent only inside this finite profile.
- Numeric patterns over rigid generic parameters remain unsupported even when a
  source signature carries a similarly spelled trait assumption.
- Nonterminal match control flow, falling-through arms, and broader result-flow
  analysis remain later work.
- Runtime staged-`integer` matching, custom compiler-builtin `Int`
  implementations, and general signed compile-time integer evaluation remain
  separate boundaries.
- A future declaration-wide typed-IR validator may reject synthetic reuse of a
  hidden match identity by another hidden or branch-local binder.  Monotone
  inference allocation already prevents that state for source-produced IR.

## Verification

Regressions cover pattern-only defaulting after late branch constraints,
wildcard non-defaulting, source grouping and spelling retention, exact builtin
evidence, rigid specialization, unsupported shapes, coverage and terminality,
branch-scope isolation, checking of unreachable arms, modulo-Word overflow,
duplicate first-match priority, once-only scrutinee evaluation, public source
execution, direct-call temporary separation, early-wildcard requirement
reconciliation, and type-general wildcard specialization.  A separate
adversarial suite mutates requirement lists, source/raw/type metadata, solved
evidence, and hidden identities and requires located Source Core rejection.
