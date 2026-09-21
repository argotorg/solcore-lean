# ADR-0347: Explicit source integer-literal carriers and builtin Int execution

## Status

Implemented as an executable vertical slice for expression-position decimal and
hexadecimal integer literals, including contextual closure through nested and
let-bound no-catalog builtin operators.  The remaining deferred boundaries are
listed below.

## Context

ADR-0344 introduced the staged `integer` type and the modulo-Word projection.
ADR-0345 made compiler-provided and source-declared trait and implementation
identities disjoint.  ADR-0346 installed premise-free builtin `Int<Word>` and
`Int<integer>` evidence.  Those changes deliberately stopped before changing
the whole-program expression inference and Source Core execution paths.

The pinned reference revision
`argotorg/solcore@1d490d8bb5f374356f06e0720655496482eb1fb4`
treats an integer spelling as an arbitrary-precision compile-time payload and
selects a builtin `Int.fromInteger : integer -> a` specialization for its result
type.  Therefore expression inference must not silently assign Word, consult a
source trait merely named `Int`, `FromLiteral`, or `Numeric`, or lose the
conversion choice while testing overload candidates.

## Decision

### Allocate one literal-owned builtin obligation immediately

When source inference encounters an expression-position decimal or hexadecimal
literal, it decodes the complete spelling to a `Nat`, allocates a fresh target
type variable `alpha`, and immediately allocates exactly one requirement for
the builtin predicate `Int<alpha>`.  The same step records an
`ExpressionForm.integerLiteral` containing:

- the original `Syntax.CoreLiteralValue` spelling;
- the decoded arbitrary-size `rawValue : Nat`;
- the current `targetType`, initially `alpha`; and
- the stable `RequirementId` of that exact builtin obligation.

The expression node owns exactly that requirement at creation.  Substitution
may close the target type but cannot change the source spelling, raw value, or
requirement identity.  Candidate forks validate and specialize this preexisting
row; they do not allocate a replacement requirement or mutate the shared
origin.  Consequently failed candidates cannot leak duplicate literal rows and
the requirement order remains source-traversal order before any enclosing
operator, call-signature, or coercion requirements.

There is no expression-literal Word default.  An expected type, argument
matching, result matching, or later monomorphic use may close `alpha`.  If it
remains flexible at whole-expression or function finalization, inference reports
an unresolved integer-literal target.  Finalization then solves every retained
requirement and applies the final substitution to both the typed nodes and their
literal carriers.

Builtin `Int` is identified by `ProgramTraitId.builtin .int`; source declarations
named `Int`, `FromLiteral`, or `Numeric` remain ordinary, mutually independent
source declarations.  They neither satisfy nor replace a literal's builtin
obligation.

### Preserve literal origins through overload selection

Overload checking carries every literal origin introduced in the current
argument subtree.  It also carries an older still-flexible origin, such as a
monomorphic let-bound literal, when that target variable flows through the
argument type.  This permits an outer candidate to close a nested or let-bound
literal without making unrelated earlier literals participate in its ranking.

After argument and result fitting, each candidate revalidates the retained
literal rows and all requirements visible in that candidate state, including
requirements inherited from a nested call.  A closed literal target must resolve
its builtin predicate immediately.  A still-flexible literal target marks the
candidate as deferred and is checked again after an enclosing context closes it
and at finalization.

Successful ground candidates form the preferred rank.  Deferred candidates are
considered only when no ground candidate succeeds; normal coercion-cost ranking
then applies inside the preferred rank.  This prevents a cheaper open generic
candidate from blocking a concrete candidate while still allowing a unique
deferred candidate to be selected and closed by an outer context.

`Int<Word>` and `Int<integer>` are equally supported primitive solutions.  The
rule-list order is not a default or a tie-breaker.  Thus an expected Word or
`integer` result can select the corresponding overload, while otherwise equal
Word and `integer` overloads remain ambiguous.

An otherwise builtin-compatible Word-domain unary or binary operator may retain
an open operand/result type without an operator catalog only when that type was
an open carried integer-literal target before contextual unification.  The
surrounding call parameter, return type, or later monomorphic use can then close
the same literal origins.  This supports direct and let-bound forms such as
`accept(1 + 1)` and `accept(~1)` without inventing Word defaulting.  Bool-domain
logical operators never use this deferral.  It also does not authorize an
unrelated generic or merely co-located literal, nor bypass a visible operator
catalog: cataloged functions or trait methods remain authoritative and their
ordinary evidence failures remain failures.

### Validate and erase the builtin conversion at Core lowering

Specialization closes the carrier's target type while preserving its source,
raw value, and requirement identity.  Source Core lowering accepts the Word
case only after checking all of the following:

- the carrier target equals the typed expression's pre-coercion type;
- after exact output-coercion requirements are separated, the base expression
  owns exactly the carrier's one literal requirement;
- decoding the retained source spelling reproduces the recorded raw value;
- exactly one solved row has that requirement identity;
- the row predicate and evidence goal equal builtin `Int<Word>`;
- the evidence selects builtin implementation `intWord`; and
- that primitive evidence has no premises.

The dedicated literal path then erases `Int.fromInteger` and emits a Core Word
constant `Word.ofNatModulo rawValue`.  Decimal and hexadecimal overflow
therefore reduce modulo `2^256`; for example `2^256` becomes zero.  A coercion
from that Word is prepared only after the literal contract has been validated at
its raw Word type.

This is dedicated compiler-primitive erasure, not general execution of a builtin
trait method or a source `fromInteger` body.  A carrier closed to `integer`
retains builtin `Int<integer>` evidence during source checking, but the staged
type is still rejected before runtime Core construction.

`ExpressionForm.literal` remains available only for manually assembled legacy
typed IR.  It has no requirement and continues to use the strict in-range Word
decoder; source inference does not emit it for integer syntax, and overflow in
that manual compatibility form remains an error rather than gaining modulo
semantics.

## Proof and validation scope

This is an executable-first slice.  Small laws cover literal-carrier
substitution and specialization preserving the raw value and stable requirement
identity, on top of ADR-0344's soundness and completeness results for the
arbitrary-size decoder and modulo-Word projection.  Executable regressions cover
immediate single-row allocation, candidate rollback, contextual Word and
`integer` selection, equal-support ambiguity, ground-over-deferred ranking,
nested and let-bound origin capture, no-catalog operator closure and catalog
authority, final unresolved-target rejection, specialization, modulo lowering,
staged `integer` rejection, legacy strict overflow rejection, and defensive
lowering validation.

A broad soundness/completeness development for whole-program inference,
overload ranking, specialization, and lowering is not required for this
vertical slice.  That proof-density choice does not weaken the executable
invariant checks at the lowering boundary.

## Deferred boundaries

- Executing a custom implementation of the compiler builtin `Int` trait remains
  unsupported.  A source trait spelled `Int` is intentionally disjoint and is
  not an extension point for this primitive carrier.
- ADR-0349 evaluates the first closed signed subset: literal/group/nested
  `integerSub` trees are computed as Lean `Int` and an outer
  `wordFromInteger` projects modulo `2^256`.  The carrier itself still decodes
  nonnegative decimal and hexadecimal spellings to `Nat`, and the source
  grammar has no unary minus.  General staged arithmetic and control flow
  remain deferred.
- ADR-0348 adds a separate typed carrier and executable boundary for terminal
  single-scrutinee numeric-pattern matches.  Pattern literals do not reuse this
  expression carrier; broader pattern forms remain deferred there.
- Additional synthetic corruption tests for inference-state origin/requirement
  invariants remain useful follow-up work.  The lowering suite already rejects
  malformed target, attachment, spelling/value, solved-row, predicate, evidence,
  implementation, and premise combinations.

## Verification

The source-inference, requirement-identity, overload-ranking, typed-IR,
specialization, Source Core elaboration, direct-linking, program-checking,
public source-execution, and structural-expression regressions exercise this
slice.  Repository-wide tests, kernel-policy checks, metadata verification, and
formatting checks remain the integration boundary.
