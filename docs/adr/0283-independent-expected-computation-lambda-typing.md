# ADR-0283: independent expected computation lambda typing

## Status

Accepted; an additive source-only typing interface for the standalone expected
unary computation lambda profile. Canonical Rust remains fixed at
`18fd9f75d290df0070e21ee56e0a5691f232596f`. ADR-0281 and ADR-0282 executable
entry points and all older source admission and contracts remain unchanged.

## Motivation and evidence

ADR-0282 describes original lambda elaboration with a particular Core expression
as output. Its typing theorem preserves that expression's expected type, but
there is not yet a lambda judgment that states only the original source type
without mentioning a Core expression or an executable checker.

The fixed `crates/hir-ty/src/infer/expr.rs:938–1080` uses the supplied expected
function domain/codomain while checking original parameters and body. Together
with the outer-annotation/inner-body scope order in
`crates/hir/src/nameres/body_resolver.rs:166–184`, this supports the same restricted
expected-type profile as ADR-0282. No new canonical syntax or runtime behavior is
inferred here. The distinction between supplied expected types and inference of
a nominal closure without an expected type remains unchanged.

Existing shared `ComputationReturnTreeHasType` is independent of Core output and
checker execution. Its correspondence with body elaboration requires only each
fixed child's typing/elaboration existence correspondence. Reuse that interface
rather than defining lambda source typing by successful checking or by the
existence of a Core output.

## Decision

Add `ExpectedComputationLambdaTyping` with the independent judgment
`ExpectedComputationLambdaHasType`, parameterized by `ChildHasType`. Its sole
lambda constructor retains the original expected-header declaration, both Core
component well-formedness proofs in the fixed empty data environment, and an
independent shared computation-body typing derivation at the expected codomain
under exactly the declared inner inputs.

The judgment takes the original expression and expected type, not a Core
expression. Its definition contains neither a checker graph nor an existential
Core elaboration. Preserve original body, annotations, spans and ordered scope
through the existing header evidence. No new runtime values or body are built.

Publish only two accompanying correspondence laws:

- Source typing is equivalent to existence of an independent ADR-0282 lambda
  elaboration, assuming only each child's source typing is equivalent to
  existence of a child elaboration.
- Source typing is equivalent to existence of a successful result from the
  unchanged ADR-0282 checker, additionally assuming only the fixed child's exact
  checker/elaboration correspondence.

Neither law requires child Core typing, a deterministic elaboration relation,
runtime inhabitants, actual captures, a store, a world or an execution path.
Do not strengthen the first law with the second law's checker premise. Checker
absence and `isSome` variants can be derived in consumers without more public
wrappers or a new executable entry point.

The expected type is an input. An inferred identity lambda can have Word-to-Word
and Bool-to-Bool derivations for the very same original source. Do not add a
source-only type-uniqueness theorem or claim principal type inference. Existence
of an elaboration also does not imply uniqueness for an arbitrary child relation.
Well-formed component guards and all opt-in profile limitations remain explicit;
there is no general canonical typechecking completeness claim.

## Consumers and validation

Build independent original-body typing derivations before applying either new
law. Include arbitrary well-formed expected components, outer same-name shadowing,
captured names, typed/inferred local bindings and existing shared body forms.
Parsed tests should obtain source-only typing before consulting the lambda
checker, and should distinguish a valid header from a mismatched or unsupported
body. Retain original annotations and source ranges.

Use boundary models to show that a nondeterministic child can satisfy the first
law without admitting an exact optional checker, and that one unannotated source
can support different supplied expected types. Missing child correspondence
premises must not be silently replaced by Core typing or successful checking.
Any Core observations remain consumers of existing Core semantics, not new raw
source-lambda evaluation or canonical backend execution proofs.

Run focused and aggregate builds, full tests, exact standard-only public and
consumer axiom audits, independent reviews, old byte/header/import checks and
kernel-policy, EOF, and whitespace checks. Keep each new file below 300 lines and use
small separate decision, implementation/proof, consumer and publication commits.

## Non-goals

No new checker or source admission branch, expected-type propagation into nested
children, principal inference, source-only type uniqueness, general nominal type
resolution, capture conversion, source operational correspondence or runtime
safety. Existing literal insertion contracts are preserved. Parser and
diagnostic proofs remain paused.
