# ADR-0323: Three-or-more grouped expected lambda applications

## Status

Accepted; add one standalone opt-in adapter for a maximal finite spine of at
least three source groups ending immediately at a direct computation lambda.

## Context

ADR-0321 handles exactly two groups around a direct expected lambda, and
ADR-0322 places that adapter before the unchanged ADR-0320 entry. A lambda
inside three or more groups remains unsupported even though the unchanged
recursive checker already treats groups around ordinary inferable expressions
as Core-transparent.

The earlier arbitrary-spine prototype preserved the required source evidence,
but structural recursion compiled a public partial `_unsafe_rec` helper. That
made the design inadmissible under the repository's compiled-declaration
policy. A private extractor defined with an explicit
`WellFounded.fix (measure sizeOf).wf` gives the finite descent argument directly
without `termination_by`, fuel, a public recursion certificate or a generated
public partial helper.

## Decision

Add `DirectLambdaGroupSpine`, a public source-evidence relation containing the
original terminal computation lambda and every original group span in
outermost-to-innermost order. A valid three-or-more spine has spans of the form
`first :: second :: third :: rest`; depths zero, one and two do not inhabit this
boundary. The extractor must peel the maximal consecutive group spine, so its
terminal child is the immediate direct lambda rather than another group.

Implement the recursive syntax walk as a private explicit `WellFounded.fix`
over `(measure sizeOf).wf`. Its recursive call must be justified by the strict
size decrease from a group node to its child. Do not use `termination_by`,
`partial`, fuel, `unsafe`, an exported helper or a postulated termination fact.
Audit the compiled environment as well as authored source: every owned public
and private declaration must remain safe and total.

Expose a public total syntax-only classifier that is true exactly for a call
with one argument whose value has such a maximal spine. It must inspect only
the original syntax tree and must not dispatch on elaboration success. The
classifier, declarative relation and executable checker all enforce the same
minimum-depth witness `first :: second :: third :: rest`, while accepting every
finite depth at least three.

The standalone checker infers the unchanged original local callee with the
unchanged recursive local checker, requires its literal unary function type,
and passes that literal parameter type to the unchanged expected computation-
lambda checker on the recorded terminal source. It produces the literal Core
application and inferred result type. Every source group is transparent only
in Core; the source evidence retains the call, argument-list, terminal and all
group spans.

Once the complete singleton spine shape is recognized, the standalone result
is final. A callee, unary-type, lambda-header, lambda-body or expected-type
failure returns `none`; do not retry another checker, shorten the spine, rebuild
the AST, use `Option.orElse` or otherwise fall back. Prove exact executable and
declarative correspondence, exact absence, Core typing and complete source
provenance.

## Prototype and independent consumers

The prototype must compile the private well-founded extractor and inventory
all generated declarations before production is copied. The independent audit
must verify exact declaration ownership, public axiom closure, safe/total flags,
the absence of `_unsafe_rec`, masked source-policy scans and acceptance at
depths three, four and a deeper finite control.

A symbolic consumer constructs the unchanged callee and expected terminal-
lambda derivations independently before using correspondence. It retains
duplicate names, foreign owners, sparse indices, opaque runtime values, a
nonempty store and an independently executed Core application. It checks every
group span in order, minimum-depth exclusion, arbitrary finite-tail support and
recognized-failure commitment.

A parsed consumer fixes the complete AST and spans for
`apply((((lam(x){return x;}))))`: call `0..30`, argument list `5..30`, group
spans `6..29`, `7..28` and `8..27`, and terminal lambda `9..26`. Additional
four-group and deeper fixtures verify maximal extraction and ordered span
retention. It checks clean diagnostics, EOF, exact checker equality, provenance
and the established Core fuel/store boundary.

Negative and preservation controls cover depths zero through two; malformed
recognized spines; non-function and unresolved callees; a non-lambda terminal;
nested calls, tuples, conditionals and calls inside groups; zero and multiple
arguments; top-level forms; return-position lambdas and inferred-let
propagation. Ordinary grouped expressions remain behavior of existing entries,
not this standalone adapter.

## Preserved and deferred boundaries

ADR-0317 through ADR-0322, the recursive checker, canonical source unions and
every existing entry point remain unchanged. This ADR adds no wrapper. A future
wrapper may classify this exact source first, use ADR-0323 when true and return
exactly ADR-0322 when false; recognized ADR-0323 failure must never fall through.

Expected-type propagation through conditionals is viable but deferred. This
decision adds no nested-call, tuple, return, inferred-let, typed-body or
multi-argument propagation, and no global catalog, source closure, runtime
inhabitant, world safety, cost theorem, backend guarantee, principal inference,
coercion or overload policy. Parser and diagnostic proof work remains paused.

Keep every proof and consumer file below 300 lines and every commit within 300
changed lines. Verify focused and aggregate builds, full tests, exact public
axioms and declaration ownership, compiled totality, independent consumers and
preservation of the paused parser and diagnostic files.
