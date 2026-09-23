# ADR-0369: Source-language effectful runtime

## Status

Accepted for the restricted phase-7 source-language profile.  Whole-program
inference now retains nominal constructors and patterns, local places,
assignment, mappings, proxies, matches, loops, and structured control flow.
`Solcore.Frontend.SourceTypedRuntime` executes that retained typed source with
mutable lexical cells and explicit structural fuel.  It is an additive runtime
boundary; the established Semantic Core and finite structural-runtime paths
keep rejecting forms that they cannot represent faithfully.

## Context

ADR-0366 through ADR-0368 made recursive and higher-order structural source
programs executable in a finite checked runtime table.  That table deliberately
used only Unit, Bool, Word, products, and functions.  It could not represent a
closed nominal value, a mapping, a proxy, a mutable place, or a loop transfer
without either erasing source type information or inventing a misleading Core
encoding.

The typed-source IR already has stable nominal constructor identities,
constructor instantiations, nested pattern instructions, place projections,
assignment resolutions, and explicit statement control.  Phase 7 therefore
keeps those forms intact and interprets them at a source-typed boundary rather
than widening the older Core carriers.

## Decision

### Treat constructor qualification as namespace resolution

Program signatures assign every data declaration and constructor a stable
identity.  Explicit `Type.Constructor` syntax is resolved through the data-type
namespace, and a leading-dot constructor is resolved from the expected nominal
type.  Generic constructor payload and result types are obtained from the exact
parameter substitution.  A namespace-qualified nullary constructor is also
normalized to `ExpressionForm.constructor`; it is not a general member read.

The runtime value retains the complete `DataConstructorInstantiation` and its
ordered payload.  For an external constructed argument, the safe execution
boundary reconstructs that metadata from `ProgramSignatures`, rejects forged or
stale constructor identities and substitutions, and recursively validates the
payload before entering the function body.

### Retain nested patterns and source-ordered matching

Constructor, tuple, binder, wildcard, and integer-literal patterns are retained
as a self-delimiting prefix instruction stream.  This represents nested
constructor and tuple patterns without equating one source arm with one flat
Core constructor branch.  Runtime matching tests arms in source order, binds
the first matching arm in an isolated lexical scope, and evaluates the
scrutinee once.  A match may fall through to following statements; return,
break, continue, fault, and fuel exhaustion propagate explicitly.

Inference checks duplicate binders, constructor arity and ownership, nested
expected types, and the implemented top-level exhaustiveness boundary.  The
runtime IR has one scrutinee; tuple-normalized patterns provide the retained
product form without adding a separate multi-scrutinee machine rule.

### Make local places and assignment explicit

An assignable place is rooted at one monomorphic lexical binder and carries an
ordered list of mapping-index or positional member projections.  Source
inference currently admits local roots and mapping indexes; it rejects a broad
expression left-hand side instead of relying on a later backend failure.
Simple assignment checks its right-hand side against the selected place type.
Word compound assignments and bitwise complement update the selected leaf.

Every index expression in a place is evaluated once, from left to right, before
the right-hand side.  Compound assignment snapshots the selected old leaf at
that point.  The final structural update starts from the latest root value, so
unrelated effects performed by the right-hand side are not overwritten.

### Represent mappings, proxies, and mutable closure capture directly

Mappings are source-typed runtime values with ordered finite entries.  For the
implemented runtime-equality key carriers, lookup returns the stored entry or
the supported type-directed default, and indexed assignment reconstructs the
mapping along the resolved place path.  A proxy is retained as a typed source
value; this phase does not reinterpret it as contract storage or an ABI object.

Lexical environments map stable local identities to heap locations.  Let-bound
values and parameters occupy typed cells, and closures capture locations rather
than copied values.  Consequently a closure observes later writes to a captured
local, while leaving a block discards only its local bindings and preserves heap
effects.  Named declarations and supported builtins remain callable values in
the same evaluator.

The runtime can read or structurally update a positional payload of an already
validated constructed value.  This is an internal typed-IR capability, not
source admission of arbitrary struct or object members.

### Execute structured loop and function control

`FlowOutcome` distinguishes fallthrough, return, break, continue, fault, and
fuel exhaustion.  `while` reevaluates its Bool condition before each iteration.
A `for` initializer establishes the loop scope, its condition is checked before
each iteration, and both normal fallthrough and `continue` execute the post
items before the next condition.  `break` exits the nearest loop and `return`
exits the current function or closure.  Inference rejects loop control outside
a loop and resets loop depth at a lambda boundary.

### Bound every recursive execution path

Expression evaluation, calls, statement sequencing, pattern descent, and loop
iteration are bounded by explicit fuel.  Completion, runtime fault, and
out-of-fuel retain the exact source-typed runtime state.  Fuel is a structural
depth bound: sibling computations reuse the same remaining depth rather than
sharing a total-work counter.  Public `run` also uses a finite depth while
recursively validating product, mapping, and constructor inputs.

### Preserve the older compatibility boundaries

`SourceCoreElaboration`, `SourceCoreDirectLinking`, and
`SourceRuntimeLinking` keep their explicit rejection cases for constructors,
members, proxies, indexes, assignments, general matches, loops, and loop
control.  Phase 7 does not erase those forms into Unit/product/Core store
surrogates.  The additional `SourceTypedRuntime.run` entry validates runtime
inputs against both `ProgramSignatures` and the specialization plan;
`runTrusted` is reserved for callers which have already established that
input boundary, and `run?` is only the successful-result projection.  The
specialization plan and typed IR remain trusted outputs of program checking and
the canonical worklist; `run` does not reconstruct an arbitrary supplied plan.
This boundary is invoked explicitly; it does not change
`SourceProgramExecution` backend selection or the result carrier of either
compatibility path.

Before invoking each specialization, the source-typed runtime validates its
executable metadata.  It accepts the exact solved builtin `Int` evidence owned
by an integer literal, but rejects other expression or assignment requirements,
result coercions, and indirect argument coercions.  A selected user trait
method is therefore never reinterpreted as a similarly shaped builtin
operation merely because this runtime does not yet dispatch that evidence.

This separation also leaves the existing staged evaluators unchanged.  A
nominal value, mapping, proxy, or mutation is not silently promoted into the
Unit/Bool/Word/product staged carrier.

### Use an executable-first proof boundary

Phase 7 intentionally uses low proof density.  Stable identities, exact source
types, checked substitutions, explicit control outcomes, safe runtime-input
validation, and focused positive and rejection regressions are required now.
General progress/preservation, determinism, exhaustiveness completeness,
place-update algebra, fuel monotonicity, and end-to-end source/runtime
correspondence remain separate proof work.

## Phase boundary

Roadmap phase 7 now includes:

- generic enum construction through explicit namespaces or an expected type;
- nested constructor/tuple/binder/literal matching in source order;
- nonterminal match control and explicit lexical arm scopes;
- monomorphic local assignment, Word compound assignment, and bitwise update;
- local mapping reads, defaults, indexed places, and indexed writes;
- typed proxy values without contract-storage interpretation;
- `for` and `while` with correctly scoped break, continue, and return;
- location-capturing closures which observe later local mutation; and
- source-typed completion, fault, and exhaustion under structural fuel.

Still deferred are:

- general struct/object member lookup, method dispatch, and arbitrary member
  assignment at the source boundary;
- string and comptime pattern execution, redundancy diagnostics, and complete
  recursive exhaustiveness analysis;
- contract storage layout, storage-reference proxies, external calls, ABI
  encoding/decoding, and transaction effects;
- transparent use of type aliases as nominal constructor namespaces and the
  complete alias-normalization policy;
- nominal, mapping, proxy, or mutation support in staged evaluation;
- general trait-evidence dispatch, source coercion-plan execution, and mapping
  key operations beyond the runtime's implemented structural equality;
- validated external closure inputs and closure serialization;
- automatic public entry discovery, multi-root execution, and a published
  source-runtime wire protocol; and
- broad static- and dynamic-semantics proof families.

## Verification target

The phase-7 regression boundary checks generic qualified and leading-dot enum
construction, nested constructor patterns, duplicate binders, constructor
arity and expected-type failures, tuple-normalized matches, nonterminal
matches, local and mapping-index assignment, `for`/`while`, nested
break/continue, loop-external rejection, and the lambda loop boundary.  Runtime
checks cover constructor validation, nested pattern selection, mapping default
and update behavior, once-only place-index evaluation, compound assignment,
captured-cell mutation, `continue` post execution, function return, faults, and
fuel exhaustion.  Existing Core and structural-runtime rejection tests remain
the compatibility guardrail.  The intentionally small theorem layer fixes the
primitive and proxy input-validation cases, zero-fuel exhaustion, and the exact
relationship between `run` completion and the `run?` success projection.
