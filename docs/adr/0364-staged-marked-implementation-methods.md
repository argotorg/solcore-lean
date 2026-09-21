# ADR-0364: Staged marked implementation methods

## Status

Accepted for an evidence-selected implementation method at the root of a
Core-representable staged coercion or required unary/binary operation.  The
validated trait and implementation method may mark parameters and the result
as `comptime`; those markers are erased only after closed staged operands have
been supplied.  Ordinary runtime evidence execution continues to reject the
same marked method contract.  This completes roadmap phase 4,
evidence-aware staging.

## Context

Function-marker metadata already survives signature resolution,
implementation conformance, executable-method checking, specialization, and
typed source.  ADR-0362 and ADR-0363 nevertheless used the ordinary detached
method elaborator, which rejected a method as soon as any parameter or its
result was marked.  Consequently an unmarked `Add.add` or `Coerce.coerce`
could execute during staging, while an otherwise identical trait contract
that stated its compile-time intent explicitly could not.

Removing that rejection globally would be unsound for the current boundary.
Runtime operator and coercion lowering has no authority to erase a marked
result, and a runtime-dependent value must never satisfy a marked parameter.
The permission therefore has to belong to the exact staged evidence operation,
not to detached method linking in general.

## Decision

### Admit only the selected staged method root

Detached method elaboration now takes an internal root-contract permission.
The staged coercion, required-unary, and required-binary adapters enable it for
the one method selected by their already validated evidence plan.  At that
point every operand is a closed `SourceStagedValue.Value`, its source and Core
type have been checked, and the result will cross back only through the staged
carrier boundary.

The ordinary runtime adapters keep the permission disabled.  They continue to
return `detachedComptimeUnsupported` with the exact parameter-marker vector and
result marker.  Thus enabling a marked staged method does not weaken runtime
call boundaries or turn marker metadata into documentation-only annotations.

### Keep nested expansion conservative

The permission is not inherited.  Direct function calls and further
implementation methods reached while lowering the selected method receive the
ordinary unmarked contract gate.  Existing call-metadata validation,
assumption evidence, cycle detection, and decreasing link fuel are unchanged.
This admits the intended selected root without recursively declaring every
reachable marked declaration safe for compile-time execution.

### Retain all method and execution checks

Marker erasure does not bypass trait/implementation conformance.
`ExecutableImplMethods` defensively rechecks the trait method's parameter and
result markers against the implementation method before exposing the checked
specialization.  It also retains name, arity, type, generic-substitution, and
predicate/evidence checks.

After root elaboration, ADR-0362/0363's execution boundary is unchanged: the
capture-free closed resolved application is independently lowered and typed,
runs under structural fuel in an empty store, must leave that store empty, and
must return Unit, Bool, Word, or a supported product of those values.  Marker
permission cannot manufacture a value or suppress a method fault.

## Phase boundary

The completed evidence-aware staging phase includes:

- proof-only signature-predicate forwarding through partially generic staged
  calls;
- exact staged coercion paths using selected `Coerce.coerce` methods;
- exact required unary/binary dispatch using selected trait/impl methods; and
- staged-only execution of those selected methods when their validated
  contract carries `comptime` parameter or result markers.

Still deferred are:

- marked direct calls or marked method dispatch reached from inside the
  selected implementation method;
- arbitrary trait methods outside the supported operator/coercion profiles;
- effects, store mutation, indirect calls, nominal or unsupported carriers;
- value-indexed specialization and memoization;
- staged recursion, including selected-branch recursion and compile-time
  Fibonacci; and
- broad proof hardening and a public source Oracle.

Staged recursion is the next roadmap phase.

## Verification target

One end-to-end program declares both `Add.add` parameters and its result as
`comptime`; staged generic dispatch executes the selected implementation and
materializes its nonstandard result `94`.  A second program shape executes a
marked `Coerce<Bool, Word>.coerce` method and materializes `93`.  Both preserve
a nonempty caller store.

The same methods are also selected from ordinary runtime Add and coercion
paths.  Both preparations must still fail with
`detachedComptimeUnsupported`, including the exact `[true, true]` or `[true]`
parameter markers and marked result.  Separate executable-method regressions
reject independently tampered parameter and result markers.
