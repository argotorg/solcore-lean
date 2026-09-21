# ADR-0356: Canonical comptime function contracts

## Status

Implemented for resolved named-function signatures, checked typed source,
specialization, direct-call metadata, and the current executable whole-program
boundary.  Parameter and result staging markers are canonical metadata distinct
from ordinary semantic types.

## Context

ADR-0355 added a deliberately provisional direct-call evaluator for closed
bare-`integer` functions.  Raw syntax already retained the optional marker in
`comptime value: T`, but signature construction discarded it.  A written
`returns (comptime<T>)` instead became the structural type `Ty.comptime T`; a
body producing `T` therefore failed unification before staging could use the
annotation.

The pinned reference revision
`argotorg/solcore@1d490d8bb5f374356f06e0720655496482eb1fb4` keeps these concerns
separate.  Each parameter owns `paramComptime`, a signature owns
`sigRetComptime`, and the ordinary function type contains only the bare
parameter and result types.  Specialization copies the marker bits rather than
substituting them.  An explicitly comptime parameter rejects a definitely
runtime actual, while a marked result is comptime only when all actuals are
comptime.  The backend may still partially evaluate suitable unmarked pure
calls, so the marker is a contract rather than the only source of partial
evaluation authority.

Lean's surface syntax permits a list of return type expressions, unlike the
pinned reference's single optional return type plus one result bit.  This ADR
therefore needs an explicit canonical boundary instead of deriving staging
from every structural occurrence of `Ty.comptime`.

## Decision

### Keep parameter rows and a separate result bit

`ProgramFunctionParameter` stores a parameter's source-order name, resolved
bare type, and `comptime` bit in one row.  Top-level function, trait-method, and
implementation-method signatures retain lists of those rows.  Compatibility
projections expose the previous parameter-name and parameter-type lists, plus
the marker list.

Every named-function signature also retains `returnComptime : Bool`.  For the
one accepted marked-result surface form,

```text
returns (comptime<T>)
```

signature construction removes exactly the outer wrapper and records

```text
returnTypes = [T]
returnComptime = true
```

The declaration scheme, body expectation, selected call type, and expression
node type all use bare `T`.  This avoids a dual representation in which a flag
and `Ty.comptime T` describe the same contract, and it lets ordinary type
inference check the body against `T`.

An outer comptime wrapper among multiple result items is rejected rather than
collapsed into one ambiguous function bit.  A directly nested
`comptime<comptime<T>>` result is also rejected.  Structural comptime types in
other type positions remain ordinary type syntax and do not imply this
function-level result contract.

Trait and implementation methods use the same normalization.  Method
conformance requires parameter marker vectors and the result marker to agree in
addition to the existing types and predicates.  A synthetic function view of
an implementation method preserves the same rows and result bit.

### Carry the contract through typed source and specialization

Each declaration input `TypedBinder` retains its parameter marker.
`CheckedFunction` retains the result marker.  A selected
`DeclarationInstantiation` copies both the parameter vector and result bit, so
the call node and its declaration-reference node remain self-contained and can
be checked without repeating name resolution.

Type substitution changes only types.  Binder record updates, checked-function
specialization, and declaration-instantiation substitution preserve staging
metadata unchanged.  The specialization boundary compares the canonical
signature marker vector with the checked input binders and compares the
signature result bit with the checked function.  The worklist and direct linker
then compare every call occurrence's retained marker metadata with the
canonical specialized callee.  A forged, shortened, reordered, or flipped
profile is rejected independently of function-type equality.

### Enforce the current executable boundary

A runtime seed may not expose a marked parameter as an external Core input or a
marked result as an ordinary Core result.  A runtime direct call may pass an
argument proved closed to a marked parameter, but an actual that is definitely
runtime because it depends on an unmarked caller input is rejected.  This early
check is transparent through groups, unary and binary expressions,
conditionals, and tuples.  Unknown forms remain distinguishable as deferred
and reject explicitly at this final linker boundary rather than being
mislabeled runtime or entering ordinary Core lowering.

A marked result which reaches ordinary runtime call lowering is rejected.  The
existing closed integer staged-call path accepts the newly canonical marked
form and continues to validate all arguments through its closed evaluator.
ADR-0355's unmarked, pure bare-`integer` partial-evaluation path remains as an
intentional compatibility path, matching the reference's ability to partially
evaluate suitable unmarked calls.

Executable implementation methods with staging markers remain outside the
detached runtime-method profile and reject explicitly.  Their marker metadata
is nevertheless retained and checked, so a later staged-method evaluator can
extend the boundary without reconstructing lost source facts.

## Deferred boundaries

- A complete `Comptime`/`Deferred`/`Runtime` expression and local-binding
  classification, including assignments, general lets, calls, constructors,
  lambdas, and control flow, remains later.
- General staged Word, Bool, tuple, nominal, function, mapping, proxy, and
  structural `comptime<T>` values are not evaluated by this slice.
- Marked implementation-method execution, predicate-bearing or coerced staged
  calls, indirect invocation, and partially staged generic calls remain later.
- Mixed or per-item comptime metadata for multiple returns needs a surface and
  semantic design beyond the pinned single-bit contract.
- Recursive staged execution, selected-branch recursion, memoization, and
  compile-time Fibonacci remain outside the eager acyclic evaluator.
- Broad soundness, completeness, ownership, and preservation metatheory is
  deferred; the new carrier and rejection boundaries are executable and
  adversarially checked.

## Verification

Signature regressions cover ordered marked and unmarked parameters, bare result
normalization, generic function types, trait/implementation propagation,
method-marker mismatch, nested result wrappers, and marked multiple returns.
Checked-source and specialization regressions verify that a generic marked
identity retains both bits while its rigid type is substituted, and reject
signature/body marker disagreement.

Worklist tests mutate both call and reference instantiations together and
confirm that canonical callee comparison still rejects changed parameter or
result markers.  Whole-program execution covers a marked integer helper, an
unmarked ADR-0355 compatibility helper, an unmarked parameter of a marked
result function, a closed Word literal passed to a marked parameter, runtime
input rejection, deferred call-argument rejection, marked runtime-root
rejection, and marked runtime-result rejection.  The complete Lean test driver
remains green.
