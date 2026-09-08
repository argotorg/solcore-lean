# ADR-0154: Resolved local-expression semantics

- Status: Accepted
- Decision date: 2026-09-08
- Scope: internal resolved identities, local expressions, and Core elaboration

## Decision

Begin the semantic frontend with an internal, monomorphic local-expression
fragment under `Solcore.Resolved`. This is a foundation for ADR-0002's Resolved
layer, not an implementation of the complete canonical source language.

A declaration identity contains an existing `Workspace.ModuleId` and a
source-declaration index. A local identity adds a binder index within its
owning declaration. Reusing the workspace module identity retains the library
namespace: main, standard, and external modules do not become equal merely
because they share a module path. These are caller-supplied identities; this
slice does not allocate indices or prove an allocator fresh.

Ordered local tables carry identities and semantic types or values. Lookup
selects the first matching identity. This also specifies deterministic behavior
on repeated identities in an arbitrary table. It does not permit a future
resolver to conflate distinct declarations or define source spelling shadowing.
Independent lookup and position judgments fix the exact selected binding and
exclude missing or out-of-range references.

The initial resolved expression forms are unit, Boolean and Word values,
local references, already-selected Core unary and binary primitives, immutable
expression binding, and conditional selection. Primitive meanings and types
are reused from Semantic Core; this slice introduces no new primitive behavior.
Binding extends the environment only for the body, never for its initializer.
Conditional evaluation executes only its selected branch.

Elaboration replaces local identities by de Bruijn indices and preserves the
remaining structure exactly. Missing references return `none`, never a default
index. Both branches of a conditional must elaborate and type check, even
though evaluation may skip one of them. Independent resolved typing and
evaluation judgments are not abbreviations for their Core counterparts.

## Proof boundary

- Executable lookup agrees in both directions with independent first-match
  lookup and position judgments.
- Executable elaboration agrees exactly with the independent `Lowers` relation.
- Every independently typed expression has a type-preserving elaboration;
  typing also reflects from an exact Core elaboration.
- The total checker accepts exactly independently typed resolved expressions.
- Named-environment evaluation and Core evaluation agree in both directions
  for an elaborated expression, including the exact value and final store.
- Independent evaluation is deterministic and store-preserving, including
  expressions whose unselected branch cannot elaborate.
- Closed typed expressions evaluate, elaborate to executable Core, return the
  same value at every sufficiently large fuel, and cannot fault at any fuel.

The store-preservation result is the effect boundary of this fragment. No
staging judgment is claimed. Fuel is a Core evaluator resource, not source
rejection or EVM gas.

## Deliberate exclusions

This slice does not interpret numeric or string spelling, bind source `true`
or `false`, resolve source operators or type classes, or assign mutable source
`let` declarations the semantics of immutable expression binding. It has no
imports, declaration collection, closures, mutable cells, data declarations,
source type annotations, polymorphism, staging, or source-to-Resolved adapter.
The literal constructors contain semantic values after a future frontend
has performed the required interpretation and resolution.
Open local tables may carry any existing Core type or value; an opaque cell
reference or closure can be looked up, but this fragment cannot dereference,
mutate, or call it.

The new Lean umbrella is internal/additive. Oracle v1 through v5, Core Wire
v1 through v3, the canonical parser, and historical Surface interfaces retain
their existing behavior and bytes. In particular, this is not a source-text
execution endpoint or a completed source resolver.

## Validation

Public theorem dependencies are audited under the existing standard Lean
foundations. Resolved files are included in the semantic-kernel policy scan.
Regressions cover lexical binding extent, capture avoidance under distinct
identities, explicit duplicate-table behavior, unbound references, type errors,
conditional selection, and exact Core execution. Full build, test, metadata,
and kernel checks remain required.
