# ADR-0370: Transparent type aliases and strict module visibility

## Status

Accepted for the restricted phase-8 source-frontend profile.  Type aliases are
transparent during program type resolution, constructor access follows
explicit interface visibility, and source names are found only through lexical
scope or declared imports.  Relative, library, standard-library, and external
module paths share one canonical resolver.

This remains an executable-first boundary with focused regression coverage and
low proof density.

## Context

ADR-0342 established stable whole-program declaration identities, fixed-point
public interfaces, imports, type resolution, unification, and tabled class
resolution.  ADR-0369 then retained nominal enum construction and matching in
the source-typed runtime.  Four compatibility gaps remained between those
layers:

- a parsed type alias still behaved like a distinct nominal type instead of a
  transparent synonym;
- enum declarations could cross an interface without preserving which of their
  constructors were public;
- an unimported declaration could still be reached through a whole-program or
  direct canonical-path fallback; and
- interface construction and import consumption used separate module-path
  lookup rules.

Those gaps made a successful lookup depend on unrelated modules in the
workspace and could expose constructors which the exporting module had not
published.  They also prevented expected-type constructor inference from using
an alias of an enum consistently.

## Decision

### Normalize aliases as transparent type synonyms

Resolving a type alias resolves its right-hand side in the alias declaration's
module scope, not in the use site's scope.  Generic arguments are substituted
simultaneously for the alias parameters before normalization continues.  Alias
applications are therefore transparent wherever a resolved type is required,
including nested type arguments, predicates, function signatures, and expected
types.

Alias declarations are validated eagerly while program signatures are
collected.  An unused alias with an unknown right-hand-side name, incorrect
arity, duplicate generic parameter, cycle, or exhausted expansion budget is an
error rather than latent invalid state.  Direct and mutual cycles carry an
explicit closed declaration-identity path.  The independent normalization-node
budget is shared across branches and produces a distinct diagnostic instead of
being reported as a cycle or unknown type.

An alias remains a type synonym, not a new namespace.  Consequently
`Alias.Constructor` is rejected.  A leading-dot constructor such as
`.Constructor` is accepted when its expected type normalizes through an alias
to the owning enum.  This matches the upstream distinction between type
normalization and explicit constructor qualification.

### Carry constructor visibility in public interfaces

Every public data entity records one of three constructor states: not a data
declaration, opaque data, or a visible set of constructor names.  The set is
part of fixed-point interface equality and combines monotonically.

Local bare and wildcard exports publish the data type opaquely.  A constructor
selector such as `Type(*)` or `Type(Constructor)` publishes the requested
constructors after validating ownership and spelling.  A remote wildcard
re-export preserves the source interface's constructor visibility; a named
remote bare re-export strips it to opaque data.  A selective re-export can only
narrow constructors already visible at its source and can never recover a
hidden constructor.  Repeated paths union visible subsets without weakening
the exposure already obtained from another path; an opaque duplicate neither
exposes names nor erases names already exposed.

Imports retain this visibility metadata.  Explicit and expected-type source
constructor lookup filter candidates through it, so a type may be visible while
one or all of its constructors remain inaccessible.  Operator export selectors
use the ordinary exported-name mechanism; the frontend does not maintain a
second operator-only namespace.

### Require declared visibility for program names

After lexical generics and declarations in the current module, type, trait,
value, and constructor lookup consult only bindings introduced by declared
imports.  The former no-import whole-program search is removed.  A written
canonical module path also does not bypass imports.  Adding an unrelated import
therefore cannot expose every declaration in the workspace, and two modules
with the same spelling do not become candidates unless both are imported.

Compiler intrinsics keep their existing explicitly documented lowest-priority
rules.  They are not a general source-module fallback.

### Resolve all module paths through one function

Interface construction and import processing share the same canonical module
resolver:

- an unmarked path is relative to the importing module's directory;
- a multi-component `lib.*` path starts at the current library root, while the
  bare spelling `lib` remains an ordinary relative module name;
- `std` and `std.*` address the standard library; only a multi-component path
  receives the pinned upstream-compatible local-relative interpretation when
  that standard module is absent; and
- `@library.*` addresses the named external library root when the source
  module-path form carries an external marker.

Imports and remote exports share the unmarked component resolver; export-side
qualified names have no external-marker form.  Unknown targets remain explicit
errors, and the resolver does not fall through to a global declaration search.

## Phase boundary

Roadmap phase 8 includes:

- definition-site, generic, recursively transparent alias normalization;
- explicit alias-cycle and normalization-node-budget diagnostics plus eager
  validation;
- constructor visibility across exports, re-exports, imports, explicit
  qualification, and expected-type lookup;
- strict import visibility with no global or direct canonical-name bypass; and
- one relative/`lib`/`std`/external module-path policy shared by imports and
  exports.

Still deferred are:

- nested contract namespaces and the full contract/module ownership model;
- method-local generics, higher-rank and higher-kinded types, and polymorphic
  recursion;
- coinductive trait or coercion cycles and an overlap/default policy beyond
  explicit ambiguity;
- let-polymorphic source runtime execution and general evidence dispatch;
- general struct/object member admission, storage/ABI effects, and staged
  nominal/effectful values; and
- broad resolution soundness/completeness, interface-algebra, normalization,
  and source-runtime correspondence proofs.

## Verification target

Focused regressions cover generic and nested alias substitution, definition-site
shadowing, unused invalid aliases, direct and mutual cycles, shared node-budget
exhaustion, and expected-type constructor inference through an alias while
rejecting `Alias.Constructor`.  Interface tests cover opaque, wildcard,
selective, hidden, and cyclic re-exports; constructor names cannot be regained
after being hidden.  Resolution tests cover unimported and canonical-path
rejection, explicit ambiguity, and constructor isolation between equal module
paths in different libraries.  Module-path tests cover nested relatives, bare
and multi-component `lib`, bare and multi-component `std`, the documented local
fallback for a missing multi-component standard path, external roots, and
identical import/export target selection.

The aggregate Lean build and test suite remain the acceptance boundary.  This
ADR adds no axiom, `sorry`, unsafe definition, or native decision procedure.
