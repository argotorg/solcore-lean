# ADR-0378: Declarative resolved-source static, dynamic, and staging semantics

## Status

Accepted for the resolved, occurrence-addressed source carrier. This decision
does not specify raw-source name/module resolution, make an executable frontend
pass normative, or establish whole-language compiler correctness.

## Context

ADR-0377 established independent contexts, occurrence lookup, exact generic
instantiation, and trait-evidence validity, but deliberately stopped before
whole-expression and whole-program semantics. The executable frontend and its
three backends cover a useful source fragment, yet successful execution by one
of those algorithms is not an adequate definition of the source language.

The retained typed source carrier already records stable declaration, local,
occurrence, requirement, constructor, trait, and implementation identities.
It is suitable as the first proof-facing carrier provided that it remains
forgeable and that independent judgments validate its graph, ownership,
catalog, typing, evidence, and staging data.

## Decision

Extend `Solcore.SourceSemantics` into a declarative specification of the
resolved carrier in three layers.

### Static semantics

- Validate flexible type variables, rigid declaration parameters, nominal
  applications, schemes, predicates, binders, literals, operator profiles,
  calls, patterns, places, and retained coercion paths without taking
  successful source inference or trait search as a premise.
- Give every resolved declaration body a body-wide residual-inference scope.
  `TypeAdmissible` admits the free inference variables retained by occurrences
  in that scope. Keep it distinct from the lexical `typeVariables` added by
  `withTypeVariables` only while checking a generalized initializer; nested
  initializers inherit those lexical variables, and the body-wide residual
  scope does not itself enlarge the generalization barrier.
- Admit rank-1 generalized initialized locals with `SchemeGeneralizes`. Its
  barrier is a conservative whole-body approximation of the executable
  frontend's point-in-time policy: lexical initializer variables, preceding
  local schemes, and the complete retained requirement ledger block
  generalization. A later requirement in a forgeable body can therefore block
  more variables than were visible to frontend inference at that source point.
  The proposition does not assume frontend success, but its policy and pure
  predicate-variable projection are not claimed to be implementation-
  independent. Catalog signatures and the replacement ranges accepted by
  `Valid` retain closed `TypeWellFormed` types; static retained occurrences use
  the broader `TypeAdmissible` and `Admissible` judgments.
- Require a closed, reachable, acyclic occurrence graph; declaration-owned,
  unique local identities; and exact ownership of the solved-requirement
  ledger.
- Define mutually inductive typing for every retained expression, statement,
  `for` item, match case, statement sequence, and declaration root form.
  Control summaries include return, break, continue, ordinary fallthrough, and
  the final semicolon-free expression convention.
- Define forgeable semantic function and implementation-method bodies and a
  whole-program judgment. Catalog well-formedness checks source types,
  predicates, trait/implementation method agreement, identity uniqueness, and
  exact body coverage.

### Generic instantiation and dynamic semantics

- Define `StructuralSubstitution` as the syntax-directed action of a rigid-
  parameter substitution over every retained typed-source and evidence field.
  It performs no inference, specialization discovery, stage analysis,
  worklist construction, or execution.
- Keep the existing frontend substitution helper non-normative.
  `SubstitutionCorrespondence` proves explicit equations between
  `StructuralSubstitution` and `Frontend.SourceSpecialization` rather than
  using successful specialization as a semantic premise.
- Define independent mathematical values, lexical environments, typed heaps,
  runtime evidence environments, defaults, primitive operations, patterns,
  mutable places, and coercion execution. Closures retain typed occurrence
  graphs and captured locations; generic calls and selected trait/coercion
  methods invoke structurally instantiated source bodies with closed evidence.
- Keep instantiated runtime body contexts free of rigid declaration parameters
  and lexical generalized-initializer variables, but deliberately
  residual-open. A closure may retain code with symbolic residual occurrence
  types, and a proxy value may retain its symbolic residual inner type.
- Require closed `DeclarationInstantiation.Valid` or
  `DataConstructorInstantiation.Valid` evidence for every successful dynamic
  declaration reference, direct call, or constructor occurrence. Static typing
  may use the broader `Admissible` judgments, but the successful runtime rules
  do not treat a residual rigid-parameter replacement as an executable generic
  instantiation.
- Define fuel-free, mutually inductive successful big-step relations for every
  retained expression and statement form, left-to-right expression vectors,
  calls, function bodies, assignments, matches, `for` headers, and loops.
  Recursion and iteration are represented by finite derivation trees.
- Define positive fault judgments for retained lookup, evidence, operand,
  place, call, pattern, assignment, control, and staging-boundary failures,
  with explicit left-to-right propagation and exact prefix heaps. These
  judgments are not a total complement of successful evaluation.
- Keep successful local allocation monomorphic at the current runtime boundary.
  A generalized local binder has the explicit
  `unsupportedPolymorphicBinder` fault instead of being silently treated as a
  monomorphic heap cell. Static rank-1 let-polymorphism is therefore specified
  compositionally, while runtime instantiation of generalized local values is
  an explicit deferred feature.
- Prove structural substitution preserves the mutually recursive static
  judgments and their requirement/evidence dependencies. Compose deep dynamic
  preservation through expressions, statements, loops, instantiated body
  calls, and whole-program entry for successful derivations in runtime contexts
  whose rigid and lexical flexible binders are closed while residual admission
  remains open.

### Staging and materialization

- Define the independent `comptime`/`runtime`/`deferred` stage domain,
  flow-insensitive mutation deferral, scope-aware classification of every
  expression and statement form, and whole-program staging admission.
- Define an independent closed materialized-value carrier for Unit, Bool, Word,
  and products. Materialization validates heap, local-value, parameter, and
  dictionary boundaries and gives conditionals selected-branch-only evaluation
  premises.
- Connect materialized values to `Frontend.SourceStagedValue` through the
  explicit `FrontendValueRepresents` relation and prove existence, uniqueness,
  and type agreement. The compile-time materialization judgment remains
  parameterized by an ambient expression-evaluation relation; it does not make
  an executable staged evaluator authoritative.

These judgments describe the meaning and admission of a forgeable resolved
program. Executable algorithms may be related to them only by separate
soundness or completeness theorems.

## Proof boundary

The tranche includes structural functionality and preservation lemmas for
lookup, packing, defaults, primitives, mappings, heap allocation/update,
pattern bindings, places, evidence closure, and materialization. It also proves
structural substitution of the complete static derivation and successful
whole-language subject reduction, plus selected correspondence facts at
explicit frontend boundaries, including structural substitution equations and
staged-value representation.

Here `HeapWellTyped` states recursive agreement between initialized values and
their cell annotations. It does not by itself prove formation of an
uninitialized cell annotation, an empty mapping's key/value annotations, or a
proxy's inner annotation; reachable program-produced annotations are governed
by the accompanying static derivation.

It does **not** claim:

- declarative raw-source parsing, module/import lookup, or name resolution;
- source-checker, stage-analyzer, specializer, evaluator, or backend
  soundness/completeness for the whole language;
- trait overlap coherence or completeness of executable class resolution;
- a complete relation for semantic faults or rejected/stuck executions;
- progress, determinism, or termination; or
- correctness of lowering to Semantic Core or either source runtime.

In particular, the dynamic relations specify successful derivations. The
`SemanticFault` carrier and fault judgments name intended failure categories
and propagate them, but are not a fault-complete evaluation semantics. For
example, a statically well-typed absent mapping lookup can remain stuck when
its value type has no canonical `DefaultValue`. The preservation theorem is
therefore conditional on an actual successful derivation; it proves subject
reduction, not progress or fault totality. A residual generic global reference
or direct call can also be statically `Admissible` but have no successful
dynamic derivation when its instantiation lacks a closed `Valid` witness; no
fault rule is promised for that case. Likewise, function types retain a packed
parameter type rather than source arity, so differently shaped argument lists
can share a type; indirect application retains and checks arity metadata and
may produce an explicit arity fault in that case.
Likewise, a statically admitted generalized local cannot currently have a
successful `StatementExecutes` or `ForItemExecutes` allocation derivation: the
successful rules require an empty quantified-variable list and the positive
fault relation reports `unsupportedPolymorphicBinder`. Whole-language
preservation makes no claim that generalized local values execute.

## Verification target

Focused examples must exercise static whole-program admission, representative
successful and faulting dynamic rules, evidence/coercion closure, static
substitution, mutation and pattern operations, stage classification,
materialization/frontend correspondence, and program-level preservation. The
aggregate build and tests, semantic-kernel policy scan, metadata validation,
axiom inspection, and diff hygiene remain the acceptance boundary.
