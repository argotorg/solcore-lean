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
  calls, patterns, places, and retained coercion paths independently of source
  inference and trait search.
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
- Define fuel-free, mutually inductive successful big-step relations for every
  retained expression and statement form, left-to-right expression vectors,
  calls, function bodies, assignments, matches, `for` headers, and loops.
  Recursion and iteration are represented by finite derivation trees.
- Define positive fault judgments for retained lookup, evidence, operand,
  place, call, pattern, assignment, control, and staging-boundary failures,
  with explicit left-to-right propagation and exact prefix heaps. These
  judgments are not a total complement of successful evaluation.
- Prove structural substitution preserves the mutually recursive static
  judgments and their requirement/evidence dependencies. Compose deep dynamic
  preservation through expressions, statements, loops, instantiated body
  calls, and whole-program entry for successful derivations in closed runtime
  contexts.

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
reduction, not progress or fault totality. Likewise, function types retain a
packed parameter type rather than source arity, so differently shaped argument
lists can share a type; indirect application retains and checks arity metadata
and may produce an explicit arity fault in that case.

## Verification target

Focused examples must exercise static whole-program admission, representative
successful and faulting dynamic rules, evidence/coercion closure, static
substitution, mutation and pattern operations, stage classification,
materialization/frontend correspondence, and program-level preservation. The
aggregate build and tests, semantic-kernel policy scan, metadata validation,
axiom inspection, and diff hygiene remain the acceptance boundary.
