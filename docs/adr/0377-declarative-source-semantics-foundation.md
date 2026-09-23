# ADR-0377: Declarative source-semantics foundation

## Status

Accepted as the foundation of the source-level formal semantics and extended
by [ADR-0378](0378-declarative-resolved-source-semantics.md). This decision
adds independent judgments over the current resolved, occurrence-addressed
source carrier. It does not make the source checker, specializer, compiler
facade, or any runtime backend normative by itself.

## Context

The canonical source pipeline is executable end to end for a documented
fragment.  Whole-program loading, type inference, trait search, overload
selection, specialization, and three execution backends are implemented.
Most of that behavior is currently specified by the algorithms themselves.

`Solcore.Resolved.HasType` and `Solcore.Resolved.Evaluates` provide independent
judgments, checker correspondence, and evaluation correspondence for a small
monomorphic local-expression language.  They deliberately exclude modules,
source generics, traits, closures, mutation, statements, and staging.  They
therefore cannot serve as the static or dynamic semantics of the canonical
source language.

The specification charter gives versioned declarative Lean definitions higher
authority than executable definitions.  Extending compiler preservation proofs
without first defining source judgments would verify implementations against
their own annotated carriers rather than state the source language rules.

## Decision

Create `Solcore.SourceSemantics` as the independent source-semantics namespace.
The initial carrier is the resolved occurrence-addressed source representation:
names, overloads, constructors, and trait obligations have stable identities,
but its records remain forgeable and are not assumed to have come from the
checker.

The first tranche defines:

1. semantic global and local contexts without inference fuel or compiler
   options;
2. declarative membership and uniqueness conditions for expression and
   statement occurrences, plus correspondence with executable lookup;
3. exact source-scheme and declaration-parameter instantiation relations;
4. exact simultaneous implementation-head instantiation and algorithm-
   independent validity of trait and assumption evidence, including assumptions
   at nested where-premise depth;
5. an explicit representation bridge for evidence retained by the executable
   frontend; and
6. resolved-reference raw typing based on those judgments.

No judgment may use successful source inference, specialization, compilation,
or execution as a premise.  Executable algorithms are connected later by
separate soundness and completeness theorems.  Search depth, staging fuel,
specialization budgets, and runtime fuel are implementation inputs and do not
appear in the declarative judgments.

The resolved carrier is reused initially to avoid defining a second source AST.
Carrier well-formedness must nevertheless establish occurrence uniqueness,
owner agreement, valid roots and edges, lexical binding, and catalog validity
before whole-expression or whole-body typing can rely on it.  Reusing a data
carrier does not grant semantic authority to the checker which currently
constructs it.

## Proof boundary

This tranche must establish, without forbidden trust escapes:

- exact instantiation substitutes every quantified or rigid parameter once and
  substitutes no unrelated variable;
- a valid declaration instantiation agrees with one catalog signature in its
  type, predicates, and staging metadata;
- valid implementation evidence names a catalog rule whose instantiated head
  is the goal and whose evidence recursively validates every instantiated
  premise;
- assumption evidence names an explicit contextual assumption;
- occurrence-table lookup agrees with declarative membership when occurrence
  identities are unique; and
- reference raw typing covers locals, declarations, compiler-provided
  functions, and Boolean constants without invoking source inference.

## Deferred boundary

ADR-0378 subsequently adds whole-expression, pattern, statement, declaration-
body, implementation-method, and whole-program typing; explicit coercion and
literal judgments; structural generic substitution; successful source
big-step dynamics; positive fault propagation; successful-evaluation subject
reduction; independent staging classification; and the materialization
boundary. The following remain outside this foundation and ADR-0378:

- declarative module/import lookup and raw-source-to-resolved resolution;
- trait-catalog overlap/coherence and soundness/completeness of the executable
  implementation-head matcher against declarative instantiation;
- soundness and completeness of the source checker, stage analyzer,
  specializer, and executable evaluators against the declarative judgments;
- total or deterministic fault/rejection semantics; and
- whole-evaluator progress, determinism, termination, and backend
  correspondence derived from the source judgments.

`Solcore.SourceSemantics` therefore specifies the resolved carrier's static,
successful dynamic, and staging layers, but is not a claim that the complete
raw source language or every failing execution has been formalized. Semantic
Core and Oracle v5 retain their existing public meanings.

## Verification target

Focused examples exercise polymorphic local instantiation, exact generic
declaration instantiation, occurrence lookup, nested assumption evidence,
retained-evidence representation, and resolved-reference raw typing. The
additional ADR-0378 modules have their own focused examples. The aggregate
build and test suite, semantic-kernel audit, metadata validation, and diff
hygiene remain the acceptance boundary.
