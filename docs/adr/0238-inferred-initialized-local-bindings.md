# ADR-0238: Inferred initialized local bindings

- Status: Accepted for implementation
- Decision date: 2026-09-09
- Scope: Unannotated initialized lets in the existing recursive body adapter

## Primary reference and context

The canonical reference remains `argotorg/solcore-rs` at
`18fd9f75d290df0070e21ee56e0a5691f232596f`.
`crates/parser/src/parse/stmt.rs:175–188` retains an optional written type
annotation. `crates/hir-ty/src/infer/stmt.rs:64–98` creates a fresh type variable
when no annotation is written, unifies it with the initializer type, then adds
the local name. `crates/specialize/src/specialize/body.rs:272–312` processes the
initializer before extending its local environment, retaining the optional
annotation. These support initialized local inference without introducing
another syntax node, an implicit annotation, or initializer self-reference.

The current monomorphic expression adapter already infers exactly its unique
independent source type and exact Core expression. The recursive body adapter
currently requires a structural annotation despite having this information.
Its raw evaluator independently requires annotation presence. Both boundaries
must advance together to retain the existing checked/raw correspondence.

## Decision

Accept `let name = initializer; tail` in the existing recursive body checker.
Check the initializer in the original input scope, retain its inferred type and
exact Core expression, and check the original tail under the existing fresh
binding with that type. Preserve the current unused-spelling check, owner-relative
allocation, first-match caller tables, original statement/body spans and tail
order. Do not rewrite an unannotated original node into an annotated one.

Add separate `inferred` constructors to independent whole typing, exact
elaboration, raw evaluation and costed evaluation. Keep each old annotated
`binding` constructor's exact name and type. The static rule needs independent
initializer typing, not a synthesized source annotation or table membership for
the inferred type. Raw rules require only original initializer and fresh-tail
evaluations, threading actual values and both stores without type checking.

The direct raw evaluator and source-only bound accept either annotation shape
when the initializer is present. Strict execution remains the existing Core
`letE`, with initializer cost plus tail cost plus two transitions. Unused
initializers still execute. Missing initializers remain unsupported. Preserve
all existing generic checking, exact-provenance, evaluation, cost, safety,
store, owner, lookup, extension, runner and resumption theorem statements.
The old annotated-prefix adapters and successful embedding statements remain
unchanged; no full optional-result equality with those narrower adapters is claimed.

## Independent consumers and boundaries

Construct original annotated/unannotated mixed sequences, exact source typing,
Resolved lowering and manual Core paths independently of tested checker output.
Cover arbitrary depth, unique inferred types, sparse mixed-owner inputs,
first-match duplicates, nominal static types without inhabitants, and actual
typed opaque values. Test Unit, Word, Bool and nested products without flattening
or manufacturing runtime values. Preserve parameter-only entry records.

Complete parsed consumers must retain the original `none` annotation and byte
ranges. Specify exact Core, ordered values and costs externally, checking whole
entries, all bounded fuel thresholds and genuine saved-environment/continuation
checkpoints with residual execution. Migrate only obsolete unannotated-initializer
rejection claims into independent positives, preserving neighboring rejections
and explicitly renaming any source contract whose old statement becomes false.
Keep strict invalid initializers, self/forward/sibling references, ancestor
shadowing, invalid unselected arms and raw-selected/whole-check distinctions.

This is inference within the existing monomorphic initialized fragment, not
general Hindley–Milner inference, polymorphism, overload resolution, missing
initializer support, assignment or a new shadowing policy. Core/Resolved
definitions, parameter/return annotation policies, parser, diagnostics and
Core Wire does not change. Run focused/aggregate builds, full tests,
all public and consumer axiom audits, kernel-policy and whitespace checks, and independent
reviews. Keep proof/test modules under 300 lines and scratch repository-local.
