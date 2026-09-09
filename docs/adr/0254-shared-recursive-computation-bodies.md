# ADR-0254: Shared mixed bodies with recursive computation children

Status: Accepted
Date: 2026-09-09

## Context

ADR-0253 provides exact recursive single-argument calls and grouping, but the
mixed bodies and explicit entries of ADR-0251/0252 deliberately still use the
nonrecursive child. Integrating every subsequent expression profile by copying
the seven static and eight raw body cases would duplicate the same scope,
discard and control-flow proofs.

Keep the original syntax, names, positional contexts, fresh allocator, Core
and stores concrete. Abstract only the child expression operations and
judgments. Old definitions, signatures and endpoint acceptance stay frozen.
This is not a claim that unsupported syntax is rejected by the full language.

The primary reference remains Rust commit
`18fd9f75d290df0070e21ee56e0a5691f232596f`, especially
`crates/hir-ty/src/infer/stmt.rs` for initializer-before-binding, ordered
statements, return annotations and Bool guards. Body syntax/policy is unchanged
from ADR-0251. Source lambda generation remains separate: expected Function
checking, Core type well-formedness and literal capture insertion require
different contracts.

## Decision

Add a shared mixed-return-tree engine. The executable checker receives only
a child checker; independent body typing receives only a child typing relation;
independent exact elaboration receives only a child elaboration relation.
Raw evaluation receives only a child raw relation and cost evaluation only a
child cost relation. Do not bundle checkers, typing, runtime worlds or laws
into parameters of either raw definition.

The static body cases remain bare return, expression return, terminal block,
annotated/inferred fresh let, strict discard and terminal if/else. Preserve
original nodes/spans, statement order and branch bodies. A named initializer
runs in the old scope; only the original tail sees its fresh binding.
Strict discard does not add a source identity: it emits a Core let with the
complete tail weakened at zero. Annotation meanings and no-shadowing checks
are static only. Recursion decreases the original body size.

Raw/cost body cases preserve every actual intermediate store and bound value,
with only the selected conditional arm evaluated. Fresh IDs come from the
original name table and owner, not environment length or a foreign maximum.
Bare return costs one; expression and terminal block add no cost; let, discard
and conditional add two transitions. Raw success may exist when an unselected
written subtree prevents checking; no global source-validity premise is added.

Pass only necessary child laws to each shared theorem, quantified over all
caller tables/contexts/environments/stores so they remain available after
fresh binding. Static laws need no dynamic insertion. Runtime correspondence
needs same ordered IDs, not typed actual values or an allocated store.

## Whole-tail insertion

A separate `ComputationBodyFragment F` has unit, leaf, let and if cases.
An explicit unit case does not require arbitrary child predicates to contain
bare return. Leaves use the supplied child predicate F; enclosing lets and
conditionals are closed recursively. This differs from ADR-0253's expression
fragment, which alone cannot cover a mixed tail.

From child weakening, literal raw insertion and paired uniform-cost paths,
prove their whole-fragment counterparts. A let extends the retained prefix
with its actual bound value and increases the cutoff; actual called bodies
and captures are never reconstructed from type erasure. Cost is chosen before
every continuation. Intermediate checkpoints need not be equal, and a return
with pending frames is not necessarily a final or safe machine state.

## Concrete integration and contracts

Specialize the shared checker and four independent relations to ADR-0253 in
`RecursiveComputationReturnTree`. These five definitions are data/operation
specializations, not a parallel family of proof aliases. Consumers must apply
the shared laws to actual ADR-0253 child proofs. Conditional generic laws alone
do not establish the concrete recursive-body boundary.

Publish twelve shared proof kernels: three static laws (checker iff, typing
iff elaboration, Core typing), two raw laws (cost existence iff and joint
determinism), three execution laws (raw/Core iff, supplied-cost paths before
any continuation, exact closed-path cost iff), and four fragment laws
(weakening, source membership, raw insertion iff, paired paths).
Add two one-way old-body elaboration/cost embeddings retaining all indices.
The old and generic inductives are not definitionally identical. No new
whole-function entry, runner, fuel/safety/None aliases or source bound is added.

## Validation

Keep definition/proof/consumer files below 300 lines and separate commits.
Validate independent original syntax and static/raw certificates against
fixed Core/value/store/cost expectations: recursive call initializers, typed
and inferred bindings, discards under binders, effectful call guards, terminal
blocks, computed/returned callables, nominal value-free contexts and gates.
Test original fresh IDs, first-match lookup and exact values/captures, including
same-typed alternate values and untyped inserted slots. Exercise every new
kernel with concrete recursive children and retain old nested-body rejection.
Also compare the generic engine instantiated with the old child to the old
successful/failed checker fixtures without changing the old endpoint.

Run focused and aggregate builds, full tests, all public/consumer standard
axiom audits, policy/metadata/whitespace checks and independent reviews.
The generic engine reduces future duplication, not the initial proof effort.
General early returns, recursive operators, generated source closures, global
functions, whole-entry integration, unfuelled execution and arbitrary-store
safety remain outside this unit.
