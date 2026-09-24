# ADR-0216: Static semantics of recursive typed let/return trees

- Status: Accepted
- Decision date: 2026-09-09
- Scope: A separate value-free adapter with typed declarations inside branches

## Decision

Add `TypedLetReturnTreeHasType`, `TypedLetReturnTreeElaborates` and
`elaborateTypedLetReturnTree?` for finite mixtures of annotated initialized let
prefixes and terminal explicit if/else trees. The existing typed-prefix adapter
allows declarations only before its terminal tree; this separate adapter also
allows each branch to contain its own typed prefix and further branches.

Use three independent source constructors: an existing singleton return body,
a typed binding followed by a recursive tail, and a singleton explicit if/else
with two recursive arms. A binding retains annotation meaning, an unused name
and initializer checking in the old inputs. Only the tail sees the fresh binding.
A conditional checks its Bool condition and both complete arms in the same
original inputs, with equal result types. Keep exact source order and emit
only the existing Core `letE` and `ifE`; do not weaken an already extended tail.

Branch scopes are independent. Neither arm's declarations are visible in the
other, and an arm cannot shadow an ancestor name in this restricted adapter.
The existing owner-relative allocator is a pure function of the current scope:
both arms' first binders can therefore have the same LocalId. That is legitimate
scope-local reuse, not traversal-global uniqueness. Do not thread one branch's
allocation through its sibling, invent owners or add a global counter. Initial
input IDs are distinct as required by `LocalTypeInputs`; initial spellings need
no new duplicate-free premise.

The total checker recurses on original block size, not outer statement count:
an if's child block may contain an arbitrarily long prefix. It has no supplied
fuel, depth limit, flattened syntax or dependence on runtime values. Independent
typing and exact elaboration constructors do not use checker-success premises.

## Proof boundary

Prove exact successful child decomposition, checker soundness/completeness,
independent whole-typing equivalences, actual open Core typing, exact Core/type
uniqueness and rejection characterization. Static nominal inputs remain useful
without constructing runtime inhabitants. Same-typed alternative Core is not
source provenance, and every unselected initializer and branch remains checked.

Embed every old return-tree and typed-prefix success with its identical Core
and type. Preserve the complete Option on singleton return shapes. Do not claim
full optional equality with old conditional or prefix checkers: a branch-local
declaration is deliberately a new success. Existing body adapters and the
runtime entries integrated in ADR-0215 remain unchanged in this static unit.

## Boundaries and validation

No evaluation/cost judgment, runner, fuel bound, resumption or entry integration
is added here. Annotation inference, missing initializers, shadowing, source
calls, mutation, loops, fallthrough, if followed by additional statements,
early-return unwinding and separate nested-block wrappers remain outside this
adapter. Rejection does not assert a language-wide binding or validity policy.
No parser, Core, Resolved or Wire change is required.

Use independent arbitrary-depth alternating let/if derivations, nominal static
types, noncommutative branch initializers, exact extended variable positions and
same-ID sibling binders. Prove sibling isolation and whole checking of deep
invalid unselected children. Parse complete original declarations with positive
and negative scope/annotation/control-flow fixtures; retain old-adapter rejection
and exact old successes without supplying nominal values.

Audit all new public contracts and consumers, exact registration, standard
axioms and acyclic body-to-entry dependency direction. Run focused/aggregate
builds, parsed execution, full tests, and kernel-policy and whitespace checks. Keep
proof files below 300 lines, commits small, diagnostics paused and scratch in
the repository.
