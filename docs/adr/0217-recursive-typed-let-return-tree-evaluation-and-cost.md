# ADR-0217: Evaluation and cost of recursive typed let/return trees

- Status: Accepted
- Decision date: 2026-09-09
- Scope: Independent selected-path semantics and exact checked Core paths

## Decision

Complement ADR-0216 with independent raw and cost judgments for its original
recursive syntax. A singleton reuses the existing return-body path. A typed,
initialized binding evaluates its initializer once in the old name table and
environment, then evaluates its tail with the obtained value and the fresh
name/ID prepended. An explicit conditional evaluates the Bool condition and
only its selected recursive arm in the original scope. Keep initial, intermediate
and final stores explicit. Bindings and conditionals each add their two existing
Core transitions to the evaluated child costs; unselected arms contribute none.
Unused initializers still execute strictly and contribute their full cost.

Raw rules require the original annotation/initializer syntax but no annotation
meaning, unused-name, whole acceptance, runtime typing or store-validity premise.
They do not establish a source shadowing policy. Repeated raw names and rejected
annotation meanings can still have paths, and an invalid unselected child need
not prevent a raw path. The static checker continues to check every written
initializer and both arms before any checked-Core correspondence applies.

Choose each raw binder with `freshLocalId owner (table.map Prod.snd)`, relative
to its current name scope rather than an arbitrary inconsistent environment.
Reuse `LocalTypeInputs.names_ids` to match the static allocator. Selected arms
start from the same original inputs as their static counterparts; no sibling
allocation, value or local escapes into another arm. No new identities, second
reversal, weakening or Core primitive is introduced.

Prove raw unchanged-store and value determinism laws, erasure and existence of
costs, positive costs and value/store/cost uniqueness. Independent whole typing
with an actual aligned, typed environment separately gives evaluation existence
and preservation of the result type. Only initializer result typing justifies
an extended environment; static nominal types do not provide actual inhabitants.
Opaque cell references and captured closures may be returned without allocation
or invocation.

Accepted whole elaboration and aligned environment IDs suffice for evaluation
iff with the exact returned Core; alignment alone implies neither runtime typing
nor source acceptance. Prove the exact-cost Core path under any retained original
continuation and specialize it to an empty continuation. Reuse existing let and
conditional step composition. The endpoint retains pending frames rather than
executing or unwinding them: an incompatible frame may fault even at zero fuel,
so arbitrary-continuation paths are not unconditional exhaustion guarantees.

Embed every old raw terminal-tree and outer-prefix path and cost without adding
typing or acceptance assumptions. Preserve the same original body, owner where
present, tables, environment, value, stores and cost.

## Boundaries and validation

No parser, Core, Resolved, Wire or existing adapter/entry policy change. No new
body runner, source fuel bound, resumption or function-entry integration in this
unit. Missing initializers, inferred annotations, source calls, mutation, loops,
fallthrough, extra statements after if and general early return remain outside
the checked profile.

Use independent arbitrary-depth source paths, actual parsed typed arguments,
noncommutative old-scope initializers, different selected costs, unused work,
opaque values and distinct stores. Contrast raw success with whole rejection,
missing runtime initializer values, aligned but untyped environments and
misaligned IDs. Check exact paths with empty, safe pending and incompatible
continuations. Audit every public contract and consumer, standard axioms,
registration/dependency direction, focused and aggregate builds, parsed execution,
full tests, and kernel-policy and whitespace checks. Keep proof files below 300
lines, commits small, diagnostics paused and scratch inside the repository.
