# ADR-0170: Explicit restricted runtime function entry

- Status: Accepted
- Decision date: 2026-09-08
- Scope: composition of canonical parameters, return contracts, and single-return bodies

## Decision

Provide a restricted entry for an explicitly supplied canonical `FunctionDecl`,
caller-owned declaration identity, explicit type-name table, and structurally
typed runtime arguments. Prepare the existing parameter input bundle, check the
single-return body, and require its inferred type to equal the declared return
contract. Execute the exact prepared Core in the prepared runtime environment.
No function lookup, caller continuation, argument expression evaluation, global
declaration collection, or full program semantics is introduced.

The header profile has no generic parameters, where clause, public marker, or
payable marker. An absent return clause denotes Unit, as specified by the
canonical syntax. An explicit clause must contain exactly one type expression
accepted by the existing explicit type-name adapter. Empty and multiple return
lists are outside this entry, not declared invalid syntax: the canonical parser
accepts `returns ()`, and this decision does not choose a general tuple or
multiple-return policy. A named alias may denote any existing Core type,
including Unit, cell references, or function types; no spellings are reserved.

Reuse the existing exact runtime parameter binding relation, including arity,
type meaning, unique spellings, source-order identities, and reversed runtime
rows. The caller supplies the declaration identity; it is not inferred from
the function name or span, and no global uniqueness is claimed.

## Independent preparation and meaning

Define independent return-clause and header judgments from canonical syntax
and explicit type-name meaning. Define a two-rule exact body elaboration
judgment: bare return maps to Unit Core/Unit type; expression return uses the
existing independent source resolution, Resolved lowering, and Resolved typing
judgments. Type agreement alone is insufficient: a different Core expression
of the same type must not satisfy this exact preparation boundary.

The prepared record contains inputs, exact Core, and return type. An independent
preparation relation combines the header, runtime parameter binding, and exact
body elaboration. Its premises must not invoke the new preparation/checking
functions. Prove exact success iff this relation, failure iff no preparation,
uniqueness, and projection provenance. The executable adapter must retain the
Core actually returned by body elaboration rather than re-create an expected
Core from typing evidence.

Keep a whole-entry typing/contract judgment distinct from existing body-only
typing. In particular, a Word body with a Bool return annotation continues to
check as Word at the body-only endpoint but is rejected at the new entry.
Unsupported headers, argument bindings, body shapes, and all written expression
children still prevent entry preparation; skipped execution does not weaken
whole checking.

## Execution boundary

Use a checked-entry source cost relation combining the independent complete
entry contract with existing independent return-body cost. Existing raw body
evaluation and cost remain unchanged. The entry adds no Core transitions:
bare return costs one, and expression return retains its exact body cost.
This is an explicit external entry convention, not a function-call cost model.

Prove fixed-fuel completion and exhaustion from that exact source cost, returned
value typing, store preservation, determinism, sufficient fuel, and fault
exclusion. State safety only for successful preparation or its independent
relation: a manually assembled prepared record may contain arbitrary Core and
does not receive unconditional safety. Returning a structurally typed cell
reference does not establish its allocation; returning a closure does not call it.

## Validation

Use independent proof consumers and actual fully parsed declarations. Cover
absent/explicit Unit, mismatched return contracts, ordered typed parameters,
conditional and bitwise bodies, exact checked Core and fuel-zero suspended
states, nonempty stores, wrong arity/types/names, unsupported headers and body
shapes, empty/multiple return lists, and skipped unresolved branches. Test
parseable contract modifiers using contract-position parsing or canonical ASTs.

Audit every public declaration, register the public boundary, run focused and
aggregate builds and full tests, and keep new proof files below 300 lines.
Do not change diagnostic proofs, parser behavior, Core evaluation, or wire data.
