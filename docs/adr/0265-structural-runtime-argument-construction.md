# ADR-0265: Exact construction of structurally typed runtime arguments

- Status: Accepted for implementation
- Decision date: 2026-09-10
- Scope: Preserve actual Core values while constructing existing typed arguments

## Context and evidence

The canonical reference remains argotorg/solcore-rs at
`18fd9f75d290df0070e21ee56e0a5691f232596f`. No source syntax, lowering,
Rust execution correspondence or existing entry acceptance changes here.
ADR-0264 validates actual typed arguments and stores in one supplied world.
Its arguments already carry structural evidence, so it is intentionally not a
checker for raw Core.Value inputs. Callers still construct that evidence manually.

Core.ValueHasType checks every actual pair/selected sum payload and closure
capture. A closure also needs Core.HasType for its actual body under the
parameter followed by its captured context. ValueHasType.type_eq uniquely
determines that context from the captured values. Core.infer? already has
soundness and completeness for HasType. A raw Value.type tag alone does not
validate closure bodies or captures.

Core.ValueHasType is not the same as typing a newly constructed Expr.lambda:
it does not impose extra well-formedness on closure signature types or on
unselected sum types. Host functions have no structural typing constructor,
and constructed values cannot be typed with the current empty definitions.
Cell references are structurally typed independently of allocation.

## Decision

Add one public executable function, buildRuntimeArgument?, from Core.Value to
Option TypedRuntimeArgument. A successful record contains the literal original
value and its exact Value.type, with checked structural evidence. Add one public
exact-record iff theorem:

    buildRuntimeArgument? value = some argument ↔ argument.value = value

The right side already ranges over the existing evidence-carrying record.
Structural type uniqueness and proof irrelevance make record equality exact.
Success therefore accepts every structurally typable original value, rejects
every untypable one, and never substitutes a repaired value or unchecked tag.
No public predicate, auxiliary checker, helper, wrapper family or list API is
needed. Keep implementation helpers private in one small module.

Use a total recursive private checker over actual values and captured lists.
It may construct dependent evidence directly. Check the actual closure body
with infer? under parameterType :: captured.map Value.type and the empty
definition environment, comparing the result to its original resultType.
Traverse all actual captures including unused/nested ones. Do not evaluate the
body, invent an environment, wrap the value in Expr.lambda, or add independent
signature well-formedness checks. Preserve arbitrary selected/unselected tags
where ValueHasType permits them; reject host and constructed values exactly.
Accept structural cell references even when unallocated: allocation, complete
store validation and same-world agreement remain ADR-0264's separate boundary.

## Integration and verification

Consumers build original raw values using the new API, optionally traverse
lists without a new public adapter, and directly reuse ADR-0264's Bool/iff and
ADR-0263's existing entry safety kernel. Keep original syntax/spans/parameter
order, independent preparation, actual captures/stores and full runner results.
No existing runner is guarded, broadened or rewritten; failure is not a source
diagnostic, JSON decoding, world inference or a general source closure feature.

Cover arbitrary nested actual values/captures, exact original record round trips,
same-tag forged bodies, invalid unused captures, host/empty-definition nominal
values, valid nominal signatures/unselected alternatives and unallocated cells.
Parsed entries independently establish preparation and literal Core paths,
then use constructed evidence and same-world validation with exact effects,
costs, genuine checkpoints and contrasting raw success/fault on rejected inputs.

Keep old semantic kernels and executable definitions byte-identical. Use small
definition/proof/consumer/publication commits, independent reviews, complete
axiom, dependency, kernel-policy, EOF, and whitespace audits and focused,
aggregate, and full tests. New Lean files stay under 300 lines. Scratch remains repository-local;
parser and diagnostic proof work remains paused.
