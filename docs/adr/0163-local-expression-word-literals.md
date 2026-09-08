# ADR-0163: Strict Word literals in the monomorphic local-expression adapter

- Status: Accepted
- Decision date: 2026-09-08
- Scope: the explicit-table canonical local-expression adapter

## Decision

Connect ADR-0162's strict Word projection to the existing monomorphic
`LocalExpression` adapter. A canonical literal expression resolves to the
corresponding resolved Word constant exactly when its complete numeric spelling
denotes a natural value below `2^256`. Its source type is Word, and its source
evaluation returns that same Word without consulting names or changing stores.

This is an explicit policy for this limited adapter, not a theorem that all
source numeric literals have Word type. General source literal inference,
`fromInteger`, class resolution, and overloaded conversion remain separate.
The independent unbounded natural-number meaning from ADR-0162 is unchanged.
The narrower reference-only adapter remains unchanged and rejects literals.

Decimal and hexadecimal payloads retain the existing whole-spelling rules.
There is no modulo reduction, sign syntax, Boolean coercion, string conversion,
or digit-length cap. Raw malformed AST payloads and out-of-range numeric values
fail conversion. Source ranges are semantically irrelevant, including the
outer expression range and the literal's own range. `true` and `false` remain
ordinary caller-bound identifiers, not newly recognized Boolean literals.

## Independent semantics and existing composition laws

Add independent resolution, source typing, and source evaluation constructors
whose premise is `WordLiteralDenotes`, not executable decoder success.
Preserve exact soundness and completeness through resolved lowering and Core
checking, value-and-store evaluation correspondence, determinism, typed
execution, sufficient fuel, and absence of machine faults. A literal takes one
Core transition; grouping adds none and each unary complement adds two.

Every written branch still resolves and type-checks. Thus a skipped malformed
or overflowing literal prevents checked execution, although raw source
evaluation can skip it. A valid Word literal on the right of a short-circuit
operator resolves but fails its Boolean typing requirement. When selected,
raw evaluation still forwards that Word under ADR-0159's untyped rule; this
does not make the expression a checked program. Conditional branches must
still have the same type, and the condition must still be Boolean.

Literal nodes contain no local names. The structural unused-name predicate
therefore accepts every literal payload, not only ones with a Word meaning.
This preserves failed checking as well as successful checking under unused
input insertion. Existing arbitrary-map resolution and injective-map typing,
evaluation, and same-fuel bundled-run laws include constants unchanged.

## Validation and boundaries

Keep decimal/hexadecimal agreement, arbitrary leading zeroes, exact Word
boundaries, malformed payloads, and span-independence regressions. Add direct
independent semantic consumers and complete parsed-source execution for literal
leaves, groups, complement, and conditionals; test exact fuel, nonempty stores,
wrong Boolean uses, skipped invalid branches, unused inputs, and ID relabeling.
Replace historical unsupported-numeric fixtures with genuinely unsupported
string payloads; retain the reference-only adapter's negative literal tests.

Audit every affected public proof against standard kernel axioms, run focused
and aggregate builds and complete tests, and verify kernel and metadata policy.
This changes no parser, Core machine rule, source declaration policy, allocator,
external endpoint, Wire/Oracle format, capability, or golden bytes.
