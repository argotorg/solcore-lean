# ADR-0272: Unary structural function type annotations

- Status: Accepted for implementation
- Decision date: 2026-09-10
- Scope: Exactly one original parameter in an explicit function type annotation

## Canonical evidence and arity boundary

Use argotorg/solcore-rs at
`18fd9f75d290df0070e21ee56e0a5691f232596f`.
The parser retains the original function parameter list and its delimiter span.
An omitted return is Unit; a written return list is Unit when empty, its single
child when singleton, and a tuple otherwise
(`crates/parser/src/parse/types.rs:95–133`).
Function type lowering retains each parameter separately from the return
(`crates/parser/src/lower/items.rs:270–284`,
`crates/hir-ty/src/lower.rs:201–214`).
Tuple type lowering uses Unit, singleton identity, or right-associated Pair,
without an extra terminal Unit (`hir-ty/src/lower.rs:703–717`).

Canonical type inference checks the original source arity for direct and
indirect calls (`hir-ty/src/infer/expr.rs:446–475,548–575`).
The test `pair_domains_preserve_source_call_arity_and_explicit_tuple_arguments`
distinguishes zero arguments, two arguments and one explicit tuple argument
(`hir-ty/src/infer/tests.rs:2489–2515`).
Canonical Unit/product packing is not permission to erase that distinction.
The present Lean Core function domain and local application profile do not
retain a separate source arity. Therefore accept exactly one original parameter:
`function((A,B))` is supported when its children have meanings, but
`function(A,B)` remains rejected. Likewise `function(())` is unary, while
`function()` remains outside this profile. Do not broaden calls.

## Independent original-syntax meaning

Extend interpretStructuralType? and StructuralTypeDenotes with two cases:
a singleton original parameter list with no returns, and the same parameter
shape with an original written returns list. The independent constructors
require meanings for the original parameter and, when present, the return
list's structural tuple view. They must not assume interpreter success.

Map the absent form to Core.Ty.function parameterType Unit.
For a present list, interpret TypeExpr containing that list under its own
original delimiter span, then use the resulting type as the function codomain.
This tuple view specifies return-list semantics; it does not rewrite the
original source AST, flatten explicit nested tuples, discard list elements,
replace a present empty list by absence, or replace keyword/delimiter ranges.
Keep those original source fields in both independent constructors.

Recursive children may themselves be supported structural function types.
Keep first-match table lookup at named leaves, including arbitrary aliases,
duplicate rows and qualified components. Do not introduce builtin spellings.
Unsupported children still reject the entire function annotation; unused
return components are not skipped. No whole-function table row is required.

Zero and multiple original parameters, named generic arguments, mapping,
proxy, comptime and error types retain their existing rejection boundaries.
The named-only interpreter and its whole-result membership law remain
unchanged, including all explicit function type rejections.

## Existing consumers and unchanged execution contracts

Reprove structural soundness/completeness, unique meaning, exact rejection,
outer-span independence, extension and whole-option lookup congruence with
their existing public theorem headers unchanged. Preserve all other production
files, including local expression/application semantics, Core, runtime-world
safety and fresh local-ID selection.

Existing parameter declarations, typed lets and the single outer return
annotation consume the structural interpreter and therefore inherit this
extension without new entry or execution rules. The outer named-function
RuntimeReturnTypeDenotes policy remains absent Unit or exactly one written
annotation; empty/multiple outer return clauses remain unsupported.
An inner function type may have a multiple-element return list without
changing that separate outer declaration policy.

Migrate obsolete structural/static rejection fixtures with exact original
source text, file identity, type table and owner. Preserve old wrong-actual
argument rejection (notably Unit/Word supplied for a function) rather than
treating static type acceptance as runtime binding success.
The old generic unsupported-constructor consumer retains its exact public
header but removes the now-supported private unary-function member; add an
independent positive for that exact member and arbitrary meaningful child.

New consumers must construct independent meanings over original parsed ASTs,
cover absent/empty/single/multiple returns, nested functions and tuples,
source-arity distinctions, strict child failures, duplicate lookup priority,
arbitrary spans and type extensions. Exercise accepted annotations through
actual supplied closures and existing entry/typed-let/return execution.
Retain original captures, stores, costs, all-fuel results and genuine saved
configurations where applicable; no new source lambda is inferred.

Structural function meaning does not establish a runtime inhabitant, nominal
constructor resolution, global function lookup, polymorphism or a shared
well-typed store world. Actual runtime arguments and safety evidence remain
explicit and unchanged.

## Staged verification

Commit decision, definitions, proof migrations, old consumers, new consumers
and publication separately in small chunks. Keep proof files below 300 lines.
Require independent reviews, focused/aggregate/full tests, protected public
contracts, published-catalog/all-consumer standard-axiom audits, dependency,
kernel, metadata and EOF/whitespace checks. Keep diagnostic/parser proof work
paused and all work files inside the repository.
