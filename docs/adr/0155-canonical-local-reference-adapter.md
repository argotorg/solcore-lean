# ADR-0155: Canonical local-reference adapter

- Status: Accepted
- Decision date: 2026-09-08
- Scope: canonical identifier/group ASTs and caller-supplied local tables

## Decision

Connect the canonical `Syntax.Expr` identifier and grouping constructors to
ADR-0154's resolved local identities through `Solcore.Frontend`. This is a
narrow reference adapter, not a source resolver for arbitrary expressions or
programs. Its inputs are an existing canonical AST and explicit name/type tables.

The name table is an ordered list of exact strings and assigned `LocalId`s.
Lookup uses the first equal string. Identifier spelling is `Identifier.value`;
no case, whitespace, or Unicode normalization is performed. Source ranges do
not select an identity. Grouping preserves the selected reference recursively.
`true` and `false` remain ordinary caller-bound identifier spellings here;
the adapter neither inserts their bindings nor converts them to Boolean values.

Other AST constructors are unsupported. An absent result means unsupported or
unmapped by this adapter, not rejection by the Solcore language. The adapter
does not repeat lexical validation, check source-span validity, collect
declarations, allocate fresh IDs, resolve imports or classes, or choose the
source language's shadowing policy.

Typed elaboration first resolves the reference, locates its identity in the
caller-supplied ordered resolved context, and checks the exact Core variable.
It returns that variable and type. Missing identities receive no default
index or type. In particular, failure to find the first selected name's ID in
the context does not retry later equal spellings in the name table.

Repeated names and repeated IDs have explicit first-match table behavior.
The spelling table and the identity table are distinct stages: mere membership
of a later entry does not establish its selection. No freshness or uniqueness
of caller-supplied tables is presumed.

## Independent semantic boundary

Separate inductive relations specify name lookup, canonical reference
resolution, reference typing, and reference evaluation. Executable resolution
and typed elaboration are proved sound and complete for those relations.
The resulting Core variable, de Bruijn index, and type are fixed exactly.

For execution, the runtime environment and typing context must retain the
same identity order. Equal lengths or matching value types alone do not imply
that condition. Under it, checked Core evaluation is equivalent to independent
reference evaluation and exact store preservation. A typed environment also
provides existence of a reference value and preservation of its assigned type.

Successful local lookup takes one Core transition. At zero fuel, execution
retains the initial state as out-of-fuel; every positive fuel returns the same
value and store. Grouping depth has no Core execution cost. This is not a
complexity bound on AST traversal or table search and is not EVM gas.

Open local tables can carry any existing Core type or value. Merely returning
a closure, host function, or cell reference does not invoke or dereference it.
This adapter adds no dynamic effects.

## Publication and validation

Only the additive Lean library boundary changes. Canonical parser behavior,
Oracle versions, frozen wire languages, and published golden bytes remain
unchanged. This is not a source-text execution service or a completed source
type checker.

Regressions cover exact spelling, distinct arbitrary source spans, nested
groups, duplicate-name priority, unsupported nodes, missing context identities,
exact nonzero Core indices, caller-controlled Boolean values, and the precise
zero/positive fuel boundary. Type/value correspondence must keep identity-order
agreement explicit. New frontend files are included in the kernel policy scan;
public axioms, focused and aggregate builds, tests, and metadata are audited.
An explicit reordered-environment counterexample preserves positional Boolean
typing while changing which identity the Core index reads. It protects the
identity-order premise from being dropped in later compositions.
