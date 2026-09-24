# ADR-0379: Readable module boundaries and contract-runtime naming

## Status

Accepted. This is a source-tree and Lean-module organization decision. It does
not revise a language, evaluation rule, or Core representation.

## Context

Closely coupled definition and theorem families had accumulated as many tiny
modules. A reader following `HostRunner`, derived comparisons, local-fragment
weakening, a frontend runtime-function path, or a contract-frame result had to
cross numerous files whose separation did not represent independent public
boundaries. Many of those files shared a long prefix and were always imported
as one conceptual unit.

Conversely, the former top-level name `Solcore.Semantics` did not identify
which semantic layer it contained. It modeled checked Core programs running in
a contract world, while `Solcore.SourceSemantics` and `Solcore.Core` own other
semantic layers.

`Solcore.Syntax` has an explicit role in this organization: it is the canonical
lexer, recovery-aware AST, parser, and parser-proof tree.

## Decision

Use a **conceptual module** as the normal source boundary. A shared filename
prefix is a strong signal that definitions and their properties belong
together, but is not sufficient by itself: a merge must preserve an acyclic
Lean import graph and a coherent reading unit. Public declarations keep their
names; only private declarations may be disambiguated when previously separate
files used the same helper name.

Group the Core families by concept:

1. `Solcore.Core.Derived` contains derived unsigned and signed comparisons,
   strict and non-strict forms, boolean and word flag forms, their typing and
   evaluation judgments, and associated renaming laws.
2. `Solcore.Core.LocalFragment` contains the local-fragment predicate and the
   associated weakening, insertion, typing, evaluation, inference, cost, and
   local-right-comparison results.
3. `Solcore.Core.HostRunner`, `Machine`, and `HostMachine` each contain their
   executable definition and corresponding property and safety sections.
4. `Solcore.Core.Renaming` contains syntax, runtime, evaluation, safety, and
   insertion renaming results in dependency order.

Apply the same cohesion rule outside Core without erasing genuine layer
boundaries:

- `Solcore.Resolved` colocates local-scope, typing, evaluation, renaming,
  scope-extension, and word-less-with-identities families.
- `Solcore.ContractRuntime` groups account and world state, host driver and
  storage, frame run/outcome/trace/context, nested execution, transaction,
  balance, and checked-program families by the runtime concept they define.
- `Solcore.Frontend` groups runtime-function, computation, local-expression,
  application, typed-return-tree, compiler, and associated proof families.
- `Solcore.Abi.StaticWord` owns the complete static-word ABI feature.
- `Solcore.SourceSemantics` groups graph substitution, dynamic control facts,
  and program preservation with the definitions they refine.
- `Solcore.Syntax` groups tightly coupled parser and proof families under their
  existing conceptual names, including module paths, signatures, contract
  entries, traits, type aliases, enums, implementations, patterns, and
  expression atoms.

Keep a separate module when it represents a genuine reusable stage, when
combining it would create an import cycle, or when a large elaboration or proof
certificate benefits from an explicit resource boundary. Examples include
runtime-scalar proof shards, cyclic profile/property pairs, and independent
execution and lowering boundaries.

Removed fine-grained module names are not retained merely as one-line
forwarding modules. Callers import the conceptual module, and theorem names
remain the finer-grained navigation mechanism within it.

Rename `Solcore.Semantics` to `Solcore.ContractRuntime`. The new name states
the layer's scope: accounts and world state, checked contract registries,
frames and journals, nested calls and creation, checkpoints, commit and
rollback, traps, fuel and resumption, and top-level observations. Core's
expression evaluator and local store remain in `Solcore.Core`; resolved source
meaning remains in `Solcore.SourceSemantics`.

Canonical language and frontend work imports `Solcore.Syntax`.

The source dependency route is:

```text
Syntax → Workspace/Frontend → supported lowering → Core
```

Checked Core execution follows a separate internal route:

```text
Core → ContractRuntime
```

## Consequences

- Readers have one module per cohesive feature family and can use declaration
  namespaces, section headings, or editor search for individual results.
- Core, Resolved, ContractRuntime, Frontend, ABI, SourceSemantics, and Syntax
  use the same conceptual-module rule; public declaration names remain stable.
- `ContractRuntime` no longer competes with `SourceSemantics` for the
  unqualified word “semantics”.
- Imports and fully qualified runtime names move from `Solcore.Semantics` to
  `Solcore.ContractRuntime` as an internal Lean API migration.
- Historical ADRs retain module names that were true when those decisions were
  recorded unless the historical feature itself is removed.
- Future splits should represent a genuine reusable or resource boundary. A
  small proof file is not automatically a module boundary when it is always
  read and imported with one conceptual family, and a common prefix remains a
  prompt for review rather than a mechanical command to merge.

## Verification target

The aggregate Lean build and tests must succeed after import migration.
The semantic-kernel policy check must remain green, and repository
searches outside historical documentation must find no current
`Solcore.Semantics` import or namespace.
