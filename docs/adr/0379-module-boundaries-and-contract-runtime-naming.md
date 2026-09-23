# ADR-0379: Readable module boundaries and contract-runtime naming

## Status

Accepted. This is a source-tree and Lean-module organization decision. It does
not revise a language, evaluation rule, Core Wire version, Oracle protocol, or
canonical standard-library byte.

## Context

Several closely coupled Core theorem families had accumulated as many tiny
modules. A reader following derived comparisons or local-fragment weakening had
to cross numerous files whose separation did not represent independent public
boundaries. Conversely, the large top-level name `Solcore.Semantics` did not
say which of the repository's several semantics it contained. It actually
modeled checked Core programs running in a contract world, while
`Solcore.SourceSemantics` and `Solcore.Core` already owned different semantic
layers.

Three other names also need an explicit reading rule:

- `Solcore.Syntax` is the current canonical lexer, recovery-aware AST, parser,
  and parser-proof tree.
- `Solcore.Surface` is frozen historical Surface v1 and Multi code. It remains
  available for compatibility and reference, not as a current parser layer.
- `Solcore.Standard` embeds canonical source-file bytes and their identity,
  length, and hash pins. `Solcore.Oracle` is instead a versioned wire adapter
  around Core checking and contract execution. Neither is the implementation
  of the other.

## Decision

Group the Core theorem families by concept:

1. `Solcore.Core.Derived` contains derived unsigned and signed comparisons,
   strict and non-strict forms, boolean/word flag forms, their typing and
   evaluation judgments, and associated renaming laws.
2. `Solcore.Core.LocalFragment` contains the local-fragment predicate and the
   associated weakening/insertion, typing, evaluation, inference, cost, and
   local-right-comparison results.

The removed fine-grained module names are not retained merely as one-line
forwarding modules. Callers import the conceptual module, and theorem names
remain the finer-grained navigation mechanism inside it.

Rename `Solcore.Semantics` to `Solcore.ContractRuntime`. The new name is the
literal scope of the layer: accounts and world state, checked contract
registries, frames and journals, nested calls and creation, checkpoints,
commit/rollback, traps, fuel/resumption, and top-level observations. Core's
own expression evaluator and local store remain in `Solcore.Core`; resolved
source meaning remains in `Solcore.SourceSemantics`.

Keep the current and historical source parsers visibly separate. New language
and frontend work imports `Solcore.Syntax`. `Solcore.Surface` and
`Solcore.Surface.Multi` are frozen compatibility/reference boundaries and do
not feed the canonical pipeline.

Keep standard-library identity separate from external execution transport.
`Solcore.Standard.CanonicalData` contains the exact six canonical source-file
byte arrays, logical paths, byte counts, and SHA-256 pins. It has no parser,
typechecker, Core, runtime, or Oracle dependency. Oracle v5 is a strict
JSON/Core-Wire-v3 adapter: it decodes, checks and admits Core contracts,
materializes a `ContractRuntime` scenario, runs it, and encodes an observation
or diagnostic. It does not parse canonical source or consume `Standard`.

The execution-side dependency direction is therefore:

```text
Core → ContractRuntime → Oracle v5
```

The independent source route is:

```text
Standard bytes (when the canonical library is requested)
  → Syntax → Workspace/Frontend → supported lowering → Core
```

`Surface` is outside both current routes except where an explicitly historical
compatibility test imports it.

## Consequences

- Readers have one module per cohesive Core proof family and can use theorem
  namespaces or editor search for individual results.
- `ContractRuntime` no longer competes with `SourceSemantics` for the unqualified
  word “semantics”.
- Imports and fully qualified runtime names move from `Solcore.Semantics` to
  `Solcore.ContractRuntime`. This is an internal Lean API migration; frozen
  Core/Surface/Oracle wire versions and observations are unchanged.
- Historical ADRs keep the module names that were true when those decisions
  were recorded. They are not bulk-rewritten; `ARCHITECTURE.md`,
  `PROJECT_MAP.md`, and `CURRENT_STATUS.md` are authoritative for the current
  layout.
- Future splits should represent a genuine reusable boundary. A small proof
  file is not automatically a module boundary when it is always read and
  imported with one conceptual family.

## Verification target

The aggregate Lean build and tests must succeed after import migration. The
metadata and semantic-kernel policy checks must remain green, public wire
fixtures must be byte-identical, and repository searches outside historical
documentation must find no current `Solcore.Semantics` import or namespace.
