# ADR-0032: Backfill arbitrary renaming laws for derived builders

- Status: Accepted
- Decision date: 2026-08-27
- Scope: fourteenth internal Semantic Core vNext slice
- Implementation: Complete

## Context

ADR-0029 added general de Bruijn renaming after several derived-expression
interfaces were already complete. Those older interfaces exposed weakening
laws, but eight builders lacked the corresponding arbitrary renaming law:

- `boolToWord`, `wordToBool`, `wordIsZero`, and `wordIsNonzero`;
- `boolAnd` and `boolOr`; and
- `wordEqFlag` and `wordGtFlag`.

The generic `Expr.rename` operation can already rename their expansions. The
missing results are API and regression gaps, not missing semantics.

`Expr.rename_boolToWord` was located in `DerivedComparisonFlags` because that
later module needed it. It now belongs with the `boolToWord` builder in
`Conversions`, so earlier and unrelated modules can use it without importing
the derived comparison flags.

## Decision

Publish exactly these eight laws in the module that owns each builder:

```text
rename (boolToWord value) ρ = boolToWord (rename value ρ)
rename (wordToBool value) ρ = wordToBool (rename value ρ)
rename (wordIsZero value) ρ = wordIsZero (rename value ρ)
rename (wordIsNonzero value) ρ = wordIsNonzero (rename value ρ)

rename (boolAnd left right) ρ =
  boolAnd (rename left ρ) (rename right ρ)
rename (boolOr left right) ρ =
  boolOr (rename left ρ) (rename right ρ)

rename (wordEqFlag left right) ρ =
  wordEqFlag (rename left ρ) (rename right ρ)
rename (wordGtFlag left right) ρ =
  wordGtFlag (rename left ρ) (rename right ρ)
```

Here `ρ` is any `Renaming`, not only `Renaming.insertion`. The existing
insertion-based weakening laws remain available and unchanged.

Move `Expr.rename_boolToWord` from `DerivedComparisonFlags` to `Conversions`.
The later comparison-flag proofs continue to consume that theorem through the
owning module. Do not duplicate the declaration or introduce an import cycle.

## Implemented verification

Compile-time examples instantiate every public law. Focused executable
regressions use `swap01`, a genuinely non-insertion mapping that exchanges free
variable indices zero and one. Golden expressions check that:

- each renamed expansion contains the expected free variables;
- unary and binary derived builders rename every operand exactly once;
- the two short-circuit builders retain their branch positions; and
- evaluating a renamed closed witness under the corresponding environment
  produces the expected value.

Runtime witnesses cover all three owning families: conversions, short-circuit
booleans, and original word comparison flags. Each is evaluated in the runtime
environment corresponding to the swapped free variables.

Identity, composition, and insertion behavior remain covered by the general
ADR-0029 renaming foundation. This slice adds focused coverage for the eight
public derived APIs.

## Boundaries

No builder expansion, type, inference result, evaluation order, fuel, fault,
effect, or store behavior changes. No Core form, primitive tag, wire version,
encoding, Oracle behavior, source syntax, ABI rule, opcode, or gas rule is
added. Existing Wire v1 and v2 bytes remain unchanged.

## Consequences

All derived builders completed before ADR-0029 have an explicit arbitrary
renaming interface alongside their existing weakening interface. The theorem
ownership follows the builder ownership, which removes the current layering
surprise without changing runtime behavior.

The next feature is selected by a separate ADR; this decision does not choose
it.
