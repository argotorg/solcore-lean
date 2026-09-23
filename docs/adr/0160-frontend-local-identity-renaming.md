# ADR-0160: Frontend local identity renaming

- Status: Accepted
- Decision date: 2026-09-08
- Scope: simultaneous local-ID relabeling of explicit frontend inputs

## Decision

Extend the existing resolved identity-renaming laws to the canonical frontend
fragment and typed input bundle. A name-table operation maps only assigned
local IDs, preserving source spellings, row order, and repeated-name shadowing.
A typed binding update likewise retains its name, type, value, and typing
evidence. A bundle transformation requires an injective mapping so that its
unique-ID invariant remains true.

This is identity relabeling, not source identifier renaming: the entire source
AST, including spelling and source ranges, is unchanged. The same mapping must
be applied to the name table and all relevant context/environment IDs. Values,
types, stores, and positional Core variables are not renamed.

## Guarantees

Name-table lookup and whole resolution commute with arbitrary ID maps: they
only select by spelling. The resolver's exact optional result is the old result
with resolved IDs renamed, including failed resolution. Independent resolution
has a corresponding preimage characterization without requiring injectivity.

With an injective map, the unchanged source checks to exactly the same Core
expression and type, including check failures. Source typing is equivalent in
both directions. Raw source evaluation is also equivalent with the same value
and both store endpoints, without imposing whole resolution or source typing.
This includes short-circuit evaluation that skips an unsupported or unresolved
right operand, and its explicitly untyped selected-right-value boundary.

The typed input bundle preserves these properties automatically. For every
source, initial store, and identical fuel, its runner returns exactly the same
optional stateful result. This includes check failure, completion, and the full
suspended state on fuel exhaustion: unlike fresh insertion, identity relabeling
does not shift Core positions or runtime value lists. Identity and composition
laws describe repeated relabeling.

## Essential boundaries

Injectivity prevents distinct references from merging and selecting an earlier
row. Raw tables may already contain repeated names or aliased IDs; relabeling
preserves those existing relationships and does not claim source-wide unique
allocation. A noninjective counterexample must show changed Core position and
value, even when all positional types remain Boolean. The typed bundle cannot
admit the corresponding duplicate-ID result.

No commutation with subsequent `bindFresh` allocation is promised: the allocator
chooses IDs numerically within its explicit owner/scope, and an arbitrary
injective map need not preserve that choice. Mapping owner labels does not prove
declaration ownership, module linkage, or global resolver correctness.

## Validation and publication

Reuse the existing resolved lowering/lookup renaming laws. Keep independent raw
source evaluation proofs independent of whole-resolution success. Tests cover
Boolean/conditional expressions, repeated names, aliases, exact checked Core,
same-fuel suspended/completed results, skipped failed syntax, and the essential
noninjectivity and allocation boundaries. Audit all public proofs with standard
kernel axioms, compile the public interface, and run focused and full tests.

This adds no source syntax, type, value, Core or machine constructor, external
service, Wire tag, schema, or capability change.
