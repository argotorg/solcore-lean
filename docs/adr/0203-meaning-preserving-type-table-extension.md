# ADR-0203: Meaning-preserving type-table extension

- Status: Accepted
- Decision date: 2026-09-09
- Scope: Type-name interpretation, static declarations and exact compilation

## Decision

Define `TypeNameTable.Extends old new` as preservation of every independent
first-match lookup meaning from the old table in the new table. This is semantic
extension, not list inclusion, ordering equality or a uniqueness requirement.
Keys remain exact lists of qualified spelling components. Existing types must
not change, including types that currently have no runtime inhabitants.

Provide reflexivity, transitivity, safe right append and fresh-key prepend laws.
Appending arbitrary entries, including duplicate keys, never overrides an earlier
meaning. A fresh-key premise is sufficient for safe prepend, not necessary:
prepending a duplicate with the same meaning may also extend the table. Prepend
that changes an existing first-match meaning does not satisfy this relation.

Transport independent type annotation meanings, return clauses, complete headers,
general initial-state parameter declarations and empty-start declarations along
an extension. Preserve the exact initial/final static rows, original source and
owner. Annotation types are unchanged, so existing fresh identity allocation is
unchanged. Lift this to independent compilation by transporting header and
parameter evidence and retaining the original exact body elaboration.

The complete compiled record is retained, not merely its type or a projection.
Add successful-result preservation for type interpretation, parameter declaration
and compilation. Do not claim that one-way extension preserves rejection: a
previously unknown type name can acquire meaning and enable static compilation.

Mutual extension preserves all first-match lookup results, including absence.
Use it to prove full optional-result equality for type interpretation, parameter
declaration and compilation. No additional equivalence relation or runtime
inhabitation assumption is needed. Existing same-Core execution and cost laws can
consume transported compilation evidence when actual arguments are supplied.

## Boundaries and validation

No table lookup implementation, annotation/header/parameter/body policy, parser,
compiler, identity allocator, Core semantics, runtime evaluator or frozen interface
changes. This proves when modifying caller-supplied meanings is safe; it does not
introduce import lookup, type definitions or reserved built-in type spellings.
Full prepared-record equality is not inferred from a `toCompiled` projection.

Independent and parsed consumers cover arbitrary and nominal types, nonempty
initial inputs, duplicate/shadowed keys, qualified-component distinctions, safe
append/prepend and nonidentical mutually extending tables. Retain the contrasts:
meaning-changing shadowing is not extension, while one-way extension can turn
unknown-name rejection into success. On already compiled declarations, consume
existing contracts for identical full execution and cost with common actual
arguments, without fabricating runtime values.

Audit every public declaration and consumer with standard axioms only; run
focused/aggregate builds and full tests, kernel/metadata/whitespace checks, keep
proof files below 300 lines and commits small. Keep diagnostics paused and use
repository-local scratch files.
