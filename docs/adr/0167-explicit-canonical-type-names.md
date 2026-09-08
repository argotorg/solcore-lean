# ADR-0167: Explicit canonical type-name interpretation

- Status: Accepted
- Decision date: 2026-09-08
- Scope: a monomorphic type-name bridge for subsequent source parameter binding

## Decision

Add a total, deliberately restricted adapter from canonical `Syntax.TypeExpr`
to `Core.Ty`. Accept only a named type with no type arguments. Its meaning is
supplied by an ordered caller table from qualified spelling-component lists
to Core types. Use exact component strings in written order and first-match
lookup, including duplicate caller entries.

Represent qualified keys as lists, not joined text. A raw component containing
a dot must not alias two separate components. Do not normalize case, whitespace,
Unicode, empty components, or raw AST payloads. This adapter does not validate
lexical spelling or source ranges. Outer type ranges, qualified-name ranges,
and component occurrence ranges do not affect meaning.

The table may assign any Core type. No spelling, including `Word` or `Bool`,
has an implicit reserved meaning; distinct names may denote the same Core type.
This is explicit monomorphic interpretation, not type declaration collection,
module/import resolution, nominal identity generation, alias expansion, or
general source type inference.

## Independent specification

Define first-occurrence table lookup independently with head/tail rules. Define
canonical type meaning by the named/no-arguments AST shape and that relation,
not by successful execution of the adapter. Prove soundness, completeness,
exact success and failure characterizations, unique meaning, and provenance in
the supplied table. Prove range and exact-component invariance separately from
lexical validity.

Every other source type constructor, including a named type with arguments,
mapping, proxy, function, comptime, tuple, and recovery error, returns `none` in
this slice. `none` means unmapped or outside this adapter, not invalid in the
complete Solcore language. There is no fallback meaning for an unknown name.

## Validation and next boundary

Use independent derivations and executable regressions for exact qualified
components, duplicate priority, aliases, arbitrary target types, unknown names,
all unsupported shapes, and arbitrary invalid ranges. Include raw dotted and
empty component distinctions. Exercise the existing lexer/parser on complete
type text, retaining full-consumption checks, and feed the actual returned AST
through the adapter; well-formed unsupported source forms still parse.

This supplies the type-name premise for the next canonical runtime-parameter
binding adapter. It does not yet bind parameters, execute function bodies,
allocate declaration identities, or decide staging and overload policies.
Existing expression semantics, exact costs, input invariance, parser behavior,
Core execution, wire formats, and golden bytes remain unchanged.

Audit public declarations using only the permitted standard kernel axioms;
run focused and aggregate builds, full tests, kernel, metadata, and whitespace
checks. Keep new proof files below 300 lines.
