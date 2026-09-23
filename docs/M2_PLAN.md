# Canonical syntax implementation plan

This document records the ownership, implementation order, and completion
conditions for canonical source syntax. The current implementation lives under
`Solcore.Syntax`; [ADR-0153](adr/0153-canonical-syntax-boundary.md) fixes that
boundary.

## Target and boundary

The syntax layer turns source bytes into a source-preserving, recovery-aware
AST with deterministic diagnostics. It owns:

- file identities, positions, spans, and source slices;
- tokens, comments, keywords, operators, and literals;
- lexical and parse diagnostics;
- declarations, imports, exports, attributes, types, expressions, patterns,
  statements, contracts, and inline Yul syntax;
- recovery nodes and recovered lists; and
- declarative grammar plus executable parser agreement.

It does not own workspace consistency, name resolution, source typing, trait
selection, staging, elaboration, or execution.

## Public Lean boundary

Clients import:

```lean
import Solcore.Syntax
```

The public parser accepts a source file record and returns a `ParseResult`.
Ordinary results retain tokens, comments, lexical diagnostics, parse
diagnostics, and AST data. Malformed input is represented through diagnostics
and recovery rather than by pretending the file is well typed.

The public boundary must remain usable without importing the executable
frontend or semantic runtimes.

## Internal organization

The main module groups are:

| Group | Responsibility |
| --- | --- |
| `Identifier`, token and source records | Stable spelling and source locations |
| `Lexer` | Token/comment production and lexical diagnostics |
| `Declaration` and related syntax records | Source-preserving AST |
| `Declarative*Grammar` | Independent accepted/rejected structure |
| `Parser` and `Parser/*` | Executable parsing and component entry points |
| `Declarative*Properties` | Grammar selection, exactness, recovery, and trace laws |
| `Parser/*Properties` | Executable/declarative soundness and exactness |
| `*Validity` | Structural admission of retained AST collections and terms |

Closely coupled grammar and proof modules may be split to control elaboration
cost, but their public theorem names should make the owning production clear.

## Implementation order

For a new or changed production, work in this order:

1. define or update the source-preserving AST record;
2. update tokens and lexical rules if necessary;
3. state the declarative component grammar;
4. implement the parser component with explicit fuel and recovery behavior;
5. prove ordinary success/rejection soundness;
6. prove selection and exactness results needed by the parent production;
7. connect diagnostic and recovery traces;
8. update the enclosing declaration and complete-file grammar;
9. update public parser theorems; and
10. add focused valid, invalid, ambiguous-prefix, and recovery tests.

This order prevents the AST or executable parser from becoming the sole
definition of accepted syntax.

## Parser result policy

Every public parse has an ordinary result. Diagnostics are data. Internal
fuel, helper dispatch, or fallback branches must not leak as an unexplained
public failure.

For each component, make the following distinctions explicit:

- ordinary success with a value and remaining input;
- ordinary rejection with a deterministic diagnostic trace;
- recovery that constructs an AST node and continues; and
- impossible internal outcomes excluded by a theorem.

When several productions share a prefix, document and prove dispatch priority.
When a delimiter or terminator is missing, state which diagnostic owns the
failure and how far recovery consumes input.

## Exactness and trace obligations

Soundness alone is insufficient for a parser used as a specification
component. Depending on the production, the proof set should include:

- successful value soundness;
- rejection soundness;
- declarative-to-executable completeness;
- exact consumed prefix and remainder;
- deterministic selection among alternatives;
- fuel equations or monotonicity;
- diagnostic-trace agreement;
- recovery protection and fallback isolation; and
- lifting from components to the public file parser.

Property modules already follow these patterns for delimited sequences,
expressions, patterns, statements, declarations, contract members, source-file
items, and public results. New productions should reuse those shared lemmas
instead of introducing a separate parsing discipline.

## Current executable coverage

The present parser handles the canonical AST forms exposed by
`Solcore.Syntax.Declaration`, including:

- pragmas, imports, exports, aliases, data and trait declarations;
- functions, implementations, contracts, constructors, fallback declarations,
  fields, and attributes;
- generic parameters, predicates, function parameters, and return clauses;
- primitive, named, applied, tuple, mapping, and function type structure;
- literals, names, constructors, calls, member/index/postfix forms, lambdas,
  unary and binary operators, tuples, and conditionals;
- blocks, declarations, assignments, returns, conditionals, loops, matches,
  expression statements, and assembly statements;
- patterns and match cases; and
- the retained inline Yul forms.

The exact inventory is the AST and parser source, not this summary. A new
constructor is not publicly covered until complete-file parsing and the
relevant proof path reach it.

## Workspace and frontend handoff

The handoff is intentionally staged:

```text
ParseResult
  -> diagnostic-free syntax admission
  -> Workspace validation and module catalog
  -> Frontend name and signature resolution
  -> source inference and evidence
  -> staging and specialization
  -> selected executable backend
```

The syntax layer must not resolve names or infer types to decide whether a
token sequence parses. Conversely, later phases must not recover missing
syntax by reparsing source text with private rules.

Source identities and spans must survive the handoff so later diagnostics can
refer to the original occurrence.

## Comparison workflow

External parser comparisons use exact pinned source bytes and revisions. A
difference must be classified as one of:

- lexical acceptance or tokenization;
- grammar acceptance;
- AST structure or source retention;
- diagnostic selection/cardinality; or
- recovery behavior.

Parser agreement does not establish agreement in resolution, typing,
specialization, or execution. Record those separately in
[Compatibility evidence](COMPATIBILITY_MATRIX.md).

## Completion conditions

A syntax change is complete when:

- the AST and declarative grammar agree on the new structure;
- executable parsing reaches it from the public file entry;
- success, rejection, exactness, and recovery obligations are proved at the
  necessary component and enclosing boundaries;
- diagnostic order and input consumption are deterministic;
- focused tests cover valid, invalid, boundary, and recovery examples;
- workspace/frontend consumers either support the new node or reject it with
  an explicit later-phase diagnostic; and
- the full build, tests, repository-data checks, and kernel-policy check pass.

Future grammar work should extend this one canonical path. Do not introduce a
parallel AST or parser solely to bypass an unfinished proof obligation.
