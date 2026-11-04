# Reviewer's guide: Syntax

`Solcore/Syntax` holds the AST, the lexer, the parser and the parser proofs.
This page lists what to read and in which order.

> **Status.** Lane R3 is in progress. Paths on this page are the ones in the tree
> today. Rows marked *proposed* depend on a layout decision that is still open.

## Front

Evidence: README's "Proof status", the umbrella's imports, and three queries over
the environment:
- the declarations that `Parser.parse`, `Lexer.lex` and `Unchecked` reach;
- the declarations that the main theorems' statements reach;
- the theorems that nothing else in the area uses, ranked by what they rest on.

### Executable code

`parse` and `lex` reach 1,669 declarations in 65 modules and no named theorem, so
the executable parser does not depend on its proofs.

| What | Files |
| --- | --- |
| Source, spans, tokens | `Foundation`, `Source`, `Token`, `SpanSequence` |
| AST | `Identifier`, `Literal`, `Operator`, `Type`, `Term`, `Declaration`, `Yul`, `Module` |
| Comments | `Trivia` |
| Unchecked blocks | `Unchecked` |
| Lexer | `Lexer`, `Lexer/{Core,Character,Scan,State,Step,Result}`, `Unicode/*` |
| Parser machine | `Parser/{Diagnostic,Result,State,Primitive}` |
| Parser entry points | `Parser` (`parse`, `parseLexed`) |
| Parser productions | `Parser/*` and its `Statement/`, `Expression/` and `Yul/` subdirectories. Many of these files also hold proofs; see "Open decision". |

### Specification

The main theorems' statements reach 1,979 declarations in 139 modules. Beyond the
executable code, that is 321 declarations, nearly all in the grammar.

| What | Files |
| --- | --- |
| Token grammar basics | `DeclarativeGrammar` (`Remainder`, `TokenAt`, `IdentifierParses`) |
| Public file grammar | `DeclarativePublicSourceFileOutcomeGrammar` (`PublicSourceFileOrdinaryParses`), `DeclarativeSourceFileOutcomeGrammar`, `DeclarativeFileGrammar` |
| Per-construct grammar | `Declarative*OutcomeGrammar` and `Declarative*Grammar`: 173 modules without the trace grammars, of which 58 are in the statements' closure |
| Fuel levels | `DeclarativeCoreTermLevelOutcomeProperties` (`CoreTermLevel`), `DeclarativeCoreExpressionLevelOutcomeProperties`, `DeclarativeCorePatternLevelOutcomeProperties` |
| Validity of syntax | `*Validity` (`ParsedFile.ValidFor`, `CoreStatement.ValidFor`, `CoreExpr.ValidFor`) |
| Lexical contract | `Lexer/Contract` (`LexedFile.ValidFor`) |
| Output contract | `ParseOutput.CanonicalValidFor`, in `Parser/CompleteOutputProperties` |

### Main theorems

| Result | Theorem | File |
| --- | --- | --- |
| The lexer is total | `Lexer.lex_exists_ok`, `Lexer.lex_error_impossible` | `Lexer/Properties` |
| Lexing is valid for the file | `Lexer.lex_ok_validFor`, `Lexer.lex_total_validFor` | `Lexer/Properties` |
| The parser is total | `Parser.productionParse_exists_ok`, `Parser.productionParseLexed_exists_ok` | `Parser/CanonicalParserTotalityProperties` |
| Soundness: a parse has a grammar derivation | `Parser.parse_ok_publicSourceFileOrdinary_sound`, `Parser.parseLexed_ok_publicSourceFileOrdinary_sound` | `Parser/PublicSourceFileOrdinaryOutcomeSoundnessProperties` |
| Completeness: a result with this AST exists exactly when the grammar derives it | `Parser.parse_exists_ok_iff_publicSourceFileOrdinary`, `Parser.parseLexed_exists_ok_iff_publicSourceFileOrdinary` | `Parser/PublicParseCompletenessProperties` |
| One file has one AST | `Parser.parse_ok_parsed_value_unique`, `Parser.parseLexed_ok_parsed_value_unique` | `Parser/SyntaxExactnessProperties` |
| The grammar alone determines one AST | `DeclarativeGrammar.publicSourceFileOrdinary_exists_unique_of_validation` | `Parser/PublicSourceFileGrammarProperties` |
| Every span in the output belongs to the file | `Parser.parse_ok_completeOutput_validFor`, `Parser.productionParse_exists_ok_completeOutput_validFor` | `Parser/CompleteOutputProperties`, `Parser/CertifiedParseProperties` |
| Any derivation over valid carriers has valid spans | `DeclarativeGrammar.PublicSourceFileOrdinaryParses.validFor_of_lexing` | `Parser/PublicSourceFileGrammarProperties` |
| Every token input takes one certified branch | `Parser.productionParseLexed_certifiedOutcome` | `Parser/CertifiedLexedParseOutcomeProperties` |
| Parser errors are exactly validation failures | `Parser.productionParseLexed_error_iff_validationRejects` | `Parser/CertifiedLexedParseOutcomeProperties` |
| Diagnostic-free parses of Core | `Parser.parse_ok_coreOrdinary_sound_and_validFor` | `Parser/CorePublicParseOrdinarySoundnessProperties` |
| Exact output on complete slices | `Parser.parse_eq_ok_of_emptyTokens`, `Parser.parse_eq_ok_singlePragma_iff`, `Parser.parse_eq_ok_singleRecovery_iff` | `Parser/Public*OutputProperties` |

Below these, each construct has its own pair of results, for example
`Parser.statement_ordinary_success_iff` and
`Parser.contractDecl_ordinary_success_iff`. The trace results are summarized in
the module doc of `Parser/SyntaxDiagnosticTraceProperties`.

## Internal

Proof machinery is merged by topic. Grammar-level files, which never mention the
parser, go to `Internal/`. Parser-level files go to `Parser/Internal/`.

| File | Topic |
| --- | --- |
| `Internal/TraceBasics` | Contracts for traced relations, and cascade laws |
| `Internal/DelimitedTrace` | Traces of delimited lists |
| `Internal/NameTrace` | Traces of identifiers and expression names |
| `Internal/TypeTrace` | Traces of type expressions |
| `Internal/ParameterTrace` | Traces of function and lambda parameters |
| `Parser/Internal/DiagnosticTrace` | Foundations of the parser's trace proofs |
| `Parser/Internal/DelimitedTrace` | Delimited-list parsers against their traces |
| `Parser/Internal/TypeTrace` | Identifier and type parsers against their traces |
| `Parser/Internal/FunctionReturnsTrace` | The optional `returns` clause against its traces |
| `Parser/Internal/ParameterTrace` | Parameter parsers against their traces |
| `Parser/Internal/ParameterListTrace` | Function and lambda parameter lists against their traces |

Two constraints keep these files apart:

- `Parser/Internal/ParameterTrace` must not import
  `Parser/LambdaParameterTotalityProperties`. Both declare the public theorems
  `LambdaParameterInternals.recoverLambdaParameter_ordinary` and
  `recoverLambdaParameter_ne_invariant`, with the same statements. Lean accepts that
  across imports, but not inside a file that imports the other copy.
- `Parser/Internal/FunctionReturnsTrace` stays apart from `Parser/Internal/TypeTrace`.
  In one file, the statements of `parseFunctionReturns_eq_of_present` and
  `parseNamedTypeArguments_eq_of_present` would share a matcher whose bound names
  differ, and the snapshot would report a changed type.

## Open decision

*Proposed:* move the proofs out of the mixed parser files into `Parser/Internal/`,
and leave the executable definitions at their current paths.

- **Why.** The 43 parser modules that hold executable declarations have 31,808
  lines. Only 4,546 of those lines are executable declarations.
- **Feasibility.** 1,297 of their 1,366 theorems can leave. The other 69 reference
  a private executable helper, so they stay beside it.
- **Effect on importers.** Of the 3,139 outside modules that reference this area, 12
  would lose a declaration they use, and at most eight of those need an import kept.
