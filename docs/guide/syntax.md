# Syntax

`Solcore/Syntax` turns a source file into an AST. It holds the AST, the lexer, the executable
parser, an independent declarative grammar, and the proofs that the parser agrees with the grammar.
The [umbrella](../../Solcore/Syntax.lean) imports all of it, main theorems included.

- **What it does.** `Parser.parse` lexes a `SourceFile`, validates the lexer's output, checks
  nesting and parses. It returns a `ParseOutput`: the `ParsedFile`, the tokens, and the lexical and
  parse diagnostics. Only a broken executor invariant is an error.
- **What it builds on.** No other area. Syntax imports only its own files and Lean's `Init`.
- **What builds on it.** The [frontend](frontend.md) parses every workspace file in
  `ProgramInterfaces`, through the pass of `Syntax/Unchecked`, and rejects a file with any
  diagnostic. The AST then reaches every later layer. The typed IR of `Frontend/SourceInference`
  carries `Syntax.UnaryOp`, `Syntax.BinaryOp` and `Syntax.ValueAssignOp`, so inference, the
  lowering, the [source semantics](source-semantics.md) and [core lowering](core-lowering.md) all
  match on these types.

The grammar under `Grammar/` says which token sequences derive which AST, and never calls a parser
function. `Parser/Correctness` proves that `parse` succeeds on every file, that each result has a
derivation, that each derivation is a result, and that the AST is unique.

## Where things are

### AST and source

| File | Holds |
| --- | --- |
| [`Foundation`](../../Solcore/Syntax/Foundation.lean) | `Identifier`, `QualifiedName`, `NonemptyList`, `DelimitedList`, `NonemptyDelimitedList` |
| [`Source`](../../Solcore/Syntax/Source.lean) | `SourceFile`, `SourceId`, `SourceSpan`, `Located`, `SpannedText`, `Comment` |
| [`Token`](../../Solcore/Syntax/Token.lean) | `Token`, `TokenKind`, `HardKeyword`, `ContextualKeyword`, `Symbol`, and their spellings |
| [`SpanSequence`](../../Solcore/Syntax/SpanSequence.lean) | `SpanSequence.ValidFor`: spans in one file, in source order |
| [`Identifier`](../../Solcore/Syntax/Identifier.lean) | `isValidIdentifier` |
| [`Literal`](../../Solcore/Syntax/Literal.lean) | `CoreLiteral`, `YulLiteral` |
| [`Operator`](../../Solcore/Syntax/Operator.lean) | `UnaryOp`, `BinaryOp`, `ValueAssignOp`, their precedence, and the decoders `BinaryOp.at?` and `ValueAssignOp.at?` that the parser and the grammar share |
| [`Type`](../../Solcore/Syntax/Type.lean) | `TypeExpr`, `Predicate`, `WhereClause`, `GenericParameters`, `FunctionParameter`, `LambdaParameter` |
| [`Term`](../../Solcore/Syntax/Term.lean) | `Expr`, `Pattern`, `Statement`, `Block`, `MatchCase`, `MatchArms`, `ForItem` |
| [`Yul`](../../Solcore/Syntax/Yul.lean) | `YulExpr`, `YulStmt`, `YulCase`, `YulIdentifier` |
| [`Declaration`](../../Solcore/Syntax/Declaration.lean) | `ParsedFile`, `TopItem`, `FunctionDecl`, `EnumDecl`, `TraitDecl`, `ImplDecl`, `ContractDecl`, `TypeAliasDecl`, `DeriveAttribute` |
| [`Module`](../../Solcore/Syntax/Module.lean) | `ModulePath`, `ImportDecl`, `ExportDecl`, `PragmaDecl` |
| [`Trivia`](../../Solcore/Syntax/Trivia.lean) | `attachTopItemComments`: comments attached to items |
| [`Unchecked`](../../Solcore/Syntax/Unchecked.lean) | `prepare` and `mark`, the pass around the parser for `unchecked` blocks |

### Lexer

| File | Holds |
| --- | --- |
| [`Lexer`](../../Solcore/Syntax/Lexer.lean) | The public boundary |
| [`Lexer/Core`](../../Solcore/Syntax/Lexer/Core.lean) | `lex`, `lexLoop` |
| [`Lexer/Result`](../../Solcore/Syntax/Lexer/Result.lean), [`Lexer/Contract`](../../Solcore/Syntax/Lexer/Contract.lean) | `LexedFile`, `LexicalDiagnostic`, `LexResult`; the output contract `LexedFile.ValidFor` |
| [`Lexer/Step`](../../Solcore/Syntax/Lexer/Step.lean), [`Lexer/State`](../../Solcore/Syntax/Lexer/State.lean) | One `step`, and the lexer's `State` |
| [`Lexer/Scan`](../../Solcore/Syntax/Lexer/Scan.lean) | Comment and string scanners |
| [`Lexer/Character`](../../Solcore/Syntax/Lexer/Character.lean) | Character classes, and the symbol tables `multiSymbol?` and `singleSymbol?` |
| [`Lexer/Invariant`](../../Solcore/Syntax/Lexer/Invariant.lean) | `CursorSuffix` |
| [`Lexer/ScanProperties`](../../Solcore/Syntax/Lexer/ScanProperties.lean) | Progress laws of the scanners |
| [`Lexer/Properties`](../../Solcore/Syntax/Lexer/Properties.lean) | The lexer's main theorems |
| [`Unicode/Letter`](../../Solcore/Syntax/Unicode/Letter.lean), [`Lowercase`](../../Solcore/Syntax/Unicode/Lowercase.lean), [`Number`](../../Solcore/Syntax/Unicode/Number.lean), [`Range`](../../Solcore/Syntax/Unicode/Range.lean) | `isLetter`, `isLowercase`, `isNumber`, from the range tables of `ScalarRange` |

### Parser

The productions read in dependency order, from `Parser/Tokens` to `Parser/SourceFiles`.

| File | Holds |
| --- | --- |
| [`Parser`](../../Solcore/Syntax/Parser.lean) | `parse`, `parseLexed` |
| [`Parser/Diagnostic`](../../Solcore/Syntax/Parser/Diagnostic.lean), [`Parser/Result`](../../Solcore/Syntax/Parser/Result.lean) | `ParseDiagnostic`, `ParserInvariantError`, `SyntaxInvariantError`; `ParseOutput`, `ParseResult` |
| [`Parser/State`](../../Solcore/Syntax/Parser/State.lean) | `State`, `TokenWindow`, `Reply`, `Failure`, `Parser`, and lemmas about the state |
| [`Parser/Primitive`](../../Solcore/Syntax/Parser/Primitive.lean) | `acceptToken`, `keyword`, `symbol`, `contextual` |
| [`Parser/Tokens`](../../Solcore/Syntax/Parser/Tokens.lean) | `qualifiedName`, `coreLiteral`, `delimited`, `delimitedNoTrailing` |
| [`Parser/Types`](../../Solcore/Syntax/Parser/Types.lean) | `typeExpr`, `predicate`, `whereClause`, `namedParameter`, `lambdaParameter` |
| [`Parser/Signatures`](../../Solcore/Syntax/Parser/Signatures.lean) | `functionSignature`, `functionParameters`, `genericParameters`, `returnClause`, and proofs |
| [`Parser/Blocks`](../../Solcore/Syntax/Parser/Blocks.lean) | `captureBlock?`, `isolateBlock`, `coreBlock`, and proofs |
| [`Parser/Yul`](../../Solcore/Syntax/Parser/Yul.lean) | `yulExpression`, `yulBlock`, `yulBody` |
| [`Parser/Terms`](../../Solcore/Syntax/Parser/Terms.lean) | Expressions, patterns and statements by fuel (`coreExpressionWithFuel`, `coreStatementWithFuel`), the precedence ladder `expressionLayer`, and `expression`, `pattern`, `statement`, `block` |
| [`Parser/Declarations`](../../Solcore/Syntax/Parser/Declarations.lean) | `functionDecl`, `enumDecl`, `typeAlias`, `traitDecl`, `implDecl`, `contractDecl`, `deriveAttribute` |
| [`Parser/Modules`](../../Solcore/Syntax/Parser/Modules.lean) | `modulePath`, `importDecl`, `exportDecl`, `pragmaDecl` |
| [`Parser/SourceFiles`](../../Solcore/Syntax/Parser/SourceFiles.lean) | `sourceFile`, `topItem`, `parseItems`, `checkNesting`, `validateLexed`, the diagnostic filter `filterParseDiagnostics` |
| [`Parser/Correctness`](../../Solcore/Syntax/Parser/Correctness.lean), [`Parser/PublicOutputs`](../../Solcore/Syntax/Parser/PublicOutputs.lean) | The main theorems, and the exact output on complete slices of the language |

### Grammar and validity

This is the specification. Each grammar file imports only grammar files below it, and the relations
live in the namespace `Solcore.Syntax.DeclarativeGrammar`.

| File | Holds |
| --- | --- |
| [`Grammar/SourceFile`](../../Solcore/Syntax/Grammar/SourceFile.lean) | `PublicSourceFileOrdinaryParses`, where the main theorems start; `SourceFileOrdinaryParses`, `TopItemOrdinaryParses`, `CoreSourceFileOrdinaryParses` |
| [`Grammar/Declarations`](../../Solcore/Syntax/Grammar/Declarations.lean) | `TraitDeclOrdinaryParses`, `ContractBodyOrdinaryParses`, `ImplBodyOrdinaryParses` |
| [`Grammar/Modules`](../../Solcore/Syntax/Grammar/Modules.lean) | `ModulePathOrdinaryParses`, `PragmaDeclOrdinaryParses`, `ExportPathOrdinaryParses` |
| [`Grammar/TermLevels`](../../Solcore/Syntax/Grammar/TermLevels.lean) | The fuel levels of the terms, `CoreTermLevel` and `CoreExpressionLevel`; `CoreExpressionOrdinaryParses`, `CoreStatementOrdinaryParses` |
| [`Grammar/StatementLayer`](../../Solcore/Syntax/Grammar/StatementLayer.lean) | `StatementLayerOrdinaryParses`, `MatchStatementOrdinaryParses` |
| [`Grammar/Statements`](../../Solcore/Syntax/Grammar/Statements.lean) | `CoreBlockOrdinaryParses`, `IfStatementOrdinaryParses`, `ValueAssignOperatorParses` |
| [`Grammar/Patterns`](../../Solcore/Syntax/Grammar/Patterns.lean) | `QualifiedPatternParses`, `PatternLayerOrdinaryParses` |
| [`Grammar/Expressions`](../../Solcore/Syntax/Grammar/Expressions.lean) | `ExpressionAtomOrdinaryParses`, `ExpressionPostfixParses`, `BinaryOperatorAtPrecedenceParses`, the precedence ladder `ExpressionLayerParses` |
| [`Grammar/YulFuel`](../../Solcore/Syntax/Grammar/YulFuel.lean) | `YulStatementOrdinaryParses`, `YulBodyOrdinaryParses` |
| [`Grammar/YulOrdinary`](../../Solcore/Syntax/Grammar/YulOrdinary.lean) | `YulExpressionLevel`, `YulExpressionOrdinaryParses` |
| [`Grammar/Yul`](../../Solcore/Syntax/Grammar/Yul.lean) | `YulNameOrdinaryParses`, `YulStatementLayerOrdinaryParses` |
| [`Grammar/Signatures`](../../Solcore/Syntax/Grammar/Signatures.lean) | `FunctionParameterCoreOrdinaryParses`, `PredicateRejects` |
| [`Grammar/Types`](../../Solcore/Syntax/Grammar/Types.lean) | `TypeExprOrdinaryParses`, `TypeExprRejects` |
| [`Grammar/Basics`](../../Solcore/Syntax/Grammar/Basics.lean) | `Remainder`, `TokenAt`, `DeterministicOutcomeSpec`, `ExactDeterministicOutcomeSpec`, `LexedFileValidationAccepts` |
| [`Validity`](../../Solcore/Syntax/Validity.lean) | When a tree's spans belong to a file: `ParsedFile.ValidFor`, `TopItem.ValidFor`, `Expr.ValidFor`, `CoreStatement.ValidFor`, `CoreExpr.ValidFor` |
| [`ValidityBasics`](../../Solcore/Syntax/ValidityBasics.lean) | `List.ValidFor`, `DelimitedList.ValidFor`, `QualifiedName.ValidFor` |

### Proofs in `Internal/`

Grammar-level proofs never mention the parser, except where a trace carries a parser diagnostic
type. An *Outcomes* file proves that a relation's outcomes are deterministic, with unique values and
rejection points; an *Exactness* file, that its outcomes fix the whole result; a *Trace* file, which
diagnostics it records. A new lemma goes in the cell of its construct.

| Construct | Outcomes | Exactness | Traces |
| --- | --- | --- | --- |
| Primitive tokens, delimited lists, transactional choice | [`DelimitedOutcomes`](../../Solcore/Syntax/Internal/DelimitedOutcomes.lean) | [`DelimitedExactness`](../../Solcore/Syntax/Internal/DelimitedExactness.lean) | [`DelimitedTrace`](../../Solcore/Syntax/Internal/DelimitedTrace.lean) |
| Identifiers and expression names |  |  | [`NameTrace`](../../Solcore/Syntax/Internal/NameTrace.lean) |
| Types and qualified names | [`TypeOutcomes`](../../Solcore/Syntax/Internal/TypeOutcomes.lean) | [`TypeExactness`](../../Solcore/Syntax/Internal/TypeExactness.lean) | [`TypeTrace`](../../Solcore/Syntax/Internal/TypeTrace.lean) |
| Parameters, predicates, signatures | [`ParameterOutcomes`](../../Solcore/Syntax/Internal/ParameterOutcomes.lean), [`SignatureOutcomes`](../../Solcore/Syntax/Internal/SignatureOutcomes.lean) | [`SignatureExactness`](../../Solcore/Syntax/Internal/SignatureExactness.lean) | [`ParameterTrace`](../../Solcore/Syntax/Internal/ParameterTrace.lean) |
| Expressions: atoms, operators, postfix tails, lambdas | [`ExpressionAtomOutcomes`](../../Solcore/Syntax/Internal/ExpressionAtomOutcomes.lean), [`ExpressionOutcomes`](../../Solcore/Syntax/Internal/ExpressionOutcomes.lean) |  | [`ExpressionTrace`](../../Solcore/Syntax/Internal/ExpressionTrace.lean), [`DotConstructorTrace`](../../Solcore/Syntax/Internal/DotConstructorTrace.lean) |
| Patterns | [`PatternOutcomes`](../../Solcore/Syntax/Internal/PatternOutcomes.lean) |  |  |
| Statements, blocks, loops, `match` | [`StatementOutcomes`](../../Solcore/Syntax/Internal/StatementOutcomes.lean) | [`StatementValues`](../../Solcore/Syntax/Internal/StatementValues.lean), [`BlockExactness`](../../Solcore/Syntax/Internal/BlockExactness.lean) | [`BlockTrace`](../../Solcore/Syntax/Internal/BlockTrace.lean) |
| Yul | [`YulBlockOutcomes`](../../Solcore/Syntax/Internal/YulBlockOutcomes.lean), [`YulStatementOutcomes`](../../Solcore/Syntax/Internal/YulStatementOutcomes.lean) |  |  |
| Declarations: members, contracts, implementations, traits, enums, `derive` | [`ContractMemberOutcomes`](../../Solcore/Syntax/Internal/ContractMemberOutcomes.lean), [`ContractBodyOutcomes`](../../Solcore/Syntax/Internal/ContractBodyOutcomes.lean), [`DeriveOutcomes`](../../Solcore/Syntax/Internal/DeriveOutcomes.lean) | [`DeclarationExactness`](../../Solcore/Syntax/Internal/DeclarationExactness.lean) |  |
| Imports, exports, module paths, pragmas | [`ImportOutcomes`](../../Solcore/Syntax/Internal/ImportOutcomes.lean), [`ExportOutcomes`](../../Solcore/Syntax/Internal/ExportOutcomes.lean) |  | [`PragmaTrace`](../../Solcore/Syntax/Internal/PragmaTrace.lean) |
| Top items, files, nesting, lexed validation | [`SourceFileOutcomes`](../../Solcore/Syntax/Internal/SourceFileOutcomes.lean) |  |  |
| Trace contracts and cascade laws |  |  | [`TraceBasics`](../../Solcore/Syntax/Internal/TraceBasics.lean) |

Parser-level proofs are in `Parser/Internal/`. A *Soundness* file proves that each success and each
rejection of a parser has its derivation; a *Totality* file, that on valid input the parser makes
progress and ends in an ordinary outcome; a *Trace* file, the parser side of the traces. A `Proofs`
or `Basics` file holds what was mixed with one parser's definitions before the layout refactor.

| Construct | Soundness | Totality | Traces | Other proofs |
| --- | --- | --- | --- | --- |
| Primitives, delimited lists, identifiers | [`DelimitedSoundness`](../../Solcore/Syntax/Parser/Internal/DelimitedSoundness.lean) | [`DelimitedTotality`](../../Solcore/Syntax/Parser/Internal/DelimitedTotality.lean) | [`DelimitedTrace`](../../Solcore/Syntax/Parser/Internal/DelimitedTrace.lean) | [`Basics`](../../Solcore/Syntax/Parser/Internal/Basics.lean) |
| Types, qualified names, type aliases | [`TypeSoundness`](../../Solcore/Syntax/Parser/Internal/TypeSoundness.lean) | [`TypeTotality`](../../Solcore/Syntax/Parser/Internal/TypeTotality.lean), [`TypeFormTotality`](../../Solcore/Syntax/Parser/Internal/TypeFormTotality.lean) | [`TypeTrace`](../../Solcore/Syntax/Parser/Internal/TypeTrace.lean) | [`TypeBasics`](../../Solcore/Syntax/Parser/Internal/TypeBasics.lean), [`TypeAliasProofs`](../../Solcore/Syntax/Parser/Internal/TypeAliasProofs.lean) |
| Parameters and predicates | [`ParameterSoundness`](../../Solcore/Syntax/Parser/Internal/ParameterSoundness.lean), [`LambdaParameterSoundness`](../../Solcore/Syntax/Parser/Internal/LambdaParameterSoundness.lean) | [`ParameterTotality`](../../Solcore/Syntax/Parser/Internal/ParameterTotality.lean), [`ParameterRecoveryTotality`](../../Solcore/Syntax/Parser/Internal/ParameterRecoveryTotality.lean), [`LambdaParameterRecovery`](../../Solcore/Syntax/Parser/Internal/LambdaParameterRecovery.lean) | [`ParameterTrace`](../../Solcore/Syntax/Parser/Internal/ParameterTrace.lean), [`ParameterListTrace`](../../Solcore/Syntax/Parser/Internal/ParameterListTrace.lean) | [`ParameterBasics`](../../Solcore/Syntax/Parser/Internal/ParameterBasics.lean) |
| Function signatures | [`SignatureSoundness`](../../Solcore/Syntax/Parser/Internal/SignatureSoundness.lean) |  |  |  |
| Expression atoms, parenthesized forms, array literals | [`ExpressionAtomSoundness`](../../Solcore/Syntax/Parser/Internal/ExpressionAtomSoundness.lean), [`CollectionSoundness`](../../Solcore/Syntax/Parser/Internal/CollectionSoundness.lean) |  | [`ExpressionAtomTrace`](../../Solcore/Syntax/Parser/Internal/ExpressionAtomTrace.lean), [`ParenthesizedTrace`](../../Solcore/Syntax/Parser/Internal/ParenthesizedTrace.lean) | [`ExpressionAtomProofs`](../../Solcore/Syntax/Parser/Internal/ExpressionAtomProofs.lean) |
| Operators, postfix tails, whole expressions, lambdas | [`OperatorSoundness`](../../Solcore/Syntax/Parser/Internal/OperatorSoundness.lean) | [`ExpressionTotality`](../../Solcore/Syntax/Parser/Internal/ExpressionTotality.lean) | [`PostfixTrace`](../../Solcore/Syntax/Parser/Internal/PostfixTrace.lean), [`LambdaTrace`](../../Solcore/Syntax/Parser/Internal/LambdaTrace.lean) | [`ExpressionProofs`](../../Solcore/Syntax/Parser/Internal/ExpressionProofs.lean) |
| Patterns | [`PatternSoundness`](../../Solcore/Syntax/Parser/Internal/PatternSoundness.lean), [`PatternCoreSoundness`](../../Solcore/Syntax/Parser/Internal/PatternCoreSoundness.lean), [`PatternStepSoundness`](../../Solcore/Syntax/Parser/Internal/PatternStepSoundness.lean) |  |  | [`PatternProofs`](../../Solcore/Syntax/Parser/Internal/PatternProofs.lean) |
| Statements and blocks | [`SimpleStatementSoundness`](../../Solcore/Syntax/Parser/Internal/SimpleStatementSoundness.lean), [`ControlSoundness`](../../Solcore/Syntax/Parser/Internal/ControlSoundness.lean), [`ForStatementSoundness`](../../Solcore/Syntax/Parser/Internal/ForStatementSoundness.lean), [`MatchSoundness`](../../Solcore/Syntax/Parser/Internal/MatchSoundness.lean), [`BlockSoundness`](../../Solcore/Syntax/Parser/Internal/BlockSoundness.lean), [`AssemblySoundness`](../../Solcore/Syntax/Parser/Internal/AssemblySoundness.lean) | [`StatementTotality`](../../Solcore/Syntax/Parser/Internal/StatementTotality.lean) | [`BlockTrace`](../../Solcore/Syntax/Parser/Internal/BlockTrace.lean) |  |
| The fuel-indexed term recursion | [`TermSoundness`](../../Solcore/Syntax/Parser/Internal/TermSoundness.lean) | [`TermTotality`](../../Solcore/Syntax/Parser/Internal/TermTotality.lean), [`PublicTermTotality`](../../Solcore/Syntax/Parser/Internal/PublicTermTotality.lean) |  | [`TermBasics`](../../Solcore/Syntax/Parser/Internal/TermBasics.lean) |
| Yul | [`YulExpressionSoundness`](../../Solcore/Syntax/Parser/Internal/YulExpressionSoundness.lean), [`YulAssignmentSoundness`](../../Solcore/Syntax/Parser/Internal/YulAssignmentSoundness.lean), [`YulStatementSoundness`](../../Solcore/Syntax/Parser/Internal/YulStatementSoundness.lean), [`YulSwitchSoundness`](../../Solcore/Syntax/Parser/Internal/YulSwitchSoundness.lean), [`YulBlockSoundness`](../../Solcore/Syntax/Parser/Internal/YulBlockSoundness.lean), [`YulPublicSoundness`](../../Solcore/Syntax/Parser/Internal/YulPublicSoundness.lean) | [`YulTotality`](../../Solcore/Syntax/Parser/Internal/YulTotality.lean) |  |  |
| Declarations | [`DeriveSoundness`](../../Solcore/Syntax/Parser/Internal/DeriveSoundness.lean), [`ContractBodySoundness`](../../Solcore/Syntax/Parser/Internal/ContractBodySoundness.lean), [`ContractOutcomeSoundness`](../../Solcore/Syntax/Parser/Internal/ContractOutcomeSoundness.lean) | [`DeclarationTotality`](../../Solcore/Syntax/Parser/Internal/DeclarationTotality.lean) |  | [`Completeness`](../../Solcore/Syntax/Parser/Internal/Completeness.lean), [`ContractProofs`](../../Solcore/Syntax/Parser/Internal/ContractProofs.lean), [`ContractEntryProofs`](../../Solcore/Syntax/Parser/Internal/ContractEntryProofs.lean), [`ImplProofs`](../../Solcore/Syntax/Parser/Internal/ImplProofs.lean), [`TraitProofs`](../../Solcore/Syntax/Parser/Internal/TraitProofs.lean), [`EnumProofs`](../../Solcore/Syntax/Parser/Internal/EnumProofs.lean) |
| Imports, exports, pragmas | [`ImportSoundness`](../../Solcore/Syntax/Parser/Internal/ImportSoundness.lean), [`ExportSoundness`](../../Solcore/Syntax/Parser/Internal/ExportSoundness.lean) | [`ModuleTotality`](../../Solcore/Syntax/Parser/Internal/ModuleTotality.lean) | [`PragmaTrace`](../../Solcore/Syntax/Parser/Internal/PragmaTrace.lean) | [`ImportProofs`](../../Solcore/Syntax/Parser/Internal/ImportProofs.lean), [`ExportProofs`](../../Solcore/Syntax/Parser/Internal/ExportProofs.lean) |
| Top items, files, entry points, comments | [`SourceFileSoundness`](../../Solcore/Syntax/Parser/Internal/SourceFileSoundness.lean) | [`FileTotality`](../../Solcore/Syntax/Parser/Internal/FileTotality.lean) | [`SourceFileTrace`](../../Solcore/Syntax/Parser/Internal/SourceFileTrace.lean) | [`FileProofs`](../../Solcore/Syntax/Parser/Internal/FileProofs.lean), [`ParseProperties`](../../Solcore/Syntax/Parser/Internal/ParseProperties.lean), [`TriviaProofs`](../../Solcore/Syntax/Parser/Internal/TriviaProofs.lean) |
| Shared |  |  | [`DiagnosticTrace`](../../Solcore/Syntax/Parser/Internal/DiagnosticTrace.lean), [`TraceSummary`](../../Solcore/Syntax/Parser/Internal/TraceSummary.lean) | [`OutcomeCompleteness`](../../Solcore/Syntax/Parser/Internal/OutcomeCompleteness.lean) |

## Definitions and theorems you build on

**What other areas use.** These are definitions; no other area uses a Syntax theorem.

| Definition | Reading | Used by |
| --- | --- | --- |
| `Parser.parse`, `ParseOutput` | The total parse of one file, with its diagnostics | `parseWorkspaceFile` in `Frontend/ProgramInterfaces` |
| `Unchecked.prepare`, `Unchecked.mark`, `Unchecked.Error` | The pass around `parse` for `unchecked` blocks | The same function; its errors become `ProgramLoadError.uncheckedBlock` |
| The AST: `ParsedFile`, `TopItem`, `FunctionDecl`, `TypeExpr`, `Expr`, `Statement`, `Block`, `Pattern`, `ForItem` | What the parser produces | The frontend's loading, signatures and inference; the source semantics and core lowering through the typed IR |
| `UnaryOp`, `BinaryOp`, `ValueAssignOp`, `BinaryOp.precedence`, `ValueAssignOp.wordOnly` | The operators; `wordOnly` marks the compound assignments that take Words only | The typed IR, `SourceInference.Detail.binaryOperatorDispatch`, the lowering, the source semantics, and the assignment premises of core lowering theorems |
| `CoreLiteral` | Literal spellings | `Frontend/WordLiteral` |

**What the area proves.** The Syntax tests name these theorems, and a change must keep them proved.

| Result | Theorems | File |
| --- | --- | --- |
| The lexer is total, and its spans belong to the file in order | `Lexer.lex_exists_ok`, `Lexer.lex_error_impossible`, `Lexer.lex_ok_validFor`, `Lexer.lex_total_validFor` | `Lexer/Properties` |
| The parser is total | `Parser.productionParse_exists_ok`, `Parser.productionParseLexed_exists_ok` | `Parser/Correctness` |
| Soundness: a result has a derivation | `Parser.parse_ok_publicSourceFileOrdinary_sound`; for a diagnostic-free parse, the Core grammar, `Parser.parse_ok_coreOrdinary_sound_and_validFor` | `Parser/Correctness` |
| Completeness: a result with this AST exists exactly when the grammar derives it | `Parser.parse_exists_ok_iff_publicSourceFileOrdinary`, `Parser.parseLexed_exists_ok_iff_publicSourceFileOrdinary` | `Parser/Correctness` |
| Uniqueness | `Parser.parse_ok_parsed_value_unique`; for the grammar alone, `DeclarativeGrammar.publicSourceFileOrdinary_exists_unique_of_validation` | `Parser/Correctness` |
| Provenance: every span in the output belongs to the file | `Parser.parse_ok_completeOutput_validFor`, `DeclarativeGrammar.PublicSourceFileOrdinaryParses.validFor_of_lexing` | `Parser/Correctness` |
| One certified branch for every token input | `Parser.productionParseLexed_certifiedOutcome`, `Parser.productionParseLexed_error_iff_validationRejects` | `Parser/Correctness` |
| The exact output, diagnostics included, on complete slices | `Parser.parse_eq_ok_of_emptyTokens`, `Parser.parse_eq_ok_singlePragma_iff`, `Parser.parse_eq_ok_singleRecovery_iff` | `Parser/PublicOutputs` |

These rest on three contracts, which a new construct extends:
- `DeterministicOutcomeSpec` and `ExactDeterministicOutcomeSpec` (`Grammar/Basics`), the outcome
  contracts that the grammar relations are proved to meet. Each fuel level in `Grammar/TermLevels`
  carries its `DeterministicOutcomeSpec` as a field.
- `DeclarativeGrammar.topItemExactOutcomeSpec` (`Internal/DeclarationExactness`). Uniqueness and
  completeness are proved from it.
- `PlainTopItemTotalityContract` (`Parser/Internal/FileTotality`). Totality is proved from its
  instance `FileInternals.productionPlainTopItemTotalityContract` in `Parser/Correctness`, which has
  one field per kind of top-level declaration.

## Making changes

Two language changes have reached Syntax since the parser was built: shifts went through the grammar
and its proofs, and `unchecked` blocks went around the parser. Their commits name the paths from
before the layout refactor; [Conventions](conventions.md#following-older-notes) says how to map
them. [Adding a language feature](adding-a-feature.md) follows a change through every layer.

### An operator, or a spelling made of existing tokens

Worked example: 5b8c6e96d, the shifts `<<`, `>>`, `<<=` and `>>=`.

1. **AST and decoding**, in `Syntax/Operator`. Add the constructors, with their cases in
   `precedence` and `symbol`. A two-token spelling also needs `secondSymbol?` and a case in
   `BinaryOp.spelled?` or `ValueAssignOp.spelled?`. The parser and the grammar both decode through
   `BinaryOp.at?` and `ValueAssignOp.at?`, so they cannot disagree on spellings.
2. **Tokens**: unchanged. `<<` is two adjacent `<` tokens, so that `Box<Box<Word>>` still closes
   with two `>` tokens.
3. **Parser**, in `Parser/Terms`: `ExpressionInternals.binaryAtPrecedence?` and
   `StatementSimpleInternals.valueAssignAt?` decode with `at?`, `consumeBinary` advances by the
   operator's `tokenCount`, and `Parser.expressionLayer` holds the precedence ladder.
4. **Grammar**: `BinaryOperatorAtPrecedenceParses` and the ladder `ExpressionLayerParses` in
   `Grammar/Expressions`, and `ValueAssignOperatorParses` in `Grammar/Statements`.
5. **Grammar proofs**: `Internal/ExpressionOutcomes` and `Internal/StatementOutcomes`.
6. **Parser proofs**, in `Parser/Internal/`: `OperatorSoundness`, `ExpressionAtomSoundness`,
   `ExpressionProofs`, `ExpressionTotality`, `PostfixTrace`, `SimpleStatementSoundness` and
   `TermTotality`. The statements in `Parser/Correctness` did not change.
7. **Downstream**: every exhaustive match on the operator types. See
   [Frontend](frontend.md#a-new-construct-in-the-native-compiler).
8. **Tests**: the public-API test `Tests.SourceCoreShiftExecution` in
   [`Foundations/Execution`](../../Solcore/Test/SourceSemantics/CoreLowering/Foundations/Execution.lean),
   called from [`Tests/Main.lean`](../../Tests/Main.lean). It also checks that separated tokens,
   as in `a < < b`, are rejected.

### A form that a pass around the parser can handle

Worked example: e8d28e957, `unchecked { … }` blocks.

- `Unchecked.prepare` finds each `unchecked` at a statement start followed by `{`, and replaces the
  keyword's bytes with spaces. The parser reads a plain block, and every span stays the same.
- After parsing, `Unchecked.mark` gives the block's `+ - *` and `+= -= *=` the unchecked operators
  of `Syntax/Operator` (`uncheckedAdd` and the others), which the parser never produces.
- The frontend's `parseWorkspaceFile` runs `prepare`, `parse` and `mark` in that order, and reports
  a pass error as `ProgramLoadError.uncheckedBlock`.
- No grammar, parser or proof changed: the parser theorems describe the blanked file. In exchange,
  the grammar says nothing about `unchecked`, and `Syntax/Unchecked` has no theorems.
- A statement form was not used because inference's proofs name the numbered cases of its
  traversal; see
  [the integer design note](../design/integer-types-unchecked-shifts.md#unchecked-blocks-as-implemented-without-division).
- Tests: `Tests.SourceCoreUncheckedExecution`, in the same test file, includes programs that the
  pass rejects while loading.

### A new expression, statement or declaration form

No commit since the parser was built has added one, so this order follows the structure of the code.

1. **Tokens**, only if no spelling from existing tokens works: a `Symbol`, `HardKeyword` or
   `ContextualKeyword` in `Token` with its `spelling` (and `ofString?` for a keyword), and a symbol's
   entry in `multiSymbol?` or `singleSymbol?` in `Lexer/Character`. The lexer's proofs are in
   `Lexer/ScanProperties` and `Lexer/Properties`.
2. **AST**: a constructor in `Term`, `Type`, `Yul`, `Declaration` or `Module`.
3. **Validity**: a constructor of the matching judgment in `Validity`, such as `Expr.ValidFor`,
   covering every span of the form.
4. **Parser**: the production in its front file.
5. **Grammar**: the relation in its `Grammar/` file and, for a term, its step in
   `Grammar/TermLevels`.
6. **Grammar proofs**: the Outcomes, Exactness and Trace cells of its construct.
7. **Parser proofs**: the lemma family that `enumDecl` has, named after the production:
   `_invariantFreeOnValid` and `_ne_invariant` (totality), `_cursor_lt_onSuccess` and
   `_preservesTokenWindow` (progress), `_ordinaryOutcome_sound` and `_success_sound_and_validFor`
   (soundness and provenance), `_ordinary_success_iff` and `_ordinary_reject_iff` (completeness), and
   `_exactOutcomeSpec`. A new kind of top-level declaration also adds a field to
   `PlainTopItemTotalityContract`, and `topItemExactOutcomeSpec` must cover it.
8. **`Syntax/Unchecked`**: a case in `Unchecked.expression` or `Unchecked.statement` when the form
   holds expressions or statements. Then the downstream matches and the tests, as for an operator.

## Pitfalls

- **What the frontend imports rebuilds everything above.** `ProgramInterfaces` imports
  `Syntax/Unchecked` and `Syntax/Declaration`. Their closure holds the AST and source files but
  `Identifier`, the lexer but `Lexer/Properties`, the parser files but `Parser/Correctness` and
  `Parser/PublicOutputs`, `Grammar/Basics`, `Validity`, `ValidityBasics`, and three proof files:
  `Parser/Internal/Basics`, `TypeBasics` and `ParameterBasics`. An edit there rebuilds the frontend
  and everything that imports it; an edit elsewhere in Syntax rebuilds only Syntax and its tests.
  Keep those three proof files small, and import no other proof file from the front.
- **Some front files hold proofs.** `private` is per file, so a theorem that names a private helper
  stays in the helper's file. `Parser/Signatures` (`finishFunctionModifiers`,
  `emitModifierOutsideContract`) and `Parser/Blocks` keep every theorem that names their private
  helpers, and what those theorems need. `Parser/SourceFiles` keeps the lemmas of its diagnostic
  filter, `Parser/State` those of the parser state, and `Syntax/Operator` those of its decoders.
- **Grammar levels carry their proofs.** A fuel level such as `CoreExpressionLevel` bundles a relation
  with its `DeterministicOutcomeSpec`. So `Grammar/TermLevels`, `Grammar/StatementLayer`,
  `Grammar/YulFuel` and `Grammar/YulOrdinary` hold outcome lemmas or import `Internal/` files, and a
  changed relation there needs its determinism proof at that point.
- **The precedence ladder is written three times**: `BinaryOp.precedence`, `Parser.expressionLayer`
  and `DeclarativeGrammar.ExpressionLayerParses`. Change them together.
- **The grammar must not call the parser.** Token decoding that both need belongs in the AST layer,
  as `BinaryOp.at?` does in `Syntax/Operator`.
- **A new token can break old inputs.** A `>>` token would stop `Box<Box<Word>>` from closing, which
  is why shifts are two tokens. Their decoder requires the two tokens to touch, so `a < < b` is
  rejected.
- **`Unchecked` skips forms it does not know.** `Unchecked.expression` and `Unchecked.statement` end
  with a catch-all case that returns the form unchanged. A new form that holds expressions or
  statements builds without a case there, but an `unchecked` block does not reach inside it.
- **Downstream proofs number their cases.** Inference proofs do functional induction on
  `inferExprFuel` and name its cases by number, in `Frontend/SourceInference/Internal` and
  `SourceSemantics/Internal`. A new expression or statement constructor shifts them; see
  [Frontend](frontend.md#pitfalls).
- **Three separations are forced.**
  - `Parser/Internal/LambdaParameterRecovery` and `Parser/Internal/ParameterTotality` both declare
    `LambdaParameterInternals.recoverLambdaParameter_ordinary` and
    `recoverLambdaParameter_ne_invariant`. Lean accepts the same theorem from two imported files, but
    not in a file that imports the other copy, so neither file may import the other.
  - `Parser/Internal/AssemblySoundness` stays apart from `ControlSoundness`. It needs the public Yul
    results, and their `@[simp]` lemma `yulStatement_executableFuel_eq_publicFuel` must stay out of
    the statement totality proofs.
  - `Internal/ContractMemberOutcomes` and `Internal/ContractBodyOutcomes` each have a different
    private `absent_conflicts_token`, and the first also has `absent_conflicts_token_variant`.
- **Private helper names repeat across files**, as `absent_conflicts_token` does in many `Internal/`
  files. Moving code between files can make two of them clash; rename one. The layout refactor used
  a `_variant` suffix.
- **Tests name theorems.** The Syntax tests check theorem names with `example := @name`, internal
  ones included. Renaming or deleting a theorem breaks them, so update the tests in the same change.
- **The kernel check is textual.** Words such as `partial` fail even in comments; see
  [Conventions](conventions.md#proof-rules).

## Testing

```sh
lake build Solcore.Syntax                  # the area, with its main theorems
lake build Solcore.Test.Syntax.Statements  # one test file
lake test                                  # every test, through Tests/Main.lean
```

Lean checks a test file's examples and theorems while it builds the file. `Tests/Main.lean`
imports every Syntax test file, and runs the public-API tests that reach the compiler, such as
`Tests.SourceCoreShiftExecution` and `Tests.SourceCoreUncheckedExecution`.

| Subject | Test files in `Solcore/Test/Syntax/` |
| --- | --- |
| Lexer, tokens, spans, comment attachment | [`LexerAndTrivia`](../../Solcore/Test/Syntax/LexerAndTrivia.lean) |
| Types, parameters, declarations | [`Types`](../../Solcore/Test/Syntax/Types.lean), [`Parameters`](../../Solcore/Test/Syntax/Parameters.lean), [`Declarations`](../../Solcore/Test/Syntax/Declarations.lean) |
| Expressions, patterns, statements, blocks, Yul | [`ExpressionAtoms`](../../Solcore/Test/Syntax/ExpressionAtoms.lean), [`ExpressionsAndPatterns`](../../Solcore/Test/Syntax/ExpressionsAndPatterns.lean), [`Statements`](../../Solcore/Test/Syntax/Statements.lean), [`CoreBlocks`](../../Solcore/Test/Syntax/CoreBlocks.lean), [`Yul`](../../Solcore/Test/Syntax/Yul.lean) |
| Modules, pragmas, whole files, the public entry points | [`ModulesAndImports`](../../Solcore/Test/Syntax/ModulesAndImports.lean), [`Pragmas`](../../Solcore/Test/Syntax/Pragmas.lean), [`PublicBoundary`](../../Solcore/Test/Syntax/PublicBoundary.lean) |
| Diagnostics, recovery, traces, operator tables | [`Diagnostics`](../../Solcore/Test/Syntax/Diagnostics.lean), [`Recovery`](../../Solcore/Test/Syntax/Recovery.lean), [`CanonicalTraces`](../../Solcore/Test/Syntax/CanonicalTraces.lean) |
