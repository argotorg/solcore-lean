# Reviewer's guide: Syntax

`Solcore/Syntax` holds the AST, the lexer, the parser, and the proofs that the parser matches
an independent grammar. The [umbrella](../../Solcore/Syntax.lean) gives this reading order in
brief.

## Reading order

1. **AST.** What the parser produces.
2. **Lexer.** From a source file to tokens.
3. **Parser.** `parse` and the productions it calls.
4. **Grammar.** The specification: which token sequences derive which AST, with no reference
   to the parser. Start at `PublicSourceFileOrdinaryParses`.
5. **Main theorems.** The parser against the grammar.

Everything else is proof machinery in `Internal/` and `Parser/Internal/`.

## Front

### AST and source

| File | Main declarations |
| --- | --- |
| [`Foundation`](../../Solcore/Syntax/Foundation.lean) | `Identifier`, `QualifiedName`, `DelimitedList` |
| [`Source`](../../Solcore/Syntax/Source.lean) | `SourceFile`, `SourceSpan`, `Located`, `Comment` |
| [`Token`](../../Solcore/Syntax/Token.lean) | `Token`, `TokenKind`, `HardKeyword`, `Symbol` |
| [`SpanSequence`](../../Solcore/Syntax/SpanSequence.lean) | `SpanSequence.ValidFor` |
| [`Identifier`](../../Solcore/Syntax/Identifier.lean) | `isValidIdentifier` |
| [`Literal`](../../Solcore/Syntax/Literal.lean) | `CoreLiteral`, `YulLiteral` |
| [`Operator`](../../Solcore/Syntax/Operator.lean) | `UnaryOp`, `BinaryOp`, `ValueAssignOp` |
| [`Type`](../../Solcore/Syntax/Type.lean) | `TypeExpr`, `Predicate`, `FunctionParameter`, `LambdaParameter` |
| [`Term`](../../Solcore/Syntax/Term.lean) | `Expr`, `Pattern`, `Statement`, `Block` |
| [`Yul`](../../Solcore/Syntax/Yul.lean) | `YulExpr`, `YulStmt` |
| [`Declaration`](../../Solcore/Syntax/Declaration.lean) | `ParsedFile`, `TopItem`, `FunctionDecl`, `ContractDecl` |
| [`Module`](../../Solcore/Syntax/Module.lean) | `ModulePath`, `ImportDecl`, `ExportDecl`, `PragmaDecl` |
| [`Trivia`](../../Solcore/Syntax/Trivia.lean) | comment attachment |
| [`Unchecked`](../../Solcore/Syntax/Unchecked.lean) | `unchecked` blocks, removed around the parser |

### Lexer

| File | Main declarations |
| --- | --- |
| [`Lexer`](../../Solcore/Syntax/Lexer.lean) | the public boundary |
| [`Lexer/Core`](../../Solcore/Syntax/Lexer/Core.lean) | `lex`, `lexLoop` |
| [`Lexer/Result`](../../Solcore/Syntax/Lexer/Result.lean) | `LexedFile`, `LexicalDiagnostic`, `LexResult` |
| [`Lexer/Contract`](../../Solcore/Syntax/Lexer/Contract.lean) | `LexedFile.ValidFor` |
| [`Lexer/Step`](../../Solcore/Syntax/Lexer/Step.lean) | `step` |
| [`Lexer/State`](../../Solcore/Syntax/Lexer/State.lean) | the lexer's `State` |
| [`Lexer/Scan`](../../Solcore/Syntax/Lexer/Scan.lean) | comment and string scanners |
| [`Lexer/Character`](../../Solcore/Syntax/Lexer/Character.lean) | character classes |
| [`Lexer/Invariant`](../../Solcore/Syntax/Lexer/Invariant.lean) | `CursorSuffix` |
| [`Lexer/ScanProperties`](../../Solcore/Syntax/Lexer/ScanProperties.lean) | progress laws of the scanners |
| [`Unicode/Letter`](../../Solcore/Syntax/Unicode/Letter.lean) | `isLetter` |
| [`Unicode/Lowercase`](../../Solcore/Syntax/Unicode/Lowercase.lean) | `isLowercase` |
| [`Unicode/Number`](../../Solcore/Syntax/Unicode/Number.lean) | `isNumber` |
| [`Unicode/Range`](../../Solcore/Syntax/Unicode/Range.lean) | `ScalarRange` |

### Parser

The productions read in dependency order, top to bottom.

| File | Main declarations |
| --- | --- |
| [`Parser`](../../Solcore/Syntax/Parser.lean) | `parse`, `parseLexed` |
| [`Parser/Diagnostic`](../../Solcore/Syntax/Parser/Diagnostic.lean) | `ParseDiagnostic`, `ParserInvariantError` |
| [`Parser/Result`](../../Solcore/Syntax/Parser/Result.lean) | `ParseOutput`, `ParseResult` |
| [`Parser/State`](../../Solcore/Syntax/Parser/State.lean) | `State`, `Reply`, `Parser` |
| [`Parser/Primitive`](../../Solcore/Syntax/Parser/Primitive.lean) | `acceptToken`, `keyword`, `symbol` |
| [`Parser/Tokens`](../../Solcore/Syntax/Parser/Tokens.lean) | `qualifiedName`, `coreLiteral`, `delimited` |
| [`Parser/Types`](../../Solcore/Syntax/Parser/Types.lean) | `typeExpr`, `predicate`, `namedParameter`, `lambdaParameter` |
| [`Parser/Signatures`](../../Solcore/Syntax/Parser/Signatures.lean) | `functionSignature`, `functionParameters` |
| [`Parser/Blocks`](../../Solcore/Syntax/Parser/Blocks.lean) | `captureBlock?`, `coreBlock` |
| [`Parser/Yul`](../../Solcore/Syntax/Parser/Yul.lean) | `yulExpression`, `yulBlock`, `yulBody` |
| [`Parser/Terms`](../../Solcore/Syntax/Parser/Terms.lean) | `expression`, `pattern`, `statement`, `block` |
| [`Parser/Declarations`](../../Solcore/Syntax/Parser/Declarations.lean) | `functionDecl`, `contractDecl`, `implDecl`, `traitDecl`, `enumDecl` |
| [`Parser/Modules`](../../Solcore/Syntax/Parser/Modules.lean) | `modulePath`, `importDecl`, `exportDecl`, `pragmaDecl` |
| [`Parser/SourceFiles`](../../Solcore/Syntax/Parser/SourceFiles.lean) | `sourceFile`, `topItem`, `checkNesting`, `validateLexed` |

### Grammar

This is the specification. Read it from the top: each file uses the ones below it.

| File | Main declarations |
| --- | --- |
| [`Grammar/SourceFile`](../../Solcore/Syntax/Grammar/SourceFile.lean) | `PublicSourceFileOrdinaryParses`, `SourceFileOrdinaryParses`, `TopItemOrdinaryParses` |
| [`Grammar/Declarations`](../../Solcore/Syntax/Grammar/Declarations.lean) | `TraitDeclOrdinaryParses`, `ContractBodyOrdinaryParses`, `ImplBodyOrdinaryParses` |
| [`Grammar/Modules`](../../Solcore/Syntax/Grammar/Modules.lean) | `ModulePathOrdinaryParses`, `PragmaDeclOrdinaryParses`, `ExportPathOrdinaryParses` |
| [`Grammar/TermLevels`](../../Solcore/Syntax/Grammar/TermLevels.lean) | `CoreTermLevel`, `CoreExpressionOrdinaryParses`, `CoreStatementOrdinaryParses` |
| [`Grammar/StatementLayer`](../../Solcore/Syntax/Grammar/StatementLayer.lean) | `StatementLayerOrdinaryParses`, `MatchStatementOrdinaryParses` |
| [`Grammar/Statements`](../../Solcore/Syntax/Grammar/Statements.lean) | `CoreBlockOrdinaryParses`, `IfStatementOrdinaryParses` |
| [`Grammar/Patterns`](../../Solcore/Syntax/Grammar/Patterns.lean) | `QualifiedPatternParses`, `PatternLayerOrdinaryParses` |
| [`Grammar/Expressions`](../../Solcore/Syntax/Grammar/Expressions.lean) | `ExpressionAtomOrdinaryParses`, `ExpressionPostfixParses` |
| [`Grammar/YulFuel`](../../Solcore/Syntax/Grammar/YulFuel.lean) | `YulStatementOrdinaryParses`, `YulBodyOrdinaryParses` |
| [`Grammar/YulOrdinary`](../../Solcore/Syntax/Grammar/YulOrdinary.lean) | `YulExpressionLevel`, `YulExpressionOrdinaryParses` |
| [`Grammar/Yul`](../../Solcore/Syntax/Grammar/Yul.lean) | `YulNameOrdinaryParses`, `YulStatementLayerOrdinaryParses` |
| [`Grammar/Signatures`](../../Solcore/Syntax/Grammar/Signatures.lean) | `FunctionParameterCoreOrdinaryParses`, `PredicateRejects` |
| [`Grammar/Types`](../../Solcore/Syntax/Grammar/Types.lean) | `TypeExprOrdinaryParses`, `TypeExprRejects` |
| [`Grammar/Basics`](../../Solcore/Syntax/Grammar/Basics.lean) | `Remainder`, `TokenAt`, `DeterministicOutcomeSpec`, `LexedFileValidationAccepts` |

### Validity

| File | Main declarations |
| --- | --- |
| [`Validity`](../../Solcore/Syntax/Validity.lean) | `ParsedFile.ValidFor`, `CoreStatement.ValidFor`, `CoreExpr.ValidFor` |
| [`ValidityBasics`](../../Solcore/Syntax/ValidityBasics.lean) | `List.ValidFor`, `QualifiedName.ValidFor` |

## Main theorems

These are the results the area claims, "parser correctness" in the layout plan. They are the top
of the theorem dependencies in this area.

| Result | Theorems | File | Reading |
| --- | --- | --- | --- |
| The lexer is total | `Lexer.lex_exists_ok`, `Lexer.lex_error_impossible` | [`Lexer/Properties`](../../Solcore/Syntax/Lexer/Properties.lean) | every source file lexes |
| Lexing is valid for the file | `Lexer.lex_ok_validFor`, `Lexer.lex_total_validFor` | [`Lexer/Properties`](../../Solcore/Syntax/Lexer/Properties.lean) | every lexed span belongs to the file, in order |
| The parser is total | `Parser.productionParse_exists_ok`, `Parser.productionParseLexed_exists_ok` | [`Parser/Correctness`](../../Solcore/Syntax/Parser/Correctness.lean) | every source file parses, and valid tokens parse without an invariant error |
| Soundness | `Parser.parse_ok_publicSourceFileOrdinary_sound` | [`Parser/Correctness`](../../Solcore/Syntax/Parser/Correctness.lean) | a parse result has a derivation in the independent grammar |
| Completeness | `Parser.parse_exists_ok_iff_publicSourceFileOrdinary`, `Parser.parseLexed_exists_ok_iff_publicSourceFileOrdinary` | [`Parser/Correctness`](../../Solcore/Syntax/Parser/Correctness.lean) | a result with this AST exists exactly when the grammar derives it |
| Uniqueness of the parse | `Parser.parse_ok_parsed_value_unique` | [`Parser/Correctness`](../../Solcore/Syntax/Parser/Correctness.lean) | one source file has one AST |
| Uniqueness in the grammar | `DeclarativeGrammar.publicSourceFileOrdinary_exists_unique_of_validation` | [`Parser/Correctness`](../../Solcore/Syntax/Parser/Correctness.lean) | the grammar alone determines one AST |
| Provenance of the output | `Parser.parse_ok_completeOutput_validFor`, `Parser.productionParse_exists_ok_completeOutput_validFor` | [`Parser/Correctness`](../../Solcore/Syntax/Parser/Correctness.lean) | every span in the output belongs to the file |
| Provenance from the grammar | `DeclarativeGrammar.PublicSourceFileOrdinaryParses.validFor_of_lexing` | [`Parser/Correctness`](../../Solcore/Syntax/Parser/Correctness.lean) | any derivation over lexed carriers has valid spans |
| Certified outcome | `Parser.productionParseLexed_certifiedOutcome` | [`Parser/Correctness`](../../Solcore/Syntax/Parser/Correctness.lean) | every token input takes one of two fully described branches |
| Errors | `Parser.productionParseLexed_error_iff_validationRejects` | [`Parser/Correctness`](../../Solcore/Syntax/Parser/Correctness.lean) | a token-level error is exactly the first validation failure |
| Diagnostic-free Core | `Parser.parse_ok_coreOrdinary_sound_and_validFor` | [`Parser/Correctness`](../../Solcore/Syntax/Parser/Correctness.lean) | a parse with no diagnostics has a derivation in the Core grammar |
| Exact output on slices | `Parser.parse_eq_ok_of_emptyTokens`, `Parser.parse_eq_ok_singlePragma_iff`, `Parser.parse_eq_ok_singleRecovery_iff` | [`Parser/PublicOutputs`](../../Solcore/Syntax/Parser/PublicOutputs.lean) | on these inputs the whole `ParseOutput` is known, diagnostics included |

Below these, each construct has its own pair of results, such as
`Parser.statement_ordinary_success_iff` in `Parser/Internal/TermSoundness` and
`Parser.contractDecl_ordinary_success_iff` in `Parser/Internal/Completeness`.
[`Parser/Internal/TraceSummary`](../../Solcore/Syntax/Parser/Internal/TraceSummary.lean) describes the diagnostic-trace results layer by layer.

## Internal

Grammar-level proofs are in `Internal/`. They never mention the parser, except where a trace
relation carries a parser diagnostic type.

| File | Topic |
| --- | --- |
| [`BlockExactness`](../../Solcore/Syntax/Internal/BlockExactness.lean) | Exactness of the declarative grammar of Core blocks |
| [`BlockTrace`](../../Solcore/Syntax/Internal/BlockTrace.lean) | Exact diagnostic traces of Core blocks, block statements, return statements and terminated control |
| [`ContractBodyOutcomes`](../../Solcore/Syntax/Internal/ContractBodyOutcomes.lean) | Properties of the declarative grammar of contract bodies, contract declarations and implementations |
| [`ContractMemberOutcomes`](../../Solcore/Syntax/Internal/ContractMemberOutcomes.lean) | Properties of the declarative grammar of enums, traits, function declarations and contract members |
| [`DeclarationExactness`](../../Solcore/Syntax/Internal/DeclarationExactness.lean) | Exactness of the declarative grammar of contract members, implementations, traits and enums |
| [`DelimitedExactness`](../../Solcore/Syntax/Internal/DelimitedExactness.lean) | Exactness of the declarative grammar of delimited lists |
| [`DelimitedOutcomes`](../../Solcore/Syntax/Internal/DelimitedOutcomes.lean) | Properties of the declarative grammar of delimited lists, transactional choice and primitive tokens |
| [`DelimitedTrace`](../../Solcore/Syntax/Internal/DelimitedTrace.lean) | Exact diagnostic traces of delimited lists, with and without a trailing separator |
| [`DeriveOutcomes`](../../Solcore/Syntax/Internal/DeriveOutcomes.lean) | Properties of the declarative grammar of derive attributes, type aliases and contract entries |
| [`DotConstructorTrace`](../../Solcore/Syntax/Internal/DotConstructorTrace.lean) | Exact diagnostic traces of leading-dot constructors, postfix tails and lambda expressions |
| [`ExportOutcomes`](../../Solcore/Syntax/Internal/ExportOutcomes.lean) | Properties of the declarative grammar of exports |
| [`ExpressionAtomOutcomes`](../../Solcore/Syntax/Internal/ExpressionAtomOutcomes.lean) | Properties of the declarative grammar of expression atoms and one expression step |
| [`ExpressionOutcomes`](../../Solcore/Syntax/Internal/ExpressionOutcomes.lean) | Properties of the declarative grammar of operators, parenthesized forms, postfix tails and atom recovery |
| [`ExpressionTrace`](../../Solcore/Syntax/Internal/ExpressionTrace.lean) | Exact diagnostic traces of parenthesized forms, array literals, operators and expression atoms |
| [`ImportOutcomes`](../../Solcore/Syntax/Internal/ImportOutcomes.lean) | Properties of the declarative grammar of imports, module paths and pragmas |
| [`NameTrace`](../../Solcore/Syntax/Internal/NameTrace.lean) | Exact diagnostic traces of identifiers and expression names, with the cascade laws of a checked identifier |
| [`ParameterOutcomes`](../../Solcore/Syntax/Internal/ParameterOutcomes.lean) | Properties of the declarative grammar of parameters and predicates |
| [`ParameterTrace`](../../Solcore/Syntax/Internal/ParameterTrace.lean) | Exact diagnostic traces of function and lambda parameters |
| [`PatternOutcomes`](../../Solcore/Syntax/Internal/PatternOutcomes.lean) | Properties of the declarative grammar of patterns |
| [`PragmaTrace`](../../Solcore/Syntax/Internal/PragmaTrace.lean) | Exact diagnostic traces of pragmas |
| [`SignatureExactness`](../../Solcore/Syntax/Internal/SignatureExactness.lean) | Exactness of the declarative grammar of predicates, parameters, signatures and expression fuel |
| [`SignatureOutcomes`](../../Solcore/Syntax/Internal/SignatureOutcomes.lean) | Properties of the declarative grammar of function signatures, generic parameters and modifiers |
| [`SourceFileOutcomes`](../../Solcore/Syntax/Internal/SourceFileOutcomes.lean) | Properties of the declarative grammar of top items, file items, nesting and lexed validation |
| [`StatementOutcomes`](../../Solcore/Syntax/Internal/StatementOutcomes.lean) | Properties of the declarative grammar of simple statements, blocks, loops and `match` cases |
| [`StatementValues`](../../Solcore/Syntax/Internal/StatementValues.lean) | Exactness of the declarative grammar of statement branches, `for` items and `match` components |
| [`TraceBasics`](../../Solcore/Syntax/Internal/TraceBasics.lean) | Foundations of the grammar's exact diagnostic traces |
| [`TypeExactness`](../../Solcore/Syntax/Internal/TypeExactness.lean) | Exactness of the declarative grammar of type expressions |
| [`TypeOutcomes`](../../Solcore/Syntax/Internal/TypeOutcomes.lean) | Properties of the declarative grammar of core types and qualified names |
| [`TypeTrace`](../../Solcore/Syntax/Internal/TypeTrace.lean) | Exact diagnostic traces of type expressions |
| [`YulBlockOutcomes`](../../Solcore/Syntax/Internal/YulBlockOutcomes.lean) | Properties of the declarative grammar of Yul names, blocks and terminated statements |
| [`YulStatementOutcomes`](../../Solcore/Syntax/Internal/YulStatementOutcomes.lean) | Properties of the declarative grammar of Yul assignments, control flow, functions and switches |

Parser-level proofs are in `Parser/Internal/`. A `Proofs` file holds what was mixed with one
parser's definitions. A `Soundness`, `Totality`, `Completeness` or `Trace` file holds that stage
for one construct.

| File | Topic |
| --- | --- |
| [`AssemblySoundness`](../../Solcore/Syntax/Parser/Internal/AssemblySoundness.lean) | Soundness of the parser of inline `assembly` statements |
| [`Basics`](../../Solcore/Syntax/Parser/Internal/Basics.lean) | Basic proofs about parser primitives, names, literals and delimited lists |
| [`BlockSoundness`](../../Solcore/Syntax/Parser/Internal/BlockSoundness.lean) | Soundness of the parsers of blocks and block capture |
| [`BlockTrace`](../../Solcore/Syntax/Parser/Internal/BlockTrace.lean) | Parser side of the traces of blocks, return statements and terminated control |
| [`CollectionSoundness`](../../Solcore/Syntax/Parser/Internal/CollectionSoundness.lean) | Soundness of the parsers of parenthesized forms, array literals and postfix tails |
| [`Completeness`](../../Solcore/Syntax/Parser/Internal/Completeness.lean) | Completeness of the parsers of declarations |
| [`ContractBodySoundness`](../../Solcore/Syntax/Parser/Internal/ContractBodySoundness.lean) | Soundness of the parsers of contract bodies |
| [`ContractEntryProofs`](../../Solcore/Syntax/Parser/Internal/ContractEntryProofs.lean) | Proofs about the parsers of constructors and fallbacks |
| [`ContractOutcomeSoundness`](../../Solcore/Syntax/Parser/Internal/ContractOutcomeSoundness.lean) | Soundness of the parsers of whole contract declarations |
| [`ContractProofs`](../../Solcore/Syntax/Parser/Internal/ContractProofs.lean) | Proofs about the parsers of contracts |
| [`ControlSoundness`](../../Solcore/Syntax/Parser/Internal/ControlSoundness.lean) | Soundness of the parsers of control statements |
| [`DeclarationTotality`](../../Solcore/Syntax/Parser/Internal/DeclarationTotality.lean) | Totality of the parsers of contracts and derive attributes |
| [`DelimitedSoundness`](../../Solcore/Syntax/Parser/Internal/DelimitedSoundness.lean) | Soundness of the parsers of delimited lists and identifiers |
| [`DelimitedTotality`](../../Solcore/Syntax/Parser/Internal/DelimitedTotality.lean) | Totality of the parsers of delimited lists and primitives |
| [`DelimitedTrace`](../../Solcore/Syntax/Parser/Internal/DelimitedTrace.lean) | Parser side of the delimited-list traces |
| [`DeriveSoundness`](../../Solcore/Syntax/Parser/Internal/DeriveSoundness.lean) | Soundness of the parsers of derive attributes |
| [`DiagnosticTrace`](../../Solcore/Syntax/Parser/Internal/DiagnosticTrace.lean) | Foundations of the parser's trace proofs |
| [`EnumProofs`](../../Solcore/Syntax/Parser/Internal/EnumProofs.lean) | Proofs about the parsers of enums |
| [`ExportProofs`](../../Solcore/Syntax/Parser/Internal/ExportProofs.lean) | Proofs about the parsers of exports, module paths and pragmas |
| [`ExportSoundness`](../../Solcore/Syntax/Parser/Internal/ExportSoundness.lean) | Soundness of the parsers of export declarations and pragmas |
| [`ExpressionAtomProofs`](../../Solcore/Syntax/Parser/Internal/ExpressionAtomProofs.lean) | Proofs about the parsers of expression atoms |
| [`ExpressionAtomSoundness`](../../Solcore/Syntax/Parser/Internal/ExpressionAtomSoundness.lean) | Soundness of the parsers of expression atoms and lambda expressions |
| [`ExpressionAtomTrace`](../../Solcore/Syntax/Parser/Internal/ExpressionAtomTrace.lean) | Parser side of the traces of expression atoms and names |
| [`ExpressionProofs`](../../Solcore/Syntax/Parser/Internal/ExpressionProofs.lean) | Proofs about the parsers of whole expressions, names and leading-dot constructors |
| [`ExpressionTotality`](../../Solcore/Syntax/Parser/Internal/ExpressionTotality.lean) | Totality of the parsers of expressions |
| [`FileProofs`](../../Solcore/Syntax/Parser/Internal/FileProofs.lean) | Proofs about the parsers of top items and file items |
| [`FileTotality`](../../Solcore/Syntax/Parser/Internal/FileTotality.lean) | Totality of the parsers of file items |
| [`ForStatementSoundness`](../../Solcore/Syntax/Parser/Internal/ForStatementSoundness.lean) | Soundness of the parsers of `for` statements and the statement layer |
| [`ImplProofs`](../../Solcore/Syntax/Parser/Internal/ImplProofs.lean) | Proofs about the parsers of implementations and function declarations |
| [`ImportProofs`](../../Solcore/Syntax/Parser/Internal/ImportProofs.lean) | Proofs about the parsers of imports |
| [`ImportSoundness`](../../Solcore/Syntax/Parser/Internal/ImportSoundness.lean) | Soundness of the parsers of import declarations |
| [`LambdaParameterRecovery`](../../Solcore/Syntax/Parser/Internal/LambdaParameterRecovery.lean) | Two totality facts about `recoverLambdaParameter` |
| [`LambdaParameterSoundness`](../../Solcore/Syntax/Parser/Internal/LambdaParameterSoundness.lean) | Soundness of the parsers of lambda parameters |
| [`LambdaTrace`](../../Solcore/Syntax/Parser/Internal/LambdaTrace.lean) | Parser side of the traces of lambda expressions and proxy expressions |
| [`MatchSoundness`](../../Solcore/Syntax/Parser/Internal/MatchSoundness.lean) | Soundness of the parsers of `match` statements |
| [`ModuleTotality`](../../Solcore/Syntax/Parser/Internal/ModuleTotality.lean) | Totality of the parsers of imports, exports and pragmas |
| [`OperatorSoundness`](../../Solcore/Syntax/Parser/Internal/OperatorSoundness.lean) | Soundness of the parsers of binary, unary and conditional operators |
| [`OutcomeCompleteness`](../../Solcore/Syntax/Parser/Internal/OutcomeCompleteness.lean) | Completeness of the parsers of ordinary outcomes in general |
| [`ParameterBasics`](../../Solcore/Syntax/Parser/Internal/ParameterBasics.lean) | Basic proofs about the parameter and predicate parsers |
| [`ParameterListTrace`](../../Solcore/Syntax/Parser/Internal/ParameterListTrace.lean) | Parser side of the parameter-list traces |
| [`ParameterRecoveryTotality`](../../Solcore/Syntax/Parser/Internal/ParameterRecoveryTotality.lean) | Totality of the parsers of parameter recovery |
| [`ParameterSoundness`](../../Solcore/Syntax/Parser/Internal/ParameterSoundness.lean) | Soundness of the parsers of parameters and predicates |
| [`ParameterTotality`](../../Solcore/Syntax/Parser/Internal/ParameterTotality.lean) | Totality of the parsers of parameters and predicates |
| [`ParameterTrace`](../../Solcore/Syntax/Parser/Internal/ParameterTrace.lean) | Parser side of the parameter traces |
| [`ParenthesizedTrace`](../../Solcore/Syntax/Parser/Internal/ParenthesizedTrace.lean) | Parser side of the traces of parenthesized forms, array literals and atom recovery |
| [`ParseProperties`](../../Solcore/Syntax/Parser/Internal/ParseProperties.lean) | Proofs about the parsers of the public entry points |
| [`PatternCoreSoundness`](../../Solcore/Syntax/Parser/Internal/PatternCoreSoundness.lean) | Soundness of the parsers of core patterns |
| [`PatternProofs`](../../Solcore/Syntax/Parser/Internal/PatternProofs.lean) | Proofs about the parsers of patterns |
| [`PatternSoundness`](../../Solcore/Syntax/Parser/Internal/PatternSoundness.lean) | Soundness of the parsers of basic and constructor patterns |
| [`PatternStepSoundness`](../../Solcore/Syntax/Parser/Internal/PatternStepSoundness.lean) | Soundness of the parsers of one pattern step |
| [`PostfixTrace`](../../Solcore/Syntax/Parser/Internal/PostfixTrace.lean) | Parser side of the traces of postfix tails and operators |
| [`PragmaTrace`](../../Solcore/Syntax/Parser/Internal/PragmaTrace.lean) | Parser side of the traces of pragmas |
| [`PublicTermTotality`](../../Solcore/Syntax/Parser/Internal/PublicTermTotality.lean) | Totality of the parsers of public terms |
| [`SignatureSoundness`](../../Solcore/Syntax/Parser/Internal/SignatureSoundness.lean) | Soundness of the parsers of function signatures and predicates |
| [`SimpleStatementSoundness`](../../Solcore/Syntax/Parser/Internal/SimpleStatementSoundness.lean) | Soundness of the parsers of simple statements |
| [`SourceFileSoundness`](../../Solcore/Syntax/Parser/Internal/SourceFileSoundness.lean) | Soundness of the parsers of source files |
| [`SourceFileTrace`](../../Solcore/Syntax/Parser/Internal/SourceFileTrace.lean) | Parser side of the traces of top items and source files |
| [`StatementTotality`](../../Solcore/Syntax/Parser/Internal/StatementTotality.lean) | Totality of the parsers of statements and blocks |
| [`TermBasics`](../../Solcore/Syntax/Parser/Internal/TermBasics.lean) | Proofs about the parsers of the fuel-indexed term parsers |
| [`TermSoundness`](../../Solcore/Syntax/Parser/Internal/TermSoundness.lean) | Soundness of the parsers of terms at fuel and public blocks |
| [`TermTotality`](../../Solcore/Syntax/Parser/Internal/TermTotality.lean) | Totality of the parsers of patterns and statements through the term recursion |
| [`TraceSummary`](../../Solcore/Syntax/Parser/Internal/TraceSummary.lean) | A summary of the diagnostic-trace results, and the import that gathers them |
| [`TraitProofs`](../../Solcore/Syntax/Parser/Internal/TraitProofs.lean) | Proofs about the parsers of traits |
| [`TriviaProofs`](../../Solcore/Syntax/Parser/Internal/TriviaProofs.lean) | Proofs about the parsers of comment attachment and diagnostic filtering |
| [`TypeAliasProofs`](../../Solcore/Syntax/Parser/Internal/TypeAliasProofs.lean) | Proofs about the parsers of type aliases |
| [`TypeBasics`](../../Solcore/Syntax/Parser/Internal/TypeBasics.lean) | Basic proofs about the type parsers |
| [`TypeFormTotality`](../../Solcore/Syntax/Parser/Internal/TypeFormTotality.lean) | Totality of the parsers of named, simple and function types |
| [`TypeSoundness`](../../Solcore/Syntax/Parser/Internal/TypeSoundness.lean) | Soundness of the parsers of types and qualified names |
| [`TypeTotality`](../../Solcore/Syntax/Parser/Internal/TypeTotality.lean) | Totality of the parsers of recursive type expressions at fuel |
| [`TypeTrace`](../../Solcore/Syntax/Parser/Internal/TypeTrace.lean) | Parser side of the identifier, `returns` clause and type traces |
| [`YulAssignmentSoundness`](../../Solcore/Syntax/Parser/Internal/YulAssignmentSoundness.lean) | Soundness of the parsers of Yul assignments and expressions at fuel |
| [`YulBlockSoundness`](../../Solcore/Syntax/Parser/Internal/YulBlockSoundness.lean) | Soundness of the parsers of Yul blocks, functions and names |
| [`YulExpressionSoundness`](../../Solcore/Syntax/Parser/Internal/YulExpressionSoundness.lean) | Soundness of the parsers of Yul expressions |
| [`YulPublicSoundness`](../../Solcore/Syntax/Parser/Internal/YulPublicSoundness.lean) | Soundness of the parsers of Yul statements at the public boundary |
| [`YulStatementSoundness`](../../Solcore/Syntax/Parser/Internal/YulStatementSoundness.lean) | Soundness of the parsers of Yul statements |
| [`YulSwitchSoundness`](../../Solcore/Syntax/Parser/Internal/YulSwitchSoundness.lean) | Soundness of the parsers of Yul `switch` cases |
| [`YulTotality`](../../Solcore/Syntax/Parser/Internal/YulTotality.lean) | Totality of the parsers of Yul expressions and statements |

## What a reviewer should know

- **Production does not import the proofs.** `Unchecked` imports `Parser`, and `Parser` imports
  the front. That closure is 48 modules. Production code references no parser theorem.
- **Two parser files hold proofs.** `Parser/Signatures` and `Parser/Blocks` keep the theorems
  that name a private helper, and everything those theorems need from that file. `private` is
  per file, and the refactor keeps it. `Parser/Internal/Basics`, `TypeBasics` and
  `ParameterBasics` support them, and they are in production's closure, so keep them small.
- **Some grammar files hold lemmas.** `Grammar/YulOrdinary`, `Grammar/YulFuel`,
  `Grammar/StatementLayer` and `Grammar/TermLevels` hold outcome lemmas, because the fuel levels
  carry their determinism proofs.
- **Three separations are deliberate.**
  - `Parser/Internal/LambdaParameterRecovery` and `Parser/LambdaParameterTotalityProperties`
    declare the same two public theorems. Lean accepts that across imports, but not in a file
    that imports the other copy.
  - `Parser/Internal/AssemblySoundness` stays apart from `ControlSoundness`. It needs the public
    Yul results, whose `@[simp]` lemma `yulStatement_executableFuel_eq_publicFuel` would change
    a `simp` in the statement totality proofs.
  - `Internal/ContractMemberOutcomes` and `Internal/ContractBodyOutcomes` are two files because
    the merged file would hold three variants of a private helper, and the snapshot tool maps one
    old name to one new name.
- **Renames.** `.refactor/renames-r3-syntax.tsv` lists the private helpers renamed to resolve a
  clash. Most are named `<old>_variant`.
