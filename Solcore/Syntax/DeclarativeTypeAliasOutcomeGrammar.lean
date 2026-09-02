import Solcore.Syntax.DeclarativeCoreTypeOutcomeGrammar

/-!
Parser-independent ordinary success and exact sequential rejection for type
alias parameters, recovery-aware alias values, and complete declarations.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-! Optional parenthesized alias parameters. -/

/-- Exact allow-empty, allow-trailing type-alias parameter list. -/
abbrev TypeAliasParametersOrdinaryParses :=
  TrailingDelimitedListParses .leftParen .rightParen IdentifierParses

/-- Exact rejection of an allow-empty, allow-trailing alias parameter list. -/
abbrev TypeAliasParametersRejects :=
  DelimitedListRejects .leftParen .rightParen true true IdentifierParses
    IdentifierRejects

/-- Ordinary optional alias-parameter success is the existing exact grammar. -/
abbrev OptionalTypeAliasParametersOrdinaryParses :=
  OptionalTypeAliasParametersParses

/-- A positive `(` lookahead commits optional alias parameters to the complete
delimited-list attempt from the original remainder. -/
inductive OptionalTypeAliasParametersRejects : Remainder → Remainder → Prop where
  | present {input rejected : Remainder}
      (openingPresent : ∃ span,
        TokenAt input.tokens input.endIndex input.cursor {
          span, value := .symbol .leftParen })
      (parametersRejected : TypeAliasParametersRejects input rejected) :
      OptionalTypeAliasParametersRejects input rejected

/-! Recovery-aware type-alias values. -/

/-- Exact non-consuming boundaries checked before alias-value recovery. -/
inductive TypeAliasValueBoundaryStops : Remainder → Prop where
  | windowEnd {input : Remainder}
      (atEnd : input.endIndex ≤ input.cursor) :
      TypeAliasValueBoundaryStops input
  | semicolon {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .semicolon }) :
      TypeAliasValueBoundaryStops input

/-- Exact stops of the scan after recovery consumed its mandatory first token.
A missing carrier slot here finishes recovery rather than rejecting it. -/
inductive TypeAliasValueRecoveryStops : Remainder → Prop where
  | windowEnd {input : Remainder}
      (atEnd : input.endIndex ≤ input.cursor) :
      TypeAliasValueRecoveryStops input
  | semicolon {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .semicolon }) :
      TypeAliasValueRecoveryStops input
  | missingToken {input : Remainder}
      (inside : input.cursor < input.endIndex)
      (missing : input.tokens[input.cursor]? = none) :
      TypeAliasValueRecoveryStops input

/-- Exact scan after alias-value recovery consumed its mandatory first token. -/
inductive TypeAliasValueRecoveryScanParses (first : SourceSpan) :
    SourceSpan → Remainder → Syntax.TypeExpr → Remainder → Prop where
  | stop {last : SourceSpan} {input : Remainder}
      (stops : TypeAliasValueRecoveryStops input) :
      TypeAliasValueRecoveryScanParses first last input {
        span := SourceSpan.cover first last
        value := .error
      } input
  | next {last : SourceSpan} {input output : Remainder} {token : Token}
      {value : Syntax.TypeExpr}
      (continues : ¬ TypeAliasValueRecoveryStops input)
      (current : TokenAt input.tokens input.endIndex input.cursor token)
      (tail : TypeAliasValueRecoveryScanParses first token.span
        { input with cursor := input.cursor + 1 } value output) :
      TypeAliasValueRecoveryScanParses first last input value output

/-- Successful alias-value recovery, including its mandatory first token. -/
inductive TypeAliasValueRecoveryParses :
    Remainder → Syntax.TypeExpr → Remainder → Prop where
  | recovered {input output : Remainder} {token : Token}
      {value : Syntax.TypeExpr}
      (continues : ¬ TypeAliasValueBoundaryStops input)
      (current : TokenAt input.tokens input.endIndex input.cursor token)
      (scan : TypeAliasValueRecoveryScanParses token.span token.span
        { input with cursor := input.cursor + 1 } value output) :
      TypeAliasValueRecoveryParses input value output

/-- Exact non-consuming rejection when recovery cannot consume its first token. -/
inductive TypeAliasValueRecoveryRejects : Remainder → Remainder → Prop where
  | boundary {input : Remainder}
      (stops : TypeAliasValueBoundaryStops input) :
      TypeAliasValueRecoveryRejects input input
  | missingToken {input : Remainder}
      (inside : input.cursor < input.endIndex)
      (missing : input.tokens[input.cursor]? = none) :
      TypeAliasValueRecoveryRejects input input

/-- A rejected Core type retains its failed cursor while preserving the token
carrier and active window needed for the alias-value rewind. -/
def TypeAliasValueCoreRejectsWithPreservedWindow (input : Remainder) : Prop :=
  ∃ failed, TypeExprRejects input failed ∧
    failed.tokens = input.tokens ∧ failed.endIndex = input.endIndex

/-- Direct Core type success or exact recovery from the original cursor. -/
inductive TypeAliasValueOrdinaryParses :
    Remainder → Syntax.TypeExpr → Remainder → Prop where
  | core {input output : Remainder} {value : Syntax.TypeExpr}
      (parsed : TypeExprOrdinaryParses input value output) :
      TypeAliasValueOrdinaryParses input value output
  | recovered {input output : Remainder} {value : Syntax.TypeExpr}
      (coreRejected : TypeAliasValueCoreRejectsWithPreservedWindow input)
      (recovered : TypeAliasValueRecoveryParses input value output) :
      TypeAliasValueOrdinaryParses input value output

/-- Exact public alias-value rejection at the rewound boundary or in recovery. -/
inductive TypeAliasValueRejects : Remainder → Remainder → Prop where
  | boundary {input : Remainder}
      (coreRejected : TypeAliasValueCoreRejectsWithPreservedWindow input)
      (stops : TypeAliasValueBoundaryStops input) :
      TypeAliasValueRejects input input
  | recovery {input rejected : Remainder}
      (coreRejected : TypeAliasValueCoreRejectsWithPreservedWindow input)
      (continues : ¬ TypeAliasValueBoundaryStops input)
      (recoveryRejected : TypeAliasValueRecoveryRejects input rejected) :
      TypeAliasValueRejects input rejected

/-! Complete broad type-alias outcomes. -/

/-- Exact broad type-alias success in executable stage order. -/
inductive TypeAliasDeclOrdinaryParses :
    Remainder → Syntax.TypeAliasDecl → Remainder → Prop where
  | parsed
      {input afterKeyword afterName afterParameters afterEqual afterValue
        output : Remainder}
      {name : Syntax.Identifier}
      {parameters : Option (DelimitedList Syntax.Identifier)}
      {value : Syntax.TypeExpr}
      (keywordSpan equalSpan semicolonSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .typeKw)
        input keywordSpan afterKeyword)
      (nameParsed : IdentifierParses afterKeyword name afterName)
      (parametersParsed : OptionalTypeAliasParametersOrdinaryParses
        afterName parameters afterParameters)
      (equalParsed : ExactTokenParses (.symbol .equal)
        afterParameters equalSpan afterEqual)
      (valueParsed : TypeAliasValueOrdinaryParses afterEqual value afterValue)
      (semicolonParsed : ExactTokenParses (.symbol .semicolon)
        afterValue semicolonSpan output) :
      TypeAliasDeclOrdinaryParses input {
        span := SourceSpan.cover keywordSpan semicolonSpan
        value := { name, parameters, value }
      } output

/-- Exact first rejecting stage of one broad type-alias attempt. -/
inductive TypeAliasDeclRejects : Remainder → Remainder → Prop where
  | keywordMissing {input : Remainder}
      (keywordAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .typeKw)) :
      TypeAliasDeclRejects input input
  | nameRejected {input afterKeyword rejected : Remainder}
      (keywordSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .typeKw)
        input keywordSpan afterKeyword)
      (nameRejected : IdentifierRejects afterKeyword rejected) :
      TypeAliasDeclRejects input rejected
  | parametersRejected
      {input afterKeyword afterName rejected : Remainder}
      {name : Syntax.Identifier} (keywordSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .typeKw)
        input keywordSpan afterKeyword)
      (nameParsed : IdentifierParses afterKeyword name afterName)
      (parametersRejected : OptionalTypeAliasParametersRejects afterName
        rejected) :
      TypeAliasDeclRejects input rejected
  | equalMissing
      {input afterKeyword afterName afterParameters : Remainder}
      {name : Syntax.Identifier}
      {parameters : Option (DelimitedList Syntax.Identifier)}
      (keywordSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .typeKw)
        input keywordSpan afterKeyword)
      (nameParsed : IdentifierParses afterKeyword name afterName)
      (parametersParsed : OptionalTypeAliasParametersOrdinaryParses
        afterName parameters afterParameters)
      (equalAbsent : TokenKindAbsentAt afterParameters.tokens
        afterParameters.endIndex afterParameters.cursor (.symbol .equal)) :
      TypeAliasDeclRejects input afterParameters
  | valueRejected
      {input afterKeyword afterName afterParameters afterEqual rejected : Remainder}
      {name : Syntax.Identifier}
      {parameters : Option (DelimitedList Syntax.Identifier)}
      (keywordSpan equalSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .typeKw)
        input keywordSpan afterKeyword)
      (nameParsed : IdentifierParses afterKeyword name afterName)
      (parametersParsed : OptionalTypeAliasParametersOrdinaryParses
        afterName parameters afterParameters)
      (equalParsed : ExactTokenParses (.symbol .equal)
        afterParameters equalSpan afterEqual)
      (valueRejected : TypeAliasValueRejects afterEqual rejected) :
      TypeAliasDeclRejects input rejected
  | semicolonMissing
      {input afterKeyword afterName afterParameters afterEqual afterValue : Remainder}
      {name : Syntax.Identifier}
      {parameters : Option (DelimitedList Syntax.Identifier)}
      {value : Syntax.TypeExpr} (keywordSpan equalSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .typeKw)
        input keywordSpan afterKeyword)
      (nameParsed : IdentifierParses afterKeyword name afterName)
      (parametersParsed : OptionalTypeAliasParametersOrdinaryParses
        afterName parameters afterParameters)
      (equalParsed : ExactTokenParses (.symbol .equal)
        afterParameters equalSpan afterEqual)
      (valueParsed : TypeAliasValueOrdinaryParses afterEqual value afterValue)
      (semicolonAbsent : TokenKindAbsentAt afterValue.tokens afterValue.endIndex
        afterValue.cursor (.symbol .semicolon)) :
      TypeAliasDeclRejects input afterValue

end Solcore.Syntax.DeclarativeGrammar
