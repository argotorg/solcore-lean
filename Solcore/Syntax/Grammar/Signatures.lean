import Solcore.Syntax.Grammar.Types
import Solcore.Syntax.Grammar.Basics

/-!
Declarative grammar of predicates, parameters and signature clauses.

Main declarations: `FunctionParameterCoreOrdinaryParses`,
`FunctionParameterRecoveryParses`,
`LambdaParameterRecoveryParses`, `PredicateRejects`, `OptionalWhereClauseRejects`,
`GenericParametersRejects`.
-/

section
-- leanmerge: from Solcore.Syntax.DeclarativeReturnClauseOutcomeGrammar
/-! Parser-independent exact rejection for optional canonical `returns`. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact optional-`returns` rejection after its positively guarded marker.

The absent-marker branch is always a nonconsuming success, while a present
marker commits to the allow-empty, allow-trailing return-type list. -/
inductive OptionalReturnClauseRejects : Remainder → Remainder → Prop where
  | typesRejected
      {input afterMarker rejected : Remainder} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.returns.spelling)
        input markerSpan afterMarker)
      (typesRejected : DelimitedListRejects .leftParen .rightParen true true
        TypeExprOrdinaryParses TypeExprRejects afterMarker rejected) :
      OptionalReturnClauseRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativePredicateOutcomeGrammar
/-!
Parser-independent exact rejection traces for predicates and grouped predicate
sequences.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact first rejected stage of one trait-predicate attempt. -/
inductive PredicateRejects : Remainder → Remainder → Prop where
  | subjectRejected {input rejected : Remainder}
      (subjectRejected : TypeExprRejects input rejected) :
      PredicateRejects input rejected
  | colonMissing {input afterSubject : Remainder}
      {subject : Syntax.TypeExpr}
      (subjectParsed : TypeExprParses input subject afterSubject)
      (colonAbsent : TokenKindAbsentAt afterSubject.tokens
        afterSubject.endIndex afterSubject.cursor (.symbol .colon)) :
      PredicateRejects input afterSubject
  | nameRejected {input afterSubject afterColon rejected : Remainder}
      {subject : Syntax.TypeExpr} (colonSpan : SourceSpan)
      (subjectParsed : TypeExprParses input subject afterSubject)
      (colonParsed : ExactTokenParses (.symbol .colon) afterSubject colonSpan
        afterColon)
      (nameRejected : IdentifierRejects afterColon rejected) :
      PredicateRejects input rejected
  | argumentsRejected
      {input afterSubject afterColon afterName rejected : Remainder}
      {subject : Syntax.TypeExpr} {traitName : Syntax.Identifier}
      (colonSpan : SourceSpan)
      (subjectParsed : TypeExprParses input subject afterSubject)
      (colonParsed : ExactTokenParses (.symbol .colon) afterSubject colonSpan
        afterColon)
      (nameParsed : IdentifierParses afterColon traitName afterName)
      (argumentsRejected : NamedTypeArgumentsRejects TypeExprRejects afterName
        rejected) :
      PredicateRejects input rejected

/-- Exact ordinary rejection of the required nonempty grouped predicate list. -/
abbrev GroupedPredicateSequenceRejects :=
  DelimitedListRejects .leftParen .rightParen false true PredicateParses
    PredicateRejects

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativePredicateSequenceOutcomeGrammar
/-!
Parser-independent exact rejection traces for bare and prioritized predicate
sequences.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact rejection after at least one predicate in a bare sequence has
succeeded. Every recursive step retains its comma, positive type-start
lookahead, and successful predicate prefix. -/
inductive BarePredicateTailRejects : Remainder → Remainder → Prop where
  | predicateRejected
      {input afterComma rejected : Remainder} (commaSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan
        afterComma)
      (nextStarts : TypeExprStartsAt afterComma)
      (predicateRejected : PredicateRejects afterComma rejected) :
      BarePredicateTailRejects input rejected
  | next
      {input afterComma afterPredicate rejected : Remainder}
      {predicate : Syntax.Predicate} (commaSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan
        afterComma)
      (nextStarts : TypeExprStartsAt afterComma)
      (predicateParsed : PredicateParses afterComma predicate afterPredicate)
      (tailRejected : BarePredicateTailRejects afterPredicate rejected) :
      BarePredicateTailRejects input rejected

/-- Exact first rejection of one nonempty unparenthesized predicate sequence. -/
inductive BarePredicateSequenceRejects : Remainder → Remainder → Prop where
  | firstRejected {input rejected : Remainder}
      (firstRejected : PredicateRejects input rejected) :
      BarePredicateSequenceRejects input rejected
  | tailRejected {input afterFirst rejected : Remainder}
      {first : Syntax.Predicate}
      (firstParsed : PredicateParses input first afterFirst)
      (tailRejected : BarePredicateTailRejects afterFirst rejected) :
      BarePredicateSequenceRejects input rejected

/-- Exact rejection of grouped-first predicate dispatch.

The direct branch records that grouped parsing was not attempted. The fallback
branch separately retains the grouped attempt's intermediate rejection and the
bare attempt's final rejection from the original input. -/
inductive PredicateSequenceRejects : Remainder → Remainder → Prop where
  | direct {input rejected : Remainder}
      (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen))
      (bareRejected : BarePredicateSequenceRejects input rejected) :
      PredicateSequenceRejects input rejected
  | fallback {input groupedRejected rejected : Remainder}
      (openingPresent : ∃ span, TokenAt input.tokens input.endIndex
        input.cursor { span, value := .symbol .leftParen })
      (groupedRejection : GroupedPredicateSequenceRejects input
        groupedRejected)
      (bareRejection : BarePredicateSequenceRejects input rejected) :
      PredicateSequenceRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeWhereClauseOutcomeGrammar
/-! Parser-independent exact rejection for optional canonical `where`. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact optional-`where` rejection after its positively guarded marker.

The absent-marker branch is always a nonconsuming success, while a present
marker commits to the prioritized predicate sequence. -/
inductive OptionalWhereClauseRejects : Remainder → Remainder → Prop where
  | predicatesRejected
      {input afterMarker rejected : Remainder} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.where.spelling)
        input markerSpan afterMarker)
      (predicatesRejected : PredicateSequenceRejects afterMarker rejected) :
      OptionalWhereClauseRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeGenericParametersOutcomeGrammar
/-! Parser-independent exact rejection for canonical generic parameters. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact ordinary rejection of a required nonempty, allow-trailing generic
parameter list. -/
abbrev GenericParametersRejects :=
  DelimitedListRejects .less .greater false true IdentifierParses
    IdentifierRejects

/-- Exact rejection of optional generic parameters after their positive `<`
lookahead commits to the required generic-parameter parser.

The lookahead does not consume the opening token, so the nested rejection also
starts at the original remainder. -/
inductive OptionalGenericParametersRejects : Remainder → Remainder → Prop where
  | present {input rejected : Remainder}
      (openingPresent : ∃ span,
        TokenAt input.tokens input.endIndex input.cursor {
          span
          value := .symbol .less
        })
      (parametersRejected : GenericParametersRejects input rejected) :
      OptionalGenericParametersRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreLambdaParameterRecoveryOutcomeGrammar
/-!
Parser-independent ordinary outcomes of function-parameter recovery and the
exact lambda-parameter retagging built on top of it.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Boundary-prioritized stops of the parameter recovery scan. -/
inductive FunctionParameterRecoveryStops : Remainder → Prop where
  | windowEnd {input : Remainder}
      (atEnd : input.endIndex ≤ input.cursor) :
      FunctionParameterRecoveryStops input
  | comma {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .comma }) :
      FunctionParameterRecoveryStops input
  | rightParen {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .rightParen }) :
      FunctionParameterRecoveryStops input
  | missingToken {input : Remainder}
      (inside : input.cursor < input.endIndex)
      (missing : input.tokens[input.cursor]? = none) :
      FunctionParameterRecoveryStops input

/-- Exact scan after recovery consumed its mandatory first token. -/
inductive FunctionParameterRecoveryScanParses (first : SourceSpan) :
    SourceSpan → Remainder → Syntax.FunctionParameter → Remainder → Prop where
  | stop {last : SourceSpan} {input : Remainder}
      (stops : FunctionParameterRecoveryStops input) :
      FunctionParameterRecoveryScanParses first last input {
        span := SourceSpan.cover first last
        value := .error
      } input
  | next {last : SourceSpan} {input output : Remainder} {token : Token}
      {parameter : Syntax.FunctionParameter}
      (continues : ¬ FunctionParameterRecoveryStops input)
      (current : TokenAt input.tokens input.endIndex input.cursor token)
      (tail : FunctionParameterRecoveryScanParses first token.span
        { input with cursor := input.cursor + 1 } parameter output) :
      FunctionParameterRecoveryScanParses first last input parameter output

/-- Ordinary success of `recoverParameter`, including its mandatory token. -/
inductive FunctionParameterRecoveryParses :
    Remainder → Syntax.FunctionParameter → Remainder → Prop where
  | recovered {input output : Remainder} {token : Token}
      {parameter : Syntax.FunctionParameter}
      (current : TokenAt input.tokens input.endIndex input.cursor token)
      (scan : FunctionParameterRecoveryScanParses token.span token.span
        { input with cursor := input.cursor + 1 } parameter output) :
      FunctionParameterRecoveryParses input parameter output

/-- Exact non-consuming rejection when no mandatory first token exists. -/
inductive FunctionParameterRecoveryRejects : Remainder → Remainder → Prop where
  | windowEnd {input : Remainder}
      (atEnd : input.endIndex ≤ input.cursor) :
      FunctionParameterRecoveryRejects input input
  | missingToken {input : Remainder}
      (inside : input.cursor < input.endIndex)
      (missing : input.tokens[input.cursor]? = none) :
      FunctionParameterRecoveryRejects input input

/-- Lambda recovery is the exact span-preserving retag of function recovery. -/
inductive LambdaParameterRecoveryParses :
    Remainder → Syntax.LambdaParameter → Remainder → Prop where
  | recovered {input output : Remainder}
      {parameter : Syntax.FunctionParameter}
      (parsed : FunctionParameterRecoveryParses input parameter output) :
      LambdaParameterRecoveryParses input {
        span := parameter.span
        value := .error
      } output

/-- Lambda recovery propagates the exact function-recovery rejection. -/
abbrev LambdaParameterRecoveryRejects := FunctionParameterRecoveryRejects

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeFunctionParameterOutcomeGrammar
/-!
Parser-independent ordinary outcomes of one public named function parameter.

The Core relation retains diagnosed missing-colon successes.  The public
relation then records exact cursor rewind, boundary rejection, or the existing
function-parameter recovery scan.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Typed or diagnosed-missing-type outcome after a parsed parameter name. -/
inductive FunctionParameterTailOrdinaryParses
    (typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop)
    (start : SourceSpan) (marker : Option SourceSpan)
    (name : Syntax.Identifier) (errorSpan : SourceSpan) :
    Remainder → Syntax.FunctionParameter → Remainder → Prop where
  | typed {input afterColon output : Remainder} {type : Syntax.TypeExpr}
      (colonSpan : SourceSpan)
      (colonParsed : ExactTokenParses (.symbol .colon) input colonSpan
        afterColon)
      (typeParsed : typeOrdinary afterColon type output) :
      FunctionParameterTailOrdinaryParses typeOrdinary start marker name
        errorSpan input {
          span := SourceSpan.cover start type.span
          value := .typed marker name type
        } output
  | typeMissing {input : Remainder}
      (colonAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .colon)) :
      FunctionParameterTailOrdinaryParses typeOrdinary start marker name
        errorSpan input { span := errorSpan, value := .error } input

/-- Exact ordered ordinary success of non-recovering `namedParameterCore`. -/
inductive FunctionParameterCoreOrdinaryParses
    (typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop) :
    Remainder → Syntax.FunctionParameter → Remainder → Prop where
  | ordinary {input afterName output : Remainder}
      {name : Syntax.Identifier} {parameter : Syntax.FunctionParameter}
      (comptimePrefixAbsent : ComptimeParameterPrefixAbsentAt input)
      (nameParsed : IdentifierParses input name afterName)
      (tailParsed : FunctionParameterTailOrdinaryParses typeOrdinary
        name.span none name name.span afterName parameter output) :
      FunctionParameterCoreOrdinaryParses typeOrdinary input parameter output
  | comptime {input afterMarker afterName output : Remainder}
      {name : Syntax.Identifier} {parameter : Syntax.FunctionParameter}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.comptime.spelling)
        input markerSpan afterMarker)
      (nameParsed : IdentifierParses afterMarker name afterName)
      (tailParsed : FunctionParameterTailOrdinaryParses typeOrdinary
        markerSpan (some markerSpan) name
          (SourceSpan.cover markerSpan name.span)
            afterName parameter output) :
      FunctionParameterCoreOrdinaryParses typeOrdinary input parameter output

/-- Exact ordered ordinary rejection of non-recovering `namedParameterCore`. -/
inductive FunctionParameterCoreRejects
    (typeRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | comptimeType
      {input afterMarker afterName afterColon rejected : Remainder}
      {name : Syntax.Identifier} (markerSpan colonSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.comptime.spelling)
        input markerSpan afterMarker)
      (nameParsed : IdentifierParses afterMarker name afterName)
      (colonParsed : ExactTokenParses (.symbol .colon) afterName colonSpan
        afterColon)
      (typeRejected : typeRejects afterColon rejected) :
      FunctionParameterCoreRejects typeRejects input rejected
  | ordinaryName {input rejected : Remainder}
      (comptimePrefixAbsent : ComptimeParameterPrefixAbsentAt input)
      (nameRejected : IdentifierRejects input rejected) :
      FunctionParameterCoreRejects typeRejects input rejected
  | ordinaryType {input afterName afterColon rejected : Remainder}
      {name : Syntax.Identifier} (colonSpan : SourceSpan)
      (comptimePrefixAbsent : ComptimeParameterPrefixAbsentAt input)
      (nameParsed : IdentifierParses input name afterName)
      (colonParsed : ExactTokenParses (.symbol .colon) afterName colonSpan
        afterColon)
      (typeRejected : typeRejects afterColon rejected) :
      FunctionParameterCoreRejects typeRejects input rejected

/-- Exact non-consuming boundaries checked before public recovery. -/
inductive FunctionParameterBoundaryStops : Remainder → Prop where
  | windowEnd {input : Remainder}
      (atEnd : input.endIndex ≤ input.cursor) :
      FunctionParameterBoundaryStops input
  | comma {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .comma }) :
      FunctionParameterBoundaryStops input
  | rightParen {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .rightParen }) :
      FunctionParameterBoundaryStops input

/-- A Core rejection preserves the immutable token carrier and active window. -/
def FunctionParameterCoreRejectsWithPreservedWindow
    (typeRejects : Remainder → Remainder → Prop)
    (input : Remainder) : Prop :=
  ∃ failed, FunctionParameterCoreRejects typeRejects input failed ∧
    failed.tokens = input.tokens ∧ failed.endIndex = input.endIndex

/-- Direct Core success or exact post-rewind recovery success. -/
inductive FunctionParameterOrdinaryParses
    (typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop)
    (typeRejects : Remainder → Remainder → Prop) :
    Remainder → Syntax.FunctionParameter → Remainder → Prop where
  | core {input output : Remainder} {parameter : Syntax.FunctionParameter}
      (parsed : FunctionParameterCoreOrdinaryParses typeOrdinary input
        parameter output) :
      FunctionParameterOrdinaryParses typeOrdinary typeRejects input parameter
        output
  | recovered {input output : Remainder}
      {parameter : Syntax.FunctionParameter}
      (coreRejected : FunctionParameterCoreRejectsWithPreservedWindow
        typeRejects input)
      (continues : ¬ FunctionParameterBoundaryStops input)
      (recovered : FunctionParameterRecoveryParses input parameter output) :
      FunctionParameterOrdinaryParses typeOrdinary typeRejects input parameter
        output

/-- Exact public rejection at the rewound boundary or in recovery itself. -/
inductive FunctionParameterRejects
    (typeRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | boundary {input : Remainder}
      (coreRejected : FunctionParameterCoreRejectsWithPreservedWindow
        typeRejects input)
      (stops : FunctionParameterBoundaryStops input) :
      FunctionParameterRejects typeRejects input input
  | recovery {input rejected : Remainder}
      (coreRejected : FunctionParameterCoreRejectsWithPreservedWindow
        typeRejects input)
      (continues : ¬ FunctionParameterBoundaryStops input)
      (recoveryRejected : FunctionParameterRecoveryRejects input rejected) :
      FunctionParameterRejects typeRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeFunctionParametersOutcomeGrammar
/-!
Parser-independent ordinary outcomes for recovery-aware named function
parameter lists.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Possibly empty, allow-trailing named parameters, including exact Core and
recovery outcomes under the canonical public type relations. -/
def FunctionParametersOrdinaryParses
    (input : Remainder) (parameters : DelimitedList Syntax.FunctionParameter)
    (output : Remainder) : Prop :=
  TrailingDelimitedListParses .leftParen .rightParen
    (FunctionParameterOrdinaryParses TypeExprOrdinaryParses TypeExprRejects)
      input parameters output

/-- Exact rejection of the recovery-aware named-parameter list. -/
abbrev FunctionParametersRejects :=
  DelimitedListRejects .leftParen .rightParen true true
    (FunctionParameterOrdinaryParses TypeExprOrdinaryParses TypeExprRejects)
    (FunctionParameterRejects TypeExprRejects)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeFunctionSignatureOutcomeGrammar
/-!
Parser-independent ordinary success and exact sequential rejection for complete
named-function signatures.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact ordinary function signature, including diagnosed parameter recovery
and syntactically retained modifiers without imposing a location policy. -/
inductive FunctionSignatureOrdinaryParses :
    Remainder → Syntax.FunctionSignature → Remainder → Prop where
  | parsed
      {input afterKeyword afterName afterGenerics afterParameters
        afterModifiers afterReturns output : Remainder}
      {name : Syntax.Identifier}
      {genericParameters : Option Syntax.GenericParameters}
      {parameters : DelimitedList Syntax.FunctionParameter}
      {modifiers : Syntax.FunctionModifiers}
      {returnsClause : Option Syntax.ReturnClause}
      {whereClause : Option Syntax.WhereClause}
      (keywordSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .functionKw)
        input keywordSpan afterKeyword)
      (nameParsed : IdentifierParses afterKeyword name afterName)
      (genericsParsed : OptionalGenericParametersParses afterName
        genericParameters afterGenerics)
      (parametersParsed : FunctionParametersOrdinaryParses afterGenerics
        parameters afterParameters)
      (modifiersParsed : FunctionModifiersParses afterParameters modifiers
        afterModifiers)
      (returnsParsed : OptionalReturnClauseParses afterModifiers returnsClause
        afterReturns)
      (whereParsed : OptionalWhereClauseParses afterReturns whereClause output) :
      FunctionSignatureOrdinaryParses input {
        span := SourceSpan.cover keywordSpan
          (functionSignatureEnd parameters modifiers returnsClause whereClause)
        name
        genericParameters
        parameters
        modifiers
        returnsClause
        whereClause
      } output

/-- Exact first rejecting stage of an ordinary function-signature attempt. -/
inductive FunctionSignatureRejects : Remainder → Remainder → Prop where
  | keywordMissing {input : Remainder}
      (keywordAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .functionKw)) :
      FunctionSignatureRejects input input
  | nameRejected {input afterKeyword rejected : Remainder}
      (keywordSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .functionKw)
        input keywordSpan afterKeyword)
      (nameRejected : IdentifierRejects afterKeyword rejected) :
      FunctionSignatureRejects input rejected
  | genericsRejected
      {input afterKeyword afterName rejected : Remainder}
      {name : Syntax.Identifier} (keywordSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .functionKw)
        input keywordSpan afterKeyword)
      (nameParsed : IdentifierParses afterKeyword name afterName)
      (genericsRejected : OptionalGenericParametersRejects afterName rejected) :
      FunctionSignatureRejects input rejected
  | parametersRejected
      {input afterKeyword afterName afterGenerics rejected : Remainder}
      {name : Syntax.Identifier}
      {genericParameters : Option Syntax.GenericParameters}
      (keywordSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .functionKw)
        input keywordSpan afterKeyword)
      (nameParsed : IdentifierParses afterKeyword name afterName)
      (genericsParsed : OptionalGenericParametersParses afterName
        genericParameters afterGenerics)
      (parametersRejected : FunctionParametersRejects afterGenerics rejected) :
      FunctionSignatureRejects input rejected
  | returnsRejected
      {input afterKeyword afterName afterGenerics afterParameters
        afterModifiers rejected : Remainder}
      {name : Syntax.Identifier}
      {genericParameters : Option Syntax.GenericParameters}
      {parameters : DelimitedList Syntax.FunctionParameter}
      {modifiers : Syntax.FunctionModifiers}
      (keywordSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .functionKw)
        input keywordSpan afterKeyword)
      (nameParsed : IdentifierParses afterKeyword name afterName)
      (genericsParsed : OptionalGenericParametersParses afterName
        genericParameters afterGenerics)
      (parametersParsed : FunctionParametersOrdinaryParses afterGenerics
        parameters afterParameters)
      (modifiersParsed : FunctionModifiersParses afterParameters modifiers
        afterModifiers)
      (returnsRejected : OptionalReturnClauseRejects afterModifiers rejected) :
      FunctionSignatureRejects input rejected
  | whereRejected
      {input afterKeyword afterName afterGenerics afterParameters
        afterModifiers afterReturns rejected : Remainder}
      {name : Syntax.Identifier}
      {genericParameters : Option Syntax.GenericParameters}
      {parameters : DelimitedList Syntax.FunctionParameter}
      {modifiers : Syntax.FunctionModifiers}
      {returnsClause : Option Syntax.ReturnClause}
      (keywordSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .functionKw)
        input keywordSpan afterKeyword)
      (nameParsed : IdentifierParses afterKeyword name afterName)
      (genericsParsed : OptionalGenericParametersParses afterName
        genericParameters afterGenerics)
      (parametersParsed : FunctionParametersOrdinaryParses afterGenerics
        parameters afterParameters)
      (modifiersParsed : FunctionModifiersParses afterParameters modifiers
        afterModifiers)
      (returnsParsed : OptionalReturnClauseParses afterModifiers returnsClause
        afterReturns)
      (whereRejected : OptionalWhereClauseRejects afterReturns rejected) :
      FunctionSignatureRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end
