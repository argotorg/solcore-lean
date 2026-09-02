import Solcore.Syntax.DeclarativeFunctionParametersOutcomeGrammar
import Solcore.Syntax.DeclarativeGenericParametersOutcomeGrammar
import Solcore.Syntax.DeclarativeReturnClauseOutcomeGrammar
import Solcore.Syntax.DeclarativeWhereClauseOutcomeGrammar

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
