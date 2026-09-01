import Solcore.Syntax.DeclarativeCoreIdentifierOutcomeGrammar
import Solcore.Syntax.DeclarativeCoreLambdaGrammar
import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar

/-!
Parser-independent ordinary outcomes of the non-recovering lambda-parameter
core.  Unlike the older clean grammar, these relations retain successful
constraint diagnostics in the ordinary outcome.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Inferred or typed ordinary suffix, including a diagnosed comptime type. -/
inductive OrdinaryLambdaParameterTailOrdinaryParses
    (typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop)
    (name : Syntax.Identifier) :
    Remainder → Syntax.LambdaParameter → Remainder → Prop where
  | inferred {input : Remainder}
      (colonAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .colon)) :
      OrdinaryLambdaParameterTailOrdinaryParses typeOrdinary name input {
        span := name.span
        value := .inferred name
      } input
  | typed {input afterColon output : Remainder} {type : Syntax.TypeExpr}
      (colonSpan : SourceSpan)
      (colonParsed : ExactTokenParses (.symbol .colon) input colonSpan
        afterColon)
      (typeParsed : typeOrdinary afterColon type output) :
      OrdinaryLambdaParameterTailOrdinaryParses typeOrdinary name input {
        span := SourceSpan.cover name.span type.span
        value := .typed none name type
      } output

/-- Ordinary-name branch, including the diagnosed spelling `comptime`. -/
inductive OrdinaryLambdaParameterOrdinaryParses
    (typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop) :
    Remainder → Syntax.LambdaParameter → Remainder → Prop where
  | parsed {input afterName output : Remainder}
      {name : Syntax.Identifier} {parameter : Syntax.LambdaParameter}
      (nameParsed : IdentifierParses input name afterName)
      (tail : OrdinaryLambdaParameterTailOrdinaryParses typeOrdinary name
        afterName parameter output) :
      OrdinaryLambdaParameterOrdinaryParses typeOrdinary input parameter output

/-- Contextual-comptime branch, including its diagnosed successful forms. -/
inductive ComptimeLambdaParameterOrdinaryParses
    (typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop) :
    Remainder → Syntax.LambdaParameter → Remainder → Prop where
  | typed {input afterMarker afterName afterColon output : Remainder}
      {name : Syntax.Identifier} {type : Syntax.TypeExpr}
      (markerSpan colonSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.comptime.spelling) input markerSpan
          afterMarker)
      (nameParsed : IdentifierParses afterMarker name afterName)
      (colonParsed : ExactTokenParses (.symbol .colon) afterName colonSpan
        afterColon)
      (typeParsed : typeOrdinary afterColon type output) :
      ComptimeLambdaParameterOrdinaryParses typeOrdinary input {
        span := SourceSpan.cover markerSpan type.span
        value := .typed (some markerSpan) name type
      } output
  | typeMissing {input afterMarker afterName : Remainder}
      {name : Syntax.Identifier} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.comptime.spelling) input markerSpan
          afterMarker)
      (nameParsed : IdentifierParses afterMarker name afterName)
      (colonAbsent : TokenKindAbsentAt afterName.tokens afterName.endIndex
        afterName.cursor (.symbol .colon)) :
      ComptimeLambdaParameterOrdinaryParses typeOrdinary input {
        span := SourceSpan.cover markerSpan name.span
        value := .error
      } afterName

/-- Exact ordered ordinary success of `lambdaParameterCore`. -/
inductive LambdaParameterCoreOrdinaryParses
    (typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop) :
    Remainder → Syntax.LambdaParameter → Remainder → Prop where
  | comptime {input output : Remainder}
      {parameter : Syntax.LambdaParameter}
      (parsed : ComptimeLambdaParameterOrdinaryParses typeOrdinary input
        parameter output) :
      LambdaParameterCoreOrdinaryParses typeOrdinary input parameter output
  | ordinary {input output : Remainder}
      {parameter : Syntax.LambdaParameter}
      (comptimeAbsent : ¬ ComptimeLambdaParameterStartsAt input)
      (parsed : OrdinaryLambdaParameterOrdinaryParses typeOrdinary input
        parameter output) :
      LambdaParameterCoreOrdinaryParses typeOrdinary input parameter output

/-- Exact ordered ordinary rejection of `lambdaParameterCore`. -/
inductive LambdaParameterCoreRejects
    (typeRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | comptimeType {input afterMarker afterName afterColon rejected : Remainder}
      {name : Syntax.Identifier} (markerSpan colonSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.comptime.spelling) input markerSpan
          afterMarker)
      (nameParsed : IdentifierParses afterMarker name afterName)
      (colonParsed : ExactTokenParses (.symbol .colon) afterName colonSpan
        afterColon)
      (typeRejected : typeRejects afterColon rejected) :
      LambdaParameterCoreRejects typeRejects input rejected
  | ordinaryName {input rejected : Remainder}
      (comptimeAbsent : ¬ ComptimeLambdaParameterStartsAt input)
      (nameRejected : IdentifierRejects input rejected) :
      LambdaParameterCoreRejects typeRejects input rejected
  | ordinaryType {input afterName afterColon rejected : Remainder}
      {name : Syntax.Identifier} (colonSpan : SourceSpan)
      (comptimeAbsent : ¬ ComptimeLambdaParameterStartsAt input)
      (nameParsed : IdentifierParses input name afterName)
      (colonParsed : ExactTokenParses (.symbol .colon) afterName colonSpan
        afterColon)
      (typeRejected : typeRejects afterColon rejected) :
      LambdaParameterCoreRejects typeRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
