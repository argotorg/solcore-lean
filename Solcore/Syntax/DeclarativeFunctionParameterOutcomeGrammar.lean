import Solcore.Syntax.DeclarativeCoreLambdaParameterRecoveryOutcomeGrammar
import Solcore.Syntax.DeclarativeCoreTypeOutcomeGrammar

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
