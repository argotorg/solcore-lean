import Solcore.Syntax.DeclarativeCoreLambdaParameterOutcomeGrammar
import Solcore.Syntax.DeclarativeCoreLambdaParameterRecoveryOutcomeGrammar

/-!
Parser-independent ordinary outcomes at the public lambda-parameter rewind,
boundary, diagnostic-emission, and recovery layer.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact non-consuming boundaries checked before parameter recovery. -/
inductive LambdaParameterBoundaryStops : Remainder → Prop where
  | windowEnd {input : Remainder}
      (atEnd : input.endIndex ≤ input.cursor) :
      LambdaParameterBoundaryStops input
  | comma {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .comma }) :
      LambdaParameterBoundaryStops input
  | rightParen {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .rightParen }) :
      LambdaParameterBoundaryStops input

/-- A Core rejection preserves the immutable token carrier and active window. -/
def LambdaParameterCoreRejectsWithPreservedWindow
    (typeRejects : Remainder → Remainder → Prop)
    (input : Remainder) : Prop :=
  ∃ failed, LambdaParameterCoreRejects typeRejects input failed ∧
    failed.tokens = input.tokens ∧ failed.endIndex = input.endIndex

/-- Direct Core success or exact post-rewind recovery success. -/
inductive LambdaParameterOrdinaryParses
    (typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop)
    (typeRejects : Remainder → Remainder → Prop) :
    Remainder → Syntax.LambdaParameter → Remainder → Prop where
  | core {input output : Remainder} {parameter : Syntax.LambdaParameter}
      (parsed : LambdaParameterCoreOrdinaryParses typeOrdinary input parameter
        output) :
      LambdaParameterOrdinaryParses typeOrdinary typeRejects input parameter
        output
  | recovered {input output : Remainder} {parameter : Syntax.LambdaParameter}
      (coreRejected : LambdaParameterCoreRejectsWithPreservedWindow
        typeRejects input)
      (continues : ¬ LambdaParameterBoundaryStops input)
      (recovered : LambdaParameterRecoveryParses input parameter output) :
      LambdaParameterOrdinaryParses typeOrdinary typeRejects input parameter
        output

/-- Exact public rejection at the rewound boundary or in recovery itself. -/
inductive LambdaParameterRejects
    (typeRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | boundary {input : Remainder}
      (coreRejected : LambdaParameterCoreRejectsWithPreservedWindow
        typeRejects input)
      (stops : LambdaParameterBoundaryStops input) :
      LambdaParameterRejects typeRejects input input
  | recovery {input rejected : Remainder}
      (coreRejected : LambdaParameterCoreRejectsWithPreservedWindow
        typeRejects input)
      (continues : ¬ LambdaParameterBoundaryStops input)
      (recoveryRejected : LambdaParameterRecoveryRejects input rejected) :
      LambdaParameterRejects typeRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
