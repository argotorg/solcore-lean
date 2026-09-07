import Solcore.Syntax.DeclarativeCoreExpressionLambdaOutcomeGrammar
import Solcore.Syntax.Parser.Diagnostic

/-! Independent exact traces for optional lambda return annotations. An absent
arrow is silent; a present arrow contributes no event before the supplied type
outcome. The final rejection report remains separate from committed events. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive OptionalLambdaReturnTypeTraceParses
    (typeTrace : SourceId → Nat → Remainder → Syntax.TypeExpr →
      Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Option Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop where
  | absent {input : Remainder}
      (arrowAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .arrow)) :
      OptionalLambdaReturnTypeTraceParses typeTrace source endByte input none input []
  | present {input afterArrow output : Remainder} {type : Syntax.TypeExpr}
      {trace : List ParseDiagnostic} (arrowSpan : SourceSpan)
      (arrowParsed : ExactTokenParses (.symbol .arrow) input arrowSpan afterArrow)
      (typeParsed : typeTrace source endByte afterArrow type output trace) :
      OptionalLambdaReturnTypeTraceParses typeTrace source endByte input (some type) output trace

inductive OptionalLambdaReturnTypeTraceRejects
    (typeRejects : SourceId → Nat → Remainder → Remainder →
      ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | typeRejected {input afterArrow rejected : Remainder}
      {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} (arrowSpan : SourceSpan)
      (arrowParsed : ExactTokenParses (.symbol .arrow) input arrowSpan afterArrow)
      (typeRejected : typeRejects source endByte afterArrow rejected diagnostic trace) :
      OptionalLambdaReturnTypeTraceRejects typeRejects source endByte input rejected diagnostic trace

end Solcore.Syntax.DeclarativeGrammar
