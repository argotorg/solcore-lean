import Solcore.Frontend.LocalExpressionEvaluator
import Solcore.Frontend.LocalExpressionCost
import Solcore.Frontend.LocalReferenceProperties
import Solcore.Frontend.WordLiteralProperties
import Solcore.Resolved.LocalScopeProperties

/-! Every independent raw derivation is executed directly on its original
syntax and caller rows. Store endpoints impose no extra evaluator premise. -/
set_option autoImplicit false
namespace Solcore.Frontend

theorem evaluateLocalExpressionWithCost?_complete {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {source : Syntax.Expr} {value : Core.Value} {cost : Nat}
    (evaluation : LocalExpressionEvaluatesWithCost table environment
      initialStore source value finalStore cost) :
    evaluateLocalExpressionWithCost? table environment source = some (value, cost) := by
  induction evaluation with
  | identifier named found =>
      simp [evaluateLocalExpressionWithCost?, LocalNameTable.lookup?_iff.mpr named,
        Resolved.LocalScope.lookup?_iff.mpr found]
  | wordLiteral meaning =>
      simp [evaluateLocalExpressionWithCost?, interpretWordLiteral?_complete meaning]
  | group _ ih => simpa only [evaluateLocalExpressionWithCost?] using ih
  | unit => simp only [evaluateLocalExpressionWithCost?]
  | many _ _ headIH tailIH =>
      rw [evaluateLocalExpressionWithCost?]
      simp only [headIH, tailIH, bind, Option.bind_some, pure]
  | logicalNot _ ih | bitNot _ ih | andFalse _ ih | orTrue _ ih =>
      simp [evaluateLocalExpressionWithCost?, ih]
  | pair _ _ leftIH rightIH
  | add _ _ leftIH rightIH | subtract _ _ leftIH rightIH | multiply _ _ leftIH rightIH
  | divide _ _ leftIH rightIH | modulo _ _ leftIH rightIH
  | bitAnd _ _ leftIH rightIH | bitOr _ _ leftIH rightIH | bitXor _ _ leftIH rightIH
  | greater _ _ leftIH rightIH | less _ _ leftIH rightIH
  | equal _ _ leftIH rightIH | notEqual _ _ leftIH rightIH
  | lessEqual _ _ leftIH rightIH | greaterEqual _ _ leftIH rightIH
  | andTrue _ _ leftIH rightIH | orFalse _ _ leftIH rightIH
  | ifTrue _ _ leftIH rightIH | ifFalse _ _ leftIH rightIH =>
      simp [evaluateLocalExpressionWithCost?, evaluateLocalWordBinaryWithCost?, leftIH, rightIH]

end Solcore.Frontend
