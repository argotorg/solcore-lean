import Solcore.Frontend.RustHull.NamedCallCorrespondence

/-! A failed argument bundle skips the named callee after the actual function
slot read. The call wrapper preserves its reason and the arguments' final store. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.NamedCallCorrespondence

theorem primitive_not_language (name : String) (type : Ty)
    (arguments : List Semantics.Value) (reason : Core.Word) :
    Semantics.primitive? name type arguments ≠ some (.fault (.language reason)) := by
  intro computed
  simp only [Semantics.primitive?] at computed
  split at computed
  all_goals try simp only [Semantics.binaryWords, Semantics.unaryWord, Semantics.ternaryWords,
    Semantics.compareWords, Semantics.booleanResult] at computed
  all_goals repeat (any_goals (first | cases computed | split at computed))

theorem call_argument_failure {codes : List Lowered} {functionCode : Lowered}
    {resultType inputType outputType : Core.Ty} {body : Core.Expr}
    {captured environment : Core.Environment} {mapping : Core.Renaming}
    {initial final : Core.Store} {reason : Core.Word}
    (functionEvaluated : Core.Evaluates environment initial (functionCode.expression.rename mapping)
      (.inRight .word (.closure inputType outputType body captured)) initial)
    (argumentsEvaluated : Core.Evaluates
      (.closure inputType outputType body captured :: environment) initial
      ((packArguments codes).expression.rename (fun index => 1 + mapping index))
      (.inLeft (packArguments codes).type (.word reason)) final) :
    Core.Evaluates environment initial
      ((Core.LanguageResult.bind resultType functionCode.expression
        (Core.LanguageResult.bind resultType ((packArguments codes).expression.weakenAt 0)
          (.apply (.var 1) (.var 0)))).rename mapping)
      (.inLeft resultType (.word reason)) final := by
  have shifted : ((packArguments codes).expression.weakenAt 0).rename mapping.lift =
      (packArguments codes).expression.rename (fun index => 1 + mapping index) := by
    rw [← Core.Expr.rename_insertion, Core.Expr.rename_comp,
      Core.Renaming.lift_comp_insertion_zero]
    congr 1
    funext index
    simp [Core.Renaming.comp, Core.Renaming.insertion, Nat.add_comm]
  apply Core.LanguageResult.bind_success resultType functionEvaluated
  exact Core.LanguageResult.bind_failure resultType
    (by simpa only [shifted] using argumentsEvaluated)

end Solcore.Frontend.RustHull.NamedCallCorrespondence
