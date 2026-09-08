import Solcore.Frontend.LocalInputsExtensionTyping
import Solcore.Frontend.LocalExpressionEvaluation

/-! Adding a differently named fresh typed input preserves existing source
typing and evaluation. No source binding syntax or global allocation rule is
introduced; the exact value and both store endpoints are retained. -/

set_option autoImplicit false

namespace Solcore.Frontend

open LocalInputExtensionSupport

/-- Avoidance preserves and reflects raw source evaluation. Missing names in
an unselected branch need not resolve or type-check for this exact-store law. -/
theorem AvoidsLocalName.bindFresh_evaluates_iff {name : String} {source : Syntax.Expr}
    (avoids : AvoidsLocalName name source) (inputs : LocalInputs)
    (owner : Resolved.DeclarationId) (newType : Core.Ty) (newValue : Core.Value)
    (valueTyped : Core.ValueHasType newValue newType)
    {initialStore finalStore : Core.Store} {result : Core.Value} :
    LocalExpressionEvaluates (inputs.bindFresh owner name newType newValue valueTyped).names
        (inputs.bindFresh owner name newType newValue valueTyped).environment
        initialStore source result finalStore ↔
      LocalExpressionEvaluates inputs.names inputs.environment initialStore source result finalStore := by
  induction avoids generalizing initialStore finalStore result with
  | identifier different =>
      constructor
      · intro evaluation
        cases evaluation with
        | identifier named found =>
            have oldNamed := (LocalNameTable.lookup_cons_iff_of_ne different).mp named
            exact .identifier oldNamed
              ((identity_lookup_cons_iff (fresh_ne_of_named inputs owner oldNamed)).mp found)
      · intro evaluation
        cases evaluation with
        | identifier named found =>
            exact .identifier ((LocalNameTable.lookup_cons_iff_of_ne different).mpr named)
              ((identity_lookup_cons_iff (fresh_ne_of_named inputs owner named)).mpr found)
  | literal =>
      constructor
      · intro evaluation
        cases evaluation with
        | wordLiteral meaning => exact .wordLiteral meaning
      · intro evaluation
        cases evaluation with
        | wordLiteral meaning => exact .wordLiteral meaning
  | group _ ih =>
      constructor
      · intro evaluation
        cases evaluation with
        | group child => exact .group (ih.mp child)
      · intro evaluation
        cases evaluation with
        | group child => exact .group (ih.mpr child)
  | logicalNot _ ih =>
      constructor
      · intro evaluation
        cases evaluation with
        | logicalNot child => exact .logicalNot (ih.mp child)
      · intro evaluation
        cases evaluation with
        | logicalNot child => exact .logicalNot (ih.mpr child)
  | bitNot _ ih =>
      constructor
      · intro evaluation
        cases evaluation with
        | bitNot child => exact .bitNot (ih.mp child)
      · intro evaluation
        cases evaluation with
        | bitNot child => exact .bitNot (ih.mpr child)
  | add _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | add left right => exact .add (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | add left right => exact .add (leftIH.mpr left) (rightIH.mpr right)
  | subtract _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | subtract left right => exact .subtract (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | subtract left right => exact .subtract (leftIH.mpr left) (rightIH.mpr right)
  | multiply _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | multiply left right => exact .multiply (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | multiply left right => exact .multiply (leftIH.mpr left) (rightIH.mpr right)
  | greater _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | greater left right => exact .greater (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | greater left right => exact .greater (leftIH.mpr left) (rightIH.mpr right)
  | equal _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | equal left right => exact .equal (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | equal left right => exact .equal (leftIH.mpr left) (rightIH.mpr right)
  | notEqual _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | notEqual left right => exact .notEqual (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | notEqual left right => exact .notEqual (leftIH.mpr left) (rightIH.mpr right)
  | bitAnd _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | bitAnd left right => exact .bitAnd (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | bitAnd left right => exact .bitAnd (leftIH.mpr left) (rightIH.mpr right)
  | bitOr _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | bitOr left right => exact .bitOr (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | bitOr left right => exact .bitOr (leftIH.mpr left) (rightIH.mpr right)
  | bitXor _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | bitXor left right => exact .bitXor (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | bitXor left right => exact .bitXor (leftIH.mpr left) (rightIH.mpr right)
  | logicalAnd _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | andTrue left right => exact .andTrue (leftIH.mp left) (rightIH.mp right)
        | andFalse left => exact .andFalse (leftIH.mp left)
      · intro evaluation
        cases evaluation with
        | andTrue left right => exact .andTrue (leftIH.mpr left) (rightIH.mpr right)
        | andFalse left => exact .andFalse (leftIH.mpr left)
  | logicalOr _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | orTrue left => exact .orTrue (leftIH.mp left)
        | orFalse left right => exact .orFalse (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | orTrue left => exact .orTrue (leftIH.mpr left)
        | orFalse left right => exact .orFalse (leftIH.mpr left) (rightIH.mpr right)
  | conditional _ _ _ conditionIH thenIH elseIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | ifTrue condition branch => exact .ifTrue (conditionIH.mp condition) (thenIH.mp branch)
        | ifFalse condition branch => exact .ifFalse (conditionIH.mp condition) (elseIH.mp branch)
      · intro evaluation
        cases evaluation with
        | ifTrue condition branch => exact .ifTrue (conditionIH.mpr condition) (thenIH.mpr branch)
        | ifFalse condition branch => exact .ifFalse (conditionIH.mpr condition) (elseIH.mpr branch)

end Solcore.Frontend
