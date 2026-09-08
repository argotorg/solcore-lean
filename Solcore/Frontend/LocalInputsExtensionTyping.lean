import Solcore.Frontend.LocalInputsExtensionLookupSupport
import Solcore.Frontend.LocalExpressionTyping
import Solcore.Frontend.LocalNameAvoidanceProperties

/-! Adding a differently named fresh typed input preserves and reflects source
typing. The supplied value does not change any existing identity lookup. -/

set_option autoImplicit false

namespace Solcore.Frontend

open LocalInputExtensionSupport

theorem AvoidsLocalName.bindFresh_hasType_iff {name : String} {source : Syntax.Expr}
    (avoids : AvoidsLocalName name source) (inputs : LocalInputs)
    (owner : Resolved.DeclarationId) (newType : Core.Ty) (newValue : Core.Value)
    (valueTyped : Core.ValueHasType newValue newType) {resultType : Core.Ty} :
    LocalExpressionHasType (inputs.bindFresh owner name newType newValue valueTyped).names
        (inputs.bindFresh owner name newType newValue valueTyped).context source resultType ↔
      LocalExpressionHasType inputs.names inputs.context source resultType := by
  induction avoids generalizing resultType with
  | identifier different =>
      constructor
      · intro typing
        cases typing with
        | identifier named found =>
            have oldNamed := (LocalNameTable.lookup_cons_iff_of_ne different).mp named
            exact .identifier oldNamed
              ((identity_lookup_cons_iff (fresh_ne_of_named inputs owner oldNamed)).mp found)
      · intro typing
        cases typing with
        | identifier named found =>
            exact .identifier ((LocalNameTable.lookup_cons_iff_of_ne different).mpr named)
              ((identity_lookup_cons_iff (fresh_ne_of_named inputs owner named)).mpr found)
  | literal =>
      constructor
      · intro typing
        cases typing with
        | wordLiteral meaning => exact .wordLiteral meaning
      · intro typing
        cases typing with
        | wordLiteral meaning => exact .wordLiteral meaning
  | group _ ih =>
      constructor
      · intro typing
        cases typing with
        | group child => exact .group (ih.mp child)
      · intro typing
        cases typing with
        | group child => exact .group (ih.mpr child)
  | logicalNot _ ih =>
      constructor
      · intro typing
        cases typing with
        | logicalNot child => exact .logicalNot (ih.mp child)
      · intro typing
        cases typing with
        | logicalNot child => exact .logicalNot (ih.mpr child)
  | bitNot _ ih =>
      constructor
      · intro typing
        cases typing with
        | bitNot child => exact .bitNot (ih.mp child)
      · intro typing
        cases typing with
        | bitNot child => exact .bitNot (ih.mpr child)
  | add _ _ leftIH rightIH =>
      constructor
      · intro typing
        cases typing with
        | add left right => exact .add (leftIH.mp left) (rightIH.mp right)
      · intro typing
        cases typing with
        | add left right => exact .add (leftIH.mpr left) (rightIH.mpr right)
  | subtract _ _ leftIH rightIH =>
      constructor
      · intro typing
        cases typing with
        | subtract left right => exact .subtract (leftIH.mp left) (rightIH.mp right)
      · intro typing
        cases typing with
        | subtract left right => exact .subtract (leftIH.mpr left) (rightIH.mpr right)
  | multiply _ _ leftIH rightIH =>
      constructor
      · intro typing
        cases typing with
        | multiply left right => exact .multiply (leftIH.mp left) (rightIH.mp right)
      · intro typing
        cases typing with
        | multiply left right => exact .multiply (leftIH.mpr left) (rightIH.mpr right)
  | greater _ _ leftIH rightIH =>
      constructor
      · intro typing
        cases typing with
        | greater left right => exact .greater (leftIH.mp left) (rightIH.mp right)
      · intro typing
        cases typing with
        | greater left right => exact .greater (leftIH.mpr left) (rightIH.mpr right)
  | equal _ _ leftIH rightIH =>
      constructor
      · intro typing
        cases typing with
        | equal left right => exact .equal (leftIH.mp left) (rightIH.mp right)
      · intro typing
        cases typing with
        | equal left right => exact .equal (leftIH.mpr left) (rightIH.mpr right)
  | notEqual _ _ leftIH rightIH =>
      constructor
      · intro typing
        cases typing with
        | notEqual left right => exact .notEqual (leftIH.mp left) (rightIH.mp right)
      · intro typing
        cases typing with
        | notEqual left right => exact .notEqual (leftIH.mpr left) (rightIH.mpr right)
  | lessEqual _ _ leftIH rightIH =>
      constructor
      · intro typing
        cases typing with
        | lessEqual left right => exact .lessEqual (leftIH.mp left) (rightIH.mp right)
      · intro typing
        cases typing with
        | lessEqual left right => exact .lessEqual (leftIH.mpr left) (rightIH.mpr right)
  | bitAnd _ _ leftIH rightIH =>
      constructor
      · intro typing
        cases typing with
        | bitAnd left right => exact .bitAnd (leftIH.mp left) (rightIH.mp right)
      · intro typing
        cases typing with
        | bitAnd left right => exact .bitAnd (leftIH.mpr left) (rightIH.mpr right)
  | bitOr _ _ leftIH rightIH =>
      constructor
      · intro typing
        cases typing with
        | bitOr left right => exact .bitOr (leftIH.mp left) (rightIH.mp right)
      · intro typing
        cases typing with
        | bitOr left right => exact .bitOr (leftIH.mpr left) (rightIH.mpr right)
  | bitXor _ _ leftIH rightIH =>
      constructor
      · intro typing
        cases typing with
        | bitXor left right => exact .bitXor (leftIH.mp left) (rightIH.mp right)
      · intro typing
        cases typing with
        | bitXor left right => exact .bitXor (leftIH.mpr left) (rightIH.mpr right)
  | logicalAnd _ _ leftIH rightIH =>
      constructor
      · intro typing
        cases typing with
        | logicalAnd left right => exact .logicalAnd (leftIH.mp left) (rightIH.mp right)
      · intro typing
        cases typing with
        | logicalAnd left right => exact .logicalAnd (leftIH.mpr left) (rightIH.mpr right)
  | logicalOr _ _ leftIH rightIH =>
      constructor
      · intro typing
        cases typing with
        | logicalOr left right => exact .logicalOr (leftIH.mp left) (rightIH.mp right)
      · intro typing
        cases typing with
        | logicalOr left right => exact .logicalOr (leftIH.mpr left) (rightIH.mpr right)
  | conditional _ _ _ conditionIH thenIH elseIH =>
      constructor
      · intro typing
        cases typing with
        | conditional condition thenBranch elseBranch =>
            exact .conditional (conditionIH.mp condition) (thenIH.mp thenBranch) (elseIH.mp elseBranch)
      · intro typing
        cases typing with
        | conditional condition thenBranch elseBranch =>
            exact .conditional (conditionIH.mpr condition) (thenIH.mpr thenBranch) (elseIH.mpr elseBranch)

end Solcore.Frontend
