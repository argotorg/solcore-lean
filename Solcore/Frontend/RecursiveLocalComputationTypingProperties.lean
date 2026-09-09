import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Frontend.LocalExpressionTypingProperties

/-! Independent source typing and Core typing retain every written child,
including both children of the fixed short-circuit interpretation. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem recursiveLocalComputationHasType_iff_elaborates
    {table : LocalNameTable} {context : Resolved.Context} {source : Syntax.Expr} {type : Core.Ty} :
    RecursiveLocalComputationHasType table context source type ↔
      ∃ core, RecursiveLocalComputationElaborates table context source core type := by
  constructor
  · intro typing
    induction typing with
    | pure child =>
        obtain ⟨resolved, resolution, typed⟩ := child.resolves
        obtain ⟨core, lowered, _⟩ := typed.lowers
        exact ⟨core, .pure resolution lowered typed⟩
    | group _ ih =>
        obtain ⟨core, child⟩ := ih
        exact ⟨core, .group child⟩
    | application _ _ functionIH argumentIH =>
        obtain ⟨functionCore, functionElaborated⟩ := functionIH
        obtain ⟨argumentCore, argumentElaborated⟩ := argumentIH
        exact ⟨.apply functionCore argumentCore, .application functionElaborated argumentElaborated⟩
    | pair _ _ leftIH rightIH =>
        obtain ⟨leftCore, leftChild⟩ := leftIH
        obtain ⟨rightCore, rightChild⟩ := rightIH
        exact ⟨.pair leftCore rightCore, .pair leftChild rightChild⟩
    | many _ _ headIH tailIH =>
        obtain ⟨headCore, headChild⟩ := headIH
        obtain ⟨tailCore, tailChild⟩ := tailIH
        exact ⟨.pair headCore tailCore, .many headChild tailChild⟩
    | binary operator _ _ leftIH rightIH =>
        obtain ⟨leftCore, leftElaborated⟩ := leftIH
        obtain ⟨rightCore, rightElaborated⟩ := rightIH
        exact ⟨.binary _ leftCore rightCore, .binary operator leftElaborated rightElaborated⟩
    | conditional _ _ _ conditionIH thenIH elseIH =>
        obtain ⟨conditionCore, conditionElaborated⟩ := conditionIH
        obtain ⟨thenCore, thenElaborated⟩ := thenIH
        obtain ⟨elseCore, elseElaborated⟩ := elseIH
        exact ⟨.ifE conditionCore thenCore elseCore, .conditional conditionElaborated thenElaborated elseElaborated⟩
    | logicalNot _ ih =>
        obtain ⟨core, child⟩ := ih
        exact ⟨.unary .boolNot core, .logicalNot child⟩
    | bitNot _ ih =>
        obtain ⟨core, child⟩ := ih
        exact ⟨.unary .wordNot core, .bitNot child⟩
    | logicalAnd _ _ leftIH rightIH =>
        obtain ⟨leftCore, leftChild⟩ := leftIH
        obtain ⟨rightCore, rightChild⟩ := rightIH
        exact ⟨.ifE leftCore rightCore (.bool false), .logicalAnd leftChild rightChild⟩
    | logicalOr _ _ leftIH rightIH =>
        obtain ⟨leftCore, leftChild⟩ := leftIH
        obtain ⟨rightCore, rightChild⟩ := rightIH
        exact ⟨.ifE leftCore (.bool true) rightCore, .logicalOr leftChild rightChild⟩
    | notEqual _ _ leftIH rightIH =>
        obtain ⟨leftCore, leftChild⟩ := leftIH
        obtain ⟨rightCore, rightChild⟩ := rightIH
        exact ⟨.unary .boolNot (.binary .wordEq leftCore rightCore), .notEqual leftChild rightChild⟩
    | lessEqual _ _ leftIH rightIH =>
        obtain ⟨leftCore, leftChild⟩ := leftIH
        obtain ⟨rightCore, rightChild⟩ := rightIH
        exact ⟨.unary .boolNot (.binary .wordGt leftCore rightCore), .lessEqual leftChild rightChild⟩
    | less _ _ leftIH rightIH =>
        obtain ⟨leftCore, leftChild⟩ := leftIH
        obtain ⟨rightCore, rightChild⟩ := rightIH
        exact ⟨leftCore.wordLt rightCore, .less leftChild rightChild⟩
    | greaterEqual _ _ leftIH rightIH =>
        obtain ⟨leftCore, leftChild⟩ := leftIH
        obtain ⟨rightCore, rightChild⟩ := rightIH
        exact ⟨.unary .boolNot (leftCore.wordLt rightCore), .greaterEqual leftChild rightChild⟩
  · rintro ⟨core, elaboration⟩
    induction elaboration with
    | pure resolution _ typing => exact .pure (resolution.reflects_type typing)
    | group _ ih => exact .group ih
    | application _ _ functionIH argumentIH => exact .application functionIH argumentIH
    | pair _ _ leftIH rightIH => exact .pair leftIH rightIH
    | many _ _ headIH tailIH => exact .many headIH tailIH
    | binary operator _ _ leftIH rightIH => exact .binary operator leftIH rightIH
    | conditional _ _ _ conditionIH thenIH elseIH => exact .conditional conditionIH thenIH elseIH
    | logicalNot _ ih => exact .logicalNot ih
    | bitNot _ ih => exact .bitNot ih
    | logicalAnd _ _ leftIH rightIH => exact .logicalAnd leftIH rightIH
    | logicalOr _ _ leftIH rightIH => exact .logicalOr leftIH rightIH
    | notEqual _ _ leftIH rightIH => exact .notEqual leftIH rightIH
    | lessEqual _ _ leftIH rightIH => exact .lessEqual leftIH rightIH
    | less _ _ leftIH rightIH => exact .less leftIH rightIH
    | greaterEqual _ _ leftIH rightIH => exact .greaterEqual leftIH rightIH

theorem RecursiveLocalComputationElaborates.core_hasType
    {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : RecursiveLocalComputationElaborates table context source core type) :
    Core.HasType context.values core type := by
  induction elaboration with
  | pure _ lowered typing => exact lowered.preserves_type typing
  | group _ ih => exact ih
  | application _ _ functionIH argumentIH => exact .apply functionIH argumentIH
  | pair _ _ leftIH rightIH | many _ _ leftIH rightIH => exact .pair leftIH rightIH
  | binary _ _ _ leftIH rightIH => exact .binary leftIH rightIH
  | conditional _ _ _ conditionIH thenIH elseIH => exact .ifE conditionIH thenIH elseIH
  | logicalNot _ ih | bitNot _ ih => exact .unary ih
  | logicalAnd _ _ leftIH rightIH => exact .ifE leftIH rightIH .bool
  | logicalOr _ _ leftIH rightIH => exact .ifE leftIH .bool rightIH
  | notEqual _ _ leftIH rightIH | lessEqual _ _ leftIH rightIH => exact .unary (.binary leftIH rightIH)
  | less _ _ leftIH rightIH => exact leftIH.wordLt rightIH
  | greaterEqual _ _ leftIH rightIH => exact .unary (leftIH.wordLt rightIH)

end Solcore.Frontend
