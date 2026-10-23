import Solcore.Frontend.RustHull.SemanticsCorrespondenceSupport
import Solcore.Frontend.RustHull.LoweringSafety

/-! The actual type and zero-initializer translations agree with Hull's
independent layouts. Recursive references keep their specified opaque word
representation; successful lowering supplies the layout premise. -/
set_option autoImplicit false

namespace Solcore.Frontend.RustHull.Correspondence

def coreType : Semantics.Shape → Core.Ty
  | .word => .word
  | .bool => .bool
  | .unit => .unit
  | .product left right => .product (coreType left) (coreType right)
  | .sum left right => .sum (coreType left) (coreType right)

theorem coreType_injective : Function.Injective coreType := by
  intro left target same
  induction left generalizing target with
  | word => cases target <;> simp_all [coreType]
  | bool => cases target <;> simp_all [coreType]
  | unit => cases target <;> simp_all [coreType]
  | product left right leftIH rightIH =>
      cases target with
      | product otherLeft otherRight =>
          obtain ⟨a, b⟩ := Core.Ty.product.inj same
          rw [leftIH a, rightIH b]
      | _ => cases same
  | sum left right leftIH rightIH =>
      cases target with
      | sum otherLeft otherRight =>
          obtain ⟨a, b⟩ := Core.Ty.sum.inj same
          rw [leftIH a, rightIH b]
      | _ => cases same

theorem lowerType_shape {fuel : Nat} {type : Ty} {lowered : Core.Ty}
    (accepted : lowerType fuel type = .ok lowered) :
    ∃ shape, Semantics.shape type = some shape ∧ coreType shape = lowered := by
  induction fuel generalizing type lowered with
  | zero => simp [lowerType, fail] at accepted
  | succ fuel ih =>
      cases type with
      | word => cases accepted; exact ⟨.word, rfl, rfl⟩
      | bool => cases accepted; exact ⟨.bool, rfl, rfl⟩
      | unit => cases accepted; exact ⟨.unit, rfl, rfl⟩
      | namedRef name => cases accepted; exact ⟨.word, rfl, rfl⟩
      | named name inner => exact ih (type := inner) accepted
      | located span inner => exact ih (type := inner) accepted
      | function parameters result => simp [lowerType, fail] at accepted
      | product left right =>
          simp only [lowerType] at accepted
          obtain ⟨leftType, leftAccepted, accepted⟩ := lower_bind_eq_ok.mp accepted
          obtain ⟨rightType, rightAccepted, returned⟩ := lower_bind_eq_ok.mp accepted
          cases returned
          obtain ⟨leftShape, leftShapeEq, leftEq⟩ := ih leftAccepted
          obtain ⟨rightShape, rightShapeEq, rightEq⟩ := ih rightAccepted
          refine ⟨.product leftShape rightShape, ?_, ?_⟩
          · simp [Semantics.shape, leftShapeEq, rightShapeEq]
          · simp [coreType, leftEq, rightEq]
      | sum left right =>
          simp only [lowerType] at accepted
          obtain ⟨leftType, leftAccepted, accepted⟩ := lower_bind_eq_ok.mp accepted
          obtain ⟨rightType, rightAccepted, returned⟩ := lower_bind_eq_ok.mp accepted
          cases returned
          obtain ⟨leftShape, leftShapeEq, leftEq⟩ := ih leftAccepted
          obtain ⟨rightShape, rightShapeEq, rightEq⟩ := ih rightAccepted
          refine ⟨.sum leftShape rightShape, ?_, ?_⟩
          · simp [Semantics.shape, leftShapeEq, rightShapeEq]
          · simp [coreType, leftEq, rightEq]

theorem zeroValue_evaluates (shape : Semantics.Shape)
    {expression : Core.Expr} (accepted : zeroValue (coreType shape) = .ok expression)
    (environment : Core.Environment) (store : Core.Store) :
    ∃ value, ValueRel (coreType shape) shape.zero value ∧
      Core.Evaluates environment store expression value store := by
  induction shape generalizing expression with
  | word => cases accepted; exact ⟨_, .word _, .word⟩
  | bool => cases accepted; exact ⟨_, .bool _, .bool⟩
  | unit => cases accepted; exact ⟨_, .unit, .unit⟩
  | product left right leftIH rightIH =>
      simp only [coreType, zeroValue] at accepted
      obtain ⟨leftCode, leftAccepted, accepted⟩ := lower_bind_eq_ok.mp accepted
      obtain ⟨rightCode, rightAccepted, returned⟩ := lower_bind_eq_ok.mp accepted
      cases returned
      obtain ⟨leftValue, leftRel, leftEval⟩ := leftIH leftAccepted
      obtain ⟨rightValue, rightRel, rightEval⟩ := rightIH rightAccepted
      exact ⟨_, .pair leftRel rightRel, .pair leftEval rightEval⟩
  | sum left right leftIH _ =>
      simp only [coreType, zeroValue] at accepted
      obtain ⟨leftCode, leftAccepted, returned⟩ := lower_bind_eq_ok.mp accepted
      cases returned
      obtain ⟨value, related, evaluation⟩ := leftIH leftAccepted
      exact ⟨_, .inl related, .inLeft evaluation⟩

end Solcore.Frontend.RustHull.Correspondence
