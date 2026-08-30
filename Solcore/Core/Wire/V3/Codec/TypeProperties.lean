import Solcore.Core.Wire.V3.Codec.Type

/-! Round-trip and canonicalization laws for Wire v3 types. -/

set_option autoImplicit false

namespace Solcore.Core.Wire.V3

theorem decodeTypeAtWithDepth_encodeType
    (type : Ty)
    (path : DecodePath)
    (depth : Nat)
    (enough : typeDepth type ≤ depth) :
    decodeTypeAtWithDepth depth path (encodeType type) = .ok type := by
  induction type generalizing depth path with
  | unit =>
      cases depth with
      | zero => simp [typeDepth] at enough
      | succ depth =>
          simp [decodeTypeAtWithDepth, encodeType]
          rfl
  | bool =>
      cases depth with
      | zero => simp [typeDepth] at enough
      | succ depth =>
          simp [decodeTypeAtWithDepth, encodeType]
          rfl
  | word =>
      cases depth with
      | zero => simp [typeDepth] at enough
      | succ depth =>
          simp [decodeTypeAtWithDepth, encodeType]
          rfl
  | product left right leftIH rightIH =>
      cases depth with
      | zero => simp [typeDepth] at enough
      | succ depth =>
          have bothEnough :
              Nat.max (typeDepth left) (typeDepth right) ≤ depth := by
            simpa [typeDepth] using enough
          have leftEnough : typeDepth left ≤ depth := by
            exact Nat.le_trans (Nat.le_max_left _ _) bothEnough
          have rightEnough : typeDepth right ≤ depth := by
            exact Nat.le_trans (Nat.le_max_right _ _) bothEnough
          simp only [decodeTypeAtWithDepth, encodeType]
          change (do
            let decodedLeft ←
              decodeTypeAtWithDepth depth (path.field "left") (encodeType left)
            let decodedRight ←
              decodeTypeAtWithDepth depth (path.field "right") (encodeType right)
            pure (Ty.product decodedLeft decodedRight)) =
              .ok (Ty.product left right)
          rw [leftIH (path.field "left") depth leftEnough,
            rightIH (path.field "right") depth rightEnough]
          rfl
  | function parameter result parameterIH resultIH =>
      cases depth with
      | zero => simp [typeDepth] at enough
      | succ depth =>
          have bothEnough :
              Nat.max (typeDepth parameter) (typeDepth result) ≤ depth := by
            simpa [typeDepth] using enough
          have parameterEnough : typeDepth parameter ≤ depth := by
            exact Nat.le_trans (Nat.le_max_left _ _) bothEnough
          have resultEnough : typeDepth result ≤ depth := by
            exact Nat.le_trans (Nat.le_max_right _ _) bothEnough
          simp only [decodeTypeAtWithDepth, encodeType]
          change (do
            let decodedParameter ← decodeTypeAtWithDepth depth
              (path.field "parameter") (encodeType parameter)
            let decodedResult ← decodeTypeAtWithDepth depth
              (path.field "result") (encodeType result)
            pure (Ty.function decodedParameter decodedResult)) =
              .ok (Ty.function parameter result)
          rw [parameterIH (path.field "parameter") depth parameterEnough,
            resultIH (path.field "result") depth resultEnough]
          rfl
  | sum left right leftIH rightIH =>
      cases depth with
      | zero => simp [typeDepth] at enough
      | succ depth =>
          have bothEnough :
              Nat.max (typeDepth left) (typeDepth right) ≤ depth := by
            simpa [typeDepth] using enough
          have leftEnough : typeDepth left ≤ depth := by
            exact Nat.le_trans (Nat.le_max_left _ _) bothEnough
          have rightEnough : typeDepth right ≤ depth := by
            exact Nat.le_trans (Nat.le_max_right _ _) bothEnough
          simp only [decodeTypeAtWithDepth, encodeType]
          change (do
            let decodedLeft ←
              decodeTypeAtWithDepth depth (path.field "left") (encodeType left)
            let decodedRight ←
              decodeTypeAtWithDepth depth (path.field "right") (encodeType right)
            pure (Ty.sum decodedLeft decodedRight)) = .ok (Ty.sum left right)
          rw [leftIH (path.field "left") depth leftEnough,
            rightIH (path.field "right") depth rightEnough]
          rfl
  | cell elementType elementIH =>
      cases depth with
      | zero => simp [typeDepth] at enough
      | succ depth =>
          have elementEnough : typeDepth elementType ≤ depth := by
            simpa [typeDepth] using enough
          simp only [decodeTypeAtWithDepth, encodeType]
          change (do
            let decodedElement ← decodeTypeAtWithDepth depth
              (path.field "elementType") (encodeType elementType)
            pure (Ty.cell decodedElement)) = .ok (Ty.cell elementType)
          rw [elementIH (path.field "elementType") depth elementEnough]
          rfl
  | namedData dataType =>
      cases depth with
      | zero => simp [typeDepth] at enough
      | succ depth =>
          simp only [decodeTypeAtWithDepth, encodeType]
          change (do
            let decodedDataType ← decodeDataTypeIdAt (path.field "dataType")
              (encodeDataTypeId dataType)
            pure (Ty.namedData decodedDataType)) = .ok (Ty.namedData dataType)
          rw [decodeDataTypeIdAt_encodeDataTypeId]
          rfl

theorem decodeTypeWithDepth_encodeType
    (maxDepth : Nat)
    (type : Ty)
    (enough : typeDepth type ≤ maxDepth) :
    decodeTypeWithDepth maxDepth (encodeType type) = .ok type :=
  decodeTypeAtWithDepth_encodeType type .root maxDepth enough

theorem decodeType_encodeType
    (type : Ty)
    (enough : typeDepth type ≤ defaultTypeDepth) :
    decodeType (encodeType type) = .ok type :=
  decodeTypeWithDepth_encodeType defaultTypeDepth type enough

theorem canonicalizeTypeWithDepth_of_decode_eq_ok
    (maxDepth : Nat)
    (json : Lean.Json)
    (type : Ty)
    (success : decodeTypeWithDepth maxDepth json = .ok type) :
    canonicalizeTypeWithDepth maxDepth json = .ok (encodeType type) := by
  rw [canonicalizeTypeWithDepth, success]
  rfl

theorem canonicalizeTypeWithDepth_encodeType
    (maxDepth : Nat)
    (type : Ty)
    (enough : typeDepth type ≤ maxDepth) :
    canonicalizeTypeWithDepth maxDepth (encodeType type) =
      .ok (encodeType type) := by
  apply canonicalizeTypeWithDepth_of_decode_eq_ok
  exact decodeTypeWithDepth_encodeType maxDepth type enough

end Solcore.Core.Wire.V3
