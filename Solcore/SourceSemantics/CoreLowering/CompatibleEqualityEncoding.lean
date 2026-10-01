import Solcore.SourceSemantics.CoreLowering.CompatibleEqualityMeaning

/-! Public compatible encoding receipts feed real generated comparators.
The second encoding may extend the registry; the first value is transported
through that authenticated extension before the comparison proof is used. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleEquality
open Core Frontend SourceCoreCompatibleDataEquality DataEquality CompatiblePayload

 theorem encoded_compare_run {fuel : Nat} {context : SourceCoreCompatibleValues.Context}
    (prepared : Prepared context.checked)
    {left right : SourceCoreDataValues.Value} {sourceLeft sourceRight : Dynamic.Value}
    {encodedLeft : SourceCoreCompatibleValues.Encoded fuel context prepared.sourceType left}
    {encodedRight : SourceCoreCompatibleValues.Encoded fuel encodedLeft.context prepared.sourceType right}
    (leftAccepted : SourceCoreCompatibleValues.encode fuel context prepared.sourceType left = .ok encodedLeft)
    (rightAccepted : SourceCoreCompatibleValues.encode fuel encodedLeft.context prepared.sourceType right = .ok encodedRight)
    (leftMeaning : CompatibleEncoding.Means left sourceLeft) (rightMeaning : CompatibleEncoding.Means right sourceRight)
    {functions : FunctionModel context.checked.catalog} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) (functionLeaves : FunctionObservations context.checked.catalog functions identities)
    (mapping : GeneralHeap.LocationMap) (world : StoreTyping) (environment : Environment) (store : Store)
    (leftExpression rightExpression : Expr)
    (leftSelected : Selects environment leftExpression encodedLeft.value)
    (rightSelected : Selects environment rightExpression encodedRight.value) :
    ∃ result, (result = true ↔ Dynamic.ValueEquivalent sourceLeft sourceRight) ∧
      (∃ required, ∀ budget, required ≤ budget →
        runStateful budget (.initial (comparison prepared leftExpression rightExpression) environment store) =
          .done (.bool result) (preparedStore prepared environment store)) ∧
      (∀ budget actual actualStore,
        runStateful budget (.initial (comparison prepared leftExpression rightExpression) environment store) = .done actual actualStore →
          actual = .bool result ∧ actualStore = preparedStore prepared environment store) := by
  have first := CompatibleEncoding.encode_represents_at (functions := functions) leftAccepted leftMeaning mapping world
  have second := CompatibleEncoding.encode_represents_at (context := encodedLeft.context) (functions := functions) rightAccepted rightMeaning mapping world
  have first := first.extend encodedRight.preserves (.refl mapping) (.refl world)
  have firstType := Except.ok.inj (encodedLeft.projected.symm.trans prepared.projection)
  have secondType := Except.ok.inj (encodedRight.projected.symm.trans prepared.projection)
  rw [firstType] at first
  rw [secondType] at second
  exact represented_compare_run prepared faithful functionLeaves first second environment store _ _ leftSelected rightSelected

end Solcore.SourceSemantics.CoreLowering.CompatibleEquality
