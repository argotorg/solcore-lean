import Solcore.Frontend.SourceInference.LocalHeaderRequirementTiming

/-! An initializer receipt is determined by its exact checker call. Source
syntax determines the annotation, and the executable child determines its
returned value and pre-generalization state. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference
open TypeSystem Detail

theorem LocalLetRequirementTiming.Annotation.unique
    {context : Context} {syntaxType : Option Syntax.TypeExpr} {left right : Option Ty}
    (first : LocalLetRequirementTiming.Annotation context syntaxType left)
    (second : LocalLetRequirementTiming.Annotation context syntaxType right) : left = right := by
  cases first with
  | none => cases second; rfl
  | some accepted =>
      cases second with
      | some other =>
          have same := Except.ok.inj (accepted.symm.trans other)
          exact congrArg Option.some same

theorem LocalLetRequirementTiming.Receipt.unique
    {fuel : Nat} {context : Context} {statement : Syntax.Statement}
    {initial : State} {result : StatementResult}
    (first second : LocalLetRequirementTiming.Receipt fuel context statement initial result) :
    first = second := by
  rcases first with ⟨name, initializer, annotation, expected, annotationAccepted,
    form, value, ready, child, completed⟩
  rcases second with ⟨otherName, otherInitializer, otherAnnotation, otherExpected,
    otherAnnotationAccepted, otherForm, otherValue, otherReady, otherChild, otherCompleted⟩
  have forms := form.symm.trans otherForm
  cases Syntax.StatementValue.letDecl.inj forms with
  | intro sameName rest =>
      rcases rest with ⟨sameAnnotation, sameInitializer⟩
      cases sameName
      cases sameAnnotation
      cases Option.some.inj sameInitializer
      have sameExpected := annotationAccepted.unique otherAnnotationAccepted
      cases sameExpected
      have sameChild := Except.ok.inj (child.symm.trans otherChild)
      cases Prod.mk.inj sameChild with
      | intro sameValue sameReady =>
          cases sameValue
          cases sameReady
          rfl

theorem LocalHeaderRequirementTiming.Receipt.unique
    {fuel : Nat} {context : Context} {statement : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State}
    (first second : LocalHeaderRequirementTiming.Receipt fuel context statement initial result) :
    first = second := by
  rcases first with ⟨name, initializer, annotation, expected, annotationAccepted,
    form, value, ready, child, completed⟩
  rcases second with ⟨otherName, otherInitializer, otherAnnotation, otherExpected,
    otherAnnotationAccepted, otherForm, otherValue, otherReady, otherChild, otherCompleted⟩
  have forms := form.symm.trans otherForm
  cases Syntax.ForItemValue.letDecl.inj forms with
  | intro sameName rest =>
      rcases rest with ⟨sameAnnotation, sameInitializer⟩
      cases sameName
      cases sameAnnotation
      cases Option.some.inj sameInitializer
      have sameExpected := annotationAccepted.unique otherAnnotationAccepted
      cases sameExpected
      have sameChild := Except.ok.inj (child.symm.trans otherChild)
      cases Prod.mk.inj sameChild with
      | intro sameValue sameReady =>
          cases sameValue
          cases sameReady
          rfl

end Solcore.Frontend.SourceInference
