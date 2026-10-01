import Solcore.SourceSemantics.CoreLowering.TypedImperativeNative

/-! Static inversion of the actual for closure. This removes only syntactic
administrative insertions; it makes no runtime capture or source-type claim. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedImperativeFor.Native
open Core TypedLexicalWhile.Native

theorem advance_children {definitions : DataEnvironment} {context : Core.Context} {type result : Ty} {computation body : Expr}
    (typed : HasType context (LocalLoop.advance type computation body) result definitions) :
    (∃ headType, HasType context computation headType definitions) ∧
    (∃ tailType, HasType context body tailType definitions) := by
  cases typed with
  | caseE computation failure next =>
    cases next with
    | caseE outer inner transfer =>
      cases inner with
      | caseE tested continued returned =>
        exact ⟨⟨_, computation⟩, ⟨_, remove_front (remove_front (remove_front continued))⟩⟩

theorem iterate_children {definitions : DataEnvironment} {context : Core.Context} {type result : Ty}
    {condition body post : Expr} {reason : Word}
    (typed : HasType context (LocalLoop.iterate type condition body post reason) result definitions) :
    (∃ bodyType, HasType context body bodyType definitions) ∧
    (∃ postType, HasType context post postType definitions) ∧
    HasType context (LocalLoop.iterate type condition body post reason) (LocalLoop.resultType type) definitions := by
  cases typed with
  | letE allocation installed =>
    cases allocation with
    | newCell empty =>
      cases installed with
      | letE written invoked =>
        cases written with
        | storeCell reference closure =>
          cases closure with
          | inRight unitWF raw =>
            cases raw with
            | lambda parameterWF resultWF loop =>
              obtain ⟨⟨_, yes⟩, _⟩ := conditional_children loop
              obtain ⟨⟨_, bodyTyped⟩, ⟨_, postAdvance⟩⟩ := advance_children yes
              obtain ⟨_, postTyped⟩ := advance_child postAdvance
              refine ⟨⟨_, remove_front (remove_front bodyTyped)⟩,
                ⟨_, remove_front (remove_front postTyped)⟩, ?_⟩
              apply HasType.letE (.newCell empty)
              apply HasType.letE (.storeCell reference (.inRight unitWF (.lambda parameterWF resultWF loop)))
              apply LocalLoop.invoke_hasType reason ?_ (.var rfl)
              cases resultWF with
              | sum _ control =>
                cases control with
                | sum normal transfer =>
                  cases normal with | sum _ returned => exact returned

/-- The annotation on the emitted Unit closure fixes its body result. -/
theorem installed_body {definitions : DataEnvironment} {context : Core.Context}
    {type : Ty} {condition body post : Expr} {reason : Word}
    (typed : HasType context (LocalLoop.iterate type condition body post reason) (LocalLoop.resultType type) definitions) :
    HasType (.unit :: OptionalCell.referenceType (LocalLoop.functionType type) :: context)
      (LocalLoop.loopBody type condition body post reason) (LocalLoop.resultType type) definitions := by
  cases typed with
  | letE allocation next =>
    cases allocation with
    | newCell initializer =>
      cases next with
      | letE write invocation =>
        cases write with
        | storeCell reference value =>
          cases reference with
          | var found =>
            simp only [List.getElem?_cons_zero, Option.some.injEq, Ty.cell.injEq] at found
            cases found
            cases value with
            | inRight _ closure =>
              cases closure with
              | lambda _ _ typedBody => exact typedBody
end Solcore.SourceSemantics.CoreLowering.TypedImperativeFor.Native
