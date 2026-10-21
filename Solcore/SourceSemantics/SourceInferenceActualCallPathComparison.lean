import Solcore.SourceSemantics.SourceInferenceActualCallGraph

/-! Two actual paths have an ancestor relation or diverge at distinct
children of one reached call. This retains paths, not guessed source order. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution

theorem CallOccurrence.uncons {root call : CallIndex}
    (path : CallOccurrence root call) :
    root = call ∨ ∃ child, ChildStep root child ∧ CallOccurrence child call := by
  induction path with
  | root accepted => exact .inl rfl
  | child prior step ih =>
      rcases ih with rfl | ⟨first, firstStep, rest⟩
      · exact .inr ⟨_, step, .root step.child_accepted⟩
      · exact .inr ⟨first, firstStep, .child rest step⟩

theorem CallOccurrence.compare_paths {root left right : CallIndex}
    (leftPath : CallOccurrence root left) (rightPath : CallOccurrence root right) :
    CallOccurrence left right ∨ CallOccurrence right left ∨
      ∃ parent first second,
        CallOccurrence root parent ∧ ChildStep parent first ∧ ChildStep parent second ∧
        first ≠ second ∧ CallOccurrence first left ∧ CallOccurrence second right := by
  induction leftPath generalizing right with
  | root accepted => exact .inl rightPath
  | @child parent left prior step ih =>
      rcases ih rightPath with forward | backward | ⟨split, first, second, reached, a, b, distinct, rest, other⟩
      · rcases forward.uncons with rfl | ⟨first, firstStep, rest⟩
        · exact .inr (.inl (.child (.root step.parent_accepted) step))
        · by_cases same : left = first
          · cases same
            exact .inl rest
          · exact .inr (.inr ⟨parent, left, first, prior, step, firstStep, same,
              .root step.child_accepted, rest⟩)
      · exact .inr (.inl (.child backward step))
      · exact .inr (.inr ⟨split, first, second, reached, a, b, distinct, .child rest step, other⟩)

end Solcore.SourceSemantics.SourceInferenceExecution
