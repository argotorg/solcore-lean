import Solcore.SourceSemantics.Staging.SelectedRecursivePreservation
import Solcore.SourceSemantics.TraitSubstitutionProperties

/-! Compatibility for callers that already have whole-program validity.
Selected public callers supply their actual registry certificate directly. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
open Solcore.SourceSemantics.Dynamic

theorem SelectedBodies.of_program {program : Program} {registry : Registry}
    (wellFormed : ProgramWellFormed program) : SelectedBodies program registry := by
  refine ⟨wellFormed.signatures, ?_, ?_⟩
  · intro instantiation body evidence roots scope instantiated _roots _selected
    exact instantiated.certificate wellFormed
  · intro context evidence dictionary traitName methodName requirements body roots child selected _roots _child
    cases selected with
    | intro selects closed implementation trait traitName goal head method methodName owner
        requirements instantiated assembled covers =>
      exact .intro selects closed implementation trait traitName goal head method methodName owner
        requirements instantiated assembled covers (instantiated.certificate wellFormed)

end Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
