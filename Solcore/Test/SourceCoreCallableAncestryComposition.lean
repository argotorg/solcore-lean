import Solcore.SourceSemantics.CoreLowering.CallableAncestryComposition

#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Actual closed-matcher ranges justify composition through quantified
binders. The final key keeps requirements, and equal authenticated keys
determine the entire metadata state, for arbitrary ancestry depth. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableAncestryComposition
open Solcore Solcore.Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.CoreLowering.CallableAncestryMetadata
open Solcore.SourceSemantics.CoreLowering.CallableAncestryProfiles.SourceComposition

example {scheme : Scheme} {actual : Ty} {substitution : Substitution}
    (matched : SourceSpecialization.matchClosedSchemeInstance? scheme actual = some substitution) :
    RangesClosed substitution := matchClosed_ranges matched

example (sourceValue : TypedSource) (newer older : Substitution) (closed : RangesClosed older) :
    sourceValue.applySubstitution (newer.compose older) = (sourceValue.applySubstitution older).applySubstitution newer :=
  source newer older closed sourceValue

example {checked : Checked} {base : Base checked} {owned : Owned base}
    {frame : ContextFrame} {state : Solcore.SourceSemantics.CoreLowering.CallableAncestryMetadata.State}
    (authenticated : Authenticates owned frame (some state)) :
    ∃ (id : Core.Word) (named : Named owned id), state.owner = named.state.owner ∧
      RangesClosed state.active ∧
      eraseRequirements state.source = eraseRequirements (named.state.source.applySubstitution state.active) :=
  Authenticates.canonical authenticated

example {checked : Checked} {base : Base checked} {owned : Owned base}
    {leftFrame rightFrame : ContextFrame}
    {left right : Solcore.SourceSemantics.CoreLowering.CallableAncestryMetadata.State}
    (leftAuthenticated : Authenticates owned leftFrame (some left))
    (rightAuthenticated : Authenticates owned rightFrame (some right))
    (same : stateKey left = stateKey right) : left = right :=
  stateKey_injective leftAuthenticated rightAuthenticated same

private def first : TypeVarId := ⟨0⟩
private def bound : TypeVarId := ⟨1⟩
private def quantified : Scheme := ⟨[bound], .variable first⟩
private def olderOpen : Substitution := [(first, .variable bound)]
private def newerClosed : Substitution := [(bound, .word)]

/-- Removing the closed-range condition would make binder composition false:
the older open replacement can introduce the binder's protected variable. -/
example : quantified.apply (newerClosed.compose olderOpen) ≠ (quantified.apply olderOpen).apply newerClosed := by
  decide

example : ¬RangesClosed olderOpen := by
  intro closed
  have impossible := closed (first, .variable bound) (by simp [olderOpen])
  simp [Ty.freeVariables] at impossible

example : RangesClosed [(first, .word)] := by
  intro entry member
  cases List.mem_singleton.mp member
  rfl

end Tests.SourceCoreCallableAncestryComposition
