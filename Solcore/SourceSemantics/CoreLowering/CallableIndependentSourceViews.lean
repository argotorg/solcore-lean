import Solcore.SourceSemantics.CoreLowering.CallableAppliedDynamicSourceMaterialization
import Solcore.SourceSemantics.CoreLowering.LambdaMetadataViews

/-! The Source graph retained by a live closure and its authentic metadata
history have the same node shapes. Requirement rewriting is kept separate;
this does not identify the native candidate's complete compilation source. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndependentSourceViews
open Frontend SourceInference
open CallableAncestryMetadata LambdaMetadataViews

private theorem erased_nodes (nodes : List Node) :
    DataPatternValues.ListRel NodeView nodes (nodes.map eraseNodeRequirements) := by
  induction nodes with
  | nil => exact .nil
  | cons node nodes ih =>
    apply DataPatternValues.ListRel.cons _ ih
    cases node with
    | expression => exact .expression rfl rfl
    | statement => exact .statement _

theorem erased_view (source : TypedSource) :
    MetadataView source (eraseRequirements source) :=
  ⟨rfl, rfl, rfl, erased_nodes source.nodes⟩

theorem of_erased_eq {source metadata : TypedSource}
    (same : eraseRequirements source = eraseRequirements metadata) :
    MetadataView source metadata := by
  have left := erased_view source
  rw [same] at left
  exact left.trans (erased_view metadata).symm

/-- This correspondence follows from the actual finite paired history. It
does not require full Source equality at an applied read. -/
theorem of_pair
    {checked : SourceCoreCompatibleCatalog.Checked}
    {base : SourceCoreCompatibleFunctions.Prepared checked}
    {inputs : SourceCoreCallableAncestryPreparation.Inputs base}
    {frame : SourceCoreCallablePairedFrames.Frame}
    {state : SourceCoreCallableAncestryReadRecipes.State} {source : TypedSource}
    (paired : CallableAppliedDynamicSourceMaterialization.Pair inputs frame state source) :
    MetadataView source state.metadata.source :=
  of_erased_eq (CallableAppliedDynamicSourceMaterialization.erase_source paired).symm

end Solcore.SourceSemantics.CoreLowering.CallableIndependentSourceViews
