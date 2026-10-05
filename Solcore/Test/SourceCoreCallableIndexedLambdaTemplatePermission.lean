import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaTemplatePermission
import Solcore.Test.SourceCoreCallableIndexedLambdaRuntimeBody

/-! Formal consumers of actual template preparation and actual retained code.
Dispatch permission is separate from call-time catalogue authority and from
execution of any lambda body. This module adds no runtime runner. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedLambdaTemplatePermission
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableIndexedLambdaValues CallableIndexedHistory CallableAppliedViewProvenance

abbrev actual_prepare := @CallableAppliedViewProvenance.prepared_template
abbrev actual_template := @CallableIndexedLambdaTemplatePermission.selected
abbrev old_header := @CallableAppliedViewProvenance.header_of_prepared
abbrev old_body := @CallableIndexedLambdaRuntimeBody.Body.of_tree

section ActualCode
variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code prepared function scope administrative) (history : History code)

theorem actual_permission :
    SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs
      history.metadata code.descriptor.id = true :=
  CallableIndexedLambdaTemplatePermission.lambda_allowed code history

theorem actual_caller {currentNative : NativeFrame} {currentGhost : GhostFrame}
    {current : Option CallableIndexedHistory.MetadataState}
    (carried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table
      currentNative currentGhost current) :
    Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table
      (SourceCoreCallableIndexedDispatch.selectedFrame prepared.ancestry.graph.table code.descriptor.id
        history.native currentNative)
      (.lambda code.descriptor.id history.ghost) (some history.metadata) :=
  CallableIndexedLambdaTemplatePermission.ordinary_history code history carried

/-- The selected first-match template keeps the complete ordered source header. -/
theorem actual_ordered_header :
    ∃ template, prepared.ancestry.graph.inputs.templates.lambdaAt? code.descriptor.id = some template ∧
      PreparedTemplate prepared.base template ∧
      template.owner = code.compilation.owner ∧ template.id = code.id ∧ template.active = code.active ∧
      template.node.form = .lambda function.parameters function.resultType function.body :=
  CallableIndexedLambdaTemplatePermission.selected code

/-- Permission does not alter the value's ordered captures, including unused
and shadowed suffix slots, or either retained active substitution. -/
theorem same_value_and_history {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {actual : Core.Environment} (captured : Captures prepared mapping world scope function.captured actual) :
    SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs
      history.metadata code.descriptor.id = true ∧
    CallableIndexedLambdaValues.value code captured.embedding history.native actual =
      .pair (.pair (.inLeft .word .unit)
        (.closure code.receipt.parameterCore (LanguageResult.resultType code.receipt.resultCore)
          (code.body.rename captured.embedding.lift.lift)
          (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame history.native :: actual)))
        (.word code.descriptor.id) ∧
    history.metadata.metadata.source = function.source ∧ history.metadata.metadata.owner = code.compilation.owner ∧
    history.metadata.nativeActive = code.active :=
  ⟨actual_permission code history, rfl, history.source, history.owner, history.active⟩
end ActualCode

section Prepared
variable {checked : SourceCoreCompatibleCatalog.Checked} {base : SourceCoreCompatibleFunctions.Prepared checked}
  {inventory : SourceCoreLambdaTemplates.Inventory checked} {template : SourceCoreLambdaTemplates.Lambda}

/-- Successful preparation retains the entire original source and the exact
ordered inherited witness list, even when rows repeat. -/
theorem ordered_principal_source
    (accepted : SourceCoreLambdaTemplates.prepare base = .ok inventory)
    (member : template ∈ inventory.lambdas) :
    template.principalSource = SourceTypedRuntime.rewriteLocalRequirements
      (((base.contexts.find? (fun parent => decide
        (parent.caller.key = template.owner ∧ parent.substitution = template.active))).map
          (·.witnesses)).getD [])
      (template.originalSource.applySubstitution template.active) := by
  obtain ⟨_, _, _, _, original, _, _, _, _, _, _, _, _, _, _, _, _, source, principal, _⟩ :=
    prepared_template accepted member
  rw [source]
  exact principal

theorem actual_table_uniqueness (inputs : SourceCoreCallableAncestryPreparation.Inputs base) :
    (inputs.callable.table.entries.map (·.id)).Nodup ∧
    (inputs.callable.table.entries.map (·.origin)).Nodup :=
  ⟨inputs.callable.table.idsUnique, inputs.callable.table.originsUnique⟩
end Prepared

section Boundaries
variable {checked : SourceCoreCompatibleCatalog.Checked} {base : SourceCoreCompatibleFunctions.Prepared checked}
  (inputs : SourceCoreCallableAncestryPreparation.Inputs base) (state : CallableIndexedHistory.MetadataState) (id : Word)

theorem missing_template (missing : inputs.templates.lambdaAt? id = none) :
    SourceCoreCallableAncestryPairedPreparation.lambdaAllowed inputs state id = false := by
  simp [SourceCoreCallableAncestryPairedPreparation.lambdaAllowed, missing]

/-- The guard reads the native context; it does not equate it with the
semantic substitution retained by an applied source view. -/
theorem semantic_active_separate (active : TypeSystem.Substitution) :
    SourceCoreCallableAncestryPairedPreparation.lambdaAllowed inputs
      {state with metadata := {state.metadata with active := active}} id =
    SourceCoreCallableAncestryPairedPreparation.lambdaAllowed inputs state id := rfl

end Boundaries
end Tests.SourceCoreCallableIndexedLambdaTemplatePermission
