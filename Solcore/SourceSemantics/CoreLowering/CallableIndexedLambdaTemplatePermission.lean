import Solcore.SourceSemantics.CoreLowering.CallableAppliedViewProvenance
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaValues
import Solcore.SourceSemantics.CoreLowering.CallableSpecializationEquality

/-! Template permission follows the actual compiler hook and the actual
prepared inventory. Source and native active substitutions remain distinct;
no call entry or body execution is asserted here. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaTemplatePermission
open Core Frontend SourceInference CallableIndexedLambdaValues
open CallableAppliedViewProvenance

private theorem find_unique_key {α β : Type} [DecidableEq β] (items : List α) (key : α → β)
    (unique : (items.map key).Nodup) {item : α} (member : item ∈ items) :
    items.find? (fun candidate => decide (key candidate = key item)) = some item := by
  induction items with
  | nil => cases member
  | cons head tail ih =>
    simp only [List.map_cons, List.nodup_cons] at unique
    rcases List.mem_cons.mp member with same | member
    · subst item; simp
    · have different : key head ≠ key item := by
        intro same
        exact unique.1 (List.mem_map.mpr ⟨item, member, same.symm⟩)
      simpa [List.find?_cons, different] using ih unique.2 member

private theorem type_beq (left right : Core.Ty) : (left == right) = true ↔ left = right := by
  induction left generalizing right <;> cases right <;>
    simp_all [BEq.beq, Core.instBEqTy.beq, Core.instBEqDataTypeId.beq]
  rename_i left right
  cases left; cases right; simp_all

/-- The successful raw hook retains its actual first selected template and
all checked native header fields. -/
theorem hook_template {checked : SourceCoreCompatibleCatalog.Checked}
    {inventory : SourceCoreLambdaTemplates.Inventory checked}
    {owner : SourceCompilationPlan.Key} {active : TypeSystem.Substitution}
    {compilation : SourceCoreFunctions.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {node : ExpressionNode}
    {parameter result : Core.Ty} {body emitted : Expr}
    (accepted : SourceCoreLambdaTemplates.hook inventory owner active compilation source scope
      node parameter result body = .ok emitted) :
    ∃ template, inventory.lambdas.find? (fun candidate => decide
        (candidate.owner = owner ∧ candidate.id = node.id ∧ candidate.active = active)) = some template ∧
      node.form = template.node.form ∧ parameter = template.parameterType ∧ result = template.resultType := by
  unfold SourceCoreLambdaTemplates.hook at accepted
  split at accepted
  · next template found =>
    simp only [bind, Except.bind, pure, Except.pure] at accepted
    split at accepted
    · cases accepted
    · split at accepted
      · cases accepted
      · next shape =>
        have shape : node.form = template.node.form ∧ parameter = template.parameterType ∧
            result = template.resultType := by
          have checks : node.form = template.node.form ∧
              (parameter == template.parameterType) = true ∧ (result == template.resultType) = true := by
            simpa [bne, and_assoc] using shape
          exact ⟨checks.1, (type_beq _ _).mp checks.2.1, (type_beq _ _).mp checks.2.2⟩
        exact ⟨template, found, shape⟩
  · cases accepted

/-- Prepared templates refer to actual rows in the same selected table. -/
theorem prepared_entry {checked : SourceCoreCompatibleCatalog.Checked}
    {base : SourceCoreCompatibleFunctions.Prepared checked}
    (inputs : SourceCoreCallableAncestryPreparation.Inputs base)
    {template : SourceCoreLambdaTemplates.Lambda} (authentic : PreparedTemplate base template) :
    ∃ entry, entry ∈ inputs.callable.table.entries ∧
      entry.origin = .lambda template.owner template.id template.active ∧
      entry.id = template.descriptor := by
  obtain ⟨_, _, callable, entry, _, _, _, _, _, _, selected, member, origin, id, _⟩ := authentic
  cases Option.some.inj (selected.symm.trans inputs.callableSelected)
  exact ⟨entry, member, origin, id⟩

/-- Equal actual lookup keys select the same full node in the prepared source. -/
theorem prepared_node {checked : SourceCoreCompatibleCatalog.Checked}
    {base : SourceCoreCompatibleFunctions.Prepared checked}
    {left right : SourceCoreLambdaTemplates.Lambda}
    (leftPrepared : PreparedTemplate base left) (rightPrepared : PreparedTemplate base right)
    (owner : left.owner = right.owner) (id : left.id = right.id)
    (active : left.active = right.active) : left.node = right.node := by
  obtain ⟨receipts, metadata, _, _, _, _, _, _, receiptsAccepted, metadataAccepted,
    _, _, _, _, contextFound, _, _, _, _, nodeFound, _⟩ := leftPrepared
  obtain ⟨otherReceipts, otherMetadata, _, _, _, _, _, _, otherReceiptsAccepted,
    otherMetadataAccepted, _, _, _, _, otherContextFound, _, _, _, _, otherNodeFound, _⟩ := rightPrepared
  cases Except.ok.inj (receiptsAccepted.symm.trans otherReceiptsAccepted)
  cases Except.ok.inj (metadataAccepted.symm.trans otherMetadataAccepted)
  rw [owner, active] at contextFound
  have contexts := Option.some.inj (contextFound.symm.trans otherContextFound)
  rw [contexts, id] at nodeFound
  exact Option.some.inj (nodeFound.symm.trans otherNodeFound)

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}

/-- The actual code and inventory determine the same descriptor, full source
node, ordered lambda parameters and native header. -/
theorem selected (code : Code prepared function scope administrative) :
    ∃ template, prepared.ancestry.graph.inputs.templates.lambdaAt? code.descriptor.id = some template ∧
      PreparedTemplate prepared.base template ∧
      template.owner = code.compilation.owner ∧ template.id = code.id ∧ template.active = code.active ∧
      template.node.form = .lambda function.parameters function.resultType function.body := by
  have hook := code.receipt.bodyHook
  rw [code.manifest] at hook
  obtain ⟨hookTemplate, hookFound, hookForm, _, _⟩ := hook_template hook
  have hookKeys : hookTemplate.owner = code.compilation.owner ∧ hookTemplate.id = code.node.id ∧ hookTemplate.active = code.active := by
    simpa using List.find?_some hookFound
  have hookPrepared := prepared_template prepared.ancestry.graph.inputs.templatesPrepared
    (List.mem_of_find?_eq_some hookFound)
  obtain ⟨entry, entryMember, entryOrigin, entryId⟩ :=
    prepared_entry prepared.ancestry.graph.inputs hookPrepared
  have nodeId := (lookupExpression?_sound code.found).2
  have origin : entry.origin = .lambda code.compilation.owner code.id code.active := by
    rw [entryOrigin, hookKeys.1, hookKeys.2.1, nodeId, hookKeys.2.2]
  have idAt := code.descriptor.found
  unfold SourceCoreStageCodebook.Table.idAt? at idAt
  have entryFound := find_unique_key _ _ prepared.ancestry.graph.inputs.callable.table.originsUnique entryMember
  simp only [origin] at entryFound
  rw [entryFound] at idAt
  have descriptor : hookTemplate.descriptor = code.descriptor.id := entryId.symm.trans (Option.some.inj idAt)
  cases found : prepared.ancestry.graph.inputs.templates.lambdaAt? code.descriptor.id with
  | none =>
    have rejected := List.find?_eq_none.mp found hookTemplate (List.mem_of_find?_eq_some hookFound)
    simp [descriptor] at rejected
  | some template =>
    have authentic := prepared_template prepared.ancestry.graph.inputs.templatesPrepared
      (List.mem_of_find?_eq_some found)
    have templateId : template.descriptor = code.descriptor.id := by simpa using List.find?_some found
    obtain ⟨other, otherMember, otherOrigin, otherId⟩ :=
      prepared_entry prepared.ancestry.graph.inputs authentic
    have leftLookup := CallableAncestryPairedValidation.stage_entry_self _ entryMember
    have rightLookup := CallableAncestryPairedValidation.stage_entry_self _ otherMember
    simp only [entryId, descriptor, otherId, templateId] at leftLookup rightLookup
    have same := Option.some.inj (leftLookup.symm.trans rightLookup)
    have origins := SourceCoreStageCodebook.Origin.lambda.inj (otherOrigin.symm.trans (same ▸ origin))
    have nodeSame := prepared_node authentic hookPrepared
      (origins.1.trans hookKeys.1.symm)
      (origins.2.1.trans (hookKeys.2.1.trans nodeId).symm)
      (origins.2.2.trans hookKeys.2.2.symm)
    refine ⟨template, rfl, authentic, origins.1, origins.2.1, origins.2.2, ?_⟩
    exact congrArg ExpressionNode.form nodeSame |>.trans (hookForm.symm.trans (code.form.trans code.sourceForm))

/-- Permission is checked in the exact source and native-active history
retained by this actual code. -/
theorem lambda_allowed (code : Code prepared function scope administrative) (history : History code) :
    SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs
      history.metadata code.descriptor.id = true := by
  obtain ⟨template, found, authentic, owner, id, active, form⟩ := selected code
  obtain ⟨entry, member, origin, descriptor⟩ := prepared_entry prepared.ancestry.graph.inputs authentic
  have selectedId : template.descriptor = code.descriptor.id := by simpa using List.find?_some found
  have entryFound := CallableAncestryPairedValidation.stage_entry_self _ member
  rw [descriptor, selectedId] at entryFound
  have sourceFound := code.sourceFound
  rw [← history.source, ← id] at sourceFound
  simp [SourceCoreCallableAncestryPairedPreparation.lambdaAllowed, found, entryFound, origin,
    history.owner, owner, history.active, active, sourceFound, code.sourceForm, form]

/-- The actual permission discharges ordinary dispatch from any separately
carried stable caller. The caller need not share the lexical physical frame. -/
theorem ordinary_history (code : Code prepared function scope administrative) (history : History code)
    {currentNative : CallableIndexedHistory.NativeFrame} {currentGhost : CallableIndexedHistory.GhostFrame}
    {current : Option CallableIndexedHistory.MetadataState}
    (carried : CallableIndexedHistory.Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table
      currentNative currentGhost current) :
    CallableIndexedHistory.Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table
      (SourceCoreCallableIndexedDispatch.selectedFrame prepared.ancestry.graph.table code.descriptor.id
        history.native currentNative)
      (.lambda code.descriptor.id history.ghost) (some history.metadata) :=
  CallableIndexedHistory.ordinary_complete prepared.ancestry.graph history.carried carried
    (lambda_allowed code history)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaTemplatePermission
