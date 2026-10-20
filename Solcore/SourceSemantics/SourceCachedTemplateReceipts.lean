import Solcore.SourceSemantics.SourceCompiledGeneralizedBarrierConnection
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedFinalPlanOrigins

/-! Successful cache construction validates and scans its complete prepared
plan, including ordinary helpers discovered after the initial worklist. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.SourceCachedTemplateReceipts
open Frontend SourceInference TypeSystem SourceSpecializationWorklist
open SourceCompiledLocalFinalization SourcePreparedPlanGrowth SourcePreparedCallEdgeOrigins
open CoreLowering
open CoreLowering.CallableCoercionPreparationSteps (Specialized bind_ok)

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {f : ε → δ} {value : α}
    (accepted : action.mapError f = .ok value) : action = .ok value := by
  cases action <;> cases accepted <;> rfl

private theorem checked_none {duplicate : Option (SourceSpecialization.SpecializationKey × Nat)}
    (accepted : (match duplicate with
      | none => Except.ok ()
      | some (key, count) => Except.error (Error.duplicatePlanSpecializations key count)) = .ok ()) :
    duplicate = none := by
  cases duplicate with
  | none => rfl
  | some value => rcases value with ⟨key, count⟩; cases accepted

private theorem unique_keys {plan : Plan} (accepted : validatePlanSpecializationsUnique plan = .ok ()) :
    (plan.specializations.map (·.key)).Nodup := by
  rcases plan with ⟨seeds, entries, calls, references⟩
  induction entries with
  | nil => exact .nil
  | cons head rest ih =>
    unfold validatePlanSpecializationsUnique at accepted
    have noDuplicate := checked_none accepted
    change (if (rest.filter (fun entry => decide (entry.key = head.key))).isEmpty then _
      else some (head.key, (rest.filter (fun entry => decide (entry.key = head.key))).length + 1)) = none at noDuplicate
    split at noDuplicate
    · have absent : head.key ∉ rest.map (·.key) := by
        have empty : rest.filter (fun entry => decide (entry.key = head.key)) = [] := List.isEmpty_iff.mp ‹_ = true›
        intro member
        obtain ⟨entry, member, same⟩ := List.mem_map.mp member
        have : entry ∈ rest.filter (fun entry => decide (entry.key = head.key)) := List.mem_filter.mpr ⟨member, by simpa only [decide_eq_true_eq] using same⟩
        rw [empty] at this
        cases this
      have tailAccepted : validatePlanSpecializationsUnique ⟨seeds, rest, calls, references⟩ = .ok () := by
        unfold validatePlanSpecializationsUnique
        rw [noDuplicate]
        rfl
      exact List.nodup_cons.mpr ⟨absent, ih tailAccepted⟩
    · cases noDuplicate

private theorem member_filter {entries : List Specialized} {row : Specialized}
    (unique : (entries.map (·.key)).Nodup) (member : row ∈ entries) :
    entries.filter (fun other => decide (other.key = row.key)) = [row] := by
  induction entries with
  | nil => cases member
  | cons first rest ih =>
      obtain ⟨absent, unique⟩ := List.nodup_cons.mp unique
      rcases List.mem_cons.mp member with rfl | member
      · have empty : rest.filter (fun other => decide (other.key = row.key)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro other present matched
          exact absent (List.mem_map.mpr ⟨other, present, of_decide_eq_true matched⟩)
        simp only [List.filter_cons, decide_true, if_true, empty]
      · have different : first.key ≠ row.key := by
          intro same
          exact absent (List.mem_map.mpr ⟨row, member, same.symm⟩)
        simpa only [List.filter_cons, decide_eq_false different, Bool.false_eq_true, if_false] using ih unique member

private theorem metadata_aux {program : CheckedProgram} {budget fuel next : Nat}
    {before after : Plan}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceAux program budget fuel next before = .ok after) :
    ∀ index caller, next ≤ index → after.specializations[index]? = some caller →
      SourceCompilationPlan.validateSpecializationMetadataWith true caller = .ok () := by
  induction fuel generalizing next before after with
  | zero =>
    unfold SourceCompilationPlan.prepareExecutablePlanEvidenceAux at accepted
    split at accepted
    · rename_i ended
      cases accepted
      intro index caller bound found
      have length := List.getElem?_eq_none_iff.mp ended
      have present := (List.getElem?_eq_some_iff.mp found).1
      omega
    · cases accepted
  | succ fuel ih =>
    have growth := (SourcePreparedOpenCallEdges.aux accepted).1
    unfold SourceCompilationPlan.prepareExecutablePlanEvidenceAux at accepted
    split at accepted
    · rename_i ended
      cases accepted
      intro index caller bound found
      have length := List.getElem?_eq_none_iff.mp ended
      have present := (List.getElem?_eq_some_iff.mp found).1
      omega
    · rename_i caller found
      obtain ⟨checked, metadata, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨extended, _scan, remaining⟩ := bind_ok accepted
      intro index actual bound selected
      by_cases current : index = next
      · subst index
        have same := Option.some.inj (selected.symm.trans (growth.at found))
        subst actual
        exact metadata
      · exact ih remaining index actual (by omega) selected

/-- The actual automatic catalog pass checks uniqueness of the same final
plan retained by the completed cache. -/
theorem cached_unique (cached : SourceCoreUnifiedCompilation.Compiled) :
    (cached.indexed.base.plan.specializations.map (·.key)).Nodup := by
  have accepted := cached.compatiblePrepared
  unfold SourceCoreCompatibleFunctions.prepare at accepted
  obtain ⟨executable, executed, accepted⟩ := bind_ok accepted
  obtain ⟨locals, discovered, _accepted⟩ := bind_ok accepted
  have executed := mapError_ok executed
  have same := Except.ok.inj (executed.symm.trans
    (SourceCoreUnifiedPreparationCertificates.compiled_planPrepared cached))
  subst executable
  have discovered := mapError_ok discovered
  unfold SourceCompilationPlan.localLambdaCatalog at discovered
  obtain ⟨checked, checkedEq, _⟩ := bind_ok discovered
  cases checked
  exact unique_keys checkedEq

/-- A real cache position selects the complete source row uniquely in its
final plan, without initial-worklist membership. -/
theorem cached_exact (cached : SourceCoreUnifiedCompilation.Compiled)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (position : cached.indexed.base.functions[index]? = some named) :
    SourceCompilationPlan.exactSpecialization cached.indexed.base.plan named.specialized.key =
      .ok named.specialized := by
  have member := CoreLowering.RecursiveNamedPreparedFinalPlanOrigins.final_member cached position rfl
  have filtered := member_filter (cached_unique cached) member
  simp only [SourceCompilationPlan.exactSpecialization, filtered]

/-- Metadata validation covers every completed cache row. -/
theorem cached_metadata (cached : SourceCoreUnifiedCompilation.Compiled)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (position : cached.indexed.base.functions[index]? = some named) :
    SourceCompilationPlan.validateSpecializationMetadataWith true named.specialized = .ok () := by
  have accepted := SourceCoreUnifiedPreparationCertificates.compiled_planPrepared cached
  unfold SourceCompilationPlan.prepareExecutablePlanEvidence
    SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget at accepted
  obtain ⟨scanned, inspected, accepted⟩ := bind_ok accepted
  obtain ⟨checked, _canonical, returned⟩ := bind_ok accepted
  cases checked
  cases returned
  obtain ⟨slot, found⟩ := List.mem_iff_getElem?.mp
    (CoreLowering.RecursiveNamedPreparedFinalPlanOrigins.final_member cached position rfl)
  exact metadata_aux inspected slot named.specialized (Nat.zero_le _) found

private theorem exact_member_eq {plan : Plan} {key : SourceSpecialization.SpecializationKey}
    {selected other : Specialized}
    (accepted : SourceCompilationPlan.exactSpecialization plan key = .ok selected)
    (member : other ∈ plan.specializations) (same : other.key = key) : other = selected := by
  unfold SourceCompilationPlan.exactSpecialization at accepted
  split at accepted <;> try contradiction
  cases accepted
  rename_i found
  have present : other ∈ plan.specializations.filter (fun row => decide (row.key = key)) :=
    List.mem_filter.mpr ⟨member, by simpa only [decide_eq_true_eq] using same⟩
  rw [found] at present
  exact List.mem_singleton.mp present

private theorem exact_member {plan : Plan} {key : SourceSpecialization.SpecializationKey}
    {selected : Specialized}
    (accepted : SourceCompilationPlan.exactSpecialization plan key = .ok selected) :
    selected ∈ plan.specializations := by
  unfold SourceCompilationPlan.exactSpecialization at accepted
  split at accepted <;> try contradiction
  cases accepted
  rename_i found
  have present : selected ∈ plan.specializations.filter (fun row => decide (row.key = key)) := by
    rw [found]
    exact List.mem_cons_self
  exact (List.mem_filter.mp present).1

/-- Every real ancestry branch for a cataloged call is source-emitted by the
same complete selected row. Synthetic outer edges are eliminated by the
actual method/ordinary catalog separation. -/
theorem final_source_origin {program : CheckedProgram} {input final : Plan}
    (catalog : SignatureCatalogWellFormed program.signatures)
    (growth : Growth input final) {caller : Specialized}
    (selected : SourceCompilationPlan.exactSpecialization final caller.key = .ok caller)
    {edge : CallEdge} (origin : Origin program input final edge)
    (sameCaller : edge.caller = caller.key)
    (cataloged : edge.callee.declaration ∈ program.signatures.functions.map (·.id)) :
    CallEdge.SourceOrigin program caller.key caller.function.typedBody edge := by
  have finalSelected := selected
  cases origin with
  | input _ _ row member source =>
      have same := exact_member_eq finalSelected (growth.rows.entries.subset member)
        (source.caller_eq.symm.trans sameCaller)
      subst row
      exact source
  | outer event _ same =>
      have target : event.root.key.declaration ∈ program.signatures.functions.map (·.id) := by
        simpa only [same, Event.outer] using cataloged
      exact False.elim (SourcePreparedCatalogedCallOrigin.selection_key_not_catalog catalog event.selection target)
  | suppliedRoot event later source =>
      have root := CallableCoercionPlanProvenance.complete_root event.extended
      have member := exact_member root
      have same := exact_member_eq finalSelected (later.rows.entries.subset member)
        (source.caller_eq.symm.trans sameCaller)
      rw [same] at source
      exact source
  | ordinary event later row member source =>
      have same := exact_member_eq finalSelected (later.rows.entries.subset member)
        (source.caller_eq.symm.trans sameCaller)
      subst row
      exact source


/-- Open cataloged calls in real cached rows retain their complete original
owner, including rows discovered after the input worklist. -/
theorem cached_open_call_owner {raw : Workspace.RawWorkspace} {fuel : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreUnifiedCompilation.Compiled}
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (position : cached.indexed.base.functions[index]? = some named)
    (selected : Selected compiled named.specialized fuel)
    {node : ExpressionNode} (present : .expression node ∈ named.specialized.function.typedBody.nodes)
    {callee : ExpressionId} {arguments : List ExpressionId} {instantiation : DeclarationInstantiation}
    (form : node.form = .call callee arguments (.declaration instantiation))
    (cataloged : instantiation.declaration ∈ compiled.program.signatures.functions.map (·.id))
    (opened : SourcePreparedOpenCallEdges.InstantiationClosed instantiation = false) :
    Nonempty (SourceCompiledTemplateCallOwner.PreparedContextual compiled named.specialized node instantiation) := by
  obtain ⟨programEq, planEq, _⟩ := compiled.artifact_fields artifact
  have prepared := SourceCoreUnifiedPreparationCertificates.compiled_planPrepared cached
  rw [programEq, planEq] at prepared
  obtain ⟨growth, covered⟩ := SourcePreparedOpenCallEdges.of_default_preparation prepared
  have member := RecursiveNamedPreparedFinalPlanOrigins.final_member cached position rfl
  obtain ⟨edge⟩ := covered named.specialized member node present callee arguments instantiation form opened
  have origin := SourcePreparedFinalCallEdgeOrigins.of_default_preparation prepared
    edge.edge (edge.retained edge.present)
  have source := final_source_origin (SignatureCatalogWellFormed.ofCheckProgram checked) growth
    (cached_exact cached position) origin edge.callerEq (edge.declarationEq.symm ▸ cataloged)
  obtain ⟨contextual⟩ := SourcePreparedOpenCallOwner.contextual_of_open
    (SourceCompiledTemplateCallOwner.selected_unique selected) present form opened source edge.occurrenceEq
  obtain ⟨bodyNodes, bodyAccepted, nodeInBody, templates⟩ :=
    contextual.body (SourceCompiledTemplateCallOwner.selected_unique selected) present
  exact ⟨⟨cached.indexed.base.plan, prepared, edge, contextual,
    bodyNodes, bodyAccepted, nodeInBody, templates⟩⟩

end Solcore.SourceSemantics.SourceCachedTemplateReceipts
