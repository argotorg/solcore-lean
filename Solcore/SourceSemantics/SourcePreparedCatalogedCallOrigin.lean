import Solcore.SourceSemantics.SourceCompiledCatalogedCallOrigins
import Solcore.SourceSemantics.SourcePreparedFinalCallEdgeOrigins
import Solcore.SourceSemantics.CoreLowering.CallableOrdinaryMethodCatalogSeparation

/-! Actual cataloged declaration calls retain source ancestry through every
prepared edge origin. Method extensions cannot impersonate ordinary targets. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourcePreparedCatalogedCallOrigin
open Frontend SourceInference TypeSystem SourceSpecializationWorklist
open SourcePreparedPlanGrowth SourcePreparedCallEdgeOrigins
open CoreLowering
open CallableCoercionPreparationSteps (Specialized bind_ok)

private theorem reject_ok {α ε : Type} {condition : Prop} [Decidable condition]
    {action : Except ε α} {error : ε} {value : α}
    (accepted : (if condition then .error error else action) = .ok value) :
    action = .ok value := by
  split at accepted
  · cases accepted
  · exact accepted

/-- The actual specialization constructor uses the checked declaration in its
key. The source owner guard supplies the same declaration. -/
theorem specialization_key_owner {signature : ProgramFunctionSignature}
    {generic : CheckedFunction} {supplied : ParameterSubstitution} {row : Specialized}
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok row) :
    row.key.declaration = row.function.typedBody.owner := by
  have owner := (RecursiveNamedSpecializationBodyFacts.identities accepted).2.1
  unfold SourceSpecialization.specializeFunction at accepted
  iterate 5 have accepted := reject_ok accepted
  iterate 4 obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨canonical, _, accepted⟩ := bind_ok accepted
  iterate 4 obtain ⟨_, _, accepted⟩ := bind_ok accepted
  cases analysis : SourceStageAnalysis.analyzeFunction
      (SourceSpecialization.applyCheckedFunction canonical generic) with
  | error error => simp only [analysis] at accepted; cases accepted
  | ok stages =>
      simp only [analysis, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at accepted
      subst row
      exact owner.symm

/-- All actual method preparation branches retain a method selection, whose
owner is disjoint from the ordinary declaration catalog. -/
theorem selection_key_not_catalog {program : CheckedProgram}
    (catalog : SignatureCatalogWellFormed program.signatures)
    {caller root : Specialized} {node : ExpressionNode}
    {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    (selection : Selection program caller node available root) :
    root.key.declaration ∉ program.signatures.functions.map (·.id) := by
  intro present
  obtain ⟨signature, member, same⟩ := List.mem_map.mp present
  have excluded : ∀ (method : ExecutableImplMethods.CheckedMethod),
      CallableCoercionBodyProvenance.Selection program method →
      method.specialized.key.declaration ≠ signature.id := by
    intro method selected
    rw [specialization_key_owner selected.specialized]
    exact CallableOrdinaryMethodCatalogSeparation.method_owner_ne_function catalog member selected
  cases selection with
  | coercion _ selected _ _ =>
      obtain ⟨receipt⟩ := CallableCoercionSourceSelection.of_accepted selected
      exact excluded _ receipt.selected.toSelection same.symm
  | unary _ _ _ selected _ _ =>
      obtain ⟨_, _, _, _, _, ⟨receipt⟩⟩ := CallablePreparedMethodSelection.unary_of_accepted selected
      exact excluded _ receipt.selected.toSelection same.symm
  | binary _ _ _ selected _ _ =>
      obtain ⟨_, _, _, _, _, ⟨receipt⟩⟩ := CallablePreparedMethodSelection.binary_of_accepted selected
      exact excluded _ receipt.selected.toSelection same.symm

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
theorem source_origin {program : CheckedProgram} {input final : Plan}
    (catalog : SignatureCatalogWellFormed program.signatures)
    (growth : Growth input final) {caller : Specialized}
    (selected : SourceCompilationPlan.exactSpecialization input caller.key = .ok caller)
    {edge : CallEdge} (origin : Origin program input final edge)
    (sameCaller : edge.caller = caller.key)
    (cataloged : edge.callee.declaration ∈ program.signatures.functions.map (·.id)) :
    CallEdge.SourceOrigin program caller.key caller.function.typedBody edge := by
  have finalSelected := growth.rows.selected caller.key caller selected
  cases origin with
  | input _ _ row member source =>
      have same := exact_member_eq finalSelected (growth.rows.entries.subset member)
        (source.caller_eq.symm.trans sameCaller)
      subst row
      exact source
  | outer event _ same =>
      have target : event.root.key.declaration ∈ program.signatures.functions.map (·.id) := by
        simpa only [same, Event.outer] using cataloged
      exact False.elim (selection_key_not_catalog catalog event.selection target)
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

end Solcore.SourceSemantics.SourcePreparedCatalogedCallOrigin
