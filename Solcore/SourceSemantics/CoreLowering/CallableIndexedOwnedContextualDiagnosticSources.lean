import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDiagnosticReceipts
import Solcore.Frontend.SourceRuntimeHeapTyping

/-! Genuine contextual diagnostic sources retain the selected specialization
and its actual substitution. These finite factory receipts change no compiler
or diagnostic preparation behavior. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualDiagnosticSources
open Core Frontend SourceInference
abbrev Key := SourceSpecialization.SpecializationKey
abbrev Plan := SourceSpecializationWorklist.Plan

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β}
    {value : β} (accepted : action >>= next = .ok value) :
    ∃ intermediate, action = .ok intermediate ∧ next intermediate = .ok value := by
  cases action with
  | error error => cases accepted
  | ok intermediate => exact ⟨intermediate, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {f : ε → δ} {value : α}
    (accepted : action.mapError f = .ok value) : action = .ok value := by
  cases action <;> cases accepted <;> rfl

/-- The full-key selector accepts exactly its one retained original row. -/
theorem selected_filter {plan : Plan} {key : Key} {row : SourceSpecialization.SpecializedFunction}
    (accepted : SourceCompilationPlan.exactSpecialization plan key = .ok row) :
    plan.specializations.filter (fun actual => decide (actual.key = key)) = [row] := by
  unfold SourceCompilationPlan.exactSpecialization at accepted
  split at accepted
  · cases accepted
  · cases accepted
    assumption
  · cases accepted

theorem selected_key {plan : Plan} {key : Key} {row : SourceSpecialization.SpecializedFunction}
    (accepted : SourceCompilationPlan.exactSpecialization plan key = .ok row) : row.key = key := by
  have occurs : row ∈ plan.specializations.filter (fun actual => decide (actual.key = key)) := by
    rw [selected_filter accepted]
    exact List.mem_singleton_self _
  exact of_decide_eq_true (List.mem_filter.mp occurs).2

theorem selected_member_eq {plan : Plan} {key : Key} {row actual : SourceSpecialization.SpecializedFunction}
    (accepted : SourceCompilationPlan.exactSpecialization plan key = .ok row)
    (member : actual ∈ plan.specializations) (same : actual.key = key) : actual = row := by
  have occurs : actual ∈ plan.specializations.filter (fun actual => decide (actual.key = key)) :=
    List.mem_filter.mpr ⟨member, by simp only [same, decide_true]⟩
  rw [selected_filter accepted] at occurs
  exact List.mem_singleton.mp occurs

private theorem exact_caller_source {plan : Plan} {binding : SourceCoreLocalEvidence.Binding}
    {caller : SourceSpecialization.SpecializedFunction}
    (accepted : SourceCoreLocalEvidence.exactCaller plan binding = .ok caller) :
    SourceCompilationPlan.exactSpecialization plan binding.caller = .ok caller ∧
      caller.function.typedBody = binding.source := by
  unfold SourceCoreLocalEvidence.exactCaller at accepted
  obtain ⟨row, made, accepted⟩ := bind_ok accepted
  split at accepted
  · cases accepted
  · rename_i same
    dsimp only at accepted
    split at accepted
    · simp only [pure, Except.pure] at accepted
      cases accepted
      exact ⟨mapError_ok made, Classical.not_not.mp same⟩
    · cases accepted

/-- One accepted local factory retains the exact selected Source and active
substitution, including the original authenticated instance and full key. -/
theorem contextual_source_at {program : CheckedProgram} {plan : Plan}
    {candidate : SourceCoreLocalEvidence.Instance} {parent : Option SourceCoreLocalEvidence.Prepared}
    {item : SourceCoreLocalEvidence.Prepared}
    (accepted : SourceCoreLocalEvidence.prepare program plan candidate parent = .ok item) :
    ∃ row, SourceCompilationPlan.exactSpecialization plan item.caller.key = .ok row ∧
      item.source = row.function.typedBody.applySubstitution item.substitution ∧
      item.instance = candidate ∧ candidate.origin.source = row.function.typedBody ∧
      item.caller.key = candidate.origin.caller := by
  unfold SourceCoreLocalEvidence.prepare at accepted
  obtain ⟨caller, made, accepted⟩ := bind_ok accepted
  have facts := exact_caller_source made
  split at accepted
  · cases accepted
  · obtain ⟨discovered, _, accepted⟩ := bind_ok accepted
    dsimp only at accepted
    split at accepted
    · obtain ⟨pair, _, accepted⟩ := bind_ok accepted
      obtain ⟨active, inherited⟩ := pair
      dsimp only at accepted
      split at accepted
      · simp only [pure, Except.pure, bind, Except.bind] at accepted
        obtain ⟨reference, _, accepted⟩ := bind_ok accepted
        split at accepted
        · cases accepted
        · obtain ⟨valid, _, accepted⟩ := bind_ok accepted
          cases accepted
          have key := selected_key facts.1
          exact ⟨caller, by simpa only [SourceCoreLocalEvidence.contextualCaller, key] using facts.1,
            rfl, rfl, facts.2.symm, key⟩
      · cases accepted
    · cases accepted

/-- Every authentic returned same-key context uses that same original row. -/
theorem context_source_at_key {program : CheckedProgram} {plan : Plan}
    {candidates : List SourceCoreLocalEvidence.Instance} {contexts : List SourceCoreLocalEvidence.Prepared}
    {key : Key} {row : SourceSpecialization.SpecializedFunction} {item : SourceCoreLocalEvidence.Prepared}
    (accepted : SourceCoreStageCodebook.prepareContexts program plan candidates = .ok contexts)
    (record : SourceCompilationPlan.exactSpecialization plan key = .ok row)
    (member : item ∈ contexts) (same : item.caller.key = key) :
    item.source = row.function.typedBody.applySubstitution item.substitution := by
  obtain ⟨candidate, parent, made⟩ := SourceCoreStageCodebook.prepareContexts_authentic accepted member
  obtain ⟨original, selected, view, _, _, _⟩ := contextual_source_at made
  rw [same, record] at selected
  cases selected
  exact view

/-- The diagnostic pass receives exactly these authentic contextual sources.
The original local catalog is retained separately from its later callable rewrite. -/
structure FactoryAt {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared checked)
    (diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked)) : Prop where
  actual : ∃ locals0 : SourceCoreLocalPolymorphism.Catalog, ∃ root remaining,
    prepared.plan.seedKeys = root :: remaining ∧
    SourceCoreStageCodebook.prepareContexts prepared.sourceProgram prepared.plan
      (locals0.bindings.flatMap (·.instances)) = .ok prepared.contexts ∧
    SourceCoreCompatibleDataPlaceFaultSites.prepare (.initial checked) prepared.plan root
      (prepared.contexts.map (fun item => (item.caller.key, item.source))) = .ok diagnostics

theorem of_catalog {program : CheckedProgram} {plan : Plan}
    {checked : SourceCoreCompatibleCatalog.Checked} {ownership : checked.signatures = program.signatures}
    {fuel : Nat} {prepared : SourceCoreCompatibleFunctions.Prepared checked}
    {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked)}
    (accepted : SourceCoreCompatibleFunctions.prepareWithCatalog program plan checked ownership fuel = .ok prepared)
    (found : prepared.diagnostics = some diagnostics) : FactoryAt prepared diagnostics := by
  unfold SourceCoreCompatibleFunctions.prepareWithCatalog at accepted
  obtain ⟨executable, _, accepted⟩ := bind_ok accepted
  obtain ⟨locals0, _, accepted⟩ := bind_ok accepted
  obtain ⟨contexts, contextsMade, accepted⟩ := bind_ok accepted
  obtain ⟨functions, _, accepted⟩ := bind_ok accepted
  split at accepted
  · cases accepted
    cases found
  · rename_i root remaining roots
    obtain ⟨actual, actualMade, accepted⟩ := bind_ok accepted
    split at accepted
    · obtain ⟨table, _, accepted⟩ := bind_ok accepted
      obtain ⟨callableDiagnostics, _, accepted⟩ := bind_ok accepted
      simp only [pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨locals, _, accepted⟩ := bind_ok accepted
      obtain ⟨closures, _, accepted⟩ := bind_ok accepted
      obtain ⟨sourceInputs, _, accepted⟩ := bind_ok accepted
      obtain ⟨entries, _, accepted⟩ := bind_ok accepted
      cases accepted
      cases found
      exact ⟨⟨locals0, root, remaining, roots, mapError_ok contextsMade, mapError_ok actualMade⟩⟩
    · simp only [pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨closures, _, accepted⟩ := bind_ok accepted
      obtain ⟨sourceInputs, _, accepted⟩ := bind_ok accepted
      obtain ⟨entries, _, accepted⟩ := bind_ok accepted
      cases accepted
      cases found
      exact ⟨⟨locals0, root, remaining, roots, mapError_ok contextsMade, mapError_ok actualMade⟩⟩

theorem of_automatic {program : CheckedProgram} {plan : Plan} {fuel : Nat}
    {automatic : SourceCoreCompatibleFunctions.Automatic}
    {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial automatic.checked)}
    (accepted : SourceCoreCompatibleFunctions.prepare program plan fuel = .ok automatic)
    (found : automatic.prepared.diagnostics = some diagnostics) : FactoryAt automatic.prepared diagnostics := by
  unfold SourceCoreCompatibleFunctions.prepare at accepted
  obtain ⟨executable, _, accepted⟩ := bind_ok accepted
  obtain ⟨locals, _, accepted⟩ := bind_ok accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  · obtain ⟨base, baseMade, accepted⟩ := bind_ok accepted
    cases accepted
    exact of_catalog baseMade found

/-- Sealed compilation retains the same actual contextual source list and issuer. -/
theorem of_compiled (compiled : SourceCoreUnifiedCompilation.Compiled)
    {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (found : compiled.indexed.base.diagnostics = some diagnostics) :
    FactoryAt compiled.indexed.base diagnostics := by
  rw [SourceCoreUnifiedPreparationCertificates.indexed_base compiled.indexedPrepared] at found ⊢
  exact of_automatic compiled.compatiblePrepared found

def SourceView (original actual : TypedSource) : Prop :=
  actual = original ∨ ∃ active, actual = original.applySubstitution active

def QuerySourceViews (key : Key) (original : TypedSource) (sources : List (Key × TypedSource)) : Prop :=
  ∀ owner actual, (owner, actual) ∈ sources → owner = key → SourceView original actual

/-- Full-key singleton selection authenticates original rows and every returned
contextual row in the exact ordered source inventory. -/
theorem source_views_of_contexts {program : CheckedProgram} {plan : Plan}
    {candidates : List SourceCoreLocalEvidence.Instance} {contexts : List SourceCoreLocalEvidence.Prepared}
    {key : Key} {row : SourceSpecialization.SpecializedFunction}
    (accepted : SourceCoreStageCodebook.prepareContexts program plan candidates = .ok contexts)
    (record : SourceCompilationPlan.exactSpecialization plan key = .ok row) :
    QuerySourceViews key row.function.typedBody
      (plan.specializations.map (fun actual => (actual.key, actual.function.typedBody)) ++
        contexts.map (fun item => (item.caller.key, item.source))) := by
  intro owner actual member same
  rcases List.mem_append.mp member with original | contextual
  · obtain ⟨selected, selectedMember, pair⟩ := List.mem_map.mp original
    cases pair
    have equal := selected_member_eq record selectedMember same
    subst selected
    exact Or.inl rfl
  · obtain ⟨item, itemMember, pair⟩ := List.mem_map.mp contextual
    cases pair
    exact Or.inr ⟨item.substitution, context_source_at_key accepted record itemMember same⟩

theorem FactoryAt.source_views {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCompatibleFunctions.Prepared checked}
    {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked)}
    (factory : FactoryAt prepared diagnostics) {key : Key} {row : SourceSpecialization.SpecializedFunction}
    (record : SourceCompilationPlan.exactSpecialization prepared.plan key = .ok row) :
    QuerySourceViews key row.function.typedBody
      (prepared.plan.specializations.map (fun actual => (actual.key, actual.function.typedBody)) ++
        prepared.contexts.map (fun item => (item.caller.key, item.source))) := by
  obtain ⟨locals0, root, remaining, _, contextsMade, _⟩ := factory.actual
  exact source_views_of_contexts contextsMade record

theorem substituted_span (active : TypeSystem.Substitution) (node : ExpressionNode) :
    (node.applySubstitution active).span = node.span := rfl

theorem substituted_index_iff (active : TypeSystem.Substitution) (node : ExpressionNode)
    (base key : ExpressionId) :
    (node.applySubstitution active).form = .index base key ↔ node.form = .index base key := by
  cases form : node.form <;> simp [ExpressionNode.applySubstitution, ExpressionForm.applySubstitution, form]

theorem substituted_local_iff (active : TypeSystem.Substitution) (node : ExpressionNode)
    (name : String) (binder : Resolved.LocalId) :
    (node.applySubstitution active).form = .reference name (.local binder) ↔
      node.form = .reference name (.local binder) := by
  cases form : node.form <;> simp [ExpressionNode.applySubstitution, ExpressionForm.applySubstitution, form]
  case reference reference resolution =>
    cases resolution <;> simp [ReferenceResolution.applySubstitution]

/-- An actual substituted member comes from that same original expression
occurrence. No uniqueness or type equality is inferred here. -/
theorem substituted_contains {original : TypedSource} {active : TypeSystem.Substitution}
    {id : ExpressionId} {node : ExpressionNode}
    (contains : SourceSemantics.ContainsExpression (original.applySubstitution active) id node) :
    ∃ before, SourceSemantics.ContainsExpression original id before ∧ node = before.applySubstitution active := by
  obtain ⟨retained, member, same⟩ := List.mem_map.mp contains.1
  cases retained with
  | expression before =>
    cases same
    exact ⟨before, ⟨member, contains.2⟩, rfl⟩
  | statement before => cases same

theorem SourceView.local_origin {original actual : TypedSource} (view : SourceView original actual)
    {id : ExpressionId} {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    (contains : SourceSemantics.ContainsExpression actual id node)
    (form : node.form = .reference name (.local binder)) :
    ∃ before, SourceSemantics.ContainsExpression original id before ∧
      before.form = .reference name (.local binder) ∧ node.span = before.span := by
  rcases view with same | ⟨active, same⟩
  · subst actual
    exact ⟨node, contains, form, rfl⟩
  · subst actual
    obtain ⟨before, retained, same⟩ := substituted_contains contains
    subst node
    exact ⟨before, retained, (substituted_local_iff active before name binder).mp form, rfl⟩

theorem SourceView.index_origin {original actual : TypedSource} (view : SourceView original actual)
    {id : ExpressionId} {node : ExpressionNode} {base key : ExpressionId}
    (contains : SourceSemantics.ContainsExpression actual id node) (form : node.form = .index base key) :
    ∃ before, SourceSemantics.ContainsExpression original id before ∧
      before.form = .index base key ∧ node.span = before.span := by
  rcases view with same | ⟨active, same⟩
  · subst actual
    exact ⟨node, contains, form, rfl⟩
  · subst actual
    obtain ⟨before, retained, same⟩ := substituted_contains contains
    subst node
    exact ⟨before, retained, (substituted_index_iff active before base key).mp form, rfl⟩

/-- An authentic substituted index cannot shadow a canonical local read at
the same unique occurrence. The loop's actual issuer is still required. -/
theorem SourceView.no_index_at_read {original actual : TypedSource} (view : SourceView original actual)
    (unique : SourceSemantics.NodeOccurrencesUnique original)
    {id : ExpressionId} {read node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    {base key : ExpressionId}
    (readContains : SourceSemantics.ContainsExpression original id read)
    (readForm : read.form = .reference name (.local binder))
    (indexContains : SourceSemantics.ContainsExpression actual id node)
    (indexForm : node.form = .index base key) : False := by
  obtain ⟨before, retained, form, _⟩ := view.index_origin indexContains indexForm
  have same : before = read := Option.some.inj
    ((SourceSemantics.lookupExpression?_complete unique retained).symm.trans
      (SourceSemantics.lookupExpression?_complete unique readContains))
  subst before
  rw [readForm] at form
  cases form

theorem SourceView.index_span_at {original actual : TypedSource} (view : SourceView original actual)
    (unique : SourceSemantics.NodeOccurrencesUnique original)
    {id : ExpressionId} {before node : ExpressionNode} {base key : ExpressionId}
    (canonical : SourceSemantics.ContainsExpression original id before)
    (contains : SourceSemantics.ContainsExpression actual id node) (form : node.form = .index base key) :
    before.form = .index base key ∧ node.span = before.span := by
  obtain ⟨selected, retained, selectedForm, span⟩ := view.index_origin contains form
  have same : selected = before := Option.some.inj
    ((SourceSemantics.lookupExpression?_complete unique retained).symm.trans
      (SourceSemantics.lookupExpression?_complete unique canonical))
  subst selected
  exact ⟨selectedForm, span⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualDiagnosticSources
