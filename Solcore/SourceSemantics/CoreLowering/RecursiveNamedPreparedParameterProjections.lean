import Solcore.SourceSemantics.CoreLowering.CallableIndexedPreparedInventories
import Solcore.SourceSemantics.CoreLowering.CompatibleStatementBindingCertificates

/-! Actual named preparation authenticates every ordered binder/native pair.
The source raw type is projected at the original binder prefix. This module does
not identify a different Header binding list from its packed type and does not
supply an invocation dictionary or any source execution law. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedParameterProjections
open Core Frontend SourceInference

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : (action >>= next) = .ok value) :
    ∃ input, action = .ok input ∧ next input = .ok value := by
  cases action with
  | error error => cases accepted
  | ok input => exact ⟨input, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {f : ε → δ} {value : α}
    (accepted : action.mapError f = .ok value) : action = .ok value := by
  cases action <;> cases accepted <;> rfl

/-- The returned function inventory retains the exact ordered preparation pass. -/
theorem catalog_functions {program : CheckedProgram} {plan : SourceCompilationPlan.Plan}
    {checked : SourceCoreCompatibleCatalog.Checked} (ownership : checked.signatures = program.signatures)
    {fuel : Nat} {prepared : SourceCoreCompatibleFunctions.Prepared checked}
    (accepted : SourceCoreCompatibleFunctions.prepareWithCatalog program plan checked ownership fuel = .ok prepared) :
    prepared.plan.specializations.reverse.mapM
      (SourceCoreGeneralFunctions.prepareFunctionWithRepresentation program
        (SourceCoreCompatibleFunctions.representation (.initial checked) fuel)) = .ok prepared.functions := by
  unfold SourceCoreCompatibleFunctions.prepareWithCatalog at accepted
  obtain ⟨executable, _, accepted⟩ := bind_ok accepted
  obtain ⟨locals, _, accepted⟩ := bind_ok accepted
  obtain ⟨contexts, _, accepted⟩ := bind_ok accepted
  obtain ⟨functions, generated, accepted⟩ := bind_ok accepted
  have generated := mapError_ok generated
  cases seeds : executable.val.seedKeys with
  | nil =>
    simp only [seeds, pure, Except.pure] at accepted
    cases accepted
    exact generated
  | cons first rest =>
    simp only [seeds] at accepted
    obtain ⟨diagnostics, _, accepted⟩ := bind_ok accepted
    cases contracts : checked.catalog.callableContracts with
    | false =>
      simp only [contracts, Bool.false_eq_true, ↓reduceIte, pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨closures, _, accepted⟩ := bind_ok accepted
      obtain ⟨inputs, _, accepted⟩ := bind_ok accepted
      obtain ⟨entries, _, accepted⟩ := bind_ok accepted
      cases accepted
      exact generated
    | true =>
      simp only [contracts, ↓reduceIte] at accepted
      obtain ⟨table, _, accepted⟩ := bind_ok accepted
      obtain ⟨nativeDiagnostics, _, accepted⟩ := bind_ok accepted
      try dsimp only [pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨locals, _, accepted⟩ := bind_ok accepted
      obtain ⟨closures, _, accepted⟩ := bind_ok accepted
      obtain ⟨inputs, _, accepted⟩ := bind_ok accepted
      obtain ⟨entries, _, accepted⟩ := bind_ok accepted
      cases accepted
      exact generated

/-- The automatic compatible artifact contains that same preparation pass. -/
theorem automatic_functions {program : CheckedProgram} {plan : SourceCompilationPlan.Plan}
    {fuel : Nat} {limits : SourceCoreRawMetadata.Limits} {automatic : SourceCoreCompatibleFunctions.Automatic}
    (accepted : SourceCoreCompatibleFunctions.prepare program plan fuel limits = .ok automatic) :
    automatic.prepared.plan.specializations.reverse.mapM
      (SourceCoreGeneralFunctions.prepareFunctionWithRepresentation program
        (SourceCoreCompatibleFunctions.representation (.initial automatic.checked) fuel)) =
          .ok automatic.prepared.functions := by
  unfold SourceCoreCompatibleFunctions.prepare at accepted
  obtain ⟨executable, _, accepted⟩ := bind_ok accepted
  obtain ⟨locals, _, accepted⟩ := bind_ok accepted
  try dsimp only at accepted
  split at accepted
  · cases accepted
  · obtain ⟨prepared, preparedAccepted, accepted⟩ := bind_ok accepted
    cases accepted
    exact catalog_functions _ preparedAccepted

private theorem mapM_at {α β ε : Type} {action : α → Except ε β}
    {inputs : List α} {outputs : List β} {index : Nat} {output : β}
    (accepted : inputs.mapM action = .ok outputs) (selected : outputs[index]? = some output) :
    ∃ input, inputs[index]? = some input ∧ action input = .ok output := by
  induction inputs generalizing outputs index with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at accepted
    subst outputs
    simp at selected
  | cons head tail ih =>
    rw [List.mapM_cons] at accepted
    obtain ⟨first, generated, accepted⟩ := bind_ok accepted
    obtain ⟨rest, tailGenerated, accepted⟩ := bind_ok accepted
    cases accepted
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at selected
      subst output
      exact ⟨head, rfl, generated⟩
    | succ index =>
      obtain ⟨input, found, generated⟩ := ih tailGenerated (by simpa using selected)
      exact ⟨input, by simpa using found, generated⟩

/-- A reached cached slot returns the exact full specialization and preparation
receipt; it is not reconstructed from a key or a native signature. -/
theorem cached_preparation (compiled : SourceCoreUnifiedCompilation.Compiled)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named) :
    ∃ specialized, compiled.compatible.prepared.plan.specializations.reverse[index]? = some specialized ∧
      SourceCoreGeneralFunctions.prepareFunctionWithRepresentation compiled.sourceProgram
        (SourceCoreCompatibleFunctions.representation (.initial compiled.compatible.checked) compiled.compilationFuel)
        specialized = .ok named := by
  have generated := automatic_functions compiled.compatiblePrepared
  rw [CallableIndexedPreparedInventories.indexed_base compiled.indexedPrepared] at selected
  exact mapM_at generated selected

/-- Every accepted native input retains its source binder and actual preceding
scope. Repeated types and original binder positions are preserved. -/
theorem cached_inputs (compiled : SourceCoreUnifiedCompilation.Compiled)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named) :
    named.inputs.map Prod.fst = named.specialized.function.typedBody.inputs ∧
      ∀ position binding, named.inputs[position]? = some binding →
        SourceCoreCompatibleDataExpressions.lowerBinder compiled.compatible.checked
          named.specialized.function.typedBody
          ((named.inputs.take position).reverse.map (fun entry => (entry.1.id, entry.2))) binding.1 =
            .ok binding.2 := by
  obtain ⟨specialized, _, accepted⟩ := cached_preparation compiled selected
  obtain ⟨same, binders, preceding⟩ := SourceCoreGeneralFunctions.prepareFunctionWithRepresentation_inputs accepted
  rw [← same] at binders preceding
  exact ⟨binders, preceding⟩

private theorem projected_list {checked : SourceCoreCompatibleCatalog.Checked}
    (inputs : List (TypedBinder × Core.Ty))
    (projected : ∀ binding, binding ∈ inputs → checked.catalog.project binding.1.scheme.body = .ok binding.2) :
    (inputs.map (fun binding => binding.1.scheme.body)).mapM checked.catalog.project = .ok (inputs.map Prod.snd) := by
  induction inputs with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.map_cons, List.mapM_cons]
    rw [projected head (by simp), ih (fun binding member => projected binding (by simp [member]))]
    rfl

/-- The actual named input vector needs no external native projection callback.
This theorem concerns the compiler's own vector, not arbitrary Header bindings. -/
theorem cached_projected (compiled : SourceCoreUnifiedCompilation.Compiled)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named) :
    (named.inputs.map (fun binding => binding.1.scheme.body)).mapM compiled.compatible.checked.catalog.project =
      .ok (named.inputs.map Prod.snd) := by
  apply projected_list
  intro binding member
  obtain ⟨position, found⟩ := List.mem_iff_getElem?.mp member
  exact CompatibleStatementBindings.binder_projected ((cached_inputs compiled selected).2 position binding found)

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedParameterProjections
