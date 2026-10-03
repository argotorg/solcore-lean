import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogInitialization
import Solcore.SourceSemantics.CoreLowering.CallableIndexedPreparedInventories

/-! Every row of the actual second-pass cache is extracted with its full
lambda code and ordered signature. Successful compilation fixes both list
length and slot correspondence. No runtime typing, decoder, source execution
or function-body meaning is used to identify a cached row. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedCachedRows
open Core Frontend SourceInference RecursiveGlobalInitializationMeaning

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : action >>= next = .ok value) :
    ∃ item, action = .ok item ∧ next item = .ok value := by
  cases action with
  | error error => cases accepted
  | ok item => exact ⟨item, rfl, accepted⟩

private theorem mapM_length {α β ε : Type} {action : α → Except ε β}
    {inputs : List α} {outputs : List β} (accepted : inputs.mapM action = .ok outputs) :
    outputs.length = inputs.length := by
  induction inputs generalizing outputs with
  | nil => simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at accepted; subst outputs; rfl
  | cons head tail ih =>
    rw [List.mapM_cons] at accepted
    obtain ⟨first, _, accepted⟩ := bind_ok accepted
    obtain ⟨rest, acceptedRest, accepted⟩ := bind_ok accepted
    cases accepted
    simp only [List.length_cons, ih acceptedRest]

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {f : ε → δ} {value : α}
    (accepted : action.mapError f = .ok value) : action = .ok value := by
  cases action <;> cases accepted <;> rfl

theorem compilation_length {checked : SourceCoreCompatibleCatalog.Checked}
    {base : SourceCoreCompatibleFunctions.Prepared checked}
    {representation : SourceCoreGeneralFunctions.Representation} {fuel : Nat}
    (compiled : SourceCoreCompatibleMarkedFunctions.Compilation base representation fuel) :
    compiled.closures.length = base.functions.length := by
  have accepted := compiled.compiled
  unfold SourceCoreCompatibleMarkedFunctions.compileClosures at accepted
  by_cases empty : base.functions.isEmpty = true
  · simp only [empty, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at accepted
    rw [← accepted, List.isEmpty_iff.mp empty]
    rfl
  · simp only [empty, Bool.false_eq_true, ↓reduceIte] at accepted
    cases diagnostics : base.diagnostics with
    | none => simp [diagnostics, bind, Except.bind, throw] at accepted
    | some diagnostics =>
      simp only [diagnostics, bind, Except.bind, pure, Except.pure] at accepted
      exact mapM_length (mapError_ok accepted)

def row : Expr → LambdaRow
  | .lambda parameter result body => ⟨parameter, result, body⟩
  | _ => ⟨.unit, .unit, .unit⟩

def rows (compiled : SourceCoreUnifiedCompilation.Compiled) : List LambdaRow :=
  compiled.indexed.secondPass.closures.map row

theorem cached_length (compiled : SourceCoreUnifiedCompilation.Compiled) :
    compiled.indexed.secondPass.closures.length = compiled.indexed.base.functions.length :=
  compilation_length compiled.indexed.secondPass

/-- An actual cached slot identifies the corresponding full named compilation
receipt, including its original lambda body. -/
theorem cached_at (compiled : SourceCoreUnifiedCompilation.Compiled)
    {slot : Nat} {code : Expr} (cached : compiled.indexed.secondPass.closures[slot]? = some code) :
    ∃ named diagnostics, compiled.indexed.base.functions[slot]? = some named ∧
      Nonempty (CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics code) := by
  have bound := (List.getElem?_eq_some_iff.mp cached).1
  rw [cached_length compiled] at bound
  have selected := List.getElem?_eq_getElem bound
  obtain ⟨diagnostics, output, found, receipt⟩ := CallableIndexedNamedGeneration.compiled_at compiled.indexed selected
  have same := Option.some.inj (found.symm.trans cached)
  subst output
  exact ⟨_, diagnostics, selected, receipt⟩

theorem exact_cache (compiled : SourceCoreUnifiedCompilation.Compiled) :
    compiled.indexed.secondPass.closures = (rows compiled).map LambdaRow.expression := by
  unfold rows
  rw [List.map_map]
  calc
    compiled.indexed.secondPass.closures = compiled.indexed.secondPass.closures.map id := (List.map_id _).symm
    _ = _ := by
      apply List.map_congr_left
      intro code member
      obtain ⟨slot, cached⟩ := List.mem_iff_getElem?.mp member
      obtain ⟨_, _, _, ⟨receipt⟩⟩ := cached_at compiled cached
      rw [receipt.emitted]
      rfl

theorem row_at (compiled : SourceCoreUnifiedCompilation.Compiled)
    {slot : Nat} {selectedRow : LambdaRow} (found : (rows compiled)[slot]? = some selectedRow) :
    ∃ named diagnostics,
      compiled.indexed.base.functions[slot]? = some named ∧
      selectedRow.parameter = named.signature.parameterType ∧
      selectedRow.result = LanguageResult.resultType named.signature.resultType ∧
      Nonempty (CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics selectedRow.expression) := by
  have cached : compiled.indexed.secondPass.closures[slot]? = some selectedRow.expression := by
    rw [exact_cache compiled, List.getElem?_map, found]
    rfl
  obtain ⟨named, diagnostics, selected, ⟨receipt⟩⟩ := cached_at compiled cached
  have emitted := receipt.emitted
  rcases selectedRow with ⟨parameter, result, body⟩
  change Expr.lambda parameter result body = _ at emitted
  exact ⟨named, diagnostics, selected, (Expr.lambda.inj emitted).1,
    (Expr.lambda.inj emitted).2.1, ⟨receipt⟩⟩

/-- The full global signature comes from the real preparation inventory.
Neither type tags nor a comparison of keys supplies this equality. -/
theorem ordered (compiled : SourceCoreUnifiedCompilation.Compiled)
    (slot : Nat) (selectedRow : LambdaRow) (found : (rows compiled)[slot]? = some selectedRow) :
    ∃ signature, compiled.indexed.base.globals[slot]? = some signature ∧
      signature.functionType = .function selectedRow.parameter selectedRow.result := by
  obtain ⟨named, _, selected, parameter, result, _⟩ := row_at compiled found
  refine ⟨named.signature, CallableIndexedPreparedInventories.cached_global_at compiled selected, ?_⟩
  rw [parameter, result]
  rfl

theorem rows_length (compiled : SourceCoreUnifiedCompilation.Compiled) :
    (rows compiled).length = compiled.indexed.base.globals.length := by
  rw [rows, List.length_map, cached_length, CallableIndexedPreparedInventories.cached_globals, List.length_map]

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedCachedRows
