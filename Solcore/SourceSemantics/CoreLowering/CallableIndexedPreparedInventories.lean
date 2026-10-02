import Solcore.SourceSemantics.CoreLowering.CallableIndexedParameterNativeInversion
import Solcore.Frontend.SourceCoreUnifiedCompilation

/-! Static inventory equalities follow the actual preparation factories.
They remove the caller's global-signature correspondence premise when typing
cached named bodies. They do not certify a source body execution. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedPreparedInventories
open Core Frontend SourceInference

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : (action >>= next) = .ok value) :
    ∃ input, action = .ok input ∧ next input = .ok value := by
  cases action with
  | error error => cases accepted
  | ok input => exact ⟨input, rfl, accepted⟩

theorem compatible_catalog_globals {program : CheckedProgram} {plan : SourceCompilationPlan.Plan}
    {checked : SourceCoreCompatibleCatalog.Checked} (ownership : checked.signatures = program.signatures)
    {fuel : Nat} {prepared : SourceCoreCompatibleFunctions.Prepared checked}
    (accepted : SourceCoreCompatibleFunctions.prepareWithCatalog program plan checked ownership fuel = .ok prepared) :
    prepared.globals = prepared.functions.map (·.signature) := by
  unfold SourceCoreCompatibleFunctions.prepareWithCatalog at accepted
  obtain ⟨executable, _, accepted⟩ := bind_ok accepted
  obtain ⟨locals, _, accepted⟩ := bind_ok accepted
  obtain ⟨contexts, _, accepted⟩ := bind_ok accepted
  obtain ⟨functions, _, accepted⟩ := bind_ok accepted
  cases seeds : executable.val.seedKeys with
  | nil =>
    simp only [seeds, pure, Except.pure] at accepted
    cases accepted
    rfl
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
      rfl
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
      rfl

theorem compatible_automatic_globals {program : CheckedProgram} {plan : SourceCompilationPlan.Plan}
    {fuel : Nat} {limits : SourceCoreRawMetadata.Limits} {automatic : SourceCoreCompatibleFunctions.Automatic}
    (accepted : SourceCoreCompatibleFunctions.prepare program plan fuel limits = .ok automatic) :
    automatic.prepared.globals = automatic.prepared.functions.map (·.signature) := by
  unfold SourceCoreCompatibleFunctions.prepare at accepted
  obtain ⟨executable, _, accepted⟩ := bind_ok accepted
  obtain ⟨locals, _, accepted⟩ := bind_ok accepted
  try dsimp only at accepted
  split at accepted
  · cases accepted
  · obtain ⟨prepared, preparedAccepted, accepted⟩ := bind_ok accepted
    cases accepted
    exact compatible_catalog_globals _ preparedAccepted

theorem indexed_base {checked : SourceCoreCompatibleCatalog.Checked}
    {base : SourceCoreCompatibleFunctions.Prepared checked} {fuel : Nat}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    (accepted : SourceCoreCallableIndexedPrograms.prepare base fuel = .ok prepared) :
    prepared.base = base := by
  unfold SourceCoreCallableIndexedPrograms.prepare at accepted
  try dsimp only at accepted
  split at accepted
  · cases accepted
  · try dsimp only [pure, Except.pure, bind, Except.bind] at accepted
    split at accepted
    · cases accepted
    · try dsimp only [pure, Except.pure, bind, Except.bind] at accepted
      split at accepted
      · cases accepted
      · try dsimp only [pure, Except.pure, bind, Except.bind] at accepted
        obtain ⟨firstPass, _, accepted⟩ := bind_ok accepted
        try dsimp only at accepted
        split at accepted
        · cases accepted
        · try dsimp only [pure, Except.pure, bind, Except.bind] at accepted
          split at accepted
          · cases accepted
          · try dsimp only [pure, Except.pure, bind, Except.bind] at accepted
            obtain ⟨secondPass, _, accepted⟩ := bind_ok accepted
            obtain ⟨inputs, _, accepted⟩ := bind_ok accepted
            obtain ⟨entries, _, accepted⟩ := bind_ok accepted
            cases accepted
            rfl

theorem cached_globals (cached : SourceCoreUnifiedCompilation.Compiled) :
    cached.indexed.base.globals = cached.indexed.base.functions.map (·.signature) := by
  rw [indexed_base cached.indexedPrepared]
  exact compatible_automatic_globals cached.compatiblePrepared

theorem cached_global_at (cached : SourceCoreUnifiedCompilation.Compiled)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : cached.indexed.base.functions[index]? = some named) :
    cached.indexed.base.globals[index]? = some named.signature := by
  rw [cached_globals]
  simp [selected]

/-- A named function at an actual cached slot needs no separate claim about
its global signature. The original raw argument and wrapper inputs remain. -/
theorem cached_named_body (cached : SourceCoreUnifiedCompilation.Compiled)
    {entry : SourceCoreCallableIndexedPrograms.Entry cached.indexed.layouts}
    (member : entry ∈ cached.indexed.entries)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : cached.indexed.base.functions[index]? = some named) :
    ∃ diagnostics code,
      ∃ compiled : CallableIndexedNamedGeneration.Compilation cached.indexed named diagnostics code,
      cached.indexed.secondPass.closures[index]? = some code ∧
      HasType (named.signature.parameterType :: cached.indexed.base.globals.map (·.referenceType) ++
        .cell cached.indexed.ancestry.layout.frame.type :: SourceCoreGeneralEntry.nativeInputContext entry.native.inputTypes)
        compiled.parameterCode (LanguageResult.resultType named.signature.resultType) cached.indexed.layouts.definitions ∧
      HasType (SourceCoreLocalCell.coreContext (named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))) ++
        named.signature.parameterType :: cached.indexed.base.globals.map (·.referenceType) ++
        .cell cached.indexed.ancestry.layout.frame.type :: SourceCoreGeneralEntry.nativeInputContext entry.native.inputTypes)
        compiled.body (LanguageResult.resultType named.signature.resultType) cached.indexed.layouts.definitions :=
  CallableIndexedParameterNativeInversion.prepared_named_body cached.indexedPrepared member selected
    (cached_global_at cached selected)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedPreparedInventories
