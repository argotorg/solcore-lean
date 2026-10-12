import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicStartMeaning

/-! The actual post-issuance Session is used by the original startup encoder.
These receipts identify the exact callable bytes at the actual argument index,
retain their cached named/builtin factory, and preserve native memory and
metadata across issuance. Source function interpretation remains separate
until that factory's code and complete Source provenance are joined. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicIssuedFunctionInputs
open Core Frontend SourceInference
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning

/-- Startup consumes the same authenticated opaque handle whose native value
was retained by issuance. No value is chosen by native type or descriptor alone. -/
theorem StartAt.imported_function
    {artifact : Artifact} {session : Session artifact} {key : Key}
    {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {checkpoint : Checkpoint artifact} {recipe : Recipe} {root : Root recipe.compiled}
    {world : StoreTyping} {store : Store} {native : Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session key arguments fuel checkpoint recipe root world store native encodedValues)
    {issuanceFuel : Nat} {expected : TypeSystem.Ty} {handle : Handle} {callable : Core.Value}
    (imported : session.EncodesAt issuanceFuel expected (.function handle) callable)
    {index : Nat} (found : arguments[index]? = some (.function handle)) :
    native[index]? = some callable := by
  have receipt := started.original.imported_function imported found
  cases artifact
  rename_i authority actualRecipe
  have sameRecipe : actualRecipe = recipe := started.recipe_eq
  subst recipe
  obtain ⟨actualRoot, encodedPrefix, selected, lookup, initial⟩ := receipt
  have sameRoot := Option.some.inj (started.selected.symm.trans selected)
  subst actualRoot
  have original := started.initial
  cases checkpoint
  rename_i origin request checkpointWorld state stored typed extension registry values owner
  change state = Core.State.initial root.body
    (native.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment actualRecipe.compiled.indexed) store at original
  have sameState := initial.symm.trans original
  have sameControl := congrArg Core.State.control sameState
  have sameEnvironment := (Core.Control.eval.inj sameControl).2
  have samePrefix : encodedPrefix = native := by
    have reversed := congrArg List.reverse (List.append_inj_left' sameEnvironment rfl)
    simpa only [List.reverse_reverse] using reversed
  subst encodedPrefix
  exact lookup

/-- A real named issuance is consumed by the exact later startup. Its whole
cached factory remains attached to the selected native argument. -/
theorem StartAt.named_argument
    {artifact : Artifact} {before : Session artifact} {issued : Completion artifact}
    {name : Key} {issuanceFuel : Nat}
    (issuance : before.NamedIssuedAt name issuanceFuel issued)
    {key : Key} {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {checkpoint : Checkpoint artifact} {recipe : Recipe} {root : Root recipe.compiled}
    {world : StoreTyping} {store : Store} {native : Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt issued.session key arguments fuel checkpoint recipe root world store native encodedValues)
    {handle : Handle} (handleValue : issued.value = .function handle)
    {index : Nat} (found : arguments[index]? = some (.function handle)) :
    ∃ expected callable, before.SameRuntime issued.session ∧ issued.sourceType = expected ∧
      issued.boundaryFuel = issuanceFuel ∧ recipe.NamedCallableAt name expected callable ∧
      native[index]? = some callable := by
  obtain ⟨expected, callable, same, sourceType, budget, encoded, factory⟩ := issuance.receipt
  rw [handleValue] at encoded
  have argument := StartAt.imported_function started encoded found
  cases artifact
  rename_i authority actualRecipe
  have sameRecipe : actualRecipe = recipe := started.recipe_eq
  subst recipe
  exact ⟨expected, callable, same, sourceType, budget, factory, argument⟩

/-- Builtin issuance reaches the same original argument encoder and literal
cached closed builtin factory, while the initialized native state is retained. -/
theorem StartAt.builtin_argument
    {artifact : Artifact} {before : Session artifact} {issued : Completion artifact}
    {function : BuiltinFunctionId} {issuanceFuel : Nat}
    (issuance : before.BuiltinIssuedAt function issuanceFuel issued)
    {key : Key} {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {checkpoint : Checkpoint artifact} {recipe : Recipe} {root : Root recipe.compiled}
    {world : StoreTyping} {store : Store} {native : Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt issued.session key arguments fuel checkpoint recipe root world store native encodedValues)
    {handle : Handle} (handleValue : issued.value = .function handle)
    {index : Nat} (found : arguments[index]? = some (.function handle)) :
    ∃ expected callable, before.SameRuntime issued.session ∧ issued.sourceType = expected ∧
      issued.boundaryFuel = issuanceFuel ∧ recipe.BuiltinCallableAt function expected callable ∧
      native[index]? = some callable := by
  obtain ⟨expected, callable, same, sourceType, budget, encoded, factory⟩ := issuance.receipt
  rw [handleValue] at encoded
  have argument := StartAt.imported_function started encoded found
  cases artifact
  rename_i authority actualRecipe
  have sameRecipe : actualRecipe = recipe := started.recipe_eq
  subst recipe
  exact ⟨expected, callable, same, sourceType, budget, factory, argument⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicIssuedFunctionInputs
