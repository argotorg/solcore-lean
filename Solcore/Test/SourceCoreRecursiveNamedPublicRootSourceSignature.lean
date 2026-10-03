import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootSourceSignature

/-! Formal consumers keep complete first-find provenance, raw binder order and
the independent source Header. No encoder or runtime authority is inferred. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedPublicRootSourceSignature
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload RecursiveNamedCatalog RecursiveNamedPublicRootMeaning
open RecursiveNamedCatalogNativeContexts

abbrev actual_entry_fields := @RecursiveNamedPublicRootSourceSignature.entry_of_prepare

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory compiled.indexed.ancestry values ambient.definitions program}
  {root : SourceCoreIndexedSession.Root compiled}
  {header : Header compiled.indexed.ancestry values ambient.definitions program}

theorem actual_source_signature (selected : RootSelection headers root header) :
    root.inputs = header.bindings.map (fun binding => binding.1.scheme.body) ∧
    root.result = header.function.resultType :=
  RecursiveNamedPublicRootSourceSignature.inputs_and_result selected

/-- Successful preparation and a complete source inventory suffice to choose
the same Header before transporting the source signature. -/
theorem actual_recipe_signature {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {root : SourceCoreIndexedSession.Root recipe.compiled} (member : root ∈ recipe.roots)
    {headers : Inventory recipe.compiled.indexed.ancestry values ambient.definitions program}
    (complete : Complete headers) :
    ∃ header, RootSelection headers root header ∧
      root.inputs = header.bindings.map (fun binding => binding.1.scheme.body) ∧
      root.result = header.function.resultType := by
  obtain ⟨header, selected⟩ := selection_of_recipe accepted member complete
  exact ⟨header, selected, RecursiveNamedPublicRootSourceSignature.inputs_and_result selected⟩

/-- Even two distinct complete rows with the same key retain the first row.
The second row's raw binders cannot replace the factory's chosen signature. -/
theorem duplicate_first_row (first second : SourceCoreGeneralFunctions.Function)
    (distinct : first ≠ second) :
    [first, second].find? (fun named => decide (named.signature.key = first.signature.key)) = some first ∧
    [first, second].find? (fun named => decide (named.signature.key = first.signature.key)) ≠ some second := by
  constructor
  · simp
  · simpa using distinct

theorem indexed_first_row {α : Type} {rows : List α} {predicate : α → Bool} {row : α} {slot : Nat}
    (selected : rows.zipIdx.find? (fun item => predicate item.1) = some (row, slot)) :
    rows.find? predicate = some row :=
  RecursiveNamedPublicRootSourceSignature.first_row selected

end Tests.SourceCoreRecursiveNamedPublicRootSourceSignature
