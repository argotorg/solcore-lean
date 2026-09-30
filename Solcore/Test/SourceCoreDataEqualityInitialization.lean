import Solcore.SourceSemantics.CoreLowering.DataEqualityInitialization

/-! Equality initialization terminates independently of recursive comparison
bodies. The concrete comparison exercises those installed closures afterwards. -/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreDataEqualityInitialization
open Solcore Solcore.Frontend Solcore.SourceSemantics.CoreLowering
open SourceCoreDataEquality DataEqualityInitialization

private def moduleId : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"equality_initialization", by decide⟩], by decide⟩⟩
private def dataId : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def treeType : TypeSystem.Ty := .nominal dataId []
private def layout : Core.OrderedMapping.Layout := ⟨.word, .word, ⟨1⟩⟩
private def catalog : SourceCoreDataCatalog.Catalog := { entries := [
  { sourceType := treeType
    definition := some ⟨[.unit, .integer, .product (.namedData ⟨0⟩) (.namedData ⟨0⟩)]⟩
    constructors := [⟨dataId, 0⟩, ⟨dataId, 1⟩, ⟨dataId, 2⟩] },
  { sourceType := .mapping .word .word, definition := some layout.definition, constructors := [] }]
}
private def checked : SourceCoreDataCatalog.Checked :=
  ⟨catalog, Core.DataEnvironment.isWellFormed_sound (by decide)⟩
example (prepared : Prepared checked) : Initializer prepared.expression := prepared_initializes prepared
example (prepared : Prepared checked) : allocations prepared.expression = 2 := prepared_allocation_count prepared

/-- Neither closure bodies nor assumptions of their termination are needed to
initialize real mutually referring cells under an existing typed store. -/
example (prepared : Prepared checked) : ∃ body captured finalStore finalWorld,
    Core.Evaluates [.integer 7] [.integer 900] prepared.expression
      (.closure (.product prepared.type prepared.type) .bool body captured) finalStore ∧
    Core.WorldExtends [.integer] finalWorld ∧
    Core.RuntimeStoreHasTypes finalWorld finalStore catalog.definitions ∧
    Core.RuntimeValueHasType finalWorld (.closure (.product prepared.type prepared.type) .bool body captured)
      (comparatorType prepared.type) catalog.definitions ∧ finalStore.length = 3 := by
  have environment : Core.RuntimeEnvironmentHasTypes [.integer] [.integer 7] [.integer] catalog.definitions :=
    .cons .integer .nil
  have store : Core.RuntimeStoreHasTypes [.integer] [.integer 900] catalog.definitions := {
    length_eq := rfl
    lookup := by
      intro location type found
      cases location with
      | zero => cases found; exact ⟨_, rfl, .integer⟩
      | succ location => simp at found
  }
  obtain ⟨body, captured, finalStore, finalWorld, evaluated, extension, storeTyped, valueTyped⟩ :=
    prepared_evaluates prepared environment store
  exact ⟨body, captured, finalStore, finalWorld, evaluated, extension, storeTyped, valueTyped,
    by simpa [checked, catalog] using prepared_evaluation_length prepared evaluated⟩

private def leaf (value : Int) : Core.Expr := .construct ⟨⟨0⟩, 1⟩ (.integer value)
private def tree (right : Int) : Core.Expr := .construct ⟨⟨0⟩, 2⟩ (.pair (leaf 7) (leaf right))
private def comparison (prepared : Prepared checked) (right : Int) : Core.Expr :=
  .apply prepared.expression (.pair (tree (-3)) (tree right))

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def checkResult (result : Core.StatefulRunResult) (expected : Bool) : IO Unit := do
  match result with
  | .done value store =>
    assertTrue (value == .bool expected) "recursive initialized comparison returned the wrong value"
    assertTrue (store.length == 3) "comparison reallocated or lost helper cells"
    assertTrue (store[0]? == some (.integer 900)) "helper initialization overwrote the preexisting store"
  | other => throw (IO.userError s!"initialized comparison did not finish: {reprStr other}")

/-- Recursive comparison uses installed helper references in real captured
environments; initialization has a typed proof above rather than a finite-fuel
assumption. Runtime checks also observe prefix preservation and resumption. -/
def run : IO Unit := do
  let prepared ← match prepare 20 checked treeType with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError s!"recursive initializer rejected: {reprStr error}")
  for (right, expected) in [((-3 : Int), true), (8, false)] do
    let initial := Core.State.initial (comparison prepared right) [.integer 7] [.integer 900]
    checkResult (Core.runStateful 3000 initial) expected
    match Core.runStateful 10 initial with
    | .outOfFuel checkpoint => checkResult (Core.runStateful 3000 checkpoint) expected
    | other => throw (IO.userError s!"initialization did not expose the expected checkpoint: {reprStr other}")
  IO.println "source Core equality initialization GREEN"

end Tests.SourceCoreDataEqualityInitialization
