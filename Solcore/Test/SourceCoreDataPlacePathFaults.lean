import Solcore.SourceSemantics.CoreLowering.DataPlaceFaultTree

/-! A default-created inner mapping whose function value has no default.
Both nested lookup helpers run, but neither insertion nor the replacement
expression runs after the inner failure. -/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreDataPlacePathFaults
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreDataPlaces DataPlaceMappingIndex DataEquality DataEqualityValues DataPatternValues
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"place_path_faults", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def keyId (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def functionType : TypeSystem.Ty := .function .unit .unit
private def innerType : TypeSystem.Ty := .mapping .integer functionType
private def innerLayout : Core.OrderedMapping.Layout := ⟨.integer, TaggedFunction.functionType .unit .unit, ⟨0⟩⟩
private def outerLayout : Core.OrderedMapping.Layout := ⟨.integer, innerLayout.type, ⟨1⟩⟩
private def catalog : SourceCoreDataCatalog.Catalog := { entries := [
  { sourceType := innerType, definition := some innerLayout.definition },
  { sourceType := .mapping .integer innerType, definition := some outerLayout.definition }]
}
private def checked : SourceCoreDataCatalog.Checked := ⟨catalog, Core.DataEnvironment.isWellFormed_sound (by decide)⟩
private def route : Route := ⟨.mapping .integer innerType, outerLayout.type, innerLayout.valueType,
  [.index outerLayout (keyId 0) innerType, .index innerLayout (keyId 1) functionType], some outerLayout⟩
private theorem except_get {α ε : Type} (result : Except ε α) (positive : result.toOption.isSome = true) :
    result = .ok (result.toOption.get positive) := by
  cases result with
  | error => simp [Except.toOption] at positive
  | ok value => rfl
private theorem comparisonExists : (SourceCoreDataEquality.prepare 20 checked .integer).toOption.isSome = true := by cbv
private def comparison := (SourceCoreDataEquality.prepare 20 checked .integer).toOption.get comparisonExists
private theorem comparisonGenerated : SourceCoreDataEquality.prepare 20 checked .integer = .ok comparison := except_get _ comparisonExists
private theorem innerDefaultExists : (SourceCoreDefaultValue.prepare (functionType.size + 1) checked functionType).toOption.isSome = true := by cbv
private def innerDefault := (SourceCoreDefaultValue.prepare (functionType.size + 1) checked functionType).toOption.get innerDefaultExists
private theorem innerDefaultGenerated : SourceCoreDefaultValue.prepare (functionType.size + 1) checked functionType = .ok innerDefault := except_get _ innerDefaultExists
private theorem outerDefaultExists : (SourceCoreDefaultValue.prepare (innerType.size + 1) checked innerType).toOption.isSome = true := by cbv
private def outerDefault := (SourceCoreDefaultValue.prepare (innerType.size + 1) checked innerType).toOption.get outerDefaultExists
private theorem outerDefaultGenerated : SourceCoreDefaultValue.prepare (innerType.size + 1) checked innerType = .ok outerDefault := except_get _ outerDefaultExists
private def innerIndex : PreparedIndex := ⟨innerLayout, keyId 1, 1, comparison.expression, innerDefault.expression, Word.zero⟩
private def outerIndex : PreparedIndex := ⟨outerLayout, keyId 0, 0, comparison.expression, outerDefault.expression, Word.zero⟩
private def prepared : Prepared := ⟨route, [.index outerIndex, .index innerIndex], [(keyId 0, .integer), (keyId 1, .integer)], Word.zero⟩
private def innerCertificate : Index checked functionType innerIndex := Index.of_generated comparisonGenerated innerDefaultGenerated rfl rfl
private def outerCertificate : Index checked innerType outerIndex := Index.of_generated comparisonGenerated outerDefaultGenerated rfl rfl
private theorem accepted : prepare checked 20 route Word.zero (fun _ => Word.zero) = .ok prepared := by
  have inner : checked.catalog.entries[0]? = some ⟨innerType, some innerLayout.definition, []⟩ := rfl
  have outer : checked.catalog.entries[1]? = some ⟨.mapping .integer innerType, some outerLayout.definition, []⟩ := rfl
  have innerDefaultCompiled := innerDefaultGenerated
  have outerDefaultCompiled := outerDefaultGenerated
  simp only [innerType, functionType] at innerDefaultCompiled outerDefaultCompiled
  simp [prepare, route, innerLayout, outerLayout, inner, outer, innerType,
    comparisonGenerated, innerDefaultCompiled, outerDefaultCompiled, functionType,
    prepared, innerIndex, outerIndex, bind, Except.bind, pure, Except.pure, Except.mapError]
private theorem comparisonType : comparison.type = .integer := by
  have projection := comparison.projection
  rw [DataPlaceMappingPreparation.comparison_sourceType comparisonGenerated] at projection
  exact Except.ok.inj projection.symm
private theorem noIdentities : IdentityFaithful (fun _ _ => False) := by
  constructor <;> intros <;> contradiction
private theorem innerKey : KeyRep innerCertificate signatures (fun _ _ => False) (.integer 7) (.integer 7) := by
  change Observation _ _ _ comparison.type _ _; rw [comparisonType]; exact .integer 7
private theorem outerKey : KeyRep outerCertificate signatures (fun _ _ => False) (.integer 9) (.integer 9) := by
  change Observation _ _ _ comparison.type _ _; rw [comparisonType]; exact .integer 9
private def keys : List Value := [.integer 9, .integer 7]
private def outerEmpty : Value := Core.OrderedMapping.encode outerLayout []
private def innerEmpty : Value := Core.OrderedMapping.encode innerLayout []
private def source : Dynamic.Value := .mapping .integer innerType []
private def projections : List Dynamic.EvaluatedProjection := [.index (.integer 9), .index (.integer 7)]
private theorem innerFault : DataPlaceFaultTree.Tree checked signatures (fun _ _ => False) prepared keys
    (.mapping .integer functionType []) innerEmpty innerLayout.type [.index innerIndex] [.index (.integer 7)]
    (.missingMappingDefault functionType) Word.zero 3 :=
  .missing (valueRelation := fun _ _ => False) innerCertificate innerKey (.integer 7) rfl .nil .nil (by intro impossible; cases impossible)
private theorem fault : DataPlaceFaultTree.Tree checked signatures (fun _ _ => False) prepared keys
    source outerEmpty outerLayout.type prepared.steps projections (.missingMappingDefault functionType) Word.zero 6 := by
  apply DataPlaceFaultTree.Tree.mapping (count := 3) (valueRelation := fun _ _ => False)
    outerCertificate outerKey (.integer 9) rfl .nil (.default .nil (.mapping _ _))
  intro value represented
  rcases represented with impossible | ⟨_, tree⟩
  · contradiction
  · cases tree with
    | mapping key value id selected =>
      change some ⟨0⟩ = some id at selected
      cases selected
      exact innerFault

/-- Even a malformed replacement expression cannot be reached after the
independent source fault. Only the two lookup initializers allocate cells. -/
example : ∃ finalStore administrative,
    Dynamic.ProjectionsFaults (some source) projections (.missingMappingDefault functionType) ∧
    Evaluates [outerEmpty, packValues keys] [.integer 900]
      (select prepared prepared.steps (.var 0) (.var 1)) (.inLeft prepared.optionalLeaf (.word Word.zero)) finalStore ∧
    Evaluates [outerEmpty, packValues keys] [.integer 900]
      (update prepared prepared.steps outerLayout.type (.var 0) (.var 1) (.apply .unit .unit))
      (.inLeft outerLayout.type (.word Word.zero)) finalStore ∧
    finalStore = [.integer 900] ++ administrative ∧ administrative.length = 6 :=
  fault.preserves noIdentities rfl [outerEmpty, packValues keys] [.integer 900] (.var 0) (.var 1) (.apply .unit .unit) (.var rfl) (.var rfl)

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
def run : IO Unit := do
  let prepared ← match prepare checked 20 route Word.zero (fun _ => Word.zero) with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"nested-fault preparation failed: {reprStr error}")
  let keyType : Core.Ty := .product .integer .integer
  let replacement : Value := .pair (.inLeft .word .unit) (.closure .unit (.sum .word .unit) (.inRight .word .unit) [])
  for write in [false, true] do
    let helper := if write then setter prepared keyType else getter prepared keyType
    let argument := if write then .pair (.inLeft outerLayout.type .unit) (.pair (packValues keys) replacement)
      else .pair (.inLeft outerLayout.type .unit) (packValues keys)
    let argumentType := if write then .product (.sum .unit outerLayout.type) (.product keyType innerLayout.valueType)
      else .product (.sum .unit outerLayout.type) keyType
    let resultType := if write then outerLayout.type else .sum .unit innerLayout.valueType
    let expression := .apply helper (.var 0)
    assertTrue (infer? [argumentType] expression catalog.definitions == some (.sum .word resultType)) "nested fault helper failed checker"
    let initial := Core.State.initial expression [argument] [.integer 900]
    let check := fun result => do
      match result with
      | .done value store =>
        assertTrue (value == .inLeft resultType (.word Word.zero)) "nested fault did not retain exact language reason"
        assertTrue (store.length == 7) "nested fault ran insertion or lost lookup helpers"
        assertTrue (store[0]? == some (.integer 900)) "nested fault wrote the source prefix"
      | other => throw (IO.userError s!"nested fault became machine failure or exhaustion: {reprStr other}")
    check (runStateful 10000 initial)
    match runStateful 9 initial with
    | .outOfFuel checkpoint => check (runStateful 10000 checkpoint)
    | other => throw (IO.userError s!"nested fault expected checkpoint: {reprStr other}")
  IO.println "source Core nested path faults GREEN"

end Tests.SourceCoreDataPlacePathFaults
