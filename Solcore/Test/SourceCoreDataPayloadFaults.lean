import Solcore.SourceSemantics.CoreLowering.DataPayloadFaultPaths
import Solcore.SourceSemantics.CoreLowering.DataPayloadCatalog

/-! A default-created inner mapping whose function value has no default.
Both nested lookup helpers run, but neither insertion nor the replacement
expression runs after the inner failure. -/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreDataPayloadFaults
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
open DataPayload DataPayloadReadPaths
private def functions : GenericHeap.PayloadModel catalog where
  Represents := fun _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  extend := fun impossible _ _ => False.elim impossible
private theorem observations : FunctionObservations catalog signatures functions (fun _ _ => False) :=
  fun impossible => False.elim impossible
private theorem faithful : IdentityFaithful (fun _ _ => False) := by
  constructor <;> intros <;> contradiction
private theorem layouts : CatalogLayouts catalog := by
  apply CatalogLayouts.of_entries
  intro id entry selected
  rcases id with ⟨index⟩
  cases index with
  | zero =>
    cases selected
    exact ⟨_, _, rfl, rfl, ⟨.integer, Core.Ty.isWellFormed_sound (by decide), rfl⟩⟩
  | succ index => cases index with
    | zero => cases selected; exact ⟨_, _, rfl, rfl, ⟨.integer, .namedData (by rfl), rfl⟩⟩
    | succ index => simp [catalog] at selected
private def keys : List Value := [.integer 9, .integer 7]
private def outerEmpty : Value := Core.OrderedMapping.encode outerLayout []
private def source : Dynamic.Value := .mapping .integer innerType []
private def projections : List Dynamic.EvaluatedProjection := [.index (.integer 9), .index (.integer 7)]
private theorem represented : DataPayload.ValueRep catalog signatures functions [] [] (.mapping .integer innerType)
    source outerEmpty outerLayout.type :=
  .mapping rfl rfl rfl ⟨.integer, .namedData (by rfl), rfl⟩ (.empty _ _ _ _)
private theorem path : Path checked signatures functions [] [] keys (.mapping .integer innerType) outerLayout.type
    prepared.steps projections functionType innerLayout.valueType 6 := by
  apply Path.index (count := 3) outerCertificate rfl rfl (.integer 9) rfl
  apply Path.index (count := 0) innerCertificate rfl rfl (.integer 7) rfl
  exact .nil rfl
private theorem sourceFault : Dynamic.ProjectionsFaults (some source) projections (.missingMappingDefault functionType) :=
  .indexDefault (.integer 9) .nil (.mapping _ _) (.indexDefaultUnavailable (.integer 7) .nil (by intro impossible; cases impossible))

/-- Automatic fault correspondence consumes the independent source fault and
full payload, including the generated default-created inner mapping. -/
example : prepare checked 20 route Word.zero (fun _ => Word.zero) = .ok prepared ∧
    ∃ token finalStore admin,
      Evaluates [outerEmpty, packValues keys] [.integer 900]
        (select prepared prepared.steps (.var 0) (.var 1)) (.inLeft prepared.optionalLeaf (.word token)) finalStore ∧
      Evaluates [outerEmpty, packValues keys] [.integer 900]
        (update prepared prepared.steps outerLayout.type (.var 0) (.var 1) (.apply .unit .unit))
        (.inLeft outerLayout.type (.word token)) finalStore ∧
      finalStore = [.integer 900] ++ admin ∧ admin.length ≤ 6 :=
  ⟨accepted, path.fault_preserves observations faithful layouts prepared rfl represented sourceFault
    [outerEmpty, packValues keys] [.integer 900] (.var 0) (.var 1) (.apply .unit .unit) (.var rfl) (.var rfl)⟩

example : (match runStateful 2000 (.initial
    (update prepared prepared.steps outerLayout.type (.var 0) (.var 1) (.apply .unit .unit))
    [outerEmpty, packValues keys] [.integer 900]) with
    | .done value store => value == .inLeft outerLayout.type (.word Word.zero) && store.length == 7 && store[0]? == some (.integer 900)
    | _ => false) = true := by cbv

end Tests.SourceCoreDataPayloadFaults
