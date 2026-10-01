import Solcore.SourceSemantics.CoreLowering.CompatiblePathFaults
import Solcore.SourceSemantics.CoreLowering.CompatibleMappingMixedRuns

#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Actual route/preparation and codec receipts produce semantic trees for a
nested mapping. No hand-authored comparator tree or helper evaluation occurs. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
namespace Tests.SourceCoreCompatiblePathCertificates
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreCompatibleDataPlaces CompatiblePayload CompatibleEquality CompatibleMapping CompatibleMapping.MixedPaths CompatibleMixedRoute

private theorem except_get {α ε : Type} (result : Except ε α) (positive : result.toOption.isSome = true) :
    result = .ok (result.toOption.get positive) := by
  cases result with
  | error => simp [Except.toOption] at positive
  | ok => rfl
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"compatible_path", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "compatible_path.solc"⟩, 0, 1⟩
private def key : ExpressionId := ⟨⟨owner, 1⟩⟩
private def site : SourceCoreElaboration.ErrorSite := .occurrence ⟨owner, 0⟩
private def innerType : TypeSystem.Ty := .mapping .bool .word
private def rootType : TypeSystem.Ty := .mapping .bool innerType
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private theorem catalogExists : (SourceCoreCompatibleCatalog.prepare signatures 100 [rootType]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 100 [rootType]).toOption.get catalogExists
private def context := SourceCoreCompatibleValues.Context.initial checked
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "root", .mono rootType, [], false, none⟩
private def node : ExpressionNode := { id := key, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def source : TypedSource := { owner, inputs := [binder], roots := [.expression key], nodes := [.expression node] }
private def projections : List PlaceProjection := [.index key, .index key]
private def assignment : AssignmentResolution := ⟨⟨binder.id, projections, .word⟩, []⟩
private def innerLayout : OrderedMapping.Layout := ⟨.bool, .word, ⟨1⟩⟩
private def outerLayout : OrderedMapping.Layout := ⟨.bool, SourceCoreMappingWithDefault.type innerLayout, ⟨0⟩⟩
private def route : Route := ⟨rootType, SourceCoreMappingWithDefault.type outerLayout, .word,
  [.index outerLayout key innerType, .index innerLayout key .word], none⟩
private theorem preparedExists : (prepare context 100 route Word.zero (fun _ => Word.zero)).toOption.isSome = true := by cbv
private def prepared := (prepare context 100 route Word.zero (fun _ => Word.zero)).toOption.get preparedExists
private theorem preparedBy : prepare context 100 route Word.zero (fun _ => Word.zero) = .ok prepared := except_get _ preparedExists
private theorem routed : routeSteps checked checked.signatures source site binder.id rootType projections = .ok (route.steps, .word) := by cbv
private theorem path : PreparedPath checked source site rootType projections 0 prepared.steps prepared.keys .word :=
  (prepared_of_success routed preparedBy).2.2
private def noFunctions (catalog : SourceCoreCompatibleCatalog.Catalog) : FunctionModel catalog where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible
private def keys : List Value := [.bool true, .bool true]
private def resolved : List Dynamic.EvaluatedProjection := [.index (.bool true), .index (.bool true)]

private theorem arguments {registry : SourceCoreRawMetadata.Registry} {steps : List PreparedStep} {sites : List (ExpressionId × Ty)}
    (actualPath : PreparedPath checked source site rootType projections 0 steps sites .word) :
    Arguments checked registry (noFunctions checked.catalog) [] [] source site keys actualPath resolved := by
  cases actualPath with
  | index first generated tail =>
    have shape := TypeSystem.Ty.mapping.inj first.view
    obtain ⟨rfl, rfl⟩ := shape
    have nativeKey := Except.ok.inj first.keyProjection
    cases tail with
    | index second other final =>
      have shape := TypeSystem.Ty.mapping.inj second.view
      obtain ⟨rfl, rfl⟩ := shape
      have secondKey := Except.ok.inj second.keyProjection
      cases final
      apply Arguments.index (certificate := first) (generated := generated) rfl
      · rw [← nativeKey]; exact .bool true
      · apply Arguments.index (certificate := second) (generated := other) rfl
        · rw [← secondKey]; exact .bool true
        · exact .nil

private def w (n : Nat) : Word := Word.ofNatModulo n
private def inner : SourceCoreDataValues.Value := .mapping .bool .word [(.bool true, .word (w 2)), (.bool true, .word (w 9))]
private def carrier : SourceCoreDataValues.Value := .mapping .bool innerType [(.bool true, inner)]
private def sourceInner : Dynamic.Value := .mapping .bool .word [(.bool true, .word (w 2)), (.bool true, .word (w 9))]
private def sourceRoot : Dynamic.Value := .mapping .bool innerType [(.bool true, sourceInner)]
private theorem meaning : CompatibleEncoding.Means carrier sourceRoot :=
  .mapping (.prepend (.bool _) (.mapping (.prepend (.bool _) (.word _) (.prepend (.bool _) (.word _) .empty))) .empty)
private theorem represented {encoded : SourceCoreCompatibleValues.Encoded 100 context rootType carrier}
    (encodedBy : SourceCoreCompatibleValues.encode 100 context rootType carrier = .ok encoded) :
    ValueRep checked encoded.context.registry (noFunctions checked.catalog) [] [] rootType sourceRoot encoded.value encoded.type :=
  CompatibleEncoding.encode_represents_at encodedBy meaning [] []
private theorem sourceRead : Dynamic.ProjectionsRead (some sourceRoot) resolved (some (.word (w 2))) :=
  .indexFound (.head ⟨rfl, .bool _⟩) (.indexFound (.head ⟨rfl, .bool _⟩) .nil)

example {encoded : SourceCoreCompatibleValues.Encoded 100 context rootType carrier}
    (accepted : SourceCoreCompatibleValues.encode 100 context rootType carrier = .ok encoded) : ReadTree checked encoded.context.registry (noFunctions checked.catalog) [] [] prepared keys
    .word .word rootType sourceRoot encoded.value prepared.steps resolved (.word (w 2)) (readCost checked prepared.steps) :=
  (arguments path).readTree (represented accepted) rfl sourceRead prepared

private def changedInner : Dynamic.Value := .mapping .bool .word [(.bool true, .word (w 7)), (.bool true, .word (w 9))]
private def changedRoot : Dynamic.Value := .mapping .bool innerType [(.bool true, changedInner)]
private theorem sourceUpdate : Dynamic.ProjectionsUpdate (fun _ value => value = .word (w 7)) (some sourceRoot) resolved changedRoot :=
  .indexFound (.head ⟨rfl, .bool _⟩)
    (.indexFound (.head ⟨rfl, .bool _⟩) (.leaf rfl) (.update (.head ⟨rfl, .bool _⟩))) (.update (.head ⟨rfl, .bool _⟩))
example {encoded : SourceCoreCompatibleValues.Encoded 100 context rootType carrier}
    (accepted : SourceCoreCompatibleValues.encode 100 context rootType carrier = .ok encoded) : UpdateTree checked encoded.context.registry (noFunctions checked.catalog) [] [] prepared keys
    (.word (w 7)) (.word (w 7)) rootType sourceRoot encoded.value encoded.type prepared.steps resolved changedRoot (updateCost checked prepared.steps) :=
  (arguments path).updateTree (represented accepted) (.word (w 7)) sourceUpdate prepared

private def noIdentities : Dynamic.Value → Word → Prop := fun _ _ => False
private theorem faithful : DataEquality.IdentityFaithful noIdentities := ⟨False.elim, fun impossible _ => False.elim impossible⟩
private theorem noFunctionObservations : FunctionObservations checked.catalog (noFunctions checked.catalog) noIdentities := fun impossible => False.elim impossible

private theorem completed_read {encoded : SourceCoreCompatibleValues.Encoded 100 context rootType carrier}
    (accepted : SourceCoreCompatibleValues.encode 100 context rootType carrier = .ok encoded) : ∃ value after administrative,
    Dynamic.RootInitialValue (⟨rootType, some sourceRoot, none⟩ : Dynamic.Cell) (some sourceRoot) ∧
    Dynamic.ProjectionsRead (some sourceRoot) resolved (some (.word (w 2))) ∧
    ValueRep checked encoded.context.registry (noFunctions checked.catalog) [] [] .word (.word (w 2)) value .word ∧
    FiniteRun [.pair (.inRight .unit encoded.value) (DataPatternValues.packValues keys)] []
      (.apply (getter prepared (.product .bool .bool)) (.var 0)) (.inRight .word (.inRight .unit value)) after ∧
    after = [] ++ administrative ∧ administrative.length = readCost checked prepared.steps := by
  exact getter_preserves_run (.initialized (sourceType := rootType))
    ((arguments path).readTree (represented accepted) rfl sourceRead prepared) rfl (by cbv; intro impossible; cases impossible)
    faithful noFunctionObservations (by cbv) _ [] (.product .bool .bool) (.var 0) (.var rfl)

private theorem completed_update {encoded : SourceCoreCompatibleValues.Encoded 100 context rootType carrier}
    (accepted : SourceCoreCompatibleValues.encode 100 context rootType carrier = .ok encoded) :
    ∃ value after administrative,
      Dynamic.RootInitialValue (⟨rootType, some sourceRoot, none⟩ : Dynamic.Cell) (some sourceRoot) ∧
      Dynamic.ProjectionsUpdate (fun _ value => value = .word (w 7)) (some sourceRoot) resolved changedRoot ∧
      ValueRep checked encoded.context.registry (noFunctions checked.catalog) [] [] rootType changedRoot value encoded.type ∧
      FiniteRun [.pair (.inRight .unit encoded.value) (.pair (DataPatternValues.packValues keys) (.word (w 7)))] []
        (.apply (setter prepared (.product .bool .bool)) (.var 0)) (.inRight .word value) after ∧
      after = [] ++ administrative ∧ administrative.length = updateCost checked prepared.steps := by
  exact setter_preserves_run (.initialized (sourceType := rootType))
    ((arguments path).updateTree (represented accepted) (.word (w 7)) sourceUpdate prepared)
    rfl (by cbv; intro impossible; cases impossible) faithful noFunctionObservations (by cbv) _ []
    (.product .bool .bool) (.var 0) (.var rfl)

private def runSuccess : IO Unit := do
  match accepted : SourceCoreCompatibleValues.encode 100 context rootType carrier with
  | .error error => throw (IO.userError s!"path input encoding failed: {reprStr error}")
  | .ok encoded =>
    have _whole := completed_read accepted
    have _updated := completed_update accepted
    let code := Expr.apply (getter prepared (.product .bool .bool)) (.var 0)
    let environment := [Value.pair (.inRight .unit encoded.value) (DataPatternValues.packValues keys)]
    match runStateful 100000 (.initial code environment []) with
    | .done (.inRight .word (.inRight .unit (.word value))) _ =>
      unless value == w 2 do throw (IO.userError "automatic path read chose later duplicate")
    | other => throw (IO.userError s!"automatic path read failed: {reprStr other}")
    let write := Expr.apply (setter prepared (.product .bool .bool)) (.var 0)
    let writeEnvironment := [Value.pair (.inRight .unit encoded.value) (.pair (DataPatternValues.packValues keys) (.word (w 7)))]
    match runStateful 100000 (.initial write writeEnvironment []) with
    | .done (.inRight .word value) after =>
      let expected : SourceCoreDataValues.Value := .mapping .bool innerType [(.bool true, .mapping .bool .word [(.bool true, .word (w 7)), (.bool true, .word (w 9))])]
      match SourceCoreCompatibleValues.decode 100 encoded.context rootType value with
      | .ok actual => unless actual == expected do throw (IO.userError "automatic path update changed duplicate order")
      | .error error => throw (IO.userError s!"automatic path update decode failed: {reprStr error}")
      unless after.length == 4 * (checked.catalog.entries.length + 1) do throw (IO.userError "automatic path update allocation count changed")
    | other => throw (IO.userError s!"automatic path update failed: {reprStr other}")
  IO.println "compatible path certificate extraction GREEN"

namespace Fault
private def leaf : TypeSystem.Ty := .function .word .word
private def innerType : TypeSystem.Ty := .mapping .bool leaf
private def rootType : TypeSystem.Ty := .mapping .bool innerType
private theorem catalogExists : (SourceCoreCompatibleCatalog.prepare signatures 100 [rootType]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 100 [rootType]).toOption.get catalogExists
private def context := SourceCoreCompatibleValues.Context.initial checked
private def source : TypedSource := { owner, inputs := [⟨binder.id, "root", .mono rootType, [], false, none⟩], roots := [.expression key], nodes := [.expression node] }
private def innerLayout : OrderedMapping.Layout := ⟨.bool, CallableContract.functionType .word .word, ⟨1⟩⟩
private def outerLayout : OrderedMapping.Layout := ⟨.bool, SourceCoreMappingWithDefault.type innerLayout, ⟨0⟩⟩
private def route : Route := ⟨rootType, SourceCoreMappingWithDefault.type outerLayout, innerLayout.valueType,
  [.index outerLayout key innerType, .index innerLayout key leaf], none⟩
private theorem preparedExists : (prepare context 100 route Word.zero (fun _ => Word.zero)).toOption.isSome = true := by cbv
private def prepared := (prepare context 100 route Word.zero (fun _ => Word.zero)).toOption.get preparedExists
private theorem preparedBy : prepare context 100 route Word.zero (fun _ => Word.zero) = .ok prepared := except_get _ preparedExists
private theorem routed : routeSteps checked checked.signatures source site binder.id rootType projections = .ok (route.steps, leaf) := by cbv
private theorem path : PreparedPath checked source site rootType projections 0 prepared.steps prepared.keys leaf :=
  (prepared_of_success routed preparedBy).2.2
private theorem arguments {registry : SourceCoreRawMetadata.Registry} {steps : List PreparedStep} {sites : List (ExpressionId × Ty)}
    (actualPath : PreparedPath checked source site rootType projections 0 steps sites leaf) :
    Arguments checked registry (noFunctions checked.catalog) [] [] source site keys actualPath resolved := by
  cases actualPath with
  | index first generated tail =>
    have shape := TypeSystem.Ty.mapping.inj first.view
    obtain ⟨rfl, rfl⟩ := shape
    have nativeKey := Except.ok.inj first.keyProjection
    cases tail with
    | index second other final =>
      have shape := TypeSystem.Ty.mapping.inj second.view
      obtain ⟨rfl, rfl⟩ := shape
      have secondKey := Except.ok.inj second.keyProjection
      cases final
      apply Arguments.index (certificate := first) (generated := generated) rfl
      · rw [← nativeKey]; exact .bool true
      · apply Arguments.index (certificate := second) (generated := other) rfl
        · rw [← secondKey]; exact .bool true
        · exact .nil
private def carrier : SourceCoreDataValues.Value := .mapping .bool innerType [(.bool true, .mapping .bool leaf [])]
private def sourceRoot : Dynamic.Value := .mapping .bool innerType [(.bool true, .mapping .bool leaf [])]
private theorem meaning : CompatibleEncoding.Means carrier sourceRoot := .mapping (.prepend (.bool _) (.mapping .empty) .empty)
private theorem sourceFault : Dynamic.ProjectionsFaults (some sourceRoot) resolved (.missingMappingDefault leaf) :=
  .indexFound (.bool _) (.head ⟨rfl, .bool _⟩) (.indexDefaultUnavailable (.bool _) .nil (by intro defaulted; cases defaulted))
private theorem noFunctionObservations : FunctionObservations checked.catalog (noFunctions checked.catalog) noIdentities := fun impossible => False.elim impossible
private theorem completed_fault {encoded : SourceCoreCompatibleValues.Encoded 100 context rootType carrier}
    (accepted : SourceCoreCompatibleValues.encode 100 context rootType carrier = .ok encoded) :
    ∃ token count after administrative,
      FaultToken checked encoded.context.registry sourceRoot prepared.steps resolved (.missingMappingDefault leaf) token count ∧
      FiniteRun [.pair (.inRight .unit encoded.value) (DataPatternValues.packValues keys)] []
        (.apply (getter prepared (.product .bool .bool)) (.var 0)) (.inLeft prepared.optionalLeaf (.word token)) after ∧
      after = [] ++ administrative ∧ administrative.length = count := by
  have represented := CompatibleEncoding.encode_represents_at (functions := noFunctions checked.catalog) accepted meaning [] []
  have typeEq : encoded.type = prepared.route.rootType := by
    have projected := encoded.projected
    have expected : checked.catalog.project rootType = .ok route.rootType := by cbv
    rw [(CompatibleMixedPreparation.of_prepare preparedBy).1]
    exact Except.ok.inj (projected.symm.trans expected)
  rw [typeEq] at represented
  obtain ⟨token, count, receipt, tree⟩ := (arguments path).faultTree represented sourceFault prepared
  obtain ⟨after, administrative, _, _, ran, appended, counted⟩ := getter_fault_run
    (.initialized (sourceType := rootType)) tree rfl (by cbv; intro impossible; cases impossible)
    faithful noFunctionObservations (by cbv) [.pair (.inRight .unit encoded.value) (DataPatternValues.packValues keys)] []
    (.product .bool .bool) (.var 0) (.var rfl)
  exact ⟨token, count, after, administrative, receipt, ran, appended, counted⟩
private def run : IO Unit := do
  match accepted : SourceCoreCompatibleValues.encode 100 context rootType carrier with
  | .error error => throw (IO.userError s!"fault path input encoding failed: {reprStr error}")
  | .ok encoded =>
    have _whole := completed_fault accepted
    let code := Expr.apply (getter prepared (.product .bool .bool)) (.var 0)
    let environment := [Value.pair (.inRight .unit encoded.value) (DataPatternValues.packValues keys)]
    match runStateful 100000 (.initial code environment []) with
    | .done (.inLeft _ (.word token)) after =>
      unless encoded.context.registry.lookup token == some (.mapping .bool leaf) do throw (IO.userError "fault path token lost inner raw mapping metadata")
      unless after.length == 2 * (checked.catalog.entries.length + 1) do throw (IO.userError "fault path administrative count changed")
    | other => throw (IO.userError s!"automatic fault path failed: {reprStr other}")
end Fault

def run : IO Unit := do
  runSuccess
  Fault.run
  IO.println "compatible path fault certificate extraction GREEN"

end Tests.SourceCoreCompatiblePathCertificates
