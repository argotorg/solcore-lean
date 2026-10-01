import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadMeaning
import Solcore.Frontend.ProgramChecking
import Solcore.Frontend.SourceCoreCallableIndexedFrames

#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Actual compatible read receipts are consumed by both semantic directions.
The native heap has an administrative closure prefix and a source cell at a
different location. Mapping initialization keeps that prefix intact. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreCompatibleExpressionReads
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CompatibleExpressionReads

private theorem except_get {α ε : Type} (result : Except ε α) (positive : result.toOption.isSome = true) :
    result = .ok (result.toOption.get positive) := by
  cases result with | error => simp [Except.toOption] at positive | ok => rfl
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"compatible_read", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "compatible_read.solc"⟩, 0, 1⟩
private def id : ExpressionId := ⟨⟨owner, 1⟩⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def binder (type : TypeSystem.Ty) : TypedBinder := ⟨⟨owner, 0⟩, "value", .mono type, [], false, none⟩
private def node (type : TypeSystem.Ty) : ExpressionNode :=
  { id, span, type, form := .reference "value" (.local (binder type).id) }
private def source (type : TypeSystem.Ty) : TypedSource :=
  { owner, inputs := [binder type], roots := [.expression id], nodes := [.expression (node type)] }
private def sourceContext (type : TypeSystem.Ty) :=
  (SourceSemantics.Context.ofSignatures signatures).withLocal (binder type).id (binder type).scheme
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def sourceEnvironment (type : TypeSystem.Ty) : Dynamic.Environment := [((binder type).id, ⟨0⟩)]
private def reason : Word := Word.ofNatModulo 17
private def faults : FunctionCalls.FaultRep := fun error token =>
  (∃ location, error = .uninitializedLocation location) ∧ token = reason
private theorem unique (type : TypeSystem.Ty) : NodeOccurrencesUnique (source type) := by
  simp [NodeOccurrencesUnique, nodeOccurrenceIds, source]
private theorem contains (type : TypeSystem.Ty) : ContainsExpression (source type) id (node type) :=
  lookupExpression?_sound (by rfl)
private theorem schemeTyped {type : TypeSystem.Ty} (typed : TypeAdmissible (sourceContext type) type) :
    SchemeWellFormed (sourceContext type) (binder type).scheme := SchemeWellFormed.monoAdmissible typed
private theorem sourceTyped {type : TypeSystem.Ty} (typed : TypeAdmissible (sourceContext type) type) :
    ExpressionHasType (source type) (sourceContext type) id type := by
  apply ExpressionHasType.ofOrdinary (node := node type) (rawType := type) (contains type)
    (.reference (.local (.head) (.head) (.intro (.empty _ _ rfl) (schemeTyped typed) []
      .empty (by intro metavariable replacement member; cases member) (by exact SchemeInstantiates.empty_apply type)
      (by simp) (by intro _ member; cases member) (.nil)))) typed typed
  · intro requirement member; cases member
  · exact .nil _
  · rfl

private theorem checkExists : (SourceCoreCompatibleCatalog.prepare signatures 10 [.bool, .mapping (.comptime .bool) .word]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 10 [.bool, .mapping (.comptime .bool) .word]).toOption.get checkExists
private def context := SourceCoreCompatibleValues.Context.initial checked
private def frameLayout : SourceCoreCallableIndexedFrames.Layout := ⟨⟨checked.catalog.definitions.length⟩⟩
private def ambient : AmbientDefinitions checked.catalog.definitions := .append _ [frameLayout.definition]
private def functions : FunctionModel checked.catalog ambient where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible
private def model := CompatibleAmbientHeap.payloadModel checked context.registry functions
private def administrativeType : Ty := .function .unit frameLayout.type
private def administrativeValue : Value := .closure .unit frameLayout.type (.var 1) [SourceCoreCallableIndexedFrames.encode frameLayout .empty]
private theorem frameRegistered : frameLayout.Registered ambient.definitions := by
  constructor
  simp [ambient, AmbientDefinitions.append, frameLayout]
private theorem administrativeTyped : RuntimeValueHasType [] administrativeValue administrativeType ambient.definitions :=
  .closure (.cons (SourceCoreCallableIndexedFrames.encode_runtime_typed [] frameRegistered .empty) .nil) (.var rfl)
private theorem initialHeap : GenericHeap.HeapRepresents model [] [administrativeType] ⟨[]⟩ [administrativeValue] :=
  GenericHeap.HeapRepresents.empty.allocate_administrative administrativeTyped
private def scope (type : Ty) : SourceCoreLocalCell.Scope := [((binder .bool).id, type)]
private theorem declarations (sourceType : TypeSystem.Ty) (type : Ty) :
    ScopeDeclarations (source sourceType) (scope type) (sourceContext sourceType) := by
  intro id declared index native selected accepted
  simp only [scope, SourceCoreLocalCell.lookup?] at selected
  split at selected
  · rename_i same
    subst id
    have actual : SourceCoreDataPlaces.rootBinder (source sourceType) (binder .bool).id = .ok (binder sourceType) := by
      simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, source, binder, node, TypeSystem.Scheme.mono]
    rw [actual] at accepted
    cases accepted
    exact .head
  · simp at selected

private def boolCode : SourceCoreBasic.LoweredExpr := ⟨.bool, OptionalCell.read .bool (.var 0) reason⟩
private theorem boolAccepted : SourceCoreCompatibleDataExpressions.lowerRead 100 context (source .bool) (scope .bool) id reason = .ok boolCode.expression := by rfl
private theorem boolRead : SourceCoreCompatibleDataExpressions.readExpression checked (source .bool) id = .ok (node .bool, boolCode.type) := by rfl
private theorem boolCertificate : LoweredRead 100 context (source .bool) (sourceContext .bool) (fun _ => reason) (scope .bool) id boolCode :=
  loweredRead_of_accepted boolAccepted boolRead (unique _) (declarations _ _)
    (sourceTyped (.bool ((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal (binder .bool).id (binder .bool).scheme)))

/-- The actual read receipt discharges the child interfaces, including all
administrative environment insertions and arbitrary typed closure payloads. -/
theorem universal_forward : GenericExpressionMeaning.Preserves model program (sourceContext .bool) [] (source .bool)
    (LoweredRead 100 context (source .bool) (sourceContext .bool) (fun _ => reason)) faults :=
  loweredRead_preserves (context := context) (faults := faults) functions (.refl _) program _ [] _ (fun _ location => ⟨⟨location, rfl⟩, rfl⟩) (unique _)
theorem universal_reverse : GenericExpressionMeaning.Reflects model program (sourceContext .bool) [] (source .bool)
    (LoweredRead 100 context (source .bool) (sourceContext .bool) (fun _ => reason)) faults :=
  loweredRead_reflects (context := context) (faults := faults) functions (.refl _) program _ [] _ (fun _ location => ⟨⟨location, rfl⟩, rfl⟩)

private def boolHeap (value : Option Dynamic.Value) : Dynamic.Heap := ⟨[⟨.bool, value, none⟩]⟩
private def world (type : Ty) : StoreTyping := [administrativeType, OptionalCell.cellType type]
private def environment (type : Ty) : Environment := [.cellRef (OptionalCell.cellType type) 1]
private theorem boolAgrees (value : Option Dynamic.Value) :
    Dynamic.EnvironmentAgrees (boolHeap value) (sourceContext .bool).locals (sourceEnvironment .bool) :=
  .cons (.intro .head) rfl (.ordinary rfl rfl) .nil
private theorem visible {sourceType : TypeSystem.Ty} {nativeType : Ty} {sourceValue : Option Dynamic.Value} {native : Value}
    (cell : GenericHeap.CellRepresents model [] [administrativeType] ⟨sourceType, sourceValue, none⟩ native nativeType)
    (_projected : checked.catalog.project sourceType = .ok nativeType) :
    GenericHeap.HeapRepresents model [1] (world nativeType) ⟨[⟨sourceType, sourceValue, none⟩]⟩ [administrativeValue, native] ∧
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) [1] (world nativeType) [] (scope nativeType)
      (sourceEnvironment sourceType) (environment nativeType) ambient.definitions := by
  obtain ⟨heap, reference⟩ := initialHeap.allocate cell Dynamic.Heap.Allocates.append
  exact ⟨heap, .cons reference (.nil .nil)⟩

theorem initialized_read : ∃ value finalStore finalMap finalWorld,
    Evaluates [(.integer 99), .cellRef (OptionalCell.cellType .bool) 1]
      [administrativeValue, .inRight .unit (.bool true)] (boolCode.expression.weakenAt 0) value finalStore ∧
    FunctionCalls.ResultRepresents model finalMap finalWorld .bool .bool faults (.value (.bool true)) value ∧
    GenericHeap.HeapRepresents model finalMap finalWorld (boolHeap (some (.bool true))) finalStore ∧
    LocationMap.Extends [1] finalMap ∧ WorldExtends (world .bool) finalWorld ∧
    AdministrativePreserved [1] [administrativeValue, .inRight .unit (.bool true)] finalMap finalStore ∧
    Dynamic.HeapMetadataExtend (boolHeap (some (.bool true))) (boolHeap (some (.bool true))) := by
  obtain ⟨heaps, environments⟩ := visible (.initialized (.bool true)) (show checked.catalog.project .bool = .ok .bool by cbv)
  have result := universal_forward boolCertificate (show (source .bool).lookupExpression? id = some (node .bool) by rfl)
    environments heaps (boolAgrees _) (GenericExpressionMeaning.agree_prefix (show EnvironmentsAgree Renaming.id (environment .bool) (environment .bool) from fun {_ _} found => found) (.integer 99))
    (Dynamic.ExpressionEvaluatesOutcome.value (.intro (contains _) (.local rfl .head (.intro .head) rfl rfl) .nil))
  have renamed : boolCode.expression.rename (Renaming.comp (Renaming.insertion 0) Renaming.id) = boolCode.expression.weakenAt 0 := by
    change boolCode.expression.rename (Renaming.insertion 0) = _
    exact Expr.rename_insertion _ _
  rw [renamed] at result
  exact result

theorem uninitialized_reflected : ∃ outcome after finalMap finalWorld,
    Dynamic.ExpressionEvaluatesOutcome program (sourceContext .bool) [] (source .bool) (sourceEnvironment .bool)
      (boolHeap none) id outcome after ∧
    FunctionCalls.ResultRepresents model finalMap finalWorld .bool .bool faults outcome (.inLeft .bool (.word reason)) ∧
    GenericHeap.HeapRepresents model finalMap finalWorld after [administrativeValue, .inLeft .bool .unit] ∧
    LocationMap.Extends [1] finalMap ∧ WorldExtends (world .bool) finalWorld ∧
    AdministrativePreserved [1] [administrativeValue, .inLeft .bool .unit] finalMap [administrativeValue, .inLeft .bool .unit] ∧
    Dynamic.HeapMetadataExtend (boolHeap none) after := by
  obtain ⟨heaps, environments⟩ := visible (.uninitialized (show checked.catalog.project .bool = .ok .bool by rfl))
    (show checked.catalog.project .bool = .ok .bool by rfl)
  have evaluated : Evaluates (environment .bool) [administrativeValue, .inLeft .bool .unit]
      boolCode.expression (.inLeft .bool (.word reason)) [administrativeValue, .inLeft .bool .unit] :=
    OptionalCell.read_failure reason (.var rfl) rfl
  exact universal_reverse boolCertificate (show (source .bool).lookupExpression? id = some (node .bool) by rfl)
    environments heaps (boolAgrees _) (ξ := Renaming.id) (fun {_ _} found => found)
    (by simpa only [Expr.rename_id] using evaluated)

private def mappingType : TypeSystem.Ty := .mapping (.comptime .bool) .word
private theorem mappingProjectionExists : (checked.catalog.project mappingType).toOption.isSome = true := by rfl
private def mappingNative := (checked.catalog.project mappingType).toOption.get mappingProjectionExists
private theorem mappingProjection : checked.catalog.project mappingType = .ok mappingNative := except_get _ mappingProjectionExists
private theorem mappingRead : SourceCoreCompatibleDataExpressions.readExpression checked (source mappingType) id =
    .ok (node mappingType, mappingNative) := by rfl
private theorem mappingTyped : TypeAdmissible (sourceContext mappingType) mappingType :=
  .mapping (.comptime (.bool ((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal (binder mappingType).id (binder mappingType).scheme)))
    (.word ((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal (binder mappingType).id (binder mappingType).scheme))
private theorem mappingCertificate {code : Expr}
    (accepted : SourceCoreCompatibleDataExpressions.lowerRead 100 context (source mappingType) (scope mappingNative) id reason = .ok code) :
    LoweredRead 100 context (source mappingType) (sourceContext mappingType)
      (fun _ => reason) (scope mappingNative) id ⟨mappingNative, code⟩ :=
  loweredRead_of_accepted accepted mappingRead (unique _) (declarations _ _) (sourceTyped mappingTyped)
private def emptyMappingHeap : Dynamic.Heap := ⟨[⟨mappingType, none, none⟩]⟩
private def initializedMappingHeap : Dynamic.Heap := ⟨[⟨mappingType, some (.mapping (.comptime .bool) .word []), none⟩]⟩

/-- Lazy initialization preserves the raw staged key header and keeps the
administrative closure at Core index zero, outside the source location map. -/
theorem lazy_mapping_read {code : Expr}
    (accepted : SourceCoreCompatibleDataExpressions.lowerRead 100 context (source mappingType) (scope mappingNative) id reason = .ok code) :
    ∃ value finalStore finalMap finalWorld,
    Evaluates (environment mappingNative) [administrativeValue, .inLeft mappingNative .unit] code value finalStore ∧
    FunctionCalls.ResultRepresents model finalMap finalWorld mappingType mappingNative faults
      (.value (.mapping (.comptime .bool) .word [])) value ∧
    GenericHeap.HeapRepresents model finalMap finalWorld initializedMappingHeap finalStore ∧
    LocationMap.Extends [1] finalMap ∧ WorldExtends (world mappingNative) finalWorld ∧
    AdministrativePreserved [1] [administrativeValue, .inLeft mappingNative .unit] finalMap finalStore ∧
    Dynamic.HeapMetadataExtend emptyMappingHeap initializedMappingHeap := by
  obtain ⟨heaps, environments⟩ := visible (.uninitialized mappingProjection) mappingProjection
  have sourceRun : Dynamic.ExpressionEvaluatesOutcome program (sourceContext mappingType) [] (source mappingType)
      (sourceEnvironment mappingType) emptyMappingHeap id (.value (.mapping (.comptime .bool) .word [])) initializedMappingHeap :=
    .value (.intro (contains _) (.localEmptyMapping rfl .head (.intro .head) rfl rfl rfl (.intro (.intro .head) .head)) .nil)
  have locals : Dynamic.EnvironmentAgrees emptyMappingHeap (sourceContext mappingType).locals (sourceEnvironment mappingType) :=
    .cons (.intro .head) rfl (.ordinary rfl rfl) .nil
  have meaning : GenericExpressionMeaning.Preserves model program (sourceContext mappingType) [] (source mappingType)
      (LoweredRead 100 context (source mappingType) (sourceContext mappingType) (fun _ => reason)) faults :=
    loweredRead_preserves (context := context) (faults := faults) functions (.refl _) program
    (sourceContext mappingType) [] (fun _ => reason) (fun _ location => ⟨⟨location, rfl⟩, rfl⟩) (unique mappingType)
  have result := meaning (mappingCertificate accepted) (show (source mappingType).lookupExpression? id = some (node mappingType) by rfl)
    environments heaps locals (ξ := Renaming.id) (fun {_ _} found => found) sourceRun
  simpa only [Expr.rename_id, node, emptyMappingHeap] using result

/-- Mapping reflection consumes only the actual completed Core run. The source
lazy-initialization trace and final source heap are conclusions. -/
theorem lazy_mapping_reflected {code : Expr} {value : Value} {finalStore : Store}
    (accepted : SourceCoreCompatibleDataExpressions.lowerRead 100 context (source mappingType) (scope mappingNative) id reason = .ok code)
    (completed : Evaluates (environment mappingNative) [administrativeValue, .inLeft mappingNative .unit] code value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program (sourceContext mappingType) [] (source mappingType)
        (sourceEnvironment mappingType) emptyMappingHeap id outcome after ∧
      FunctionCalls.ResultRepresents model finalMap finalWorld mappingType mappingNative faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends [1] finalMap ∧ WorldExtends (world mappingNative) finalWorld ∧
      AdministrativePreserved [1] [administrativeValue, .inLeft mappingNative .unit] finalMap finalStore ∧
      Dynamic.HeapMetadataExtend emptyMappingHeap after := by
  obtain ⟨heaps, environments⟩ := visible (.uninitialized mappingProjection) mappingProjection
  have locals : Dynamic.EnvironmentAgrees emptyMappingHeap (sourceContext mappingType).locals (sourceEnvironment mappingType) :=
    .cons (.intro .head) rfl (.ordinary rfl rfl) .nil
  have meaning : GenericExpressionMeaning.Reflects model program (sourceContext mappingType) [] (source mappingType)
      (LoweredRead 100 context (source mappingType) (sourceContext mappingType) (fun _ => reason)) faults :=
    loweredRead_reflects (context := context) (faults := faults) functions (.refl _) program
      (sourceContext mappingType) [] (fun _ => reason) (fun _ location => ⟨⟨location, rfl⟩, rfl⟩)
  exact meaning (mappingCertificate accepted) (show (source mappingType).lookupExpression? id = some (node mappingType) by rfl)
    environments heaps locals (ξ := Renaming.id) (fun {_ _} found => found)
    (by simpa only [Expr.rename_id] using completed)

private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def assertTrue (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)
private def checkedSource (checkedProgram : CheckedProgram) (name : String) : IO TypedSource := do
  let signature ← match checkedProgram.signatures.functions.filter (·.name == name) with
    | [signature] => pure signature | _ => throw (IO.userError "read fixture function missing")
  match SourceSpecializationWorklist.run checkedProgram [⟨signature.id, []⟩] 100 with
  | .ok (.complete plan) => match plan.specializations with
    | [specialized] => pure specialized.function.typedBody
    | _ => throw (IO.userError "read fixture specialization changed")
  | other => throw (IO.userError s!"read fixture specialization: {reprStr other}")

/-- Checked source uses the actual compatible callback; the erased certificate
is extracted from the same successful call used to build the native program. -/
def run : IO Unit := do
  let checkedProgram ← get "source checker" (checkProgram {
    entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
      "function initialized(value: Bool) returns (Bool) { return value; }",
      "function absent() returns (Bool) { let value: Bool; return value; }",
      "function lazy() returns (mapping(Word => Word)) { let value: mapping(Word => Word); return value; }"
    ]}] })
  for name in ["initialized", "absent", "lazy"] do
    let source ← checkedSource checkedProgram name
    let (readNode, selected) ← match source.nodes.filterMap (fun
      | .expression node => match node.form with
        | .reference _ (.local binder) => some (node, binder) | _ => none
      | _ => none) with
      | [found] => pure found | _ => throw (IO.userError "read fixture occurrence count changed")
    let declared ← get "source declaration" (SourceCoreDataPlaces.rootBinder source selected)
    let checked ← get "read catalog" (SourceCoreCompatibleCatalog.prepare checkedProgram.signatures 100 [declared.scheme.body])
    let context := SourceCoreCompatibleValues.Context.initial checked
    let type ← get "read projection" (checked.catalog.project declared.scheme.body)
    let scope := [(selected, type)]
    let expression ← match accepted : SourceCoreCompatibleDataExpressions.lowerRead 100 context source scope readNode.id reason with
      | .ok code =>
        have receipt : Nonempty (Certificate 100 context source scope readNode.id reason code) := of_accepted accepted
        let _receipt := receipt
        pure code
      | .error error => throw (IO.userError s!"actual compatible read: {reprStr error}")
    let initial := if name == "initialized" then OptionalCell.allocateInitialized type (.bool true) else OptionalCell.allocate type
    let native : Core.Program := ⟨LanguageResult.resultType type, .letE initial expression, checked.catalog.definitions⟩
    assertTrue native.check "native checker rejected actual read"
    let expected ← if name == "initialized" then pure (.inRight .word (.bool true))
      else if name == "absent" then pure (.inLeft type (.word reason))
      else do
        let encoded ← get "empty mapping encoder" (SourceCoreCompatibleValues.encode 100 context declared.scheme.body (.mapping .word .word []))
        pure (.inRight .word encoded.value)
    for fuel in [0, 1, 3, 1000] do
      let completed := match native.runStateful fuel with
        | .outOfFuel checkpoint => Core.runStateful 1000 checkpoint
        | other => other
      match completed with
      | .done value store =>
        assertTrue (value == expected) s!"{name} read outcome mismatch"
        assertTrue (store.length == 1) s!"{name} read allocated an extra source cell"
        if name == "lazy" then
          match value with
          | .inRight .word payload => assertTrue (store[0]? == some (.inRight .unit payload)) "lazy read did not initialize the original cell"
          | _ => throw (IO.userError "lazy read failed")
      | other => throw (IO.userError s!"{name} native completion: {reprStr other}")
  IO.println "compatible actual read receipts and native resume GREEN"

end Tests.SourceCoreCompatibleExpressionReads
