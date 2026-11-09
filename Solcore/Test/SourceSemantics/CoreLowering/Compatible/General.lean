import Solcore.Frontend.SourceCore.GeneralFunctions
import Solcore.Frontend.SourceCore.Compatible
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionGeneralBuiltins
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionTyped
import Solcore.Test.Frontend.Source.CompilerFeatureSupport
import Solcore.Frontend.SourceCore.CompatibleFunctions
import Solcore.Frontend.SourceCore.Internal.Carriers
import Solcore.Frontend.ProgramChecking
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.DiagnosticOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionRuntime
import Solcore.Test.SourceSemantics.CoreLowering.UnifiedCorpusSupport
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceWriteback
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceKeys
import Solcore.Frontend.SourceCore.Internal.CallableOutputs
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceReflection
import Solcore.Frontend.SourceCore.Internal.CallableViews
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.Statements
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.Paths
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogAndSpecialization
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaValues
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CallEvidence

/-!
# Compatible general tests

General expressions and indices, heaps, functions, marked ledgers, inputs, outputs and reflection.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleFunctions
/-! Actual checked functions use compatible leaves through the common
contextual function compiler. Evidence, local instances and coercions share
the original plan and stage descriptors. Invocation evaluates cached Core. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleFunctions
open Solcore Solcore.Frontend SourceInference
abbrev DataValue := SourceCoreCompatibleValues.Value

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Marker<T> {}", "impl Marker<mapping(Word => Word)> {}",
    "function keep<T>(value: T) returns (T) where T: Marker { return value; }",
    "function local(table: mapping(Word => Word)) returns (mapping(Word => Word)) { let f = lam(item) { return keep(item); }; return f(table); }",
    "function alias(table: mapping(@Word => Word)) returns (Word) { let f = lam(item) { return item; }; let copied = f(table); return copied[@Word]; }",
    "trait Coerce<From, To> { function coerce(value: From) returns (To); }",
    "impl Coerce<Bool, mapping(Word => Word)> { function coerce(value: Bool) returns (mapping(Word => Word)) { let table: mapping(Word => Word); return table; } }",
    "function converted(flag: Bool) returns (mapping(Word => Word)) { return flag; }",
    "function marked(first: Bool, second: Bool) returns (Bool) { let copied: Bool = first; return second; }"
  ]}]
}

private def check (program : CheckedProgram) (name : String) (arguments : List DataValue)
    (expected : DataValue) (marked : Bool := false) : IO Unit := do
  let root ← match program.signatures.functions.filter (·.name == name) with
    | [signature] => pure signature
    | _ => throw (IO.userError s!"compatible function root missing: {name}")
  let plan ← match SourceSpecializationWorklist.run program [⟨root.id, []⟩] 128 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"compatible worklist failed: {reprStr result}")
  let plan ← match SourceCompilationPlan.prepareExecutablePlanEvidence program plan with
    | .ok plan => pure plan
    | .error error => throw (IO.userError s!"compatible plan failed: {reprStr error}")
  let entries ← match SourceCompilationPlan.localLambdaCatalog plan with
    | .ok entries => pure entries
    | .error error => throw (IO.userError s!"compatible local discovery failed: {reprStr error}")
  let types := (SourceCorePlanCatalog.planTypes plan ++ entries.flatMap (fun entry =>
    SourceCorePlanCatalog.sourceTypes (entry.source.applySubstitution entry.substitution))).filter
      SourceCoreDataCatalog.closed |>.eraseDups
  let checked ← match SourceCoreCompatibleCatalog.prepare program.signatures 300 types with
    | .ok checked => pure checked
    | .error error => throw (IO.userError s!"compatible catalog failed: {reprStr error}")
  let strict ← match SourceCoreDataCatalog.prepare program.signatures 300 types true with
    | .ok strict => pure strict
    | .error error => throw (IO.userError s!"diagnostic catalog failed: {reprStr error}")
  let context := SourceCoreCompatibleValues.Context.initial checked
  let reference := Core.OptionalCell.referenceType .bool
  let markerDefinitions : Core.DataEnvironment := [⟨[.unit]⟩, ⟨[reference]⟩,
    ⟨[.product reference reference]⟩]
  let allocate : SourceCoreSourceCells.Allocator := SourceCoreSourceCells.marked fun request =>
    pure ⟨⟨checked.catalog.definitions.length + request.scope.length⟩,
      SourceCoreSourceCells.captureType request.scope⟩
  let representation : SourceCoreGeneralFunctions.Representation := {
    expressions := {SourceCoreCompatibleDataExpressions.functionPolicy 300 context with
      sourceCells := if marked then some allocate else none}
    allowStaged := true
    loops := fun _ _ _ _ child => SourceCoreCompatibleDataExpressions.loopPolicy context child
  }
  let project : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty := fun type =>
    (checked.project type).map (·.type) |>.mapError fun _ => .initializerMetadataMismatch ⟨⟨root.id, 0⟩⟩
  let locals ← match SourceCoreLocalPolymorphism.prepareWithProjection project plan with
    | .ok locals => pure locals
    | .error error => throw (IO.userError s!"compatible local projection failed: {reprStr error}")
  let functions ← match plan.specializations.reverse.mapM
      (SourceCoreGeneralFunctions.prepareFunctionWithRepresentation program representation) with
    | .ok functions => pure functions
    | .error error => throw (IO.userError s!"compatible signatures failed: {reprStr error}")
  let globals := functions.map (·.signature)
  let key : SourceSpecialization.SpecializationKey := ⟨root.id, []⟩
  let diagnostics ← match SourceCoreDataPlaceFaultSites.prepare strict program.signatures plan key with
    | .ok diagnostics => pure diagnostics
    | .error error => throw (IO.userError s!"compatible diagnostics failed: {reprStr error}")
  let table ← match SourceCoreStageCodebook.prepareWithProjection program plan project with
    | .ok table => pure table
    | .error error => throw (IO.userError s!"compatible descriptors failed: {reprStr error}")
  let callableDiagnostics ← match SourceCoreCallableFaultSites.prepare plan table diagnostics.rootTable with
    | .ok diagnostics => pure diagnostics
    | .error error => throw (IO.userError s!"compatible call diagnostics failed: {reprStr error}")
  let native : SourceCoreGeneralFunctions.CallableContext := ⟨table, callableDiagnostics⟩
  let locals ← match locals.withCallableContracts (fun caller initializer active =>
      table.idAt? (.lambda caller initializer active)) with
    | .ok locals => pure locals
    | .error error => throw (IO.userError s!"compatible local descriptors failed: {reprStr error}")
  let diagnostics := {diagnostics with rootTable := callableDiagnostics.rootTable}
  let closures ← match functions.mapM (SourceCoreGeneralFunctions.compileClosureWithRepresentation
      program representation program.signatures plan globals diagnostics locals (some native) 128) with
    | .ok closures => pure closures
    | .error error => throw (IO.userError s!"{name} compatible body failed: {reprStr error}")
  let function ← match functions.find? (·.signature.key == key) with
    | some function => pure function
    | none => throw (IO.userError "compatible compiled root missing")
  let mut inputContext := context
  let mut lowered := []
  for ((binder, type), argument) in function.inputs.zip arguments do
    let encoded ← match SourceCoreCompatibleValues.encode 300 inputContext binder.scheme.body argument with
      | .ok encoded => pure encoded
      | .error error => throw (IO.userError s!"compatible input failed: {reprStr error}")
    inputContext := encoded.context
    let literal ← match SourceCoreCompatibleDataExpressions.quote encoded.value with
      | some literal => pure literal
      | none => throw (IO.userError "compatible data input contained code")
    lowered := lowered ++ [⟨type, Core.LanguageResult.success literal⟩]
  let body ← match SourceCoreGeneralFunctions.assembleCall globals functions closures key
      (SourceCoreCalls.packArguments lowered) with
    | .ok body => pure body
    | .error error => throw (IO.userError s!"compatible assembly failed: {reprStr error}")
  let executable : Core.Program := ⟨Core.LanguageResult.resultType function.signature.resultType,
    body, checked.catalog.definitions ++ (if marked then markerDefinitions else [])⟩
  unless executable.check do throw (IO.userError s!"{name} failed actual compatible Core checker")
  for initialFuel in [0, 8, 65536] do
    let result := executable.runStateful initialFuel
    let result := match result with
      | .outOfFuel state => Core.runStateful 65536 state
      | result => result
    match Core.LanguageResult.observeResult result with
    | .succeeded value store =>
        let resultType := function.specialized.function.inferredBodyType
        let decoded ← match SourceCoreCompatibleValues.decode 300 inputContext resultType value with
          | .ok value => pure value
          | .error error => throw (IO.userError s!"compatible output failed: {reprStr error}")
        unless decoded == expected do throw (IO.userError s!"{name} compatible result changed: {reprStr decoded}")
        if marked then
          let marker := fun n captures => SourceCoreHeapMarkers.markerValue
            ⟨⟨checked.catalog.definitions.length + n⟩,
              if n = 0 then .unit else if n = 1 then reference else .product reference reference⟩ captures
          let expectedTail : List Core.Value := [marker 0 .unit, .inRight .unit (.bool false),
            marker 1 (.cellRef (Core.OptionalCell.cellType .bool) 2), .inRight .unit (.bool true),
            marker 2 (.pair (.cellRef (Core.OptionalCell.cellType .bool) 4)
              (.cellRef (Core.OptionalCell.cellType .bool) 2)), .inRight .unit (.bool false)]
          unless store.drop 1 == expectedTail do
            throw (IO.userError s!"marked root parameters captured temporary/global cells: {reprStr store}")
    | result => throw (IO.userError s!"{name} compatible execution failed: {reprStr result}")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"compatible function fixture rejected: {reprStr error}")
  let w := fun n => Core.Word.ofNatModulo n
  let table : DataValue := .mapping .word .word [(.word (w 1), .word (w 7))]
  check program "local" [table] table
  check program "alias" [.mapping (.proxy (.comptime .word)) .word
    [(.proxy (.comptime .word), .word (w 7))]] (.word (w 0))
  check program "alias" [.mapping (.proxy .word) .word
    [(.proxy .word, .word (w 7))]] (.word (w 7))
  check program "converted" [.bool true] (.mapping .word .word [])
  check program "marked" [.bool false, .bool true] (.bool true) true
  IO.println "compatible general functions, qualified local evidence, coercions and resumed Core execution GREEN"

end Tests.SourceCoreCompatibleFunctions
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleGeneralExpressions
#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! General product-key indexing discharges its own child meanings. The theorem
fixture has an ambient closure and a typed hidden Integer slot; generated
comparators allocate after that prefix while lazy source initialization persists. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
set_option linter.unusedSimpArgs false
namespace Tests.SourceCoreCompatibleGeneralExpressions
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleExpressionGeneral CompatiblePayload GeneralHeap ReadOnly

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"index_meaning", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "index_meaning.solc"⟩, 0, 4⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def keyType : TypeSystem.Ty := .product .bool .bool
private def mappingType : TypeSystem.Ty := .mapping keyType .bool
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "table", .mono mappingType, [], false, none⟩
private def baseNode : ExpressionNode := { id := id 0, span, type := mappingType, form := .reference "table" (.local binder.id) }
private def trueNode : ExpressionNode := { id := id 1, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def falseNode : ExpressionNode := { id := id 2, span, type := .bool, form := .reference "false" (.builtinBoolean false) }
private def keyNode : ExpressionNode := { id := id 3, span, type := keyType, form := .tuple [id 1, id 2] }
private def indexNode : ExpressionNode := { id := id 4, span, type := .bool, form := .index (id 0) (id 3) }
private def unaryNode : ExpressionNode := { id := id 5, span, type := .bool, form := .unary .logicalNot (id 4) }
private def source : TypedSource := { owner, inputs := [binder], roots := [.expression (id 5)], nodes := [.expression baseNode, .expression trueNode, .expression falseNode, .expression keyNode, .expression indexNode, .expression unaryNode] }
private def context : SourceSemantics.Context := (SourceSemantics.Context.ofSignatures signatures).withLocal binder.id binder.scheme
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def compilation : SourceCoreFunctions.Context := ⟨⟨[], [], [], []⟩, ⟨owner, []⟩, [], 0, [], Word.zero⟩
private def noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .ok .unit
private def reason : Word := Word.ofNatModulo 17
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem metadata {expression : ExpressionId} {node : ExpressionNode} (found : source.lookupExpression? expression = some node) :
    node.requirements = CompatibleExpressionLiterals.owned node.form ∧ node.coercions = [] := by
  have member := (lookupExpression?_sound found).1
  simp only [source, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, Node.expression.injEq] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
private theorem boolAdmitted : TypeAdmissible context .bool :=
  .bool ((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal binder.id binder.scheme)
private theorem keyAdmitted : TypeAdmissible context keyType := .product boolAdmitted boolAdmitted
private theorem mappingAdmitted : TypeAdmissible context mappingType := .mapping keyAdmitted boolAdmitted
private theorem baseTyped : ExpressionHasType source context (id 0) mappingType := by
  apply ExpressionHasType.ofOrdinary (node := baseNode) (rawType := mappingType) (lookupExpression?_sound (by rfl))
    (.reference (.local (.head) (.head) (.intro (.empty _ _ rfl) (SchemeWellFormed.monoAdmissible mappingAdmitted) []
      .empty (by intro metavariable replacement member; cases member) (by exact SchemeInstantiates.empty_apply mappingType)
      (by simp) (by intro _ member; cases member) (.nil)))) mappingAdmitted mappingAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem trueTyped : ExpressionHasType source context (id 1) .bool := by
  apply ExpressionHasType.ofOrdinary (node := trueNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.reference (.builtinBoolean true)) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem falseTyped : ExpressionHasType source context (id 2) .bool := by
  apply ExpressionHasType.ofOrdinary (node := falseNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.reference (.builtinBoolean false)) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem keyTyped : ExpressionHasType source context (id 3) keyType := by
  apply ExpressionHasType.ofOrdinary (node := keyNode) (rawType := keyType)
    (lookupExpression?_sound (by cbv)) (.tuple (.cons trueTyped (.cons falseTyped (.nil _)))) keyAdmitted keyAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem indexTyped : ExpressionHasType source context (id 4) .bool := by
  apply ExpressionHasType.ofOrdinary (node := indexNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.index baseTyped keyTyped) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem unaryTyped : ExpressionHasType source context (id 5) .bool := by
  apply ExpressionHasType.ofOrdinary (node := unaryNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.unary indexTyped .logicalNot) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem indexSyntax : CompatibleExpressionGeneral.Syntax source (id 4) :=
  .index (node := indexNode) (keyNode := keyNode) (by cbv) rfl (by cbv)
    (.fragment (.fragment (.fragment (.fragment (.primitive (.product (.read (node := baseNode) (by cbv) rfl)))))))
    (.pair (node := keyNode) (by cbv) rfl
      (.fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal (node := trueNode) (by cbv) (.bool _ _))))))))
      (.fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal (node := falseNode) (by cbv) (.bool _ _)))))))))
private theorem syntaxTree : CompatibleExpressionGeneral.Syntax source (id 5) :=
  .unary (node := unaryNode) (by cbv) rfl indexSyntax
private theorem contextValid : CompatibleExpressionLiterals.ContextValid [] context [] := by
  refine ⟨rfl, ⟨?_, ?_⟩, ?_⟩
  · simp [RequirementIdsUnique, context, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal]
  · intro requirement member; cases member
  · constructor
    · intro goal evidence found; cases found
    · intro predicate member; cases member
private theorem checkExists : (SourceCoreCompatibleCatalog.prepare signatures 10 [mappingType]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 10 [mappingType]).toOption.get checkExists
private def values := SourceCoreCompatibleValues.Context.initial checked
private theorem nativeExists : (checked.catalog.project mappingType).toOption.isSome = true := by cbv
private def nativeType := (checked.catalog.project mappingType).toOption.get nativeExists
private theorem projected : checked.catalog.project mappingType = .ok nativeType := by cbv
private def scope : SourceCoreLocalCell.Scope := [(binder.id, nativeType)]
private theorem declarations : CompatibleExpressionReads.ScopeDeclarations source scope context := by
  intro actual declared index native selected accepted
  simp only [scope, SourceCoreLocalCell.lookup?] at selected
  split at selected
  · rename_i same
    subst actual
    have actual : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder := by rfl
    rw [actual] at accepted
    cases accepted
    exact .head
  · simp at selected
private abbrev policy := SourceCoreCompatibleDataExpressions.functionPolicy 100 values
private theorem certified {code : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 5 compilation source scope (id 5) (fun _ => reason) = .ok code) :
    Tree 100 values source context [] (fun _ => reason) scope (id 5) code :=
  tree_of_functions unique declarations (by rfl) rfl rfl ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩
    (fun _ _ _ found => (metadata found).2) syntaxTree (by cbv) unaryTyped accepted

private def frameLayout : SourceCoreCallableIndexedFrames.Layout := ⟨⟨checked.catalog.definitions.length⟩⟩
private def ambient : AmbientDefinitions checked.catalog.definitions := .append _ [frameLayout.definition]
private def functions : FunctionModel checked.catalog ambient where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible
private def identities : Dynamic.Value → Word → Prop := fun _ _ => False
private theorem faithful : DataEquality.IdentityFaithful identities :=
  ⟨fun impossible => False.elim impossible, fun impossible => False.elim impossible⟩
private theorem functionLeaves : CompatibleEquality.FunctionObservations checked.catalog functions identities :=
  fun impossible => False.elim impossible
private theorem functionTypes : CompatiblePayload.FunctionRuntimeViews functions := fun impossible => False.elim impossible

/-- Raw staging aliases remain distinct values even when their projected native
types coincide; the independently specified equality retains that distinction. -/
theorem proxy_aliases_distinct :
    ¬ Dynamic.ValueEquivalent (.proxy (.comptime .word)) (.proxy .word) := by
  rintro ⟨same, _⟩
  cases same

/-- Mapping contents have no comparable source-value witness. -/
theorem mapping_keys_unmatched {key value : TypeSystem.Ty}
    {entries : List (Dynamic.Value × Dynamic.Value)} {other : Dynamic.Value} :
    ¬ Dynamic.ValueEquivalent (.mapping key value entries) other := by
  rintro ⟨_, comparable⟩
  cases comparable
private def model := CompatibleAmbientHeap.payloadModel checked values.registry functions
private def faults : FunctionCalls.FaultRep := fun error token =>
  (((∃ location, error = .uninitializedLocation location) ∧ token = reason) ∨
   (∃ key value tag, MetadataRep values.registry (.mapping key value) tag ∧ error = .missingMappingDefault value ∧ token = reason.add tag)) ∨
  ∃ code, error = .panic code ∧ token = Solcore.Frontend.SourceCorePanics.reason code
/-- Every panic fails with its code's reason. -/
private instance : FunctionCalls.FaultTokens faults := ⟨fun code => .inr ⟨code, rfl, rfl⟩⟩
private theorem uninitialized : ∀ (id : ExpressionId) location, faults (.uninitializedLocation location) ((fun _ => reason) id) :=
  fun _ location => .inl (.inl ⟨⟨location, rfl⟩, rfl⟩)
private theorem missing : ∀ (id : ExpressionId) key value tag, MetadataRep values.registry (.mapping key value) tag →
    faults (.missingMappingDefault value) (((fun _ => reason) id).add tag) :=
  fun _ key value tag owned => .inl (.inr ⟨key, value, tag, owned, rfl, rfl⟩)
private def administrativeType : Ty := .function .unit frameLayout.type
private def administrativeValue : Value := .closure .unit frameLayout.type (.var 1) [SourceCoreCallableIndexedFrames.encode frameLayout .empty]
private theorem frameRegistered : frameLayout.Registered ambient.definitions := by
  constructor
  simp [ambient, AmbientDefinitions.append, frameLayout]
private theorem administrativeTyped : RuntimeValueHasType [] administrativeValue administrativeType ambient.definitions :=
  .closure (.cons (SourceCoreCallableIndexedFrames.encode_runtime_typed [] frameRegistered .empty) .nil) (.var rfl)
private def world : StoreTyping := [administrativeType, OptionalCell.cellType nativeType]
private def store : Store := [administrativeValue, .inLeft nativeType .unit]
private def environment : Environment := [.cellRef (OptionalCell.cellType nativeType) 1]
private def sourceEnvironment : Dynamic.Environment := [(binder.id, ⟨0⟩)]
private def before : Dynamic.Heap := ⟨[⟨mappingType, none, none⟩]⟩
private def after : Dynamic.Heap := ⟨[⟨mappingType, some (.mapping keyType .bool []), none⟩]⟩
private theorem initial : GenericHeap.HeapRepresents model [1] world before store ∧
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) [1] world [] scope sourceEnvironment environment ambient.definitions := by
  have empty := (GenericHeap.HeapRepresents.empty (model := model)).allocate_administrative administrativeTyped
  obtain ⟨heap, reference⟩ := empty.allocate (.uninitialized projected) Dynamic.Heap.Allocates.append
  exact ⟨heap, .cons reference (.nil .nil)⟩
private theorem locals : Dynamic.EnvironmentAgrees before context.locals sourceEnvironment :=
  .cons (.intro .head) rfl (.ordinary rfl rfl) .nil
private theorem actualTyped : RuntimeEnvironmentHasTypes world (.integer 99 :: administrativeValue :: environment)
    [.integer, administrativeType, .cell (OptionalCell.cellType nativeType)] ambient.definitions :=
  .cons .integer (.cons (administrativeTyped.weaken ⟨world, rfl⟩) (.cons (.cellRef rfl) .nil))
private def ξ : Renaming := Renaming.comp (Renaming.insertion 0) (Renaming.insertion 0)
private theorem agrees : EnvironmentsAgree ξ environment (.integer 99 :: administrativeValue :: environment) :=
  GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix (show EnvironmentsAgree Renaming.id environment environment from fun {_ _} found => found) administrativeValue) (.integer 99)
private theorem indexTrace : Dynamic.ExpressionEvaluatesOutcome program context [] source sourceEnvironment before (id 4) (.value (.bool false)) after := by
  apply Dynamic.ExpressionEvaluatesOutcome.value
  apply Dynamic.ExpressionEvaluates.intro (raw := .bool false) (middle := after) (lookupExpression?_sound (node := indexNode) (by cbv))
  · change Dynamic.ExpressionFormEvaluates program context [] source sourceEnvironment before (.index (id 0) (id 3)) [] [] (.bool false) after
    apply Dynamic.ExpressionFormEvaluates.indexDefault (coercions := []) rfl
    · exact .intro (lookupExpression?_sound (node := baseNode) (by rfl))
        (.localEmptyMapping rfl .head (.intro .head) rfl rfl rfl (.intro (.intro .head) .head)) .nil
    · exact .intro (lookupExpression?_sound (node := keyNode) (by cbv))
        (.tuple rfl (.cons (.intro (lookupExpression?_sound (node := trueNode) (by cbv)) (.builtinBoolean rfl) .nil)
          (.cons (.intro (lookupExpression?_sound (node := falseNode) (by cbv)) (.builtinBoolean rfl) .nil) .nil))
          (.cons (.singleton _))) .nil
    · exact .nil
    · exact .bool
  · exact .nil

private theorem sourceTrace : Dynamic.ExpressionEvaluatesOutcome program context [] source sourceEnvironment before
    (id 5) (.value (.bool true)) after := by
  cases indexTrace with
  | value trace =>
    exact .value (.intro (lookupExpression?_sound (node := unaryNode) (by cbv))
      (.unary (owned := []) rfl trace (.primitive (.logicalNot false))) .nil)

/-- A real accepted expression constructs its own comparator execution after
source initialization, retaining an ambient closure that is not base-typable. -/
theorem accepted_lazy_preserves {code : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 5 compilation source scope (id 5) (fun _ => reason) = .ok code) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (.integer 99 :: administrativeValue :: environment) store (code.expression.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents model finalMap finalWorld .bool code.type faults (.value (.bool true)) value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends [1] finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved [1] store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  preserves (values := values) functions (.refl _) faithful functionLeaves functionTypes program [] contextValid unique uninitialized missing (certified accepted)
    (show source.lookupExpression? (id 5) = some unaryNode by cbv) initial.2 initial.1 locals agrees actualTyped sourceTrace

/-- Source traces and effects follow from completion alone; no source run or
helper evaluation is supplied as a premise. -/
theorem accepted_index_reflects {code : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 5 compilation source scope (id 5) (fun _ => reason) = .ok code)
    {value : Value} {finalStore : Store} (completed : Evaluates (.integer 99 :: administrativeValue :: environment) store (code.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context [] source sourceEnvironment before (id 5) outcome after ∧
      FunctionCalls.ResultRepresents model finalMap finalWorld .bool code.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends [1] finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved [1] store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  reflects (values := values) functions (.refl _) faithful functionLeaves functionTypes program [] contextValid uninitialized missing (certified accepted)
    (show source.lookupExpression? (id 5) = some unaryNode by cbv) initial.2 initial.1 locals agrees actualTyped completed


private def rawWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Key { Key(Bool) }",
    "enum Missing { Missing(Word) }",
    "enum Box { Box(Bool) }",
    "function product(m: mapping((Bool, Bool) => Bool)) returns (Bool) { return m[(true, false)]; }",
    "function lazyProduct() returns (Bool) { let m: mapping((Bool, Bool) => Bool); return m[(true, false)]; }",
    "function nestedProduct(m: mapping(((Bool, Bool), Word) => Bool)) returns (Bool) { return m[((true, false), 7)]; }",
    "function nestedGeneral(m: mapping((Bool, Bool) => mapping(@Word => Bool))) returns (Bool) { return m[(true, false)][@Word]; }",
    "function proxy(m: mapping(@Word => Bool)) returns (Bool) { return m[@Word]; }",
    "function nominal(m: mapping(Key => Bool)) returns (Bool) { return m[Key(true)]; }",
    "function mappingKey(m: mapping(mapping(Bool => Bool) => Bool), k: mapping(Bool => Bool)) returns (Bool) { return m[k]; }",
    "function operator(m: mapping((Bool, Bool) => Bool)) returns (Bool) { return !m[(true, false)] || m[(false, true)]; }",
    "function paired(m: mapping((Bool, Bool) => Bool)) returns ((Bool, Bool)) { return (m[(true, false)], !m[(false, true)]); }",
    "function choose(m: mapping((Bool, Bool) => Bool)) returns (Bool) { return m[(true, false)] ? m[(false, true)] : !m[(true, false)]; }",
    "function construct(m: mapping((Bool, Bool) => Bool)) returns (Box) { return Box(!m[(true, false)]); }",
    "function keyIndex(m: mapping((Bool, Bool) => Bool), n: mapping(Bool => Bool)) returns (Bool) { return n[m[(true, false)]]; }",
    "function skipped() returns (Box) { let m: mapping((Bool, Bool) => Bool); let missing: Bool; return Box(false && m[(true, missing)]); }",
    "function constructorFault() returns (Box) { let m: mapping((Bool, Bool) => Bool); let missing: Bool; return Box(m[(true, missing)]); }",
    "function parent(seed: Bool) returns (Box) { let make = lam(item) -> Box { let m: mapping((Bool, Bool) => Bool); return Box(!m[(seed, item)]); }; return make(false); }",
    "function keyFault() returns (Bool) { let m: mapping((Bool, Bool) => Bool); let missing: Bool; return m[(true, missing)]; }",
    "function defaultFault() returns (Missing) { let m: mapping((Bool, Bool) => Missing); return m[(true, false)]; }"]}] }

def run : IO Unit := do
  let code ← SourceCompilerFeatureSupport.get "general index actual lowering"
    (SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 5 compilation source scope (id 5) (fun _ => reason))
  let state : Core.State := ⟨.eval (code.expression.rename ξ) (.integer 99 :: administrativeValue :: environment), [], store⟩
  let complete := Core.runStateful 30000 state
  match Core.LanguageResult.observeResult complete with
  | .succeeded (.bool true) finalStore =>
      SourceCompilerFeatureSupport.require (finalStore[0]? == some administrativeValue) "general index changed ambient closure"
  | _ => throw (IO.userError "general index static fixture failed")
  for fuel in [0, 5, 23] do
    match Core.runStateful fuel state with
    | .outOfFuel suspended =>
        SourceCompilerFeatureSupport.require (Core.runStateful 30000 suspended == complete) "general index resume changed native result/store"
    | _ => throw (IO.userError "general index prefix unexpectedly completed")
  let checked ← SourceCompilerFeatureSupport.get "general index source checker" (checkProgram rawWorkspace)
  let product ← SourceCompilerFeatureSupport.compileNamed checked "product"
  let pair : SourceCoreExecution.Value := .product (.bool true) (.bool false)
  let duplicate : SourceCoreExecution.Value := .mapping keyType .bool [(pair, .bool true), (pair, .bool false)]
  SourceCompilerFeatureSupport.require ((← product.run [duplicate]) == .bool true) "compound key lost first duplicate"
  product.checkResume [duplicate] (.bool true)
  let empty : SourceCoreExecution.Value := .mapping keyType .bool []
  SourceCompilerFeatureSupport.require ((← product.run [empty]) == .bool false) "compound key lost default"
  product.checkResume [empty] (.bool false)
  for name in ["operator", "choose"] do
    let entry ← SourceCompilerFeatureSupport.compileNamed checked name
    for (input, expected) in [(duplicate, false), (empty, true)] do
      SourceCompilerFeatureSupport.require ((← entry.run [input]) == .bool expected)
        "general index under primitive/conditional changed result"
      entry.checkResume [input] (.bool expected)
  let paired ← SourceCompilerFeatureSupport.compileNamed checked "paired"
  let pairResult : SourceCoreExecution.Value := .product (.bool true) (.bool true)
  SourceCompilerFeatureSupport.require ((← paired.run [duplicate]) == pairResult) "general index tuple slots changed"
  paired.checkResume [duplicate] pairResult
  let boxDeclaration : ProgramDataSignature ← match checked.signatures.dataTypes.find? (·.name == "Box") with
    | some declaration => pure declaration | none => throw (IO.userError "general recursive Box absent")
  let boxConstructor : ProgramDataConstructorSignature ← match boxDeclaration.constructors[0]? with
    | some constructor => pure constructor | none => throw (IO.userError "general recursive Box constructor absent")
  let boxMetadata : DataConstructorInstantiation := ⟨boxConstructor.id, [], [.bool], .nominal boxDeclaration.id []⟩
  let construct ← SourceCompilerFeatureSupport.compileNamed checked "construct"
  let boxTrue : SourceCoreExecution.Value := .constructed boxMetadata [.bool true]
  SourceCompilerFeatureSupport.require ((← construct.run [empty]) == boxTrue) "constructor lost general index payload"
  construct.checkResume [empty] boxTrue
  let skipped ← SourceCompilerFeatureSupport.compileNamed checked "skipped"
  let boxFalse : SourceCoreExecution.Value := .constructed boxMetadata [.bool false]
  SourceCompilerFeatureSupport.require ((← skipped.run []) == boxFalse) "short circuit ran general index child"
  skipped.checkResume [] boxFalse
  skipped.checkCells [] [(mappingType, none), (.bool, none)]
  let parent ← SourceCompilerFeatureSupport.compileNamed checked "parent"
  SourceCompilerFeatureSupport.require ((← parent.run [.bool true]) == boxTrue) "contextual lambda lost general index child"
  parent.checkResume [.bool true] boxTrue
  let keyIndex ← SourceCompilerFeatureSupport.compileNamed checked "keyIndex"
  let boolMap : SourceCoreExecution.Value := .mapping .bool .bool [(.bool true, .bool true)]
  SourceCompilerFeatureSupport.require ((← keyIndex.run [duplicate, boolMap]) == .bool true) "index key lost recursive general child"
  keyIndex.checkResume [duplicate, boolMap] (.bool true)
  let lazy ← SourceCompilerFeatureSupport.compileNamed checked "lazyProduct"
  SourceCompilerFeatureSupport.require ((← lazy.run []) == .bool false) "compound key lost lazy initialization"
  lazy.checkResume [] (.bool false)
  lazy.checkCells [] [(mappingType, some empty)]
  let nested ← SourceCompilerFeatureSupport.compileNamed checked "nestedProduct"
  let nestedKey : SourceCoreExecution.Value := .product pair (.word (Word.ofNatModulo 7))
  let nestedInput : SourceCoreExecution.Value := .mapping (.product keyType .word) .bool [(nestedKey, .bool true)]
  SourceCompilerFeatureSupport.require ((← nested.run [nestedInput]) == .bool true) "nested compound key changed equality"
  nested.checkResume [nestedInput] (.bool true)
  let nestedGeneral ← SourceCompilerFeatureSupport.compileNamed checked "nestedGeneral"
  let nestedGeneralInput : SourceCoreExecution.Value := .mapping keyType (.mapping (.proxy .word) .bool)
    [(pair, .mapping (.proxy .word) .bool [(.proxy .word, .bool true)])]
  SourceCompilerFeatureSupport.require ((← nestedGeneral.run [nestedGeneralInput]) == .bool true)
    "general index chain lost its intermediate mapping metadata"
  nestedGeneral.checkResume [nestedGeneralInput] (.bool true)
  let proxy ← SourceCompilerFeatureSupport.compileNamed checked "proxy"
  let proxyInput : SourceCoreExecution.Value := .mapping (.proxy (.comptime .word)) .bool
    [(.proxy (.comptime .word), .bool true), (.proxy .word, .bool false), (.proxy .word, .bool true)]
  SourceCompilerFeatureSupport.require ((← proxy.run [proxyInput]) == .bool false) "proxy key collapsed distinct raw metadata"
  proxy.checkResume [proxyInput] (.bool false)
  let declaration : ProgramDataSignature ← match checked.signatures.dataTypes.find? (·.name == "Key") with
    | some declaration => pure declaration | none => throw (IO.userError "general index nominal declaration missing")
  let constructor : ProgramDataConstructorSignature ← match declaration.constructors[0]? with
    | some constructor => pure constructor | none => throw (IO.userError "general index nominal constructor missing")
  let metadata : DataConstructorInstantiation := ⟨constructor.id, [], [.bool], .nominal declaration.id []⟩
  let nominal ← SourceCompilerFeatureSupport.compileNamed checked "nominal"
  let nominalInput : SourceCoreExecution.Value := .mapping metadata.resultType .bool
    [(.constructed metadata [.bool true], .bool true), (.constructed metadata [.bool true], .bool false)]
  SourceCompilerFeatureSupport.require ((← nominal.run [nominalInput]) == .bool true) "nominal key lost constructor payload/duplicate order"
  nominal.checkResume [nominalInput] (.bool true)
  let mapping ← SourceCompilerFeatureSupport.compileNamed checked "mappingKey"
  let keyMapping : SourceCoreExecution.Value := .mapping .bool .bool [(.bool true, .bool false)]
  let mappingInput : SourceCoreExecution.Value := .mapping (.mapping .bool .bool) .bool [(keyMapping, .bool true)]
  SourceCompilerFeatureSupport.require ((← mapping.run [mappingInput, keyMapping]) == .bool false) "noncomparable mapping key incorrectly matched"
  mapping.checkResume [mappingInput, keyMapping] (.bool false)
  for name in ["keyFault", "constructorFault", "defaultFault"] do
    let failed ← SourceCompilerFeatureSupport.compileNamed checked name
    let invocation ← failed.invoke []
    match invocation.outcome with
    | .failed token _ =>
        match ← invocation.diagnostic token with
        | some {error := .uninitializedLocal _, span := some _, ..} =>
            SourceCompilerFeatureSupport.require (name == "keyFault" || name == "constructorFault") "general key failure diagnostic changed"
        | some {error := .typeMismatch _ none, span := some _, ..} =>
            SourceCompilerFeatureSupport.require (name == "defaultFault") "general default failure diagnostic changed"
        | _ => throw (IO.userError "general index lost exact failure diagnostic")
    | _ => throw (IO.userError "general index fault did not fail")
    if name == "keyFault" || name == "constructorFault" then
      failed.checkCells [] [(mappingType, some empty), (.bool, none)]
  IO.println "general recursive expressions: typed compound keys, metadata, duplicate order, lazy effects, faults and resume GREEN"
end Tests.SourceCoreCompatibleGeneralExpressions
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleGeneralIndices
#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! General product-key indexing discharges its own child meanings. The theorem
fixture has an ambient closure and a typed hidden Integer slot; generated
comparators allocate after that prefix while lazy source initialization persists. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
set_option linter.unusedSimpArgs false
namespace Tests.SourceCoreCompatibleGeneralIndices
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleGeneralIndex CompatiblePayload GeneralHeap ReadOnly

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"index_meaning", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "index_meaning.solc"⟩, 0, 4⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def keyType : TypeSystem.Ty := .product .bool .bool
private def mappingType : TypeSystem.Ty := .mapping keyType .bool
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "table", .mono mappingType, [], false, none⟩
private def baseNode : ExpressionNode := { id := id 0, span, type := mappingType, form := .reference "table" (.local binder.id) }
private def trueNode : ExpressionNode := { id := id 1, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def falseNode : ExpressionNode := { id := id 2, span, type := .bool, form := .reference "false" (.builtinBoolean false) }
private def keyNode : ExpressionNode := { id := id 3, span, type := keyType, form := .tuple [id 1, id 2] }
private def indexNode : ExpressionNode := { id := id 4, span, type := .bool, form := .index (id 0) (id 3) }
private def source : TypedSource := { owner, inputs := [binder], roots := [.expression (id 4)], nodes := [.expression baseNode, .expression trueNode, .expression falseNode, .expression keyNode, .expression indexNode] }
private def context : SourceSemantics.Context := (SourceSemantics.Context.ofSignatures signatures).withLocal binder.id binder.scheme
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def compilation : SourceCoreFunctions.Context := ⟨⟨[], [], [], []⟩, ⟨owner, []⟩, [], 0, [], Word.zero⟩
private def noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .ok .unit
private def reason : Word := Word.ofNatModulo 17
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem metadata {expression : ExpressionId} {node : ExpressionNode} (found : source.lookupExpression? expression = some node) :
    node.requirements = CompatibleExpressionLiterals.owned node.form ∧ node.coercions = [] := by
  have member := (lookupExpression?_sound found).1
  simp only [source, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, Node.expression.injEq] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
private theorem boolAdmitted : TypeAdmissible context .bool :=
  .bool ((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal binder.id binder.scheme)
private theorem keyAdmitted : TypeAdmissible context keyType := .product boolAdmitted boolAdmitted
private theorem mappingAdmitted : TypeAdmissible context mappingType := .mapping keyAdmitted boolAdmitted
private theorem baseTyped : ExpressionHasType source context (id 0) mappingType := by
  apply ExpressionHasType.ofOrdinary (node := baseNode) (rawType := mappingType) (lookupExpression?_sound (by rfl))
    (.reference (.local (.head) (.head) (.intro (.empty _ _ rfl) (SchemeWellFormed.monoAdmissible mappingAdmitted) []
      .empty (by intro metavariable replacement member; cases member) (by exact SchemeInstantiates.empty_apply mappingType)
      (by simp) (by intro _ member; cases member) (.nil)))) mappingAdmitted mappingAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem trueTyped : ExpressionHasType source context (id 1) .bool := by
  apply ExpressionHasType.ofOrdinary (node := trueNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.reference (.builtinBoolean true)) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem falseTyped : ExpressionHasType source context (id 2) .bool := by
  apply ExpressionHasType.ofOrdinary (node := falseNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.reference (.builtinBoolean false)) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem keyTyped : ExpressionHasType source context (id 3) keyType := by
  apply ExpressionHasType.ofOrdinary (node := keyNode) (rawType := keyType)
    (lookupExpression?_sound (by cbv)) (.tuple (.cons trueTyped (.cons falseTyped (.nil _)))) keyAdmitted keyAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem indexTyped : ExpressionHasType source context (id 4) .bool := by
  apply ExpressionHasType.ofOrdinary (node := indexNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.index baseTyped keyTyped) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem syntaxTree : CompatibleGeneralIndex.Syntax source (id 4) :=
  .index (node := indexNode) (keyNode := keyNode) (by cbv) rfl (by cbv)
    (.fragment (.fragment (.fragment (.fragment (.fragment (.primitive (.product (.read (node := baseNode) (by cbv) rfl))))))))
    (.fragment (.pair (node := keyNode) (by cbv) rfl
      (.fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal (node := trueNode) (by cbv) (.bool _ _))))))))
      (.fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal (node := falseNode) (by cbv) (.bool _ _))))))))))
private theorem contextValid : CompatibleExpressionLiterals.ContextValid [] context [] := by
  refine ⟨rfl, ⟨?_, ?_⟩, ?_⟩
  · simp [RequirementIdsUnique, context, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal]
  · intro requirement member; cases member
  · constructor
    · intro goal evidence found; cases found
    · intro predicate member; cases member
private theorem checkExists : (SourceCoreCompatibleCatalog.prepare signatures 10 [mappingType]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 10 [mappingType]).toOption.get checkExists
private def values := SourceCoreCompatibleValues.Context.initial checked
private theorem nativeExists : (checked.catalog.project mappingType).toOption.isSome = true := by cbv
private def nativeType := (checked.catalog.project mappingType).toOption.get nativeExists
private theorem projected : checked.catalog.project mappingType = .ok nativeType := by cbv
private def scope : SourceCoreLocalCell.Scope := [(binder.id, nativeType)]
private theorem declarations : CompatibleExpressionReads.ScopeDeclarations source scope context := by
  intro actual declared index native selected accepted
  simp only [scope, SourceCoreLocalCell.lookup?] at selected
  split at selected
  · rename_i same
    subst actual
    have actual : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder := by rfl
    rw [actual] at accepted
    cases accepted
    exact .head
  · simp at selected
private abbrev policy := SourceCoreCompatibleDataExpressions.functionPolicy 100 values
private theorem certified {code : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 5 compilation source scope (id 4) (fun _ => reason) = .ok code) :
    Tree 100 values source context [] (fun _ => reason) scope (id 4) code :=
  tree_of_functions unique declarations (by rfl) rfl rfl ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩
    (fun _ _ _ found => (metadata found).2) syntaxTree (by cbv) indexTyped accepted

private def frameLayout : SourceCoreCallableIndexedFrames.Layout := ⟨⟨checked.catalog.definitions.length⟩⟩
private def ambient : AmbientDefinitions checked.catalog.definitions := .append _ [frameLayout.definition]
private def functions : FunctionModel checked.catalog ambient where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible
private def identities : Dynamic.Value → Word → Prop := fun _ _ => False
private theorem faithful : DataEquality.IdentityFaithful identities :=
  ⟨fun impossible => False.elim impossible, fun impossible => False.elim impossible⟩
private theorem functionLeaves : CompatibleEquality.FunctionObservations checked.catalog functions identities :=
  fun impossible => False.elim impossible
private theorem functionTypes : CompatiblePayload.FunctionRuntimeViews functions := fun impossible => False.elim impossible

/-- Raw staging aliases remain distinct values even when their projected native
types coincide; the independently specified equality retains that distinction. -/
theorem proxy_aliases_distinct :
    ¬ Dynamic.ValueEquivalent (.proxy (.comptime .word)) (.proxy .word) := by
  rintro ⟨same, _⟩
  cases same

/-- Mapping contents have no comparable source-value witness. -/
theorem mapping_keys_unmatched {key value : TypeSystem.Ty}
    {entries : List (Dynamic.Value × Dynamic.Value)} {other : Dynamic.Value} :
    ¬ Dynamic.ValueEquivalent (.mapping key value entries) other := by
  rintro ⟨_, comparable⟩
  cases comparable
private def model := CompatibleAmbientHeap.payloadModel checked values.registry functions
private def faults : FunctionCalls.FaultRep := fun error token =>
  (((∃ location, error = .uninitializedLocation location) ∧ token = reason) ∨
   (∃ key value tag, MetadataRep values.registry (.mapping key value) tag ∧ error = .missingMappingDefault value ∧ token = reason.add tag)) ∨
  ∃ code, error = .panic code ∧ token = Solcore.Frontend.SourceCorePanics.reason code
/-- Every panic fails with its code's reason. -/
private instance : FunctionCalls.FaultTokens faults := ⟨fun code => .inr ⟨code, rfl, rfl⟩⟩
private theorem uninitialized : ∀ (id : ExpressionId) location, faults (.uninitializedLocation location) ((fun _ => reason) id) :=
  fun _ location => .inl (.inl ⟨⟨location, rfl⟩, rfl⟩)
private theorem missing : ∀ (id : ExpressionId) key value tag, MetadataRep values.registry (.mapping key value) tag →
    faults (.missingMappingDefault value) (((fun _ => reason) id).add tag) :=
  fun _ key value tag owned => .inl (.inr ⟨key, value, tag, owned, rfl, rfl⟩)
private def administrativeType : Ty := .function .unit frameLayout.type
private def administrativeValue : Value := .closure .unit frameLayout.type (.var 1) [SourceCoreCallableIndexedFrames.encode frameLayout .empty]
private theorem frameRegistered : frameLayout.Registered ambient.definitions := by
  constructor
  simp [ambient, AmbientDefinitions.append, frameLayout]
private theorem administrativeTyped : RuntimeValueHasType [] administrativeValue administrativeType ambient.definitions :=
  .closure (.cons (SourceCoreCallableIndexedFrames.encode_runtime_typed [] frameRegistered .empty) .nil) (.var rfl)
private def world : StoreTyping := [administrativeType, OptionalCell.cellType nativeType]
private def store : Store := [administrativeValue, .inLeft nativeType .unit]
private def environment : Environment := [.cellRef (OptionalCell.cellType nativeType) 1]
private def sourceEnvironment : Dynamic.Environment := [(binder.id, ⟨0⟩)]
private def before : Dynamic.Heap := ⟨[⟨mappingType, none, none⟩]⟩
private def after : Dynamic.Heap := ⟨[⟨mappingType, some (.mapping keyType .bool []), none⟩]⟩
private theorem initial : GenericHeap.HeapRepresents model [1] world before store ∧
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) [1] world [] scope sourceEnvironment environment ambient.definitions := by
  have empty := (GenericHeap.HeapRepresents.empty (model := model)).allocate_administrative administrativeTyped
  obtain ⟨heap, reference⟩ := empty.allocate (.uninitialized projected) Dynamic.Heap.Allocates.append
  exact ⟨heap, .cons reference (.nil .nil)⟩
private theorem locals : Dynamic.EnvironmentAgrees before context.locals sourceEnvironment :=
  .cons (.intro .head) rfl (.ordinary rfl rfl) .nil
private theorem actualTyped : RuntimeEnvironmentHasTypes world (.integer 99 :: administrativeValue :: environment)
    [.integer, administrativeType, .cell (OptionalCell.cellType nativeType)] ambient.definitions :=
  .cons .integer (.cons (administrativeTyped.weaken ⟨world, rfl⟩) (.cons (.cellRef rfl) .nil))
private def ξ : Renaming := Renaming.comp (Renaming.insertion 0) (Renaming.insertion 0)
private theorem agrees : EnvironmentsAgree ξ environment (.integer 99 :: administrativeValue :: environment) :=
  GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix (show EnvironmentsAgree Renaming.id environment environment from fun {_ _} found => found) administrativeValue) (.integer 99)
private theorem sourceTrace : Dynamic.ExpressionEvaluatesOutcome program context [] source sourceEnvironment before (id 4) (.value (.bool false)) after := by
  apply Dynamic.ExpressionEvaluatesOutcome.value
  apply Dynamic.ExpressionEvaluates.intro (raw := .bool false) (middle := after) (lookupExpression?_sound (node := indexNode) (by cbv))
  · change Dynamic.ExpressionFormEvaluates program context [] source sourceEnvironment before (.index (id 0) (id 3)) [] [] (.bool false) after
    apply Dynamic.ExpressionFormEvaluates.indexDefault (coercions := []) rfl
    · exact .intro (lookupExpression?_sound (node := baseNode) (by rfl))
        (.localEmptyMapping rfl .head (.intro .head) rfl rfl rfl (.intro (.intro .head) .head)) .nil
    · exact .intro (lookupExpression?_sound (node := keyNode) (by cbv))
        (.tuple rfl (.cons (.intro (lookupExpression?_sound (node := trueNode) (by cbv)) (.builtinBoolean rfl) .nil)
          (.cons (.intro (lookupExpression?_sound (node := falseNode) (by cbv)) (.builtinBoolean rfl) .nil) .nil))
          (.cons (.singleton _))) .nil
    · exact .nil
    · exact .bool
  · exact .nil

/-- A real accepted expression constructs its own comparator execution after
source initialization, retaining an ambient closure that is not base-typable. -/
theorem accepted_lazy_preserves {code : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 5 compilation source scope (id 4) (fun _ => reason) = .ok code) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (.integer 99 :: administrativeValue :: environment) store (code.expression.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents model finalMap finalWorld .bool code.type faults (.value (.bool false)) value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends [1] finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved [1] store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  preserves (values := values) functions (.refl _) faithful functionLeaves functionTypes program [] contextValid unique uninitialized missing (certified accepted)
    (show source.lookupExpression? (id 4) = some indexNode by cbv) initial.2 initial.1 locals agrees actualTyped sourceTrace

/-- Source traces and effects follow from completion alone; no source run or
helper evaluation is supplied as a premise. -/
theorem accepted_index_reflects {code : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 5 compilation source scope (id 4) (fun _ => reason) = .ok code)
    {value : Value} {finalStore : Store} (completed : Evaluates (.integer 99 :: administrativeValue :: environment) store (code.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context [] source sourceEnvironment before (id 4) outcome after ∧
      FunctionCalls.ResultRepresents model finalMap finalWorld .bool code.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends [1] finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved [1] store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  reflects (values := values) functions (.refl _) faithful functionLeaves functionTypes program [] contextValid uninitialized missing (certified accepted)
    (show source.lookupExpression? (id 4) = some indexNode by cbv) initial.2 initial.1 locals agrees actualTyped completed


private def rawWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Key { Key(Bool) }",
    "enum Missing { Missing(Word) }",
    "function product(m: mapping((Bool, Bool) => Bool)) returns (Bool) { return m[(true, false)]; }",
    "function lazyProduct() returns (Bool) { let m: mapping((Bool, Bool) => Bool); return m[(true, false)]; }",
    "function nestedProduct(m: mapping(((Bool, Bool), Word) => Bool)) returns (Bool) { return m[((true, false), 7)]; }",
    "function nestedGeneral(m: mapping((Bool, Bool) => mapping(@Word => Bool))) returns (Bool) { return m[(true, false)][@Word]; }",
    "function proxy(m: mapping(@Word => Bool)) returns (Bool) { return m[@Word]; }",
    "function nominal(m: mapping(Key => Bool)) returns (Bool) { return m[Key(true)]; }",
    "function mappingKey(m: mapping(mapping(Bool => Bool) => Bool), k: mapping(Bool => Bool)) returns (Bool) { return m[k]; }",
    "function keyFault() returns (Bool) { let m: mapping((Bool, Bool) => Bool); let missing: Bool; return m[(true, missing)]; }",
    "function defaultFault() returns (Missing) { let m: mapping((Bool, Bool) => Missing); return m[(true, false)]; }"]}] }

def run : IO Unit := do
  let code ← SourceCompilerFeatureSupport.get "general index actual lowering"
    (SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 5 compilation source scope (id 4) (fun _ => reason))
  let state : Core.State := ⟨.eval (code.expression.rename ξ) (.integer 99 :: administrativeValue :: environment), [], store⟩
  let complete := Core.runStateful 30000 state
  match Core.LanguageResult.observeResult complete with
  | .succeeded (.bool false) finalStore =>
      SourceCompilerFeatureSupport.require (finalStore[0]? == some administrativeValue) "general index changed ambient closure"
  | _ => throw (IO.userError "general index static fixture failed")
  for fuel in [0, 5, 23] do
    match Core.runStateful fuel state with
    | .outOfFuel suspended =>
        SourceCompilerFeatureSupport.require (Core.runStateful 30000 suspended == complete) "general index resume changed native result/store"
    | _ => throw (IO.userError "general index prefix unexpectedly completed")
  let checked ← SourceCompilerFeatureSupport.get "general index source checker" (checkProgram rawWorkspace)
  let product ← SourceCompilerFeatureSupport.compileNamed checked "product"
  let pair : SourceCoreExecution.Value := .product (.bool true) (.bool false)
  let duplicate : SourceCoreExecution.Value := .mapping keyType .bool [(pair, .bool true), (pair, .bool false)]
  SourceCompilerFeatureSupport.require ((← product.run [duplicate]) == .bool true) "compound key lost first duplicate"
  product.checkResume [duplicate] (.bool true)
  let empty : SourceCoreExecution.Value := .mapping keyType .bool []
  SourceCompilerFeatureSupport.require ((← product.run [empty]) == .bool false) "compound key lost default"
  product.checkResume [empty] (.bool false)
  let lazy ← SourceCompilerFeatureSupport.compileNamed checked "lazyProduct"
  SourceCompilerFeatureSupport.require ((← lazy.run []) == .bool false) "compound key lost lazy initialization"
  lazy.checkResume [] (.bool false)
  lazy.checkCells [] [(mappingType, some empty)]
  let nested ← SourceCompilerFeatureSupport.compileNamed checked "nestedProduct"
  let nestedKey : SourceCoreExecution.Value := .product pair (.word (Word.ofNatModulo 7))
  let nestedInput : SourceCoreExecution.Value := .mapping (.product keyType .word) .bool [(nestedKey, .bool true)]
  SourceCompilerFeatureSupport.require ((← nested.run [nestedInput]) == .bool true) "nested compound key changed equality"
  nested.checkResume [nestedInput] (.bool true)
  let nestedGeneral ← SourceCompilerFeatureSupport.compileNamed checked "nestedGeneral"
  let nestedGeneralInput : SourceCoreExecution.Value := .mapping keyType (.mapping (.proxy .word) .bool)
    [(pair, .mapping (.proxy .word) .bool [(.proxy .word, .bool true)])]
  SourceCompilerFeatureSupport.require ((← nestedGeneral.run [nestedGeneralInput]) == .bool true)
    "general index chain lost its intermediate mapping metadata"
  nestedGeneral.checkResume [nestedGeneralInput] (.bool true)
  let proxy ← SourceCompilerFeatureSupport.compileNamed checked "proxy"
  let proxyInput : SourceCoreExecution.Value := .mapping (.proxy (.comptime .word)) .bool
    [(.proxy (.comptime .word), .bool true), (.proxy .word, .bool false), (.proxy .word, .bool true)]
  SourceCompilerFeatureSupport.require ((← proxy.run [proxyInput]) == .bool false) "proxy key collapsed distinct raw metadata"
  proxy.checkResume [proxyInput] (.bool false)
  let declaration : ProgramDataSignature ← match checked.signatures.dataTypes.find? (·.name == "Key") with
    | some declaration => pure declaration | none => throw (IO.userError "general index nominal declaration missing")
  let constructor : ProgramDataConstructorSignature ← match declaration.constructors[0]? with
    | some constructor => pure constructor | none => throw (IO.userError "general index nominal constructor missing")
  let metadata : DataConstructorInstantiation := ⟨constructor.id, [], [.bool], .nominal declaration.id []⟩
  let nominal ← SourceCompilerFeatureSupport.compileNamed checked "nominal"
  let nominalInput : SourceCoreExecution.Value := .mapping metadata.resultType .bool
    [(.constructed metadata [.bool true], .bool true), (.constructed metadata [.bool true], .bool false)]
  SourceCompilerFeatureSupport.require ((← nominal.run [nominalInput]) == .bool true) "nominal key lost constructor payload/duplicate order"
  nominal.checkResume [nominalInput] (.bool true)
  let mapping ← SourceCompilerFeatureSupport.compileNamed checked "mappingKey"
  let keyMapping : SourceCoreExecution.Value := .mapping .bool .bool [(.bool true, .bool false)]
  let mappingInput : SourceCoreExecution.Value := .mapping (.mapping .bool .bool) .bool [(keyMapping, .bool true)]
  SourceCompilerFeatureSupport.require ((← mapping.run [mappingInput, keyMapping]) == .bool false) "noncomparable mapping key incorrectly matched"
  mapping.checkResume [mappingInput, keyMapping] (.bool false)
  for name in ["keyFault", "defaultFault"] do
    let failed ← SourceCompilerFeatureSupport.compileNamed checked name
    let invocation ← failed.invoke []
    match invocation.outcome with
    | .failed token _ =>
        match ← invocation.diagnostic token with
        | some {error := .uninitializedLocal _, span := some _, ..} =>
            SourceCompilerFeatureSupport.require (name == "keyFault") "general key failure diagnostic changed"
        | some {error := .typeMismatch _ none, span := some _, ..} =>
            SourceCompilerFeatureSupport.require (name == "defaultFault") "general default failure diagnostic changed"
        | _ => throw (IO.userError "general index lost exact failure diagnostic")
    | _ => throw (IO.userError "general index fault did not fail")
    if name == "keyFault" then
      failed.checkCells [] [(mappingType, some empty), (.bool, none)]
  IO.println "general mapping indices: typed compound keys, metadata, duplicate order, lazy effects, faults and resume GREEN"
end Tests.SourceCoreCompatibleGeneralIndices
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleGeneralRuntime
/-! The semantic family uses the old General Tree plus static receipts for
its literal leaves. The formal consumer obtains a repeated numeric child from
the actual compiler and builds its exact pair tree. Whole-root support
extraction is intentionally not claimed. Runtime fixtures separately exercise
actual control/data compilation, full stores and first-fault resume. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreCompatibleGeneralRuntime
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatiblePayload GeneralHeap ReadOnly

section Accepted
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {fuel readFuel : Nat} {compilation : SourceCoreFunctions.Context} {values : SourceCoreCompatibleValues.Context}
  {source : TypedSource} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {id pairId : ExpressionId} {node pairNode : ExpressionNode} {reasonAt : ExpressionId → Word}
  {lowered : SourceCoreBasic.LoweredExpr}
  (found : source.lookupExpression? id = some node) (atomic : CompatibleExpressionLiterals.Atomic node.form)
  (unitType : node.form = .tuple [] → node.type = .unit)
  (special : ∀ child budget, (match policy.lowerSpecial? with
    | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
    | some lower => lower compilation child budget source scope id reasonAt) = .ok none)
  (readPolicy : policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
  (leafPolicy : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
  (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope id reasonAt = .ok lowered)
  (metadata : CompatibleExpressionPrimitives.Metadata values.checked source pairId pairNode (.product lowered.type lowered.type))
  (form : pairNode.form = .tuple [id, id]) (pairType : pairNode.type = .product node.type node.type)

include found atomic unitType special readPolicy leafPolicy accepted metadata form pairType

/-- Repeated leaves keep both occurrences and the same full selected row.
The parent metadata is explicit static data, not a compiler-root receipt. -/
theorem accepted_pair :
    CompatibleExpressionGeneralRuntime.Certificate readFuel values source context compilation.solvedRequirements reasonAt
      scope pairId ⟨.product lowered.type lowered.type,
        LocalSequence.pair lowered.type lowered.type lowered.expression lowered.expression⟩ := by
  have leaf := CompatibleExpressionLiteralRuntime.of_functions found atomic unitType special readPolicy leafPolicy accepted
  let tree : CompatibleExpressionProducts.Tree readFuel values source context compilation.solvedRequirements reasonAt scope pairId
      ⟨.product lowered.type lowered.type, LocalSequence.pair lowered.type lowered.type lowered.expression lowered.expression⟩ :=
    .pair metadata form found found pairType (.literal leaf.forget) (.literal leaf.forget)
  have sites : tree.LiteralSites (fun _ i code => CompatibleExpressionLiteralRuntime.Certificate compilation.solvedRequirements source i code) :=
    .pair metadata form found found pairType _ _ (.literal leaf.forget leaf) (.literal leaf.forget leaf)
  exact ⟨.fragment (.fragment (.fragment (.fragment (.primitive (.product tree))))),
    .fragment _ (.fragment _ (.fragment _ (.fragment _ (.primitive _ (.product _ sites)))))⟩

variable {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (program : SourceSemantics.Program) (evidence : Dynamic.EvidenceEnvironment)
  (sameLedger : context.solvedRequirements = compilation.solvedRequirements)
  (runtime : RuntimeRequirementLedgerValid context) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ child location, faults (.uninitializedLocation location) (reasonAt child))
  (missing : ∀ child key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt child).add tag))

include extension faithful functionLeaves functionTypes sameLedger runtime uninitialized missing

theorem accepted_pair_preserves [FunctionCalls.FaultTokens faults] (unique : NodeOccurrencesUnique source) :
    TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (fun s i code => s = scope ∧ i = pairId ∧ code =
        ⟨.product lowered.type lowered.type, LocalSequence.pair lowered.type lowered.type lowered.expression lowered.expression⟩) faults := by
  have receipt := accepted_pair (readFuel := 0) (context := context) found atomic unitType special readPolicy leafPolicy accepted metadata form pairType
  intro s i code selected
  obtain ⟨rfl, rfl, rfl⟩ := selected
  exact CompatibleExpressionGeneralRuntime.preserves functions extension faithful functionLeaves functionTypes
    program evidence sameLedger runtime unique uninitialized missing receipt

theorem accepted_pair_reflects [FunctionCalls.FaultTokens faults] :
    TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (fun s i code => s = scope ∧ i = pairId ∧ code =
        ⟨.product lowered.type lowered.type, LocalSequence.pair lowered.type lowered.type lowered.expression lowered.expression⟩) faults := by
  have receipt := accepted_pair (readFuel := 0) (context := context) found atomic unitType special readPolicy leafPolicy accepted metadata form pairType
  intro s i code selected
  obtain ⟨rfl, rfl, rfl⟩ := selected
  exact CompatibleExpressionGeneralRuntime.reflects functions extension faithful functionLeaves functionTypes
    program evidence sameLedger runtime uninitialized missing receipt
end Accepted

private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def word (value : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo value)
private def content : String := String.intercalate "\n" [
  "function nested() returns (Word) { return (true ? (5 + 7) : (11 / 0)) * 3; }",
  "function shortCircuit() returns (Bool) { let absent: Word; return false && (absent == 17); }",
  "function paired() returns ((Word, Word)) { let prior = 19; return (prior, 23); }",
  "function mappingRoot() returns (Word) { let table: mapping(Word => Word); table[29] = 31; return table[29] + table[37]; }",
  "function leftFault() returns (Word) { let prior = 41; let absent: Word; return absent + (43 / 0); }",
  "function rightFault() returns (Word) { let prior = 47; let absent: Word; return (prior + 53) + absent; }"
]

/-- Inspect real numeric compiler leaves with the complete retained ledger.
Unrelated assumptions are explicit test mutations; no checker-production
claim is made for those altered ledgers. -/
private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let mut numeric := 0
  for named in compiled.indexed.base.functions do
    let actual ← get "general exact specialization" (SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key)
    require (actual == named.specialized) "general selected full record changed"
    let source := actual.function.typedBody
    let ledger := actual.function.solvedRequirements
    for retained in source.nodes do
      match retained with
      | .expression node =>
        match form : node.form with
        | .integerLiteral literal resolution =>
          numeric := numeric + 1
          let fresh : RequirementId := ⟨(ledger.map (·.id.index)).foldl max 0 + 1⟩
          let unrelated : SolvedRequirement := ⟨fresh, resolution.predicate, .assumption resolution.predicate⟩
          for rows in [ledger, unrelated :: ledger, ledger ++ [unrelated]] do
            let values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked
            let policy := SourceCoreCompatibleDataExpressions.functionPolicy 100 values
            let compilation : SourceCoreFunctions.Context := {
              plan := compiled.indexed.base.plan, owner := named.signature.key,
              globals := compiled.indexed.base.globals, administrativePrefix := 1,
              solvedRequirements := rows, internalReason := Word.zero }
            let noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .error (.unsupportedExpression node.id node.form)
            if found : source.lookupExpression? node.id = some node then
              match accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 100 compilation source [] node.id (fun _ => Word.zero) with
              | .error error => throw (IO.userError s!"general numeric compiler rejected: {reprStr error}")
              | .ok lowered =>
                have atomic : CompatibleExpressionLiterals.Atomic node.form := form ▸ .integer literal resolution
                have unitType : node.form = .tuple [] → node.type = .unit := by intro impossible; rw [form] at impossible; cases impossible
                have receipt := CompatibleExpressionLiteralRuntime.of_functions found atomic unitType (by intros; rfl) rfl rfl accepted
                let _receipt := receipt
                let selected ← match rows.filter (·.id == resolution.requirement) with
                  | [selected] => pure selected
                  | _ => throw (IO.userError "general numeric row not singleton")
                let implementation : ProgramImplId := .builtin (if node.type == .integer then .intInteger else .intWord)
                require (selected.predicate == resolution.predicate && selected.evidence == .implementation (.byImpl resolution.predicate implementation []))
                  "general exact implementation receipt changed"
                let payload := if node.type == .integer then Core.Value.integer (Int.ofNat resolution.rawValue)
                  else Core.Value.word (Word.ofNatModulo resolution.rawValue)
                let captured := Core.Value.closure .unit .word (.var 0) [.word (Word.ofNatModulo 101)]
                let store : Store := [captured, .word (Word.ofNatModulo 103)]
                for fuel in [0, 1, 7, 1000] do
                  let state := Core.runStateful fuel (.initial lowered.expression [captured] store)
                  let finished := match state with
                    | .outOfFuel checkpoint => Core.runStateful 1000 checkpoint
                    | result => result
                  match finished with
                  | .done actual after => require (actual == .inRight .word payload && after == store) "general leaf payload/store changed"
                  | other => throw (IO.userError s!"general leaf did not complete: {reprStr other}")
            else throw (IO.userError "general source lookup changed")
        | _ => pure ()
      | _ => pure ()
  require (numeric ≥ 14) "general numeric audit unexpectedly small"

private def cells (state : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) : IO Unit :=
  require (reprStr (state.heap.map fun cell => (cell.type, cell.value)) == reprStr expected)
    s!"general full source cells changed: {reprStr state.heap}"

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "general runtime literals" content
    ["nested", "shortCircuit", "paired", "mappingRoot", "leftFault", "rightFault"]
  inspect compiled
  for fuel in [0, 37, 151, 300000] do
    for name in ["nested", "shortCircuit", "paired", "mappingRoot", "leftFault", "rightFault"] do
      let started ← SourceCoreUnifiedCorpusSupport.execute compiled name [] fuel
      let finished ← get "general public resume" (started.resume 300000)
      match name, finished.observation with
      | "nested", .done value state => require (reprStr value == reprStr (word 36)) "nested result"; cells state []
      | "shortCircuit", .done (.bool false) state => cells state [(.word, none)]
      | "paired", .done value state =>
        require (reprStr value == reprStr (SourceTypedRuntime.Value.product (word 19) (word 23))) "pair result"
        cells state [(.word, some (word 19))]
      | "mappingRoot", .done value state =>
        require (reprStr value == reprStr (word 31)) "mapping result"
        cells state [(.mapping .word .word, some (.mapping .word .word [(word 29, word 31)]))]
      | "leftFault", .fault (.uninitializedLocal binder) state
      | "rightFault", .fault (.uninitializedLocal binder) state =>
        let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
        let named ← match compiled.indexed.base.functions.filter (·.signature.key == key) with
          | [named] => pure named
          | _ => throw (IO.userError "general fault function missing")
        let expected ← match (SourceCoreDataPlaces.declaredBinders named.specialized.function.typedBody).filter (·.name == "absent") with
          | [binder] => pure binder.id
          | _ => throw (IO.userError "general absent binder missing")
        require (binder == expected) "general first fault identity changed"
        cells state [(.word, some (word (if name == "leftFault" then 41 else 47))), (.word, none)]
      | _, other => throw (IO.userError s!"general unexpected {name}: {reprStr other}")
  IO.println "general runtime leaves / full ledger / ordered control-data / first fault / full heap / resume GREEN"
end Tests.SourceCoreCompatibleGeneralRuntime
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleGeneralRuntimeExtraction
/-! A real whole-root Functions acceptance now constructs all leaf support.
No separate leaf, child-tree or runtime-meaning callback is supplied. Native
reflection starts from completion alone; full-ledger and static source/type
conditions stay explicit. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreCompatibleGeneralRuntimeExtraction
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatiblePayload GeneralHeap ReadOnly CompatibleExpressionGeneral

section Accepted
variable
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {readFuel : Nat} {context : SourceCoreFunctions.Context} {values : ValuesContext}
  {source : TypedSource} {scope : Scope} {reasonAt : ExpressionId → Word}
  {sourceContext : SourceSemantics.Context}
  (unique : NodeOccurrencesUnique source)
  (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
  (signatures : sourceContext.signatures = values.checked.signatures)
  (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source sourceContext (Syntax source))
  (policyFor : PolicyFor policy context readFuel values source scope reasonAt)
  (coercions : ∀ id node, Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
  {id : ExpressionId} (syntaxTree : Syntax source id) {node : ExpressionNode}
  (found : source.lookupExpression? id = some node)
  (typed : ExpressionHasType source sourceContext id node.type)
  {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
  (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope id reasonAt = .ok lowered)

include unique declarations signatures constructorValid policyFor coercions syntaxTree found typed accepted

/-- Actual accepted root code fixes every child and ordered literal occurrence. -/
theorem accepted_support :
    CompatibleExpressionGeneralRuntime.Certificate readFuel values source sourceContext context.solvedRequirements reasonAt scope id lowered :=
  CompatibleExpressionGeneralRuntimeExtraction.of_functions unique declarations signatures constructorValid policyFor
    coercions syntaxTree found typed accepted

variable {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (program : SourceSemantics.Program) (evidence : Dynamic.EvidenceEnvironment)
  (sameLedger : sourceContext.solvedRequirements = context.solvedRequirements)
  (runtime : RuntimeRequirementLedgerValid sourceContext) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ child location, faults (.uninitializedLocation location) (reasonAt child))
  (missing : ∀ child key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt child).add tag))

include extension faithful functionLeaves functionTypes sameLedger runtime uninitialized missing

theorem accepted_preserves [FunctionCalls.FaultTokens faults] :
    TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program sourceContext evidence source (fun s i code => s = scope ∧ i = id ∧ code = lowered) faults := by
  have receipt := accepted_support unique declarations signatures constructorValid policyFor coercions syntaxTree found typed accepted
  intro s i code selected
  obtain ⟨rfl, rfl, rfl⟩ := selected
  exact CompatibleExpressionGeneralRuntime.preserves functions extension faithful functionLeaves functionTypes
    program evidence sameLedger runtime unique uninitialized missing receipt

theorem accepted_reflects [FunctionCalls.FaultTokens faults] :
    TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program sourceContext evidence source (fun s i code => s = scope ∧ i = id ∧ code = lowered) faults := by
  have receipt := accepted_support unique declarations signatures constructorValid policyFor coercions syntaxTree found typed accepted
  intro s i code selected
  obtain ⟨rfl, rfl, rfl⟩ := selected
  exact CompatibleExpressionGeneralRuntime.reflects functions extension faithful functionLeaves functionTypes
    program evidence sameLedger runtime uninitialized missing receipt
end Accepted

private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def word (value : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo value)
private def content : String := String.intercalate "\n" [
  "function compound() returns (Word) { return (false ? (1 / 0) : ((5 + 7) * 3)) + 2; }",
  "function pairRoot() returns ((Word, Word)) { return (13 + 17, 19 * 23); }",
  "function lazyRoot() returns (Bool) { return true || (29 / 0 == 31); }",
  "function faultLeft() returns (Word) { let prior = 41; let absent: Word; return absent + (43 / 0); }",
  "function faultRight() returns (Word) { let prior = 47; let absent: Word; return (prior + 53) + absent; }",
  "function mappingRoot() returns (Word) { let table: mapping(Word => Word); table[59] = 61; return table[59] + table[67]; }"
]

private def native (code : Core.Expr) (expected : Core.Value) : IO Unit := do
  let captured := Core.Value.closure .unit .word (.var 0) [.word (Word.ofNatModulo 101)]
  let store : Store := [captured, .word (Word.ofNatModulo 103)]
  for fuel in [0, 1, 17, 300000] do
    let first := Core.runStateful fuel (.initial code [captured] store)
    let result := match first with
      | .outOfFuel checkpoint => Core.runStateful 300000 checkpoint
      | result => result
    match result with
    | .done value after =>
      require (value == .inRight .word expected && after == store)
        "whole-root value/captures/full native store changed"
    | other => throw (IO.userError s!"whole-root did not finish: {reprStr other}")

private def lower (values : SourceCoreCompatibleValues.Context) (context : SourceCoreFunctions.Context)
    (source : TypedSource) (id : ExpressionId) : IO SourceCoreBasic.LoweredExpr := do
  let found ← match source.lookupExpression? id with
    | some node => pure node
    | none => throw (IO.userError "whole-root lookup missing")
  let policy := SourceCoreCompatibleDataExpressions.functionPolicy 1000 values
  let noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ =>
    .error (.unsupportedExpression id found.form)
  get "actual whole-root Functions compiler"
    (SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 1000 context source [] id (fun _ => Word.zero))

/-- Real complete roots retain their original ordered ledger. The extra
assumption variants and repeated pair below are explicit retained-IR mutations. -/
private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  for name in ["compound", "pairRoot", "lazyRoot"] do
    let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
    let named ← match compiled.indexed.base.functions.filter (·.signature.key == key) with
      | [named] => pure named
      | _ => throw (IO.userError "whole-root function missing")
    let actual ← get "whole-root full specialization"
      (SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan key)
    require (actual == named.specialized) "whole-root full record changed"
    let source := actual.function.typedBody
    let ids := source.nodes.filterMap fun
      | .statement node => match node.form with | .returnStmt (some id) => some id | _ => none
      | _ => none
    let id ← match ids with | [id] => pure id | _ => throw (IO.userError "whole-root return not singleton")
    let ledger := actual.function.solvedRequirements
    let predicate := ProgramSignatures.builtinIntPredicate .word
    let fresh : RequirementId := ⟨(ledger.map (·.id.index)).foldl max 0 + 1⟩
    let unrelated : SolvedRequirement := ⟨fresh, predicate, .assumption predicate⟩
    let values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked
    let base : SourceCoreFunctions.Context := {
      plan := compiled.indexed.base.plan, owner := key, globals := compiled.indexed.base.globals,
      administrativePrefix := 1, solvedRequirements := ledger, internalReason := Word.zero }
    let expected : Core.Value := if name == "compound" then .word (Word.ofNatModulo 38)
      else if name == "pairRoot" then .pair (.word (Word.ofNatModulo 30)) (.word (Word.ofNatModulo 437))
      else .bool true
    let original ← lower values base source id
    for rows in [ledger, unrelated :: ledger, ledger ++ [unrelated]] do
      let code ← lower values {base with solvedRequirements := rows} source id
      require (code == original) "unused full-ledger row changed whole-root code"
      native code.expression expected
    if name == "pairRoot" then
      let node ← match source.lookupExpression? id with | some node => pure node | none => throw (IO.userError "pair missing")
      match node.form with
      | .tuple [left, _] =>
        let changed := SourceCoreEvidence.withNode source {node with form := .tuple [left, left]}
        let code ← lower values base changed id
        native code.expression (.pair (.word (Word.ofNatModulo 30)) (.word (Word.ofNatModulo 30)))
      | _ => throw (IO.userError "pair root form changed")

/-- A real checked template-bearing source supplies a closed arithmetic
subtree to Functions lowering. No whole callable compilation is claimed. -/
private def template_root : IO Unit := do
  let workspace : Workspace.RawWorkspace := {
    entry := "main.solc", externalLibraries := []
    mainSources := [{path := "main.solc", content := String.intercalate "\n" [
      "trait Mark<T> {}", "impl Mark<Word> {}", "impl Mark<Bool> {}",
      "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
      "function qualified(flag: Bool) returns (Word, Bool) {",
      " let initial: Word = 61 + 67; let f = lam(item) { return keep(item); }; return (f(1), f(flag)); }"
    ]}] }
  let program ← get "template checked program" (checkProgram workspace)
  let signature ← match program.signatures.functions.filter (·.name == "qualified") with
    | [signature] => pure signature
    | _ => throw (IO.userError "template signature missing")
  let generic ← match program.functions.filter (·.declaration == signature.id) with
    | [generic] => pure generic
    | _ => throw (IO.userError "template function missing")
  let actual ← get "template actual specialization" (SourceSpecialization.specializeFunction signature generic [])
  let source := actual.function.typedBody
  let ledger := actual.function.solvedRequirements
  require (!source.localSchemeTemplateIds.isEmpty && ledger.map (·.id) == generic.solvedRequirements.map (·.id))
    "template IDs or complete ordered ledger changed"
  for id in source.localSchemeTemplateIds do
    match ledger.filter (·.id == id) with
    | [row] => match row.evidence with
      | .assumption predicate =>
        require (predicate == row.predicate && !actual.assumptions.contains predicate)
          "template assumption was promoted"
      | _ => throw (IO.userError "template implementation fabricated")
    | _ => throw (IO.userError "template row missing or duplicated")
  let checked ← get "template compatible catalog" (SourceCoreCompatibleCatalog.prepare program.signatures 100 [.word, .bool])
  let values := SourceCoreCompatibleValues.Context.initial checked
  let context : SourceCoreFunctions.Context := {
    plan := ⟨[actual.key], [actual], [], []⟩, owner := actual.key, globals := [],
    administrativePrefix := 1, solvedRequirements := ledger, internalReason := Word.zero }
  let candidates := source.nodes.filterMap fun
    | .expression node => match node.form with | .binary _ _ _ => some node.id | _ => none
    | _ => none
  let id ← match candidates with | [id] => pure id | _ => throw (IO.userError "template arithmetic root not singleton")
  let code ← lower values context source id
  native code.expression (.word (Word.ofNatModulo 128))

private def cells (state : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) : IO Unit :=
  require (reprStr (state.heap.map fun cell => (cell.type, cell.value)) == reprStr expected)
    s!"whole-root ordered source cells changed: {reprStr state.heap}"

def run : IO Unit := do
  let names := ["compound", "pairRoot", "lazyRoot", "faultLeft", "faultRight", "mappingRoot"]
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "general runtime extraction" content names
  inspect compiled
  template_root
  for fuel in [0, 37, 151, 300000] do
    for name in names do
      let started ← SourceCoreUnifiedCorpusSupport.execute compiled name [] fuel
      let finished ← get "whole-root public resume" (started.resume 300000)
      match name, finished.observation with
      | "compound", .done value state => require (reprStr value == reprStr (word 38)) "compound result"; cells state []
      | "pairRoot", .done value state =>
        require (reprStr value == reprStr (SourceTypedRuntime.Value.product (word 30) (word 437))) "pair result"
        cells state []
      | "lazyRoot", .done (.bool true) state => cells state []
      | "mappingRoot", .done value state =>
        require (reprStr value == reprStr (word 61)) "mapping result"
        cells state [(.mapping .word .word, some (.mapping .word .word [(word 59, word 61)]))]
      | "faultLeft", .fault (.uninitializedLocal binder) state
      | "faultRight", .fault (.uninitializedLocal binder) state =>
        let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
        let named ← match compiled.indexed.base.functions.filter (·.signature.key == key) with
          | [named] => pure named
          | _ => throw (IO.userError "fault function missing")
        let expected ← match (SourceCoreDataPlaces.declaredBinders named.specialized.function.typedBody).filter (·.name == "absent") with
          | [binder] => pure binder.id
          | _ => throw (IO.userError "fault binder missing")
        require (binder == expected) "first fault identity changed"
        cells state [(.word, some (word (if name == "faultLeft" then 41 else 47))), (.word, none)]
      | _, other => throw (IO.userError s!"whole-root unexpected {name}: {reprStr other}")
  IO.println "whole Functions root / same-tree literals / full template ledger / ordered duplicates / fault heaps / resume GREEN"

end Tests.SourceCoreCompatibleGeneralRuntimeExtraction
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleGetterReflection
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.SourceCoreCompatibleGetterReflection
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceLiveRoot
open SourceCoreCompatibleDataPlaces CompatiblePlaceKeys
private theorem except_get {α ε : Type} (result : Except ε α) (positive : result.toOption.isSome = true) :
    result = .ok (result.toOption.get positive) := by
  cases result with | error => simp [Except.toOption] at positive | ok => rfl
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"compatible_getter_reflection", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "compatible_getter_reflection.solc"⟩, 0, 1⟩
private def key : ExpressionId := ⟨⟨owner, 1⟩⟩
private def site : SourceCoreElaboration.ErrorSite := .occurrence ⟨owner, 0⟩
private def valueType : TypeSystem.Ty := .function .bool .bool
private def rootType : TypeSystem.Ty := .mapping .bool valueType
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private theorem catalogExists : (SourceCoreCompatibleCatalog.prepare signatures 100 [rootType]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 100 [rootType]).toOption.get catalogExists
private def compilation := SourceCoreCompatibleValues.Context.initial checked
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "root", .mono rootType, [], false, none⟩
private def node : ExpressionNode := { id := key, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def source : TypedSource := { owner, inputs := [binder], roots := [.expression key], nodes := [.expression node] }
private def assignment : AssignmentResolution := ⟨⟨binder.id, [.index key], valueType⟩, []⟩
private def context := (SourceSemantics.Context.ofSignatures signatures).withLocal binder.id binder.scheme
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def noFunctions (catalog : SourceCoreCompatibleCatalog.Catalog) : FunctionModel catalog where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible
private theorem observations : FunctionObservations checked.catalog (noFunctions checked.catalog) (fun _ _ => False) := by
  intro _ _ _ _ _ _ _ impossible; exact impossible.elim
private theorem faithful : DataEquality.IdentityFaithful (fun _ _ => False) := by
  constructor <;> intros <;> contradiction
private theorem functionViews : FunctionRuntimeViews (noFunctions checked.catalog) := fun impossible => False.elim impossible
private def carrier : SourceCoreDataValues.Value := .mapping (.comptime .bool) (.comptime valueType) []
private def sourceRoot : Dynamic.Value := .mapping (.comptime .bool) (.comptime valueType) []
private theorem carrierMeaning : CompatibleEncoding.Means carrier sourceRoot := .mapping .empty
private def before : Dynamic.Heap := ⟨[⟨rootType, some sourceRoot, none⟩]⟩
private def world (prepared : Prepared) : StoreTyping := [OptionalCell.cellType prepared.route.rootType]
private def environment (prepared : Prepared) : Environment := [.cellRef (OptionalCell.cellType prepared.route.rootType) 0, .bool true]
private def coreContext (prepared : Prepared) : Core.Context := [OptionalCell.referenceType prepared.route.rootType, .bool]
private def code (prepared : Prepared) : Expr := .apply (getter prepared .bool) (.pair (.loadCell (.var 0)) (.var 1))

private theorem pathArguments {registry : SourceCoreRawMetadata.Registry} {prepared : Prepared}
    {steps : List PreparedStep} {sites : List (ExpressionId × Ty)} {leaf : TypeSystem.Ty}
    (path : PreparedPath checked source site rootType assignment.target.projections 0 steps sites leaf) :
    Arguments checked registry (noFunctions checked.catalog) [0] (world prepared) source site [.bool true] path [.index (.bool true)] ∧
      steps ≠ [] ∧ sites.length = 1 := by
  cases path with
  | index certificate generated tail =>
    have shape := TypeSystem.Ty.mapping.inj certificate.view
    obtain ⟨rfl, rfl⟩ := shape
    have nativeKey := Except.ok.inj certificate.keyProjection
    cases tail
    refine ⟨?_, (by simp), rfl⟩
    apply Arguments.index (certificate := certificate) (generated := generated) rfl
    · rw [← nativeKey]; exact .bool true
    · exact .nil

/-- Actual compiler/encoder/checker receipts and a completed native getter
suffice to reconstruct the source classification. No source path outcome is an
input. In particular the raw staged key guard is derived from payloads. -/
theorem actual_reflection {route : Route} {prepared : Prepared}
    (described : describe compilation checked.signatures source site assignment = .ok route)
    (preparedBy : prepare compilation 100 route Word.zero (fun _ => Word.ofNatModulo 100) = .ok prepared)
    {encoded : SourceCoreCompatibleValues.Encoded 100 compilation rootType carrier}
    (accepted : SourceCoreCompatibleValues.encode 100 compilation rootType carrier = .ok encoded)
    (typed : HasType (coreContext prepared) (code prepared) (LanguageResult.resultType prepared.optionalLeaf) checked.catalog.definitions)
    {result : Value} {after : Store}
    (completed : Evaluates (environment prepared) [.inRight .unit encoded.value] (code prepared) result after) :
    ∃ futureWorld,
      (∃ leaf, CompatiblePlaceGetterReflection.ResultRep checked encoded.context.registry (noFunctions checked.catalog)
        [0] futureWorld prepared ⟨rootType, some sourceRoot, none⟩ [.index (.bool true)] leaf result) ∧
      HeapRepresents checked encoded.context.registry (noFunctions checked.catalog) [0] futureWorld before after := by
  obtain ⟨actualBinder, leaf, description⟩ := CompatiblePlaceDescription.of_describe described
  have same := Except.ok.inj (description.binding.symm.trans (show rootBinder source assignment.target.root = .ok binder by cbv))
  subst actualBinder
  obtain ⟨routeEq, _, path⟩ := description.prepared preparedBy
  have projected : checked.catalog.project rootType = .ok prepared.route.rootType := routeEq ▸ description.rootProjected
  have leafProjected : checked.catalog.project leaf = .ok prepared.route.leafType := by
    rw [← checked.catalog.project_runtimeType leaf, description.selectedType, routeEq]
    exact description.leafProjected
  have represented := CompatibleEncoding.encode_represents_at (functions := noFunctions checked.catalog) accepted carrierMeaning [] []
  have same := Except.ok.inj (represented.projection.symm.trans projected)
  rw [same] at represented
  have empty : HeapRepresents checked encoded.context.registry (noFunctions checked.catalog) [] [] ⟨[]⟩ [] := GenericHeap.HeapRepresents.empty
  obtain ⟨heaps, reference⟩ := empty.allocate (.initialized represented) Dynamic.Heap.Allocates.append
  obtain ⟨arguments, nonempty, length⟩ := pathArguments (registry := encoded.context.registry) (prepared := prepared) path
  have keyLength : prepared.keyTypes.length = ([Value.bool true] : List Value).length := by simpa [Prepared.keyTypes] using length
  have typedEnvironment : RuntimeEnvironmentHasTypes (world prepared) (environment prepared) (coreContext prepared) checked.catalog.definitions :=
    .cons (.cellRef rfl) (.cons .bool .nil)
  obtain ⟨futureWorld, _, resultRep, finalHeaps, _⟩ := CompatiblePlaceGetterReflection.reflects
    arguments leafProjected (fun key value declared => routeEq ▸ description.virtual key value declared)
    (fun ordinary => routeEq ▸ description.ordinary ordinary) encoded.preserves nonempty functionViews faithful observations keyLength
    heaps reference (Dynamic.Heap.Reads.intro .head) typedEnvironment typed (.var rfl) (.var rfl) completed
  exact ⟨futureWorld, ⟨leaf, resultRep⟩, finalHeaps⟩

/-- This fixture cannot succeed: its actual empty raw mapping has no
function default. The reflected fault and token are outputs of the theorem. -/
theorem actual_missing {route : Route} {prepared : Prepared}
    (described : describe compilation checked.signatures source site assignment = .ok route)
    (preparedBy : prepare compilation 100 route Word.zero (fun _ => Word.ofNatModulo 100) = .ok prepared)
    {encoded : SourceCoreCompatibleValues.Encoded 100 compilation rootType carrier}
    (accepted : SourceCoreCompatibleValues.encode 100 compilation rootType carrier = .ok encoded)
    (typed : HasType (coreContext prepared) (code prepared) (LanguageResult.resultType prepared.optionalLeaf) checked.catalog.definitions)
    {result : Value} {after : Store}
    (completed : Evaluates (environment prepared) [.inRight .unit encoded.value] (code prepared) result after) :
    ∃ token count futureWorld,
      result = .inLeft prepared.optionalLeaf (.word token) ∧
      Dynamic.ProjectionsFaults (some sourceRoot) [.index (.bool true)] (.missingMappingDefault (.comptime valueType)) ∧
      FaultToken checked encoded.context.registry sourceRoot prepared.steps [.index (.bool true)]
        (.missingMappingDefault (.comptime valueType)) token count ∧
      HeapRepresents checked encoded.context.registry (noFunctions checked.catalog) [0] futureWorld before after := by
  have unavailable : ¬ Dynamic.Defaultable (.comptime valueType) := by
    intro impossible; cases impossible with | comptime inner => cases inner
  obtain ⟨futureWorld, ⟨leaf, resultRep⟩, heaps⟩ := actual_reflection described preparedBy accepted typed completed
  cases resultRep with
  | read initial selection represented =>
    cases initial with
    | initialized =>
      cases selection with
      | indexFound located => cases located
      | indexDefault _ defaulted => exact (unavailable defaulted.defaultable).elim
  | @missing root reason token count initial fault receipt =>
    cases initial with
    | initialized =>
      cases fault with
      | indexDefaultUnavailable matched absent missing =>
        exact ⟨token, count, futureWorld, rfl, .indexDefaultUnavailable matched absent missing, receipt, heaps⟩
      | indexFound _ located => cases located
      | indexDefault _ _ defaulted => exact (unavailable defaulted.defaultable).elim
  | uninitialized empty => cases empty

private def lowered : SourceCoreBasic.LoweredExpr := ⟨.bool, LanguageResult.success (.bool true)⟩
private def Child : GenericExpressionMeaning.Certificate := fun _ id code => id = key ∧ code = lowered
private theorem contains : ContainsExpression source key node := lookupExpression?_sound (by cbv)

/-- The child reflection IH is proved uniformly, including every hidden-slot
renaming. Its source execution is constructed from the completed Core child. -/
private theorem childReflects (registry : SourceCoreRawMetadata.Registry) (faults : GenericExpressionMeaning.FaultRep) :
    GenericExpressionMeaning.Reflects (payloadModel checked registry (noFunctions checked.catalog))
      program context [] source Child faults := by
  intro scope id code certificate n found mapping world administrative environment canonical actual before store ξ value finalStore
    environments heaps locals agrees evaluated
  obtain ⟨rfl, rfl⟩ := certificate
  have nodeEq : n = node := Option.some.inj (found.symm.trans (show source.lookupExpression? key = some node by cbv))
  subst n
  cases evaluated with
  | inRight inner =>
    cases inner
    exact ⟨.value (.bool true), before, mapping, world, .value (.intro contains (.builtinBoolean rfl) .nil),
      .value (.bool true), heaps, .refl _, .refl _, .refl _ _, .refl _⟩

private def scope (prepared : Prepared) : SourceCoreLocalCell.Scope := [(binder.id, prepared.route.rootType)]
private def getCode (prepared : Prepared) : Expr :=
  .apply (getter prepared .bool) (.pair (.loadCell (.var 1)) (.var 0))
private def putCode (prepared : Prepared) : Expr :=
  .apply (setter prepared .bool) (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0)))
private def getContext (prepared : Prepared) : Core.Context :=
  [.bool, OptionalCell.referenceType prepared.route.rootType, OptionalCell.referenceType prepared.route.rootType]
private def putContext (prepared : Prepared) : Core.Context :=
  [prepared.route.leafType, prepared.route.leafType, prepared.optionalLeaf, .bool,
    OptionalCell.referenceType prepared.route.rootType, OptionalCell.referenceType prepared.route.rootType]

private theorem pathViews {steps : List PreparedStep} {keySites : List (ExpressionId × Ty)} {leaf : TypeSystem.Ty}
    (path : PreparedPath checked source site rootType assignment.target.projections 0 steps keySites leaf) : KeyViews path [.bool] := by
  cases path with
  | index certificate generated tail =>
    have same := TypeSystem.Ty.mapping.inj certificate.view
    obtain ⟨rfl, rfl⟩ := same
    cases tail
    exact .index (certificate := certificate) (generated := generated) rfl .nil

private theorem staticReceipt {route : Route} {prepared : Prepared}
    (described : describe compilation checked.signatures source site assignment = .ok route)
    (preparedBy : prepare compilation 100 route Word.zero (fun _ => Word.ofNatModulo 100) = .ok prepared)
    (keyTypes : prepared.keyTypes = [.bool]) (nonempty : prepared.steps ≠ [])
    (getterTyped : HasType (getContext prepared) (getCode prepared) (LanguageResult.resultType prepared.optionalLeaf) checked.catalog.definitions)
    (setterTyped : HasType (putContext prepared) (putCode prepared) (LanguageResult.resultType prepared.route.rootType) checked.catalog.definitions) :
    prepared.route.rootSourceType = rootType ∧ checked.catalog.project valueType = .ok prepared.route.leafType ∧
    checked.catalog.project rootType = .ok prepared.route.rootType ∧
    ∃ leaf, SourceCoreRawMetadata.runtimeType leaf = valueType ∧
      CompatiblePlaceAssignmentSuccess.Layout compilation source Child (scope prepared) site assignment.target prepared [lowered] [.bool] leaf [] := by
  obtain ⟨actualBinder, leaf, receipt⟩ := CompatiblePlaceDescription.of_describe described
  have same := Except.ok.inj (receipt.binding.symm.trans (show rootBinder source assignment.target.root = .ok binder by cbv))
  subst actualBinder
  obtain ⟨routeEq, _, path⟩ := receipt.prepared preparedBy
  have rootEq : prepared.route.rootSourceType = rootType := routeEq ▸ receipt.rootSource
  have leafEq : checked.catalog.project valueType = .ok prepared.route.leafType := by
    rw [routeEq]
    exact receipt.leafProjected
  have children : DataExpressionSequence.Tree source Child (scope prepared)
      (DataPlaceKeyOrder.sourceKeys assignment.target.projections) [.bool] [lowered] :=
    .single (node := node) (by cbv) ⟨rfl, rfl⟩
  have views := pathViews path
  have actualPath : PreparedPath checked source site prepared.route.rootSourceType assignment.target.projections 0 prepared.steps prepared.keys leaf := by
    simpa only [rootEq, compilation, SourceCoreCompatibleValues.Context.initial, binder, TypeSystem.Scheme.mono] using path
  refine ⟨rootEq, leafEq, by simpa only [routeEq, compilation, SourceCoreCompatibleValues.Context.initial, binder, TypeSystem.Scheme.mono] using receipt.rootProjected, leaf, receipt.selectedType, ?_⟩
  refine ⟨actualPath, by simpa only [rootEq, compilation, SourceCoreCompatibleValues.Context.initial, binder, TypeSystem.Scheme.mono] using views, children, keyTypes, ?_, ?_, nonempty, getterTyped, setterTyped⟩
  · change checked.catalog.project leaf = .ok prepared.route.leafType
    rw [← checked.catalog.project_runtimeType leaf, receipt.selectedType]; exact leafEq
  · intro key value declared
    rw [routeEq]
    apply receipt.virtual key value
    exact rootEq.symm.trans declared

private def sourceEnvironment : Dynamic.Environment := [(binder.id, ⟨0⟩)]
private def nativeEnvironment (prepared : Prepared) : Environment := [.cellRef (OptionalCell.cellType prepared.route.rootType) 0]
private def body (prepared : Prepared) : Expr :=
  execute prepared (.var 0) (SourceCoreCalls.packArguments [lowered])
    (LanguageResult.failure prepared.route.leafType (.word (Word.ofNatModulo 777)))
    (LanguageResult.failure .bool (.word (Word.ofNatModulo 888))) .bool none false Word.zero
private theorem localAgrees : Dynamic.EnvironmentAgrees before context.locals sourceEnvironment :=
  .cons (.intro .head) rfl (.ordinary rfl rfl) .nil
private theorem rootWritable : WritableLocal context binder.id rootType :=
  WritableLocal.withLocal_mono _ _ _ ⟨(TypeParameterBindersWellFormed.ofSignatures signatures).withLocal binder.id binder.scheme,
    .mapping (.builtin .bool) (.function (.builtin .bool) (.builtin .bool))⟩
private def diagnostics (registry : SourceCoreRawMetadata.Registry) (prepared : Prepared) : GenericExpressionMeaning.FaultRep :=
  fun reason token =>
    (∃ root resolved count, FaultToken checked registry root prepared.steps resolved reason token count) ∨
    (∃ location, reason = .uninitializedLocation location ∧ token = prepared.invalidProjection) ∨
    ∃ code, reason = .panic code ∧ token = Solcore.Frontend.SourceCorePanics.reason code

/-- Every panic fails with its code's reason. -/
private instance (registry : SourceCoreRawMetadata.Registry) (prepared : Prepared) :
    FunctionCalls.FaultTokens (diagnostics registry prepared) :=
  ⟨fun code => .inr (.inr ⟨code, rfl, rfl⟩)⟩

/-- A real completed emitted assignment reconstructs its source target prefix.
There is no source key, source read or native helper execution premise. -/
theorem whole_reflection {route : Route} {prepared : Prepared}
    (described : describe compilation checked.signatures source site assignment = .ok route)
    (preparedBy : prepare compilation 100 route Word.zero (fun _ => Word.ofNatModulo 100) = .ok prepared)
    (keyTypes : prepared.keyTypes = [.bool]) (nonempty : prepared.steps ≠ [])
    (getterTyped : HasType (getContext prepared) (getCode prepared) (LanguageResult.resultType prepared.optionalLeaf) checked.catalog.definitions)
    (setterTyped : HasType (putContext prepared) (putCode prepared) (LanguageResult.resultType prepared.route.rootType) checked.catalog.definitions)
    {encoded : SourceCoreCompatibleValues.Encoded 100 compilation rootType carrier}
    (accepted : SourceCoreCompatibleValues.encode 100 compilation rootType carrier = .ok encoded)
    {result : Value} {after : Store}
    (completed : Evaluates (nativeEnvironment prepared) [.inRight .unit encoded.value] (body prepared) result after) :
    ∃ leaf, CompatiblePlacePrefixReflection.Result checked encoded.context.registry (noFunctions checked.catalog) program context [] source
      (diagnostics encoded.context.registry prepared) prepared [lowered] [.bool] assignment.target leaf sourceEnvironment
      (nativeEnvironment prepared) before [.inRight .unit encoded.value] [0] (world prepared)
      (LanguageResult.failure prepared.route.leafType (.word (Word.ofNatModulo 777)))
      (LanguageResult.failure .bool (.word (Word.ofNatModulo 888))) .bool none false Word.zero result after := by
  obtain ⟨rootEq, _, rootProjection, leaf, _, layout⟩ := staticReceipt described preparedBy keyTypes nonempty getterTyped setterTyped
  obtain ⟨actualBinder, _, description⟩ := CompatiblePlaceDescription.of_describe described
  have same := Except.ok.inj (description.binding.symm.trans (show rootBinder source assignment.target.root = .ok binder by cbv))
  subst actualBinder
  have routeEq := (description.prepared preparedBy).1
  have ordinary : (∀ k v, prepared.route.rootSourceType ≠ .mapping k v) → prepared.route.rootMapping = none := by
    intro nonmapping
    rw [routeEq]
    exact description.ordinary (fun k v same => nonmapping k v (rootEq.trans same))
  have empty : HeapRepresents checked encoded.context.registry (noFunctions checked.catalog) [] [] ⟨[]⟩ [] := GenericHeap.HeapRepresents.empty
  have represented := CompatibleEncoding.encode_represents_at (functions := noFunctions checked.catalog) accepted carrierMeaning [] []
  have same := Except.ok.inj (represented.projection.symm.trans rootProjection)
  rw [same] at represented
  obtain ⟨heaps, reference⟩ := empty.allocate (.initialized represented) Dynamic.Heap.Allocates.append
  have environments : DataHeap.EnvRepresents (storageCatalog checked.catalog) [0] (world prepared) [] (scope prepared)
      sourceEnvironment (nativeEnvironment prepared) := .cons reference (.nil .nil)
  refine ⟨leaf, CompatiblePlacePrefixReflection.reflects (index := 0) layout ordinary encoded.preserves
    (childReflects encoded.context.registry _) functionViews faithful observations ?_ ?_ environments heaps localAgrees
    (by simp [scope, SourceCoreLocalCell.lookup?, assignment]) (rootEq ▸ rootWritable) completed⟩
  · intro root resolved reason token count receipt
    exact .inl ⟨root, resolved, count, receipt⟩
  · intro location
    exact .inr (.inl ⟨location, rfl, rfl⟩)

private def wholeExercise {route : Route} {prepared : Prepared}
    (described : describe compilation checked.signatures source site assignment = .ok route)
    (preparedBy : prepare compilation 100 route Word.zero (fun _ => Word.ofNatModulo 100) = .ok prepared)
    {encoded : SourceCoreCompatibleValues.Encoded 100 compilation rootType carrier}
    (accepted : SourceCoreCompatibleValues.encode 100 compilation rootType carrier = .ok encoded) : IO Unit := do
  if keyTypes : prepared.keyTypes = [.bool] then
    if nonempty : prepared.steps ≠ [] then
      if getTyped : infer? (getContext prepared) (getCode prepared) checked.catalog.definitions = some (LanguageResult.resultType prepared.optionalLeaf) then
        if putTyped : infer? (putContext prepared) (putCode prepared) checked.catalog.definitions = some (LanguageResult.resultType prepared.route.rootType) then
          unless infer? (SourceCoreLocalCell.coreContext (scope prepared)) (body prepared) checked.catalog.definitions == some (LanguageResult.resultType .bool) do
            throw (IO.userError "prefix reflection actual checker rejected")
          let initial := Core.State.initial (body prepared) (nativeEnvironment prepared) [.inRight .unit encoded.value]
          match ran : runStateful 200000 initial with
          | .done result after =>
            have _reflected := whole_reflection described preparedBy keyTypes nonempty (infer_sound getTyped) (infer_sound putTyped)
              accepted (runStateful_evaluation_sound ran)
            let header ← match encoded.value with
              | .pair (.word header) _ => pure header
              | _ => throw (IO.userError "prefix reflection header missing")
            unless result == .inLeft .bool (.word ((Word.ofNatModulo 100).add header)) &&
                after.take 1 == [.inRight .unit encoded.value] && after.length == checked.catalog.entries.length + 2 do
              throw (IO.userError "prefix reflection fault order or heap changed")
            match runStateful 11 initial with
            | .outOfFuel checkpoint => unless runStateful 200000 checkpoint == .done result after do
                throw (IO.userError "prefix reflection resume changed result")
            | _ => throw (IO.userError "prefix reflection expected checkpoint")
          | other => throw (IO.userError s!"prefix reflection failed {reprStr other}")
        else throw (IO.userError "prefix reflection setter checker rejected")
      else throw (IO.userError "prefix reflection getter checker rejected")
    else throw (IO.userError "prefix reflection missing steps")
  else throw (IO.userError "prefix reflection key types changed")

private def exercise {route : Route} {prepared : Prepared}
    (described : describe compilation checked.signatures source site assignment = .ok route)
    (preparedBy : prepare compilation 100 route Word.zero (fun _ => Word.ofNatModulo 100) = .ok prepared)
    {encoded : SourceCoreCompatibleValues.Encoded 100 compilation rootType carrier}
    (accepted : SourceCoreCompatibleValues.encode 100 compilation rootType carrier = .ok encoded) : IO Unit := do
  if typed : infer? (coreContext prepared) (code prepared) checked.catalog.definitions = some (LanguageResult.resultType prepared.optionalLeaf) then
    let initial := Core.State.initial (code prepared) (environment prepared) [.inRight .unit encoded.value]
    match ran : runStateful 200000 initial with
    | .done result after =>
      have _reflected := actual_missing described preparedBy accepted (infer_sound typed) (runStateful_evaluation_sound ran)
      let header ← match encoded.value with
        | .pair (.word header) _ => pure header
        | _ => throw (IO.userError "getter reflection header missing")
      unless result == .inLeft prepared.optionalLeaf (.word ((Word.ofNatModulo 100).add header)) &&
          after.take 1 == [.inRight .unit encoded.value] && after.length == checked.catalog.entries.length + 2 do
        throw (IO.userError "getter reflection raw key/default or heap changed")
      match runStateful 11 initial with
      | .outOfFuel checkpoint => unless runStateful 200000 checkpoint == .done result after do
          throw (IO.userError "getter reflection resume changed result")
      | _ => throw (IO.userError "getter reflection expected checkpoint")
    | other => throw (IO.userError s!"getter reflection failed {reprStr other}")
  else throw (IO.userError "getter reflection actual checker rejected")

def run : IO Unit := do
  match described : describe compilation checked.signatures source site assignment with
  | .error error => throw (IO.userError s!"getter reflection describe failed {reprStr error}")
  | .ok route =>
    match preparedBy : prepare compilation 100 route Word.zero (fun _ => Word.ofNatModulo 100) with
    | .error error => throw (IO.userError s!"getter reflection prepare failed {reprStr error}")
    | .ok _ =>
      match accepted : SourceCoreCompatibleValues.encode 100 compilation rootType carrier with
      | .error error => throw (IO.userError s!"getter reflection encode failed {reprStr error}")
      | .ok _ =>
        exercise described preparedBy accepted
        wholeExercise described preparedBy accepted
  IO.println "compatible live getter reflection derives staged key fault from actual run GREEN"

end Tests.SourceCoreCompatibleGetterReflection
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleHeap
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! The compatible profile uses the existing allocation/write/frame laws,
including a nonidentity source/native location map. Raw staged mapping headers
survive actual encoding, registry extension, and the new key-vector adapter. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.SourceCoreCompatibleHeap
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces CompatiblePlaceKeys

private theorem except_get {α ε : Type} (result : Except ε α) (positive : result.toOption.isSome = true) :
    result = .ok (result.toOption.get positive) := by
  cases result with | error => simp [Except.toOption] at positive | ok => rfl
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def rootType : TypeSystem.Ty := .mapping .bool .word
private theorem preparedExists : (SourceCoreCompatibleCatalog.prepare signatures 100 [rootType, .proxy .word]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 100 [rootType, .proxy .word]).toOption.get preparedExists
private def context := SourceCoreCompatibleValues.Context.initial checked
private def noFunctions (catalog : SourceCoreCompatibleCatalog.Catalog) : FunctionModel catalog where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible
private def w (n : Nat) : Word := Word.ofNatModulo n
private def carrier : SourceCoreDataValues.Value := .mapping (.comptime .bool) .word [(.bool true, .word (w 7)), (.bool true, .word (w 9))]
private def sourceRoot : Dynamic.Value := .mapping (.comptime .bool) .word [(.bool true, .word (w 7)), (.bool true, .word (w 9))]
private theorem meaning : CompatibleEncoding.Means carrier sourceRoot :=
  .mapping (.prepend (.bool _) (.word _) (.prepend (.bool _) (.word _) .empty))

/-- This profile really differs from strict projection; only its registered
native definitions are shared by the heap adapter. -/
example : checked.catalog.project rootType ≠ (Except.mapError SourceCoreCompatibleCatalog.Error.catalog
    ((storageCatalog checked.catalog).project rootType)) := by cbv; intro impossible; cases impossible

private theorem allocate_encoded {encoded : SourceCoreCompatibleValues.Encoded 100 context rootType carrier}
    (accepted : SourceCoreCompatibleValues.encode 100 context rootType carrier = .ok encoded) :
    HeapRepresents checked encoded.context.registry (noFunctions checked.catalog) [1]
      [.integer, OptionalCell.cellType encoded.type] ⟨[⟨rootType, some sourceRoot, none⟩]⟩ [.integer (-123), .inRight .unit encoded.value] ∧
      ReferenceRepresents [1] [.integer, OptionalCell.cellType encoded.type] ⟨0⟩ 1 encoded.type := by
  have empty : HeapRepresents checked encoded.context.registry (noFunctions checked.catalog) [] [] ⟨[]⟩ [] :=
    GenericHeap.HeapRepresents.empty
  have administrative := empty.allocate_administrative (RuntimeValueHasType.integer (value := -123))
  have represented := CompatibleEncoding.encode_represents_at (functions := noFunctions checked.catalog) accepted meaning [] [.integer]
  exact administrative.allocate (.initialized represented) .append

private theorem writes_preserve_raw_header {encoded : SourceCoreCompatibleValues.Encoded 100 context rootType carrier}
    (accepted : SourceCoreCompatibleValues.encode 100 context rootType carrier = .ok encoded) :
    ∃ updated,
      Store.write? [.integer (-123), .inRight .unit encoded.value] 1 (.inRight .unit encoded.value) = some updated ∧
      HeapRepresents checked encoded.context.registry (noFunctions checked.catalog) [1]
        [.integer, OptionalCell.cellType encoded.type] ⟨[⟨rootType, some sourceRoot, none⟩]⟩ updated ∧
      AdministrativePreserved [1] [.integer (-123), .inRight .unit encoded.value] [1] updated := by
  obtain ⟨heaps, reference⟩ := allocate_encoded accepted
  have represented := CompatibleEncoding.encode_represents_at (functions := noFunctions checked.catalog) accepted meaning [1]
    [.integer, OptionalCell.cellType encoded.type]
  exact heaps.write_initialized reference (.intro .head) represented (.intro (.intro .head) .head)

private theorem registry_transport {encoded : SourceCoreCompatibleValues.Encoded 100 context rootType carrier}
    (accepted : SourceCoreCompatibleValues.encode 100 context rootType carrier = .ok encoded)
    {future : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends encoded.context.registry future) :
    HeapRepresents checked future (noFunctions checked.catalog) [1]
      [.integer, OptionalCell.cellType encoded.type] ⟨[⟨rootType, some sourceRoot, none⟩]⟩ [.integer (-123), .inRight .unit encoded.value] :=
  (allocate_encoded accepted).1.extend_registry extension

/-- A staged type view is transported at the source level before native key
slots are equated. The same key adapter consumes the generic sequence result. -/
example {source : TypedSource} {site : SourceCoreElaboration.ErrorSite} {key : ExpressionId}
    {steps : List PreparedStep} {sites : List (ExpressionId × Ty)}
    (path : PreparedPath checked source site rootType [.index key] 0 steps sites .word)
    (registry : SourceCoreRawMetadata.Registry) :
    ∃ _views : KeyViews path [.comptime .bool],
      Arguments checked registry (noFunctions checked.catalog) [] [] source site [.bool true] path [.index (.bool true)] := by
  cases path with
  | index certificate generated tail =>
    have shape := TypeSystem.Ty.mapping.inj certificate.view
    obtain ⟨rfl, rfl⟩ := shape
    cases tail
    have views : KeyViews (site := site) (.index certificate generated .nil) [.comptime .bool] :=
      .index (certificate := certificate) (generated := generated) (tail := .nil (site := site)) rfl .nil
    refine ⟨views, ?_⟩
    apply views.arguments (.index .nil)
      (DataExpressionSequence.Values.cons (show ValueRep checked registry (noFunctions checked.catalog) [] [] (.comptime .bool) (.bool true) (.bool true) .bool from .compatible (actual := .bool) rfl (.bool true)) .nil)
    intro index value found
    simpa only [Nat.zero_add] using found

def run : IO Unit := do
  match accepted : SourceCoreCompatibleValues.encode 100 context rootType carrier with
  | .error error => throw (IO.userError s!"compatible heap encode failed: {reprStr error}")
  | .ok encoded =>
    have _allocated := allocate_encoded accepted
    have _written := writes_preserve_raw_header accepted
    match SourceCoreCompatibleValues.encode 100 encoded.context (.proxy .word) (.proxy (.comptime .word)) with
    | .error error => throw (IO.userError s!"compatible heap registry extension failed: {reprStr error}")
    | .ok extra =>
      have _transported := registry_transport accepted extra.preserves
      let before := [Value.integer (-123), Value.inRight .unit encoded.value]
      match runStateful 20 (.initial (.loadCell (.var 0)) [.cellRef (OptionalCell.cellType encoded.type) 1] before) with
      | .done (.inRight .unit value) after =>
        unless after == before do throw (IO.userError "compatible heap load wrote a cell")
        match SourceCoreCompatibleValues.decode 100 extra.context rootType value with
        | .ok decoded => unless decoded == carrier do throw (IO.userError "compatible heap lost raw header or duplicate order")
        | .error error => throw (IO.userError s!"compatible heap decode failed: {reprStr error}")
      | other => throw (IO.userError s!"compatible heap live read failed: {reprStr other}")
  IO.println "compatible generic heap and key adapter GREEN"

end Tests.SourceCoreCompatibleHeap
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleHeapOutputs
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreCompatibleHeapOutputs.Prepared.mk
#check_failure Solcore.Frontend.SourceCoreCompatibleHeapOutputs.decodeCell

/-! Actual checked source inputs, ordinary lets, updates, lazy mappings and
callable leaves are exported from their live typed marked stores. Initial
source cells are retained without validation. Generalized/lambda cells remain
explicit rejected boundaries of this first heap decoder. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleHeapOutputs
open Solcore Solcore.Frontend SourceInference
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Marked := SourceCoreCompatibleMarkedFunctions.Prepared
abbrev Decoder {checked : Checked} (marked : Marked checked) := SourceCoreCompatibleHeapOutputs.Prepared marked
abbrev Key := SourceSpecialization.SpecializationKey
abbrev Cell := SourceTypedRuntime.Cell

private def w (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def word (value : Nat) : SourceTypedRuntime.Value := .word (w value)
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function updates(value: Word) returns (Word) { let next = value; next += 2; return next; }",
    "function lazy() returns (Word) { let table: mapping(Word => Word); table[1] = 7; return 0; }",
    "function alias(value: mapping(@Word => Word)) returns (Word) { let stored = value; return 1; }",
    "function inc(value: Word) returns (Word) { return value + 1; }",
    "function holders() returns (Word) { let named = inc; let native = wordToInteger; return named(5); }",
    "function failure(value: Word) returns (Word) { let changed = value; changed = 11; let absent: Word; return absent; }",
    "function lambdaCell() returns (Word) { let f: function(Word) returns (Word) = lam(value: Word) { return value; }; return 1; }",
    "function principal() returns (Word) { let f = lam(value) { return value; }; return 1; }"
  ]}] }

private def key (program : CheckedProgram) (name : String) : IO Key :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure ⟨signature.id, []⟩
  | _ => throw (IO.userError s!"heap output fixture missing {name}")

private def initial (owner : Key) : List Cell := [
  {type := .error, value := some (.closure [] .unit []
    {owner := owner.declaration, inputs := [], roots := [], nodes := []}
    owner [(⟨owner.declaration, 999⟩, ⟨777⟩)] [])},
  {type := .word, value := some (.bool true)}]

private def checkCells {checked : Checked} (marked : Marked checked) (decoder : Decoder marked)
    (owner : Key) (arguments : List SourceTypedRuntime.Value) (expected : List Cell) : IO Unit := do
  let completion ← match marked.runSource owner arguments 100000 512 with
    | .ok result => pure result
    | .error error => throw (IO.userError s!"heap source invocation failed: {reprStr error}")
  let exported ← match SourceCoreCompatibleHeapOutputs.exportHeap decoder completion (initial owner) 512 with
    | .ok exported => pure exported
    | .error error => throw (IO.userError s!"heap export failed: {reprStr error}")
  assertTrue (reprStr exported.cells == reprStr expected)
    s!"heap values or raw source types changed: {reprStr exported.cells}"
  assertTrue (reprStr (exported.heap.take 2) == reprStr (initial owner)) "opaque heap prefix changed"
  assertTrue (exported.receipt.ledger.locations.map (·.source.index) == (List.range expected.length).map (2 + ·))
    "source-visible allocation order changed"
  assertTrue (exported.receipt.ledger.rows.map (fun row => row.environment.map Prod.fst) ==
    exported.receipt.ledger.rows.map (fun row => row.entry.key.scope.map Prod.fst)) "capture binder metadata changed"

private def checkpoints {checked : Checked} (marked : Marked checked) (decoder : Decoder marked) (owner : Key) : IO Unit := do
  let mut completion ← match marked.runSource owner [word 9] 0 512 with
    | .ok result => pure result | .error error => throw (IO.userError (reprStr error))
  let mut prior := ([] : List SourceCoreAllocationLedger.LocationEntry)
  let mut sawPending := false
  let mut finished := false
  for _ in List.range 1500 do
    let exported ← match SourceCoreCompatibleHeapOutputs.exportHeap decoder completion (initial owner) 512 with
      | .ok exported => pure exported
      | .error error => throw (IO.userError s!"checkpoint heap export failed: {reprStr error}")
    assertTrue (reprStr (exported.heap.take 2) == reprStr (initial owner)) "checkpoint lost opaque prefix"
    let locations := exported.receipt.ledger.locations
    assertTrue (decide (locations.take prior.length = prior)) "checkpoint changed prior source locations"
    prior := locations
    if exported.receipt.ledger.pending.isSome then sawPending := true
    match completion.result.native.observation with
    | .succeeded .. => finished := true; break
    | .outOfFuel _ => completion := completion.resume 1
    | observation => throw (IO.userError s!"checkpoint became unexpected result: {reprStr observation}")
  assertTrue sawPending "no pending source allocation checkpoint was exercised"
  assertTrue finished "finite update fixture did not finish"

private def rejected {checked : Checked} (marked : Marked checked) (decoder : Decoder marked) (owner : Key)
    (expected : SourceCoreCompatibleHeapOutputs.Error → Bool) : IO Unit := do
  let completion ← match marked.runSource owner [] 100000 512 with
    | .ok result => pure result | .error error => throw (IO.userError (reprStr error))
  match SourceCoreCompatibleHeapOutputs.exportHeap decoder completion [] 512 with
  | .error error => assertTrue (expected error) s!"heap boundary rejection changed: {reprStr error}"
  | .ok _ => throw (IO.userError "unsupported heap payload unexpectedly exported")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"heap fixture checker failed: {reprStr error}")
  let names := ["updates", "lazy", "alias", "holders", "failure", "lambdaCell", "principal"]
  let keys ← names.mapM (key program)
  let plan ← match SourceSpecializationWorklist.run program (keys.map (fun key => ⟨key.declaration, []⟩)) 256 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"heap fixture worklist failed: {reprStr result}")
  let automatic ← match SourceCoreCompatibleFunctions.prepare program plan 512 with
    | .ok automatic => pure automatic
    | .error error => throw (IO.userError s!"heap fixture base factory failed: {reprStr error}")
  let marked ← match SourceCoreCompatibleMarkedFunctions.prepare automatic.prepared 512 with
    | .ok marked => pure marked
    | .error error => throw (IO.userError s!"heap fixture marked factory failed: {reprStr error}")
  let decoder ← match SourceCoreCompatibleHeapOutputs.prepare marked with
    | .ok decoder => pure decoder
    | .error error => throw (IO.userError s!"heap output recipe failed: {reprStr error}")
  let updates ← key program "updates"
  checkCells marked decoder updates [word 9] [⟨.word, some (word 9)⟩, ⟨.word, some (word 11)⟩]
  checkCells marked decoder (← key program "lazy") []
    [⟨.mapping .word .word, some (.mapping .word .word [(word 1, word 7)])⟩]
  let raw : SourceTypedRuntime.Value := .mapping (.proxy (.comptime .word)) .word
    [(.proxy (.comptime .word), word 7), (.proxy (.comptime .word), word 8)]
  let aliasType := TypeSystem.Ty.mapping (.proxy .word) .word
  checkCells marked decoder (← key program "alias") [raw] [⟨aliasType, some raw⟩, ⟨aliasType, some raw⟩]
  let inc ← key program "inc"
  checkCells marked decoder (← key program "holders") []
    [⟨.function .word .word, some (.global inc [])⟩,
     ⟨.function .word .integer, some (.builtin .wordToInteger)⟩, ⟨.word, some (word 5)⟩]
  checkCells marked decoder (← key program "failure") [word 9]
    [⟨.word, some (word 9)⟩, ⟨.word, some (word 11)⟩, ⟨.word, none⟩]
  checkpoints marked decoder updates
  rejected marked decoder (← key program "lambdaCell") fun
    | .output {code := .lambdaExportRequiresLedger _, ..} => true | _ => false
  rejected marked decoder (← key program "principal") fun
    | .generalizedBinding _ _ => true | _ => false

example {checked : Checked} {marked : Marked checked} {decoder : Decoder marked}
    {completion : SourceCoreCompatibleMarkedFunctions.Completion marked} {initial : List Cell}
    (exported : SourceCoreCompatibleHeapOutputs.Export decoder completion initial) :
    exported.heap.take initial.length = initial := exported.prefix_exact

example {checked : Checked} {marked : Marked checked} {decoder : Decoder marked}
    {completion : SourceCoreCompatibleMarkedFunctions.Completion marked} {initial : List Cell}
    (exported : SourceCoreCompatibleHeapOutputs.Export decoder completion initial) :
    exported.cells.map (·.type) = exported.receipt.ledger.rows.map SourceCoreCompatibleHeapOutputs.rawType :=
  exported.decoded.types_exact

end Tests.SourceCoreCompatibleHeapOutputs
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleInputs
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreCompatibleInputs.encodeRaw

/-! Public validation precedes injection below cached, installed globals.
The fixtures compile source bodies once; invocations reuse the cached closures.
Only global/builtin source leaves pass the existing validator, even inside
nominal payloads, products and ordered mappings. Source heap export is separate. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleInputs
open Solcore Solcore.Frontend SourceInference
abbrev SourceValue := SourceTypedRuntime.Value
abbrev Key := SourceSpecialization.SpecializationKey
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Prepared := SourceCoreCompatibleFunctions.Prepared

private def w (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def assertTrue (test : Bool) (message : String) : IO Unit :=
  unless test do throw (IO.userError message)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Holder { Hold(function(Word) returns (Word)) }",
    "function inc(value: Word) returns (Word) { return value + 1; }",
    "function consume(f: function(Word) returns (Word), value: Word) returns (Word) { return f(value); }",
    "function nominal(value: Holder, n: Word) returns (Word) { match (value) { case .Hold(f) { return f(n); } } }",
    "function product(value: (Word, function(Word) returns (Word))) returns (Word) { match (value) { case (n, f) { return f(n); } } }",
    "function table(values: mapping(Word => function(Word) returns (Word)), n: Word) returns (Word) { return values[7](n); }",
    "function keyTable(values: mapping(function(Word) returns (Word) => Word), f: function(Word) returns (Word)) returns (Word) { return values[f]; }",
    "function builtin(f: function(Word) returns (integer), n: Word) returns (integer) { return f(n); }",
    "function wideData(values: mapping(Word => Word)) returns (mapping(Word => Word)) { return values; }",
    "function alias(values: mapping(@Word => Word)) returns (mapping(@Word => Word)) { return values; }",
    "function outsider(value: Word) returns (Word) { return value; }"
  ]}] }

private def key (program : CheckedProgram) (name : String) : IO Key := do
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure ⟨signature.id, []⟩
  | _ => throw (IO.userError s!"compatible input fixture missing: {name}")

example {context : Solcore.Frontend.SourceCoreCompatibleInputs.Context} {expected : List TypeSystem.Ty} {arguments : List SourceValue}
    {fuel : Nat} (encoded : Solcore.Frontend.SourceCoreCompatibleInputs.Encoded context expected arguments fuel) :
    Core.HasType context.coreContext encoded.expression (Core.LanguageResult.resultType encoded.type)
      context.definitions := encoded.typed

example {context : Solcore.Frontend.SourceCoreCompatibleInputs.Context} {expected : List TypeSystem.Ty} {arguments : List SourceValue}
    {fuel : Nat} (encoded : Solcore.Frontend.SourceCoreCompatibleInputs.Encoded context expected arguments fuel) :
    SourceTypedRuntime.validateInputs context.values.checked.signatures context.validationPlan
      fuel expected arguments = none := encoded.validated

private def inputContext {checked : Checked} (prepared : Prepared checked)
    (validationPlan : SourceSpecializationWorklist.Plan) : IO Solcore.Frontend.SourceCoreCompatibleInputs.Context := do
  match Solcore.Frontend.SourceCoreCompatibleInputs.prepare (SourceCoreCompatibleValues.Context.initial checked) prepared.plan prepared.globals
      (prepared.callableContext.map (·.table)) checked.catalog.definitions (w 900) (some validationPlan) with
  | .ok context => pure context
  | .error error => throw (IO.userError s!"compatible cached input context failed: {reprStr error}")

private def check {checked : Checked} (prepared : Prepared checked) (context : Solcore.Frontend.SourceCoreCompatibleInputs.Context)
    (owner : Key) (arguments : List SourceValue) (expected : Core.Value) (validationFuel : Nat := 256) : IO Unit := do
  let function ← match prepared.functions.find? (fun function => decide (function.signature.key = owner)) with
    | some found => pure found | none => throw (IO.userError "compatible input root absent")
  let encoded ← match Solcore.Frontend.SourceCoreCompatibleInputs.encode context (function.inputs.map (fun pair => pair.1.scheme.body)) arguments validationFuel with
    | .ok encoded => pure encoded | .error error => throw (IO.userError s!"compatible source input rejected: {reprStr error}")
  let body ← match SourceCoreGeneralFunctions.assembleCall prepared.globals prepared.functions prepared.closures
      owner ⟨encoded.type, encoded.expression⟩ with
    | .ok body => pure body | .error error => throw (IO.userError s!"compatible source call assembly failed: {reprStr error}")
  let program : Core.Program := ⟨Core.LanguageResult.resultType function.signature.resultType, body, context.definitions⟩
  assertTrue program.check "compatible expression injection failed actual closed Core checker"
  let native ← match SourceCoreGeneralEntry.NativeEntry.compile context.definitions [] function.signature.resultType body with
    | .ok native => pure native | .error error => throw (IO.userError s!"compatible input typed checkpoint check failed: {reprStr error}")
  let checkpoint ← match native.start [] with
    | .ok checkpoint => pure checkpoint | .error error => throw (IO.userError s!"compatible input typed checkpoint start failed: {reprStr error}")
  for fuel in [0, 7, 37, 150000] do
    let result := checkpoint.resume fuel
    let result := match result.checkpoint? with
      | some next => next.resume 150000
      | none => result
    match result.observation with
    | .succeeded value store =>
        assertTrue (value == expected) s!"compatible source input result changed: {reprStr value}"
        assertTrue (prepared.globals.length ≤ store.length) "compatible globals world shrank"
    | observation => throw (IO.userError s!"compatible source input execution failed: {reprStr observation}")

private def sameRejection (context : Solcore.Frontend.SourceCoreCompatibleInputs.Context) (expected : List TypeSystem.Ty)
    (arguments : List SourceValue) (validationFuel : Nat := 256) : IO Unit := do
  let old := SourceTypedRuntime.validateInputs context.values.checked.signatures context.validationPlan
    validationFuel expected arguments
  match old, Solcore.Frontend.SourceCoreCompatibleInputs.encode context expected arguments validationFuel with
  | some old, .error (.source actual) =>
      assertTrue (reprStr old == reprStr actual) s!"compatible input error/order changed: {reprStr actual}"
  | _, _ => throw (IO.userError "compatible input rejection did not preserve pure public validator")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok checked => pure checked | .error error => throw (IO.userError s!"compatible input source rejected: {reprStr error}")
  let roots := (program.signatures.functions.filter (·.name != "outsider")).map (fun signature => (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request))
  let original ← match SourceSpecializationWorklist.run program roots 300 with
    | .ok (.complete plan) => pure plan | result => throw (IO.userError s!"compatible input plan failed: {reprStr result}")
  let automatic ← match SourceCoreCompatibleFunctions.prepare program original 500 with
    | .ok prepared => pure prepared | .error error => throw (IO.userError s!"compatible input cached factory failed: {reprStr error}")
  let prepared := automatic.prepared
  let context ← inputContext prepared original
  let inc ← key program "inc"
  let named : SourceValue := .global inc []
  let functionType := TypeSystem.Ty.function .word .word
  let consume ← key program "consume"
  check prepared context consume [named, .word (w 8)] (.word (w 9))
  let holder ← match program.signatures.dataTypes.find? (·.name == "Holder") with
    | some holder => pure holder | none => throw (IO.userError "compatible input Holder absent")
  let constructor ← match holder.constructors[0]? with
    | some constructor => pure constructor | none => throw (IO.userError "compatible input Hold absent")
  let instantiation : DataConstructorInstantiation := ⟨constructor.id, [], [functionType], .nominal holder.id []⟩
  check prepared context (← key program "nominal") [.constructed instantiation [named], .word (w 8)] (.word (w 9))
  check prepared context (← key program "product") [.product (.word (w 8)) named] (.word (w 9))
  check prepared context (← key program "table")
    [.mapping .word functionType [(.word (w 7), named)], .word (w 8)] (.word (w 9))
  check prepared context (← key program "table")
    [.mapping (.comptime .word) (.comptime functionType) [(.word (w 7), named)], .word (w 8)] (.word (w 9))
  check prepared context (← key program "keyTable")
    [.mapping functionType .word [(named, .word (w 12)), (named, .word (w 19))], named] (.word (w 12))
  check prepared context (← key program "builtin") [.builtin .wordToInteger, .word (w 15)] (.integer 15)
  let incBody ← match original.specializations.find? (fun specialized => decide (specialized.key = inc)) with
    | some specialized => pure specialized.function.typedBody | none => throw (IO.userError "compatible inc body absent")
  let raw : SourceValue := .closure incBody.inputs .word
    (incBody.roots.filterMap fun | .statement id => some id | _ => none) incBody inc [] []
  sameRejection context [functionType] [raw]
  sameRejection context [functionType] [.instantiated [] [] named]
  sameRejection context [.product .word functionType] [.product (.word (w 8)) raw]
  sameRejection context [.mapping .word functionType] [.mapping .word functionType [(.word (w 7), raw)]]
  sameRejection context [.nominal holder.id []] [.constructed instantiation [raw]]
  sameRejection context [functionType] [.global (← key program "outsider") []]
  sameRejection context [functionType] [.global consume []]
  sameRejection context [functionType] [.builtin .wordToInteger]
  sameRejection context [.word, functionType] [.bool true, named, .unit]
  sameRejection context [functionType, .word] [named]
  sameRejection context [functionType] [named] 0
  sameRejection context [.word] [.word (w 1)] 0
  sameRejection context [.nominal holder.id []]
    [.constructed {instantiation with payloadTypes := [.bool]} [.bool true]]
  let entries := (List.range 100).map (fun index => (.word (w index), .word (w (index + 1))))
  let dataRoot ← key program "wideData"
  let dataFunction ← match prepared.functions.find? (fun function => decide (function.signature.key = dataRoot)) with
    | some found => pure found | none => throw (IO.userError "compatible wide input function absent")
  let wide ← match Solcore.Frontend.SourceCoreCompatibleInputs.encode context [TypeSystem.Ty.mapping .word .word] [.mapping .word .word entries] 2 with
    | .ok encoded => pure encoded | .error error => throw (IO.userError s!"accepted wide input ran out of encoding budget: {reprStr error}")
  assertTrue (wide.type == dataFunction.signature.parameterType) "compatible wide input projected type changed"
  let ordinary : SourceCoreCompatibleValues.Value := .mapping .word .word
    ((List.range 100).map (fun index => (.word (w index), .word (w (index + 1)))))
  let dataEncoded ← match SourceCoreCompatibleValues.encode 500 context.values (.mapping .word .word) ordinary with
    | .ok encoded => pure encoded | .error error => throw (IO.userError s!"compatible expected wide data encode failed: {reprStr error}")
  check prepared context dataRoot [.mapping .word .word entries] dataEncoded.value 2
  let aliasRaw : SourceCoreCompatibleValues.Value := .mapping (.proxy (.comptime .word)) (.comptime .word)
    [(.proxy (.comptime .word), .word (w 4)), (.proxy .word, .word (w 7))]
  let aliasEncoded ← match SourceCoreCompatibleValues.encode 500 context.values
      (.mapping (.proxy .word) .word) aliasRaw with
    | .ok encoded => pure encoded | .error error => throw (IO.userError s!"compatible raw input expected encode failed: {reprStr error}")
  check prepared context (← key program "alias")
    [.mapping (.proxy (.comptime .word)) (.comptime .word)
      [(.proxy (.comptime .word), .word (w 4)), (.proxy .word, .word (w 7))]] aliasEncoded.value
  match Solcore.Frontend.SourceCoreCompatibleInputs.prepare context.values prepared.plan prepared.globals.reverse (prepared.callableContext.map (·.table)) context.definitions with
  | .error .globalsOrderMismatch => pure ()
  | _ => throw (IO.userError "compatible input accepted foreign slot ordering")
  match Solcore.Frontend.SourceCoreCompatibleInputs.prepare context.values prepared.plan prepared.globals none context.definitions with
  | .error (.missingContract _) => pure ()
  | _ => throw (IO.userError "compatible input lost actual staged descriptor ownership")
  match Solcore.Frontend.SourceCoreCompatibleInputs.prepare context.values prepared.plan
      (prepared.globals.map (fun signature => {signature with resultType := .unit}))
      (prepared.callableContext.map (·.table)) context.definitions with
  | .error (.globalTypeMismatch _) => pure ()
  | _ => throw (IO.userError "compatible input accepted altered cached signatures")
  let ambient ← match Solcore.Frontend.SourceCoreCompatibleInputs.prepare context.values prepared.plan prepared.globals
      (prepared.callableContext.map (·.table)) (context.definitions ++ [⟨[.unit]⟩]) (w 900) (some original) with
    | .ok context => pure context | .error error => throw (IO.userError s!"compatible ambient context failed: {reprStr error}")
  check prepared ambient consume [named, .word (w 8)] (.word (w 9))
  let extendedPlan ← match SourceSpecializationWorklist.run program
      ((program.signatures.functions.map (fun signature => (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)))) 300 with
    | .ok (.complete plan) => pure plan | result => throw (IO.userError s!"compatible extended plan failed: {reprStr result}")
  let extended ← match SourceCoreCompatibleFunctions.prepare program extendedPlan 500 with
    | .ok prepared => pure prepared | .error error => throw (IO.userError s!"compatible extended cached factory failed: {reprStr error}")
  let retained ← inputContext extended.prepared original
  let outsider : SourceValue := .global (← key program "outsider") []
  sameRejection retained [functionType] [outsider]
  assertTrue (SourceTypedRuntime.validateInputs retained.values.checked.signatures extendedPlan 256 [functionType] [outsider]).isNone
    "compatible extended-plan fixture did not distinguish original public admission"
  IO.println "compatible public source function inputs, deep carriers, exact validation and cached/resumed Core GREEN"

end Tests.SourceCoreCompatibleInputs
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleLowerReflection
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.SourceCoreCompatibleLowerReflection
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys
open SourceCoreCompatibleDataPlaces

private theorem except_get {α ε : Type} (result : Except ε α) (positive : result.toOption.isSome = true) :
    result = .ok (result.toOption.get positive) := by
  cases result with | error => simp [Except.toOption] at positive | ok => rfl
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"compatible_lower_reflection", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "compatible_lower_reflection.solc"⟩, 0, 1⟩
private def key : ExpressionId := ⟨⟨owner, 1⟩⟩
private def site : SourceCoreElaboration.ErrorSite := .occurrence ⟨owner, 0⟩
private def rootType : TypeSystem.Ty := .mapping .bool .bool
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private theorem catalogExists : (SourceCoreCompatibleCatalog.prepare signatures 100 [rootType]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 100 [rootType]).toOption.get catalogExists
private def compilation := SourceCoreCompatibleValues.Context.initial checked
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "root", .mono rootType, [], false, none⟩
private def node : ExpressionNode := { id := key, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def source : TypedSource := { owner, inputs := [binder], roots := [.expression key], nodes := [.expression node] }
private def assignment : AssignmentResolution := ⟨⟨binder.id, [.index key], .bool⟩, []⟩
private def context := (SourceSemantics.Context.ofSignatures signatures).withLocal binder.id binder.scheme
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def noFunctions (catalog : SourceCoreCompatibleCatalog.Catalog) : FunctionModel catalog where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible
private theorem observations : FunctionObservations checked.catalog (noFunctions checked.catalog) (fun _ _ => False) := by
  intro _ _ _ _ _ _ _ impossible; exact impossible.elim
private theorem faithful : DataEquality.IdentityFaithful (fun _ _ => False) := by
  constructor <;> intros <;> contradiction
private theorem unique : NodeOccurrencesUnique source := by simp [NodeOccurrencesUnique, nodeOccurrenceIds, source]
private theorem contains : ContainsExpression source key node := lookupExpression?_sound (by cbv)
private def lowered : SourceCoreBasic.LoweredExpr := ⟨.bool, LanguageResult.success (.bool true)⟩
private def Child : GenericExpressionMeaning.Certificate := fun _ id code => id = key ∧ code = lowered

/-- The child reflection IH is proved uniformly, including every hidden-slot
renaming. Its source execution is constructed from the completed Core child. -/
private theorem childReflects (registry : SourceCoreRawMetadata.Registry) (faults : GenericExpressionMeaning.FaultRep) :
    GenericExpressionMeaning.Reflects (payloadModel checked registry (noFunctions checked.catalog))
      program context [] source Child faults := by
  intro scope id code certificate n found mapping world administrative environment canonical actual before store ξ value finalStore
    environments heaps locals agrees evaluated
  obtain ⟨rfl, rfl⟩ := certificate
  have nodeEq : n = node := Option.some.inj (found.symm.trans (show source.lookupExpression? key = some node by cbv))
  subst n
  cases evaluated with
  | inRight inner =>
    cases inner
    exact ⟨.value (.bool true), before, mapping, world, .value (.intro contains (.builtinBoolean rfl) .nil),
      .value (.bool true), heaps, .refl _, .refl _, .refl _ _, .refl _⟩

private theorem functionViews : FunctionRuntimeViews (noFunctions checked.catalog) := fun impossible => False.elim impossible
private theorem rootExists : (checked.catalog.project rootType).toOption.isSome = true := by cbv
private def rootCore := (checked.catalog.project rootType).toOption.get rootExists
private theorem rootProjected : checked.catalog.project rootType = .ok rootCore := except_get _ rootExists
private def scope : SourceCoreLocalCell.Scope := [(binder.id, rootCore)]
private def coreContext : Core.Context := [OptionalCell.referenceType rootCore]
private def before : Dynamic.Heap := ⟨[⟨rootType, none, none⟩]⟩
private def environment : Dynamic.Environment := [(binder.id, ⟨0⟩)]
private def store : Store := [.inLeft rootCore .unit]
private def world : StoreTyping := [OptionalCell.cellType rootCore]
private def nativeEnvironment : Environment := [.cellRef (OptionalCell.cellType rootCore) 0]
private theorem localAgrees : Dynamic.EnvironmentAgrees before context.locals environment :=
  .cons (.intro .head) rfl (.ordinary rfl rfl) .nil
private theorem rootWritable : WritableLocal context binder.id rootType :=
  WritableLocal.withLocal_mono _ _ _ ⟨(TypeParameterBindersWellFormed.ofSignatures signatures).withLocal binder.id binder.scheme,
    .mapping (.builtin .bool) (.builtin .bool)⟩
private theorem keyTyped : ExpressionHasType source context key .bool := by
  apply ExpressionHasType.ofOrdinary (node := node) (rawType := .bool) contains
    (.reference (.builtinBoolean true)) (.bool ((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal binder.id binder.scheme))
    (.bool ((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal binder.id binder.scheme))
  · intro id member; cases member
  · exact .nil _
  · rfl

/-- The fixture admits its only retained child occurrence and calls the real
Basic compiler in that branch. It contains no evaluator or hypothetical code. -/
private def childCompiler : ExpressionLowerer := fun fuel source scope id reasonAt =>
  if id = key then SourceCoreBasic.lowerExpression fuel source scope id (reasonAt id)
  else .error (.missingExpression id)
private theorem childReceipt (id : ExpressionId) (code : SourceCoreBasic.LoweredExpr)
    (accepted : childCompiler 100 source scope id (fun _ => Word.zero) = .ok code) :
    ∃ node, source.lookupExpression? id = some node ∧ Child scope id code ∧
      HasType (SourceCoreLocalCell.coreContext scope ++ []) code.expression (LanguageResult.resultType code.type) checked.catalog.definitions := by
  unfold childCompiler at accepted
  split at accepted
  · rename_i same
    subst id
    have actual : SourceCoreBasic.lowerExpression 100 source scope key Word.zero = .ok lowered := by cbv
    rw [actual] at accepted
    cases accepted
    exact ⟨node, (by cbv), ⟨rfl, rfl⟩, .inRight .word .bool⟩
  · cases accepted

/-- A successful run of the real lowerer's output yields a complete source
assignment and final represented heap. Path, key views and both helper typing
receipts are extracted internally, not supplied by this fixture. -/
theorem actual_lower_reflects {code : Expr}
    (accepted : lower compilation checked.signatures childCompiler 100 source scope site assignment .equal (some key) .bool
      lowered.expression (fun _ => Word.zero) Word.zero Word.zero (fun _ => Word.zero) = .ok code)
    (typed : HasType coreContext code (LanguageResult.resultType .bool) checked.catalog.definitions)
    {after : Store}
    (completed : Evaluates nativeEnvironment store code (.inRight .word (.bool true)) after) :
    ∃ updated sourceAfter finalMap finalWorld,
      Dynamic.SourcePlaceAssignment program context [] source (Dynamic.AssignmentValueApplies .equal)
        environment before assignment.target key updated sourceAfter ∧
      HeapRepresents checked compilation.registry (noFunctions checked.catalog) finalMap finalWorld sourceAfter after ∧
      LocationMap.Extends [0] finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved [0] store finalMap after ∧ Dynamic.HeapMetadataExtend before sourceAfter := by
  have empty : HeapRepresents checked compilation.registry (noFunctions checked.catalog) [] [] ⟨[]⟩ [] := GenericHeap.HeapRepresents.empty
  obtain ⟨heaps, reference⟩ := empty.allocate (.uninitialized rootProjected) Dynamic.Heap.Allocates.append
  have environments : DataHeap.EnvRepresents (storageCatalog checked.catalog) [0] world [] scope environment nativeEnvironment :=
    .cons reference (.nil .nil)
  have binding : ∀ actual, rootBinder source assignment.target.root = .ok actual → actual = binder := by
    intro actual found
    exact Except.ok.inj (found.symm.trans (show rootBinder source assignment.target.root = .ok binder by cbv))
  -- The trivial relation relates every panic too.
  haveI : FunctionCalls.FaultTokens (fun _ _ => True) := ⟨fun _ => trivial⟩
  have reflected := CompatiblePlaceLowerReflection.reflects (compilation := compilation) (ambient := .original checked.catalog.definitions) (functions := noFunctions checked.catalog) (certificate := Child)
    unique rfl (fun actual found => by cases binding actual found; exact .index keyTyped (.nil _)) keyTyped
    (fun actual found => by cases binding actual found; exact rootWritable) (by simp [assignment]) childReceipt accepted typed
    (.refl _) (childReflects compilation.registry (fun _ _ => True)) functionViews faithful observations
    (fun _ _ => True.intro) (fun _ => True.intro) (.inl rfl) environments heaps localAgrees completed
  cases reflected with
  | fault _ resultEq => cases resultEq
  | committed trace heaps maps worlds frame metadata length continuation =>
    simp only [shift, List.range, List.range.loop, List.foldl, Expr.weakenAt, lowered, LanguageResult.success] at continuation
    cases continuation with
    | inRight valueEvaluated =>
      cases valueEvaluated
      exact ⟨_, _, _, _, trace, heaps, maps, worlds, frame, metadata⟩

/-- Direct consumer of the real checked wrapper: its private compiler work
is recovered from success and its public typing field. -/
theorem checked_lower_reflects {certified : Certified checked.catalog.definitions coreContext .bool}
    (accepted : lowerChecked compilation checked.signatures childCompiler 100 source scope site assignment .equal (some key) .bool
      lowered.expression (fun _ => Word.zero) Word.zero Word.zero (fun _ => Word.zero) checked.catalog.definitions coreContext = .ok certified)
    {after : Store}
    (completed : Evaluates nativeEnvironment store certified.expression (.inRight .word (.bool true)) after) :
    ∃ updated sourceAfter finalMap finalWorld,
      Dynamic.SourcePlaceAssignment program context [] source (Dynamic.AssignmentValueApplies .equal)
        environment before assignment.target key updated sourceAfter ∧
      HeapRepresents checked compilation.registry (noFunctions checked.catalog) finalMap finalWorld sourceAfter after ∧
      LocationMap.Extends [0] finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved [0] store finalMap after ∧ Dynamic.HeapMetadataExtend before sourceAfter :=
  actual_lower_reflects (CompatiblePlaceCompilerCertificates.lower_of_lowerChecked accepted) certified.typed completed

def run : IO Unit := do
  match accepted : lowerChecked compilation checked.signatures childCompiler 100 source scope site assignment .equal (some key) .bool
      lowered.expression (fun _ => Word.zero) Word.zero Word.zero (fun _ => Word.zero) checked.catalog.definitions coreContext with
  | .error error => throw (IO.userError s!"compatible lower reflection rejected {reprStr error}")
  | .ok certified =>
      let initial := Core.State.initial certified.expression nativeEnvironment store
      match ran : runStateful 200000 initial with
      | .done result after =>
        if success : result = .inRight .word (.bool true) then
          have _source := checked_lower_reflects accepted (success ▸ runStateful_evaluation_sound ran)
          unless after.length == 1 + 3 * (checked.catalog.entries.length + 1) do
            throw (IO.userError "compatible lower reflection admin count changed")
          match after.read? 0 with
          | some (.inRight .unit value) =>
            match SourceCoreCompatibleValues.decode 100 compilation rootType value with
            | .ok actual => unless actual == .mapping .bool .bool [(.bool true, .bool true)] do
                throw (IO.userError "compatible lower reflection final source heap changed")
            | .error error => throw (IO.userError s!"compatible lower reflection decode failed {reprStr error}")
          | _ => throw (IO.userError "compatible lower reflection missing mapped write")
          match runStateful 17 initial with
          | .outOfFuel checkpoint => unless runStateful 200000 checkpoint == .done result after do
              throw (IO.userError "compatible lower reflection resume changed result")
          | _ => throw (IO.userError "compatible lower reflection expected checkpoint")
        else throw (IO.userError "compatible lower reflection expected success")
      | other => throw (IO.userError s!"compatible lower reflection run failed {reprStr other}")
  IO.println "actual compatible lower/check/run extracts layout and independent complete source assignment GREEN"

end Tests.SourceCoreCompatibleLowerReflection
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleMarkedFunctions
/-! Real checked multi-root compilation with one fixed allocation suffix.
Execution and resumption use the shared typed Core machine. Closures capture by
value: each call starts again from the values its captures had when the lambda
was created. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleMarkedFunctions
open Solcore Solcore.Frontend SourceInference
abbrev Key := SourceSpecialization.SpecializationKey

private def assertTrue (test : Bool) (message : String) : IO Unit :=
  unless test do throw (IO.userError message)
private def w (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box<T> { Box(T) }",
    "trait Marker<T> {}", "impl Marker<mapping(Word => Word)> {}",
    "function keep<T>(value: T) returns (T) where T: Marker { return value; }",
    "function local(table: mapping(Word => Word)) returns (mapping(Word => Word)) { let f = lam(item) { return keep(item); }; return f(table); }",
    "function lazy() returns (mapping(Word => Word)) { let table: mapping(Word => Word); table[1] = 7; return table; }",
    "function choose(value: Box<Word>) returns (Word) { match (value) { case .Box(bound) { return bound; } default { return 99; } } }",
    "function capture(start: Word) returns (Word) { let value = start; let f = lam(step: Word) { value += step; return value; }; f(3); return f(4); }",
    "function recursive(n: Word) returns (Word) { let f: function(Word) returns (Word); f = lam(left: Word) { return left == 0 ? 0 : f(left - 1) + 1; }; return f(n); }",
    "function unused() returns (Word) { let unused = lam(item) { return item; }; return 7; }",
    "function tuple(value: (Word, Bool)) returns (Word) { match (value) { case ((left, flag)) { return flag ? left : 99; } default { return 77; } } }",
    "function looping(limit: Word) returns (Word) { let total = 0; for (let i = 0; i < limit; i += 1) { total += i; } return total; }",
    "function absent() returns (Word) { let absent: Word; return absent; }"
    , "function getLocal(start: Word) returns (function(Word) returns (Word)) { let value = start; let f = lam(item) { value += 1; return item; }; return f; }"
    , "function useReturned(start: Word) returns (Word) { let f = getLocal(start); return f(9); }"
  ]}] }

private def key (program : CheckedProgram) (name : String) : IO Key :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure ⟨signature.id, []⟩
  | _ => throw (IO.userError s!"marked fixture missing {name}")

private def runSuccess {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Solcore.Frontend.SourceCoreCompatibleMarkedFunctions.Prepared checked) (key : Key) (arguments : List SourceTypedRuntime.Value)
    (expected : SourceCoreCompatibleValues.Value) : IO Unit := do
  for fuel in [0, 7, 37, 150000] do
    let completion ← match prepared.runSource key arguments fuel 500 with
      | .ok completion => pure completion
      | .error error => throw (IO.userError s!"marked run failed: {reprStr error}")
    let completion := completion.resume 150000
    match completion.result.native.observation with
    | .succeeded value store =>
      let decoded ← match SourceCoreCompatibleValues.decode 500 completion.result.context completion.entry.sourceResultType value with
        | .ok decoded => pure decoded
        | .error error => throw (IO.userError s!"marked output failed: {reprStr error}")
      assertTrue (decoded == expected) s!"marked result changed: {reprStr decoded}"
      assertTrue (store.any fun value => match value with
        | .constructed constructor _ => constructor.owner.index ≥ checked.catalog.definitions.length
        | _ => false) "source invocation omitted allocation markers"
    | observation => throw (IO.userError s!"marked result did not succeed: {reprStr observation}")

/-- The binder `name` declared in `key`'s checked body. -/
private def binder (plan : SourceSpecializationWorklist.Plan) (key : Key) (name : String) : IO Resolved.LocalId := do
  let specialized ← match SourceCompilationPlan.exactSpecialization plan key with
    | .ok specialized => pure specialized
    | .error error => throw (IO.userError s!"marked specialization missing: {reprStr error}")
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == name) with
  | [binder] => pure binder.id
  | _ => throw (IO.userError s!"marked fixture binder missing {name}")

/-- A lambda created before a captured local is assigned copies that local
uninitialized, so its read in the body faults at every call. -/
private def runUninitialized {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Solcore.Frontend.SourceCoreCompatibleMarkedFunctions.Prepared checked) (key : Key)
    (arguments : List SourceTypedRuntime.Value) (missing : Resolved.LocalId) : IO Unit := do
  for fuel in [0, 7, 37, 150000] do
    let completion ← match prepared.runSource key arguments fuel 500 with
      | .ok completion => pure completion
      | .error error => throw (IO.userError s!"marked run failed: {reprStr error}")
    let completion := completion.resume 150000
    match completion.result.native.observation with
    | .failed reason store =>
      let diagnostic ← match completion.result.diagnostics.diagnostic? reason with
        | some diagnostic => pure diagnostic
        | none => throw (IO.userError "marked uninitialized capture diagnostic missing")
      assertTrue (diagnostic.error == .uninitializedLocal missing && diagnostic.span.isSome)
        "read of a lambda's uninitialized capture copy did not fault at its source site"
      assertTrue (store.any fun value => match value with
        | .constructed constructor _ => constructor.owner.index ≥ checked.catalog.definitions.length
        | _ => false) "source invocation omitted allocation markers"
    | observation => throw (IO.userError s!"marked uninitialized capture changed: {reprStr observation}")

example {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Solcore.Frontend.SourceCoreCompatibleMarkedFunctions.Prepared checked) :
    Solcore.Frontend.SourceCoreCompatibleMarkedFunctions.compileClosures prepared.base (Solcore.Frontend.SourceCoreCompatibleMarkedFunctions.markedRepresentation checked prepared.fuel prepared.layouts
      (some ⟨prepared.base.sourceProgram, prepared.base.plan, prepared.views⟩))
      prepared.fuel = .ok prepared.secondPass.closures := prepared.secondPass.compiled

example {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Solcore.Frontend.SourceCoreCompatibleMarkedFunctions.Prepared checked) :
    Solcore.Frontend.SourceCoreCompatibleMarkedFunctions.compileClosures prepared.base (Solcore.Frontend.SourceCoreCompatibleMarkedFunctions.discoveryRepresentation prepared.base prepared.fuel prepared.discovery (some prepared.views))
      prepared.fuel = .ok prepared.firstPass.closures := prepared.firstPass.compiled

private def manyRoots : IO Unit := do
  let workspace : Workspace.RawWorkspace := {
    entry := "main.solc"
    externalLibraries := []
    mainSources := [{
      path := "main.solc"
      content := String.intercalate "\n" ((List.range 40).map fun index =>
        "function root" ++ toString index ++ "() returns (Word) { return 7; }")}] }
  let program ← match checkProgram workspace with
    | .ok program => pure program | .error error => throw (IO.userError s!"many roots rejected: {reprStr error}")
  let plan ← match SourceSpecializationWorklist.run program
      (program.signatures.functions.map (fun signature => ⟨signature.id, []⟩)) 500 with
    | .ok (.complete plan) => pure plan | result => throw (IO.userError s!"many roots plan failed: {reprStr result}")
  let automatic ← match SourceCoreCompatibleFunctions.prepare program plan 32 with
    | .ok automatic => pure automatic | .error error => throw (IO.userError s!"many roots base failed: {reprStr error}")
  let prepared ← match Solcore.Frontend.SourceCoreCompatibleMarkedFunctions.prepare automatic.prepared 32 with
    | .ok prepared => pure prepared | .error error => throw (IO.userError s!"many roots marked failed: {reprStr error}")
  assertTrue (prepared.entries.length == 40) "source fuel incorrectly bounded the complete Core inventory"
  let completion ← match prepared.runSource (← key program "root39") [] 50000 500 with
    | .ok completion => pure completion | .error error => throw (IO.userError s!"many roots run failed: {reprStr error}")
  match completion.result.native.observation with
  | .succeeded (.word value) _ => assertTrue (value == w 7) "many roots result changed"
  | observation => throw (IO.userError s!"many roots observation changed: {reprStr observation}")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"marked fixture rejected: {reprStr error}")
  let names := ["local", "lazy", "choose", "capture", "recursive", "unused", "tuple", "looping", "absent", "getLocal", "useReturned"]
  let keys ← names.mapM (key program)
  let plan ← match SourceSpecializationWorklist.run program (keys.map (fun key => ⟨key.declaration, []⟩)) 128 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"marked worklist failed: {reprStr result}")
  let automatic ← match SourceCoreCompatibleFunctions.prepare program plan 500 with
    | .ok automatic => pure automatic
    | .error error => throw (IO.userError s!"marked base factory failed: {reprStr error}")
  let prepared ← match Solcore.Frontend.SourceCoreCompatibleMarkedFunctions.prepare automatic.prepared 500 with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError s!"marked factory failed: {reprStr error}")
  assertTrue (prepared.entries.length == keys.length) "marked roots disappeared"
  assertTrue (!prepared.layouts.entries.isEmpty) "marked catalog is empty"
  assertTrue (prepared.layouts.definitions.take automatic.checked.catalog.definitions.length == automatic.checked.catalog.definitions)
    "marked suffix changed ambient definitions"
  runSuccess prepared (← key program "local") [.mapping .word .word [(.word (w 1), .word (w 9))]]
    (.mapping .word .word [(.word (w 1), .word (w 9))])
  runSuccess prepared (← key program "lazy") [] (.mapping .word .word [(.word (w 1), .word (w 7))])
  -- Both calls of `f` start again from `value = 10`; the second returns 10 + 4.
  runSuccess prepared (← key program "capture") [.word (w 10)] (.word (w 14))
  -- `f` is still uninitialized when its lambda is created, so the lambda's copy
  -- of `f` is too, and the first recursive read faults.
  let recursive ← key program "recursive"
  runUninitialized prepared recursive [.word (w 4)] (← binder plan recursive "f")
  runSuccess prepared (← key program "unused") [] (.word (w 7))
  runSuccess prepared (← key program "tuple") [.product (.word (w 13)) (.bool true)] (.word (w 13))
  runSuccess prepared (← key program "looping") [.word (w 4)] (.word (w 6))
  runSuccess prepared (← key program "useReturned") [.word (w 4)] (.word (w 9))
  let returned ← match prepared.runSource (← key program "getLocal") [.word (w 4)] 150000 500 with
    | .ok completion => pure completion | .error error => throw (IO.userError s!"local view output failed: {reprStr error}")
  match returned.result.native.observation with
  | .succeeded value _ =>
      let parsed ← match SourceCoreCallableViewWrappers.parse? .word .word value with
        | some parsed => pure parsed | none => throw (IO.userError "local read omitted its exact view wrapper")
      let view ← match prepared.views.entryAt? parsed.view with
        | some view => pure view | none => throw (IO.userError "local read wrapper lost its cached view")
      assertTrue (view.view.owner == (← key program "getLocal")) "local wrapper authenticated a foreign owner"
      assertTrue view.view.wrapsPrincipal "local wrapper used monomorphic metadata"
      match parsed.original with
      | .pair (.pair (.inLeft .word .unit) (.closure ..)) (.word descriptor) =>
          assertTrue (descriptor == parsed.contract) "local wrapper changed its stage descriptor"
      | _ => throw (IO.userError "local wrapper changed its original anonymous carrier")
  | observation => throw (IO.userError s!"local view output changed: {reprStr observation}")
  let box ← match program.signatures.dataTypes.find? (·.name == "Box") with
    | some box => pure box | none => throw (IO.userError "marked Box missing")
  let constructor ← match box.constructors[0]? with
    | some constructor => pure constructor | none => throw (IO.userError "marked constructor missing")
  let instantiation : DataConstructorInstantiation := ⟨constructor.id, box.parameters.zip [.word], [.word], .nominal box.id [.word]⟩
  runSuccess prepared (← key program "choose") [.constructed instantiation [.word (w 7)]] (.word (w 7))
  let absent ← match prepared.runSource (← key program "absent") [] 150000 500 with
    | .ok completion => pure completion
    | .error error => throw (IO.userError s!"marked absent run failed: {reprStr error}")
  match absent.result.native.observation with
  | .failed reason store =>
      let diagnostic ← match absent.result.diagnostics.diagnostic? reason with
        | some diagnostic => pure diagnostic | none => throw (IO.userError "marked absent diagnostic missing")
      assertTrue diagnostic.span.isSome "marked absent span lost"
      assertTrue (!store.isEmpty) "marked failure lost allocations"
  | observation => throw (IO.userError s!"marked absent result changed: {reprStr observation}")
  manyRoots
  IO.println "actual compatible function compiler and shared allocation suffix GREEN"

end Tests.SourceCoreCompatibleMarkedFunctions
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleMarkedLedger
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! A real checked source program supplies completed, failed and suspended
native observations. Every snapshot is scanned with its actual finite-world
typing; the scan does not evaluate source expressions or inspect the retained
legacy heap prefix. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleMarkedLedger
open Solcore Solcore.Frontend SourceInference
open SourceCoreCompatibleMarkedLedger
abbrev Key := SourceSpecialization.SpecializationKey

private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function success(value: Word) returns (Word) { let next = value + 1; return next; }",
    "function failure(value: Word) returns (Word) { let absent: Word; return absent; }",
    "function forever(value: Word) returns (Word) { let total = value; while (true) { total += 1; } return total; }"
  ]}] }

private def key (program : CheckedProgram) (name : String) : IO Key :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure ⟨signature.id, []⟩
  | _ => throw (IO.userError s!"marked ledger fixture missing {name}")

private def opaquePrefix (key : Key) : SourceHeap := [
  {type := .error, value := some (.closure [] .unit []
    {owner := key.declaration, inputs := [], roots := [], nodes := []}
    key [(⟨key.declaration, 999⟩, ⟨777⟩)] [])},
  {type := .word, value := some (.bool true)}]

private def inspect {checked : Checked} {prepared : Prepared checked}
    (completion : Completion prepared) (initialHeap : SourceHeap) : IO (Receipt completion initialHeap) :=
  match scan completion initialHeap with
  | .ok receipt => pure receipt
  | .error error => throw (IO.userError s!"actual marked store failed ledger scan: {reprStr error}")

private def start {checked : Checked} (prepared : Prepared checked) (key : Key) (fuel : Nat) :
    IO (Completion prepared) :=
  match prepared.runSource key [.word (Core.Word.ofNatModulo 9)] fuel 256 with
  | .ok completion => pure completion
  | .error error => throw (IO.userError s!"marked ledger execution failed: {reprStr error}")

/-- Every single transition is observed, including the gap between marker
and optional payload allocation. Only completed pairs extend the location map. -/
private def stepSuccess {checked : Checked} (prepared : Prepared checked) (key : Key) : IO Unit := do
  let initialHeap := opaquePrefix key
  let mut completion ← start prepared key 0
  let mut previous : List SourceCoreAllocationLedger.LocationEntry := []
  let mut sawPending := false
  let mut finished := false
  for _ in List.range 1000 do
    let receipt ← inspect completion initialHeap
    let current := receipt.ledger.locations
    assertTrue (decide (current.take previous.length = previous)) "resumption changed an existing source location"
    assertTrue (reprStr receipt.ledger.initialHeap == reprStr initialHeap) "opaque source prefix changed"
    if receipt.ledger.pending.isSome then sawPending := true
    previous := current
    match completion.result.native.observation with
    | .succeeded value _ =>
      assertTrue (decide (value = .word (Core.Word.ofNatModulo 10))) "source result changed"
      assertTrue (current.map (·.source.index) == [2, 3]) "source-visible allocation order changed"
      assertTrue receipt.ledger.pending.isNone "successful allocation left pending marker"
      let resumed := completion.resume 0
      assertTrue (decide (store resumed = store completion)) "terminal resumption changed the store"
      finished := true
      break
    | .outOfFuel _ => completion := completion.resume 1
    | observation => throw (IO.userError s!"unexpected success observation: {reprStr observation}")
  assertTrue finished "success fixture did not terminate"
  assertTrue sawPending "single-step fixture never observed marker-only checkpoint"

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"marked ledger checker failed: {reprStr error}")
  let successKey ← key program "success"
  let failureKey ← key program "failure"
  let foreverKey ← key program "forever"
  let plan ← match SourceSpecializationWorklist.run program
      ([successKey, failureKey, foreverKey].map (fun key => ⟨key.declaration, []⟩)) 128 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"marked ledger plan failed: {reprStr result}")
  let automatic ← match SourceCoreCompatibleFunctions.prepare program plan 256 with
    | .ok automatic => pure automatic
    | .error error => throw (IO.userError s!"marked ledger base factory failed: {reprStr error}")
  let prepared ← match SourceCoreCompatibleMarkedFunctions.prepare automatic.prepared 256 with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError s!"marked ledger factory failed: {reprStr error}")
  stepSuccess prepared successKey
  let failed ← start prepared failureKey 10000
  let failureReceipt ← inspect failed (opaquePrefix failureKey)
  match failed.result.native.observation with
  | .failed _ actual =>
    assertTrue (decide (store failed = actual)) "language failure lost actual store"
    assertTrue (failureReceipt.ledger.rows.length == 2) "language failure lost source cells"
    assertTrue ((failureReceipt.ledger.rows.map (·.payload.isSome)) == [true, false])
      "uninitialized failure changed optional source payload"
  | observation => throw (IO.userError s!"failure became another observation: {reprStr observation}")
  let suspended ← start prepared foreverKey 1000
  let first ← inspect suspended (opaquePrefix foreverKey)
  match suspended.result.native.observation with
  | .outOfFuel checkpoint =>
    assertTrue (decide (store suspended = checkpoint.store)) "suspension lost checkpoint store"
    assertTrue (first.ledger.rows.length == 2) "loop administrative cells leaked into source heap"
  | observation => throw (IO.userError s!"loop suspension became terminal: {reprStr observation}")
  let resumed := suspended.resume 1000
  let second ← inspect resumed (opaquePrefix foreverKey)
  match resumed.result.native.observation with
  | .outOfFuel _ =>
    assertTrue (decide (first.ledger.locations = second.ledger.locations)) "loop resume changed source cell locations"
    assertTrue (decide (first.ledger.rows.map (·.environment) = second.ledger.rows.map (·.environment)))
      "loop resume changed captured lexical references"
  | observation => throw (IO.userError s!"infinite loop unexpectedly completed: {reprStr observation}")

example {checked : Checked} {prepared : Prepared checked} (completion : Completion prepared) :
    Core.RuntimeStoreHasTypes (world completion) (store completion) prepared.layouts.definitions :=
  store_typed completion

example {checked : Checked} {prepared : Prepared checked} (completion : Completion prepared)
    {checkpoint : Core.State} (suspended : completion.result.native.observation = .outOfFuel checkpoint) :
    store completion = checkpoint.store := suspended_store completion suspended

end Tests.SourceCoreCompatibleMarkedLedger
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleNamedBody
#check_failure Solcore.SourceSemantics.CoreLowering.CompatibleNamedBody.Certificate.mk
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Static zero-parameter compilation receipts and concrete checked source
regressions. Semantic certificates are extracted at one actual body context;
neither a universal body IH nor a finite source execution is a static premise. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleNamedBody
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleNamedBody

private def source (owner : Resolved.DeclarationId) : TypedSource := {
  owner, inputs := [], roots := [], nodes := [] }
private def compilation (plan : SourceSpecializationWorklist.Plan)
    (owner : SourceSpecialization.SpecializationKey) : SourceCoreFunctions.Context := {
  plan, owner, globals := [], administrativePrefix := 1, solvedRequirements := [], internalReason := Word.zero }
private def policy (program : CheckedProgram) (representation : SourceCoreGeneralFunctions.Representation)
    (plan : SourceSpecializationWorklist.Plan) (owner : SourceSpecialization.SpecializationKey)
    (values : SourceCoreCompatibleValues.Context)
    (assignments : SourceCoreAssignmentFaultSites.Table) (diagnostics : SourceCoreDataPlaceFaultSites.Program) :
    SourceCoreLoops.Policy := {
  lowerExpression := SourceCoreGeneralFunctions.lowerContextualExpression program representation program.signatures
    ⟨[]⟩ [] assignments diagnostics (compilation plan owner) none none none
  readStatement := SourceCoreCompatibleDataExpressions.readStatement values.checked
}
private def code (fellThrough escaped : Word) : Expr :=
  CompatibleStatements.finish .unit (LocalLoop.fallthrough .unit) fellThrough escaped

/-- Even the empty body uses the actual contextual compiler and explicit
source context. No `BodyPreserves` or `BodyReflects` premise is hidden here. -/
theorem nil_certificate (program : CheckedProgram) (representation : SourceCoreGeneralFunctions.Representation)
    (plan : SourceSpecializationWorklist.Plan) (owner : SourceSpecialization.SpecializationKey)
    (readFuel : Nat) (values : SourceCoreCompatibleValues.Context)
    (assignments : SourceCoreAssignmentFaultSites.Table) (diagnostics : SourceCoreDataPlaceFaultSites.Program)
    (context : SourceSemantics.Context) (fellThrough escaped : Word)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (readExpression : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerRead : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafLowerer : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values) :
    Nonempty (Certificate readFuel values (source owner.declaration) context [] (fun _ => Word.zero) [] [] .unit .unit
      (policy program representation plan owner values assignments diagnostics) 10 fellThrough escaped (code fellThrough escaped)) := by
  apply of_contextual (locals := ⟨[]⟩) (compilation := compilation plan owner)
      (native := none) (parent := none) (skipInitializer := none) ?_ ?_ closed residual ?_
      readExpression lowerRead leafLowerer rfl rfl .nil rfl rfl
  · constructor
    · intro id node _ found
      change none = some node at found; cases found
    · intro id node _ found
      change none = some node at found; cases found
    · intros; rfl
    · intros; rfl
  · cbv; decide
  · intro binder declared index native selected accepted
    cases selected

example (environment : Environment) (store : Store) (fellThrough escaped : Word) :
    Evaluates environment store (code fellThrough escaped) (.inRight .word .unit) store := by
  exact LocalControl.finish_fallthrough .unit
    (LocalLoop.toControl_normal .unit escaped (LocalLoop.fallthrough_evaluates .unit environment store))
    (by simpa [LanguageResult.success, Expr.weakenAt] using
      (show Evaluates (.unit :: .inLeft .unit .unit :: environment) store (.inRight .word .unit)
        (.inRight .word .unit) store from .inRight .unit))

private def content : String := String.intercalate "\n" [
  "function empty() { }",
  "function explicitUnit() { return; }",
  "function falseValue() returns (Bool) { return false; }",
  "function pair() returns ((Word, Bool)) { return (7, false); }",
  "function discardReturn() returns (Word) { false; return 9; }",
  "function early() returns (Word) { return 11; 99; }"
]

/-- Concrete named invocation uses the actual cached indexed compiler, with
opaque initial source cells and genuine native suspension/resumption. These
runtime regressions do not replace the independent semantic proofs above. -/
def run : IO Unit := do
  let names := ["empty", "explicitUnit", "falseValue", "pair", "discardReturn", "early"]
  let artifact ← SourceCoreUnifiedCorpusSupport.prepare "certified ordinary named bodies" content names
  let expected : List SourceTypedRuntime.Value := [.unit, .unit, .bool false,
    .product (.word (Word.ofNatModulo 7)) (.bool false), .word (Word.ofNatModulo 9), .word (Word.ofNatModulo 11)]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩]}
  for (name, value) in names.zip expected do
    for fuel in [0, 13, 300000] do
      let first ← SourceCoreUnifiedCorpusSupport.execute artifact name [] fuel initial
      let result ← SourceCoreUnifiedCorpusSupport.get "named body resume" (SourceCoreUnifiedCompilation.Result.resume first 300000)
      match result.observation with
      | .done actual final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr value) s!"named result changed {name}"
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr final.heap == reprStr initial.heap) s!"zero-parameter body changed heap {name}"
      | other => throw (IO.userError s!"named body failed {name}: {reprStr other}")
  IO.println "compatible zero-parameter named bodies, real Core resume and inert source prefix GREEN"

end Tests.SourceCoreCompatibleNamedBody
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleNamedParameters
#check_failure Solcore.SourceSemantics.CoreLowering.CompatibleNamedParameters.Entry.mk
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Real marked parameter prefixes retain source-order cells, raw metadata and
function payloads, then enter the fixed-context body. Each invocation below
uses cached common compiler code and genuine native checkpoint resumption. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleNamedParameters
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleNamedParameters CallableIndexedParameterCertificates CallableIndexedParameterMeaning

/-- The zero-input case remains the actual parameter compiler's empty tree. -/
example (layouts : SourceCoreAllocationLayouts.Prepared) (owner : SourceSpecialization.SpecializationKey)
    (layout : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (source : TypedSource) (type : Ty) (body : Expr) :
    Tree layouts owner [] layout globals onError source 0 type body [] 0 [] body :=
  CallableIndexedParameterCertificates.of_accepted (bindings := []) onError rfl

/-- Packing two equal closure payloads preserves their native aliasing. The
representation premise is typed, with no first-order payload restriction. -/
example {values : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : CompatiblePayload.FunctionModel values.checked.catalog ambient)
    {registry : SourceCoreRawMetadata.Registry} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    (left right : TypedBinder) (type : Ty) (sourceValue : Dynamic.Value) (value : Value)
    (first : CompatiblePayload.ValueRep values.checked registry functions mapping world left.scheme.body sourceValue value type)
    (second : CompatiblePayload.ValueRep values.checked registry functions mapping world right.scheme.body sourceValue value type) :
    RuntimeValueHasType world (.pair value value) (.product type type) ambient.definitions := by
  have represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world [(left, type), (right, type)] [sourceValue, sourceValue] [value, value] := .cons first (.cons second .nil)
  exact CallableIndexedParameters.Arguments.pack_typed represented

private def content : String := String.intercalate "\n" [
  "function unitAfterTwo(flag: Bool, value: Word) { }",
  "function readSecond(flag: Bool, value: Word) returns (Word) { flag; return value; }",
  "function paired(value: Word, flag: Bool) returns ((Word, Bool)) { return (value, flag); }",
  "function early(value: Word, flag: Bool) returns (Word) { return value; flag; }",
  "function identity(value: Word) returns (Word) { return value; }",
  "function keepFunction(f: function(Word) returns (Word), flag: Bool) returns (function(Word) returns (Word)) { flag; return f; }",
  "function keepMap(values: mapping(Word => Word)) returns (mapping(Word => Word)) { return values; }"
]

private def check (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (expected : SourceTypedRuntime.Value)
    (initial : SourceTypedRuntime.RuntimeState) : IO Unit := do
  for fuel in [0, 19, 300000] do
    let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
    let result ← SourceCoreUnifiedCorpusSupport.get "parameter body resume" (SourceCoreUnifiedCompilation.Result.resume first 300000)
    match result.observation with
    | .done value final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr value == reprStr expected) s!"named parameter result changed {name}"
      SourceCoreUnifiedCorpusSupport.assertTrue (final.heap.length == initial.heap.length + arguments.length)
        s!"parameter cell count changed {name}"
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
        s!"inert source prefix changed {name}"
      SourceCoreUnifiedCorpusSupport.assertTrue
        (reprStr ((final.heap.drop initial.heap.length).map (·.value)) == reprStr (arguments.map some))
        s!"parameter order, payload or sharing changed {name}"
      SourceCoreUnifiedCorpusSupport.assertTrue
        (final.isDeeplySafe 500 compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.plan)
        s!"parameter heap is not deeply safe {name}"
    | other => throw (IO.userError s!"named parameter body failed {name}: {reprStr other}")

def run : IO Unit := do
  let names := ["unitAfterTwo", "readSecond", "paired", "early", "identity", "keepFunction", "keepMap"]
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "certified named parameters" content names
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩,
    ⟨.word, some (.word (SourceCoreUnifiedCorpusSupport.word 777))⟩]}
  let value : SourceTypedRuntime.Value := .word (SourceCoreUnifiedCorpusSupport.word 42)
  check compiled "unitAfterTwo" [.bool false, value] .unit initial
  check compiled "readSecond" [.bool false, value] value initial
  check compiled "paired" [value, .bool false] (.product value (.bool false)) initial
  check compiled "early" [value, .bool false] value initial
  check compiled "identity" [value] value initial
  let identity ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "identity"
  let callable : SourceTypedRuntime.Value := .global identity []
  check compiled "keepFunction" [callable, .bool false] callable initial
  let mapping : SourceTypedRuntime.Value := .mapping (.comptime .word) .word
    [(.word (SourceCoreUnifiedCorpusSupport.word 3), value),
     (.word (SourceCoreUnifiedCorpusSupport.word 3), .word (SourceCoreUnifiedCorpusSupport.word 9))]
  check compiled "keepMap" [mapping] mapping initial
  IO.println "compatible named parameters: Unit, ordered cells, raw mapping, callable payload, prefix and resume GREEN"

end Tests.SourceCoreCompatibleNamedParameters
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleOutputLeaves
#check_failure Solcore.Frontend.SourceCoreCompatibleOutputs.LeafDecoded.mk
#check_failure Solcore.Frontend.SourceCoreCompatibleOutputs.decodeWithRaw

/-! Function-leaf delegation traverses actual native tuples, nominal payloads
and ordered mappings. Failure paths and the ordinary named/builtin receipt are
retained. This unit does not reconstruct anonymous source closures. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleOutputLeaves
open Solcore Solcore.Frontend SourceInference
abbrev SourceValue := SourceTypedRuntime.Value
abbrev Key := SourceSpecialization.SpecializationKey
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Holder { Hold(Word, function(Word) returns (Word)) }",
    "function inc(value: Word) returns (Word) { return value + 1; }",
    "function plain() returns (Word, Bool) { return (7, true); }",
    "function tuple() returns (function(Word) returns (Word), function(Word) returns (integer)) { return (inc, wordToInteger); }",
    "function nominal() returns (Holder) { return .Hold(7, inc); }",
    "function mappingReturn(value: mapping(Word => function(Word) returns (Word))) returns (mapping(Word => function(Word) returns (Word))) { return value; }"
  ]}] }
private def key (program : CheckedProgram) (name : String) : IO Key := do
  match program.signatures.functions.find? (·.name == name) with
  | some signature => pure ⟨signature.id, []⟩
  | none => throw (IO.userError s!"leaf traversal function missing: {name}")

private structure Projected (checked : SourceCoreCompatibleCatalog.Checked)
    (source : TypeSystem.Ty) (native : Core.Ty) : Type where
  eq : checked.catalog.project source = .ok native

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"leaf traversal source rejected: {reprStr error}")
  let requests := program.signatures.functions.map fun signature =>
    (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
  let plan ← match SourceSpecializationWorklist.run program requests 200 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"leaf traversal plan failed: {reprStr result}")
  let automatic ← match SourceCoreCompatibleFunctions.prepare program plan 500 with
    | .ok automatic => pure automatic
    | .error error => throw (IO.userError s!"leaf traversal base failed: {reprStr error}")
  let prepared ← match SourceCoreCallableAncestryPrograms.prepare automatic.prepared 500 with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError s!"leaf traversal compiler failed: {reprStr error}")
  let recipe ← match SourceCoreCompatibleOutputs.prepareAncestry prepared with
    | .ok recipe => pure recipe
    | .error error => throw (IO.userError s!"leaf traversal recipe failed: {reprStr error}")
  let inc ← key program "inc"
  let mapping : SourceValue := .mapping .word (.comptime (.function .word .word))
    [(.word (Core.Word.ofNatModulo 4), .global inc []), (.word (Core.Word.ofNatModulo 4), .global inc [])]
  let fixtures : List (String × List SourceValue × Option (List SourceCoreCompatibleOutputs.PathStep)) :=
    [("plain", [], none), ("tuple", [], some [.productLeft]),
     ("nominal", [], some [.constructorPayload 1]),
     ("mappingReturn", [mapping], some [.mappingValue 0])]
  for (name, arguments, expectedFailure) in fixtures do
    for budget in [0, 29, 100000] do
      let completion ← match prepared.runSource (← key program name) arguments budget with
        | .ok completion => pure (completion.resume 100000)
        | .error error => throw (IO.userError s!"leaf traversal native call failed: {reprStr error}")
      let projected ← match same : automatic.checked.catalog.project completion.entry.sourceResultType with
        | .error error => throw (IO.userError s!"leaf traversal projection failed: {reprStr error}")
        | .ok type =>
          if equal : type = completion.entry.native.resultType then
            pure (show Projected automatic.checked completion.entry.sourceResultType
              completion.entry.native.resultType from ⟨by simpa [equal] using same⟩)
          else throw (IO.userError "leaf traversal result native type changed")
      let ordinary ← match SourceCoreCompatibleOutputs.decodeSuccess recipe completion.result.context
          completion.result.contextOwner completion.entry.sourceResultType projected.eq completion.result.native with
        | .ok ordinary => pure ordinary
        | .error error => throw (IO.userError s!"leaf traversal ordinary decoder failed: {reprStr error}")
      let delegated ← match SourceCoreCompatibleOutputs.decodeWithLeaves
          (SourceCoreCompatibleOutputs.decodeCallable recipe) recipe ordinary.snapshot completion.result.context
          completion.result.contextOwner completion.entry.sourceResultType ordinary.core ordinary.decoded.type
          ordinary.decoded.projected ordinary.decoded.typed with
        | .ok delegated => pure delegated
        | .error error => throw (IO.userError s!"leaf traversal delegated decoder failed: {reprStr error}")
      assertTrue (reprStr delegated.source == reprStr ordinary.decoded.source)
        "delegating callable leaves changed deep raw source data"
      assertTrue (reprStr delegated.default.source == reprStr ordinary.decoded.source)
        "delegating callable leaves lost the original decoder receipt"
      let rejecting : SourceCoreCompatibleOutputs.LeafDecoder :=
        fun _ _ => .error ⟨[], .callablePayloadMismatch⟩
      match SourceCoreCompatibleOutputs.decodeWithLeaves rejecting recipe ordinary.snapshot completion.result.context
          completion.result.contextOwner completion.entry.sourceResultType ordinary.core ordinary.decoded.type
          ordinary.decoded.projected ordinary.decoded.typed with
      | .ok value =>
        assertTrue expectedFailure.isNone "structural decoder skipped a function leaf"
        assertTrue (reprStr value.source == reprStr ordinary.decoded.source)
          "data-only traversal depended on the function-leaf policy"
      | .error error =>
        let leafFailure := match error.code with | .callablePayloadMismatch => true | _ => false
        assertTrue (expectedFailure == some error.path && leafFailure)
          s!"structural function-leaf failure path changed: {reprStr error}"
  IO.println "actual output traversal, callable-leaf delegation and deep failure paths GREEN"

end Tests.SourceCoreCompatibleOutputLeaves
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleOutputs
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreCompatibleOutputs.Recipe.mk
#check_failure Solcore.Frontend.SourceCoreCompatibleOutputs.decodeRaw

/-! Cached compatible calls export global/builtin values at every data depth.
Core-only tampering keeps native typing while changing descriptors or closure
payloads; the reverse adapter must still reject it. Lambda export is an explicit
ledger boundary, independent of the typed native execution succeeding. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleOutputs
open Solcore Solcore.Frontend SourceInference
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Prepared := SourceCoreCompatibleFunctions.Prepared
abbrev Recipe := Solcore.Frontend.SourceCoreCompatibleOutputs.Recipe
abbrev SourceValue := SourceTypedRuntime.Value
abbrev Key := SourceSpecialization.SpecializationKey

private def w (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Holder { Hold(function(Word) returns (Word)) }",
    "trait Marker<T> {}", "impl Marker<Word> {}",
    "function keep<T>(value: T) returns (T) where T: Marker { return value; }",
    "function inc(value: Word) returns (Word) { return value + 1; }",
    "function dec(value: Word) returns (Word) { return value - 1; }",
    "function getNamed() returns (function(Word) returns (Word)) { return inc; }",
    "function getBuiltin() returns (function(Word) returns (integer)) { return wordToInteger; }",
    "function getQualified() returns (function(Word) returns (Word)) { return keep; }",
    "function getNominal() returns (Holder) { return .Hold(inc); }",
    "function getTuple() returns (function(Word) returns (Word), function(Word) returns (integer)) { return (inc, wordToInteger); }",
    "function mappingReturn(value: mapping(function(Word) returns (Word) => function(Word) returns (Word))) returns (mapping(function(Word) returns (Word) => function(Word) returns (Word))) { return value; }",
    "function alias(value: mapping(@Word => function(Word) returns (Word))) returns (mapping(@Word => function(Word) returns (Word))) { return value; }",
    "function make(value: Word) returns (function(Word) returns (Word)) { return lam(delta: Word) -> Word { value = value + delta; return value; }; }"
  ]}] }

private def key (program : CheckedProgram) (name : String) : IO Key := do
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure ⟨signature.id, []⟩
  | _ => throw (IO.userError s!"compatible output function missing: {name}")

example {checked : Checked} {recipe : Recipe checked} {snapshot : SourceCoreCompatibleOutputs.Snapshot recipe}
    {context : SourceCoreCompatibleValues.Context} {expected : TypeSystem.Ty} {value : Core.Value}
    (decoded : SourceCoreCompatibleOutputs.Decoded recipe snapshot context expected value) :
    Core.RuntimeValueHasType (snapshot.store.map Core.Value.type) value decoded.type checked.catalog.definitions :=
  decoded.typed

example {definitions : Core.DataEnvironment} {world : Core.StoreTyping} {function : Core.HostFunction}
    {type : Core.Ty} (typed : Core.RuntimeValueHasType world (.hostFunction function) type definitions) : False := by
  cases typed

private structure Projected (checked : Checked) (source : TypeSystem.Ty) (native : Core.Ty) : Type where
  eq : checked.catalog.project source = .ok native
private def project (checked : Checked) (source : TypeSystem.Ty) (native : Core.Ty) : IO (Projected checked source native) := do
  match projected : checked.catalog.project source with
  | .error error => throw (IO.userError s!"compatible output projection failed: {reprStr error}")
  | .ok actual =>
      if same : actual = native then pure ⟨by simpa only [same] using projected⟩
      else throw (IO.userError "compatible output actual native projection changed")

private def check {checked : Checked} (prepared : Prepared checked) (recipe : Recipe checked)
    (owner : Key) (arguments : List SourceValue) (expected : SourceValue) : IO Unit := do
  for fuel in [0, 7, 37, 150000] do
    let completion ← match prepared.runSource owner arguments fuel with
      | .ok completion => pure (completion.resume 150000)
      | .error error => throw (IO.userError s!"compatible output source run failed: {reprStr error}")
    let projection ← project checked completion.entry.sourceResultType completion.entry.native.resultType
    let exported ← match SourceCoreCompatibleOutputs.decodeSuccess recipe completion.result.context
        completion.result.contextOwner completion.entry.sourceResultType projection.eq completion.result.native with
      | .ok exported => pure exported
      | .error error => throw (IO.userError s!"compatible output reverse failed: {reprStr error}")
    assertTrue (reprStr exported.decoded.source == reprStr expected)
      s!"compatible output source identity/metadata/order changed: {reprStr exported.decoded.source}"

private def checkMarked {checked : Checked} (prepared : SourceCoreCompatibleMarkedFunctions.Prepared checked)
    (recipe : Solcore.Frontend.SourceCoreCompatibleOutputs.Recipe checked prepared.layouts.definitions)
    (owner : Key) (arguments : List SourceValue) (expected : SourceValue) : IO Unit := do
  for fuel in [0, 7, 37, 150000] do
    let completion ← match prepared.runSource owner arguments fuel with
      | .ok completion => pure (completion.resume 150000)
      | .error error => throw (IO.userError s!"marked output source run failed: {reprStr error}")
    let projection ← project checked completion.entry.sourceResultType completion.entry.native.resultType
    let exported ← match SourceCoreCompatibleOutputs.decodeSuccess recipe completion.result.context
        completion.result.contextOwner completion.entry.sourceResultType projection.eq completion.result.native with
      | .ok exported => pure exported
      | .error error => throw (IO.userError s!"marked output reverse failed: {reprStr error}")
    assertTrue (reprStr exported.decoded.source == reprStr expected)
      s!"marked output source metadata/order changed: {reprStr exported.decoded.source}"

private def mutate {checked : Checked} (prepared : Prepared checked) (recipe : Recipe checked)
    (owner : Key) (transform : Core.Expr → Core.Expr)
    (rejected : SourceCoreCompatibleOutputs.Error → Bool) : IO Unit := do
  let function ← match prepared.functions.find? (fun function => decide (function.signature.key = owner)) with
    | some function => pure function | none => throw (IO.userError "compatible tampered output root missing")
  let body ← match SourceCoreGeneralFunctions.assembleCall prepared.globals prepared.functions prepared.closures owner
      ⟨.unit, Core.LanguageResult.success .unit⟩ with
    | .ok body => pure body | .error error => throw (IO.userError s!"compatible tamper cached assembly failed: {reprStr error}")
  let body := Core.LanguageResult.bind function.signature.resultType body (Core.LanguageResult.success (transform (.var 0)))
  let native ← match SourceCoreGeneralEntry.NativeEntry.compile checked.catalog.definitions [] function.signature.resultType body with
    | .ok native => pure native | .error error => throw (IO.userError s!"compatible tamper did not retain native typing: {reprStr error}")
  let result ← match native.run [] 150000 with
    | .ok result => pure result | .error error => throw (IO.userError s!"compatible tamper native run failed: {reprStr error}")
  let projection ← project checked function.specialized.function.inferredBodyType native.resultType
  match SourceCoreCompatibleOutputs.decodeSuccess recipe (SourceCoreCompatibleValues.Context.initial checked) rfl
      function.specialized.function.inferredBodyType projection.eq result with
  | .error error => assertTrue (rejected error) s!"compatible tamper rejection changed: {reprStr error}"
  | .ok _ => throw (IO.userError "compatible reverse accepted tampered callable output")

private def changedGlobal {checked : Checked} (prepared : Prepared checked) (recipe : Recipe checked)
    (owner : Key) : IO Unit := do
  let (signature, index) ← match prepared.globals.zipIdx.find? (fun row => decide (row.1.key = owner)) with
    | some row => pure row | none => throw (IO.userError "compatible changed global slot absent")
  let ready ← match prepared.sourceInputs with
    | some ready => pure ready | none => throw (IO.userError "compatible changed global input cache absent")
  let sourceType := TypeSystem.Ty.function .word .word
  let encoded ← match SourceCoreCompatibleInputs.encode ready.context [sourceType] [.global owner []] with
    | .ok encoded => pure encoded | .error error => throw (IO.userError s!"compatible changed global reference encode failed: {reprStr error}")
  let fake := Core.Expr.lambda signature.parameterType (Core.LanguageResult.resultType signature.resultType)
    (Core.LanguageResult.success (.word (w 999)))
  let body := SourceCoreRecursiveEntry.allocateGlobals prepared.globals.reverse
    (SourceCoreRecursiveEntry.installFunctions prepared.closures
      (.letE (.storeCell (.var index) (.inRight .unit fake)) (encoded.expression.weakenAt 0)))
  let native ← match SourceCoreGeneralEntry.NativeEntry.compile checked.catalog.definitions [] encoded.type body with
    | .ok native => pure native | .error error => throw (IO.userError s!"compatible changed slot was not natively typed: {reprStr error}")
  let result ← match native.run [] 150000 with
    | .ok result => pure result | .error error => throw (IO.userError s!"compatible changed slot Core execution failed: {reprStr error}")
  let projection ← project checked sourceType native.resultType
  match SourceCoreCompatibleOutputs.decodeSuccess recipe (SourceCoreCompatibleValues.Context.initial checked) rfl
      sourceType projection.eq result with
  | .error {code := .globalSlotMismatch _, ..} => pure ()
  | .error error => throw (IO.userError s!"compatible changed slot rejection changed: {reprStr error}")
  | .ok _ => throw (IO.userError "compatible reverse authenticated an edited installed global")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program | .error error => throw (IO.userError s!"compatible output source rejected: {reprStr error}")
  let seeds := (program.signatures.functions.filter (·.name != "keep")).map fun signature =>
    (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
  let plan ← match SourceSpecializationWorklist.run program seeds 300 with
    | .ok (.complete plan) => pure plan | result => throw (IO.userError s!"compatible output plan failed: {reprStr result}")
  let automatic ← match SourceCoreCompatibleFunctions.prepare program plan 500 with
    | .ok automatic => pure automatic | .error error => throw (IO.userError s!"compatible output cached factory failed: {reprStr error}")
  let prepared := automatic.prepared
  let recipe ← match SourceCoreCompatibleOutputs.prepare prepared with
    | .ok recipe => pure recipe | .error error => throw (IO.userError s!"compatible output recipe failed: {reprStr error}")
  let marked ← match SourceCoreCompatibleMarkedFunctions.prepare prepared 500 with
    | .ok marked => pure marked | .error error => throw (IO.userError s!"marked output factory failed: {reprStr error}")
  let markedRecipe ← match SourceCoreCompatibleOutputs.prepareMarked marked with
    | .ok recipe => pure recipe | .error error => throw (IO.userError s!"marked output recipe failed: {reprStr error}")
  let inc ← key program "inc"
  let dec ← key program "dec"
  let named : SourceValue := .global inc []
  let getNamed ← key program "getNamed"
  let getBuiltin ← key program "getBuiltin"
  check prepared recipe getNamed [] named
  checkMarked marked markedRecipe getNamed [] named
  check prepared recipe getBuiltin [] (.builtin .wordToInteger)
  checkMarked marked markedRecipe getBuiltin [] (.builtin .wordToInteger)
  let qualified ← match prepared.functions.filter (fun function => function.specialized.assumptions != []) with
    | [function] => pure function
    | _ => throw (IO.userError "compatible qualified output specialization absent")
  let evidence ← match SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program qualified.signature.key
      qualified.specialized.assumptions with
    | .ok evidence => pure evidence | .error error => throw (IO.userError s!"compatible expected qualified evidence failed: {reprStr error}")
  assertTrue (!evidence.isEmpty) "compatible qualified output test lacked evidence"
  check prepared recipe (← key program "getQualified") [] (.global qualified.signature.key evidence)
  checkMarked marked markedRecipe (← key program "getQualified") [] (.global qualified.signature.key evidence)
  let holder ← match program.signatures.dataTypes.find? (·.name == "Holder") with
    | some holder => pure holder | none => throw (IO.userError "compatible output Holder absent")
  let constructor ← match holder.constructors[0]? with
    | some constructor => pure constructor | none => throw (IO.userError "compatible output Hold absent")
  let functionType := TypeSystem.Ty.function .word .word
  let instantiation : DataConstructorInstantiation := ⟨constructor.id, [], [functionType], .nominal holder.id []⟩
  check prepared recipe (← key program "getNominal") [] (.constructed instantiation [named])
  checkMarked marked markedRecipe (← key program "getNominal") [] (.constructed instantiation [named])
  check prepared recipe (← key program "getTuple") [] (.product named (.builtin .wordToInteger))
  checkMarked marked markedRecipe (← key program "getTuple") [] (.product named (.builtin .wordToInteger))
  let mapping : SourceValue := .mapping (.comptime functionType) functionType
    [(named, named), (named, .global dec [])]
  check prepared recipe (← key program "mappingReturn") [mapping] mapping
  checkMarked marked markedRecipe (← key program "mappingReturn") [mapping] mapping
  let alias : SourceValue := .mapping (.proxy (.comptime .word)) (.comptime functionType)
    [(.proxy (.comptime .word), named), (.proxy .word, .global dec [])]
  check prepared recipe (← key program "alias") [alias] alias
  checkMarked marked markedRecipe (← key program "alias") [alias] alias
  let table ← match prepared.callableContext with
    | some native => pure native.table | none => throw (IO.userError "compatible output codebook missing")
  let decDescriptor ← match table.idAt? (.named dec) with
    | some id => pure id | none => throw (IO.userError "compatible output dec descriptor missing")
  mutate prepared recipe getNamed (fun value => .pair (.first value) (.word Core.Word.zero)) fun error =>
    match error.code with | .unknownDescriptor _ => true | _ => false
  mutate prepared recipe getNamed (fun value => .pair (.first value) (.word decDescriptor)) fun error =>
    match error.code with | .callableIdentityMismatch => true | _ => false
  mutate prepared recipe getNamed (fun value =>
    .pair (.pair (.inLeft .word .unit) (.second (.first value))) (.second value)) fun error =>
    match error.code with | .callableIdentityMismatch => true | _ => false
  mutate prepared recipe getNamed (fun value =>
    .pair (.pair (.inRight .unit (.word (w 900))) (.second (.first value))) (.second value)) fun error =>
    match error.code with | .callableIdentityMismatch => true | _ => false
  mutate prepared recipe getNamed (fun value =>
    .pair (.pair (.first (.first value)) (.lambda .word (Core.LanguageResult.resultType .word)
      (Core.LanguageResult.success (.word (w 999))))) (.second value)) fun error =>
    match error.code with | .callablePayloadMismatch => true | _ => false
  mutate prepared recipe getBuiltin (fun value =>
    .pair (.pair (.first (.first value)) (.lambda .word (Core.LanguageResult.resultType .integer)
      (Core.LanguageResult.success (.integer 999)))) (.second value)) fun error =>
    match error.code with | .callablePayloadMismatch => true | _ => false
  changedGlobal prepared recipe inc
  let made ← match prepared.runSource (← key program "make") [.word (w 3)] 150000 with
    | .ok made => pure made | .error error => throw (IO.userError s!"compatible lambda native execution failed: {reprStr error}")
  let projection ← project automatic.checked made.entry.sourceResultType made.entry.native.resultType
  match SourceCoreCompatibleOutputs.decodeSuccess recipe made.result.context made.result.contextOwner
      made.entry.sourceResultType projection.eq made.result.native with
  | .error {code := .lambdaExportRequiresLedger (.lambda _ _ _), ..} => pure ()
  | .error error => throw (IO.userError s!"compatible lambda export boundary changed: {reprStr error}")
  | .ok _ => throw (IO.userError "compatible raw source closure exported without capture ledger")
  IO.println "compatible named/builtin source outputs, deep raw metadata, exact code/evidence and tamper rejection GREEN"

end Tests.SourceCoreCompatibleOutputs
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatiblePreparedFunctions
/-! Automatic compatible artifacts own checked definitions, cached functions,
raw input extensions and dynamic diagnostics. Invocation and resume use Core. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatiblePreparedFunctions
open Solcore Solcore.Frontend SourceInference
abbrev DataValue := SourceCoreCompatibleValues.Value
abbrev Key := SourceSpecialization.SpecializationKey

private def w (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def assertTrue (test : Bool) (message : String) : IO Unit :=
  unless test do throw (IO.userError message)
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box<T> { Box(T) }",
    "trait Marker<T> {}", "impl Marker<mapping(Word => Word)> {}",
    "function keep<T>(value: T) returns (T) where T: Marker { return value; }",
    "function local(table: mapping(Word => Word)) returns (mapping(Word => Word)) { let f = lam(item) { return keep(item); }; return f(table); }",
    "function ordered(table: mapping(@Word => Word), key: @Word) returns (mapping(@Word => Word)) { table[key] += 3; return table; }",
    "function lazy() returns (mapping(Word => Word)) { let table: mapping(Word => Word); table[1] = 7; return table; }",
    "function choose(value: Box<Word>) returns (Word) { match (value) { case .Box(bound) { return bound; } default { return 99; } } }",
    "function missing(table: mapping(Word => Box<Word>), key: Word) returns (Word) { table[key] = .Box(7); return 7; }",
    "function absent() returns (Word) { let absent: Word; return absent; }"
  ]}] }

private def key (program : CheckedProgram) (name : String) : IO Key := do
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure ⟨signature.id, []⟩
  | _ => throw (IO.userError s!"compatible prepared fixture missing: {name}")

private def completed {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared checked) (key : Key)
    (arguments : List DataValue) (fuel : Nat) : IO (SourceCoreCompatibleFunctions.Completion checked) := do
  match prepared.runData key arguments fuel 500 with
  | .ok result => pure result
  | .error error => throw (IO.userError s!"compatible prepared run failed: {reprStr error}")

private def succeeded {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared checked) (key : Key)
    (arguments : List DataValue) (expected : DataValue) : IO Unit := do
  for fuel in [0, 8, 65536] do
    let completion ← completed prepared key arguments fuel
    let native := match completion.result.native.checkpoint? with
      | some checkpoint => checkpoint.resume 65536
      | none => completion.result.native
    match native.observation with
    | .succeeded value _ =>
        let decoded ← match SourceCoreCompatibleValues.decode 500 completion.result.context
            completion.entry.sourceResultType value with
          | .ok value => pure value
          | .error error => throw (IO.userError s!"compatible prepared output failed: {reprStr error}")
        assertTrue (decoded == expected) s!"compatible prepared result changed: {reprStr decoded}"
    | observation => throw (IO.userError s!"compatible prepared observation changed: {reprStr observation}")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"compatible prepared source rejected: {reprStr error}")
  let names := ["local", "ordered", "lazy", "choose", "missing", "absent"]
  let keys ← names.mapM (key program)
  let plan ← match SourceSpecializationWorklist.run program
      (keys.map (fun key => ⟨key.declaration, []⟩)) 128 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"compatible prepared worklist failed: {reprStr result}")
  let automatic ← match SourceCoreCompatibleFunctions.prepare program plan 500 with
    | .ok automatic => pure automatic
    | .error error => throw (IO.userError s!"compatible automatic factory failed: {reprStr error}")
  let prepared := automatic.prepared
  assertTrue (prepared.entries.length == keys.length) "compatible prepared roots disappeared"
  let table : DataValue := .mapping .word .word [(.word (w 1), .word (w 9))]
  succeeded prepared (← key program "local") [table] table
  succeeded prepared (← key program "lazy") [] (.mapping .word .word [(.word (w 1), .word (w 7))])
  let rawMap : DataValue := .mapping (.proxy (.comptime .word)) (.comptime .word)
    [(.proxy (.comptime .word), .word (w 1)), (.proxy (.comptime .word), .word (w 2))]
  let updated : DataValue := .mapping (.proxy (.comptime .word)) (.comptime .word)
    [(.proxy (.comptime .word), .word (w 4)), (.proxy (.comptime .word), .word (w 2))]
  succeeded prepared (← key program "ordered") [rawMap, .proxy (.comptime .word)] updated
  let box ← match program.signatures.dataTypes.find? (·.name == "Box") with
    | some box => pure box | none => throw (IO.userError "compatible Box missing")
  let ctor ← match box.constructors[0]? with
    | some ctor => pure ctor | none => throw (IO.userError "compatible constructor missing")
  let boxType := TypeSystem.Ty.nominal box.id [.word]
  let ordinary : DataConstructorInstantiation := ⟨ctor.id, box.parameters.zip [.word], [.word], boxType⟩
  let raw : DataConstructorInstantiation := ⟨ctor.id, box.parameters.zip [.comptime .word],
    [.comptime .word], .nominal box.id [.comptime .word]⟩
  succeeded prepared (← key program "choose") [.constructed ordinary [.word (w 7)]] (.word (w 7))
  succeeded prepared (← key program "choose") [.constructed raw [.word (w 7)]] (.word (w 99))
  let failure ← completed prepared (← key program "missing")
    [.mapping (.comptime .word) (.comptime boxType) [], .word (w 1)] 65536
  match failure.result.native.observation with
  | .failed reason _ =>
      let diagnostic ← match failure.result.diagnostics.diagnostic? reason with
        | some diagnostic => pure diagnostic
        | none => throw (IO.userError "compatible dynamic missing diagnostic absent")
      assertTrue (decide (diagnostic.error = .typeMismatch (.comptime boxType) none))
        "compatible dynamic fault lost its raw value type"
      assertTrue diagnostic.span.isSome "compatible dynamic fault lost its source span"
  | observation => throw (IO.userError s!"compatible missing default did not fail: {reprStr observation}")
  let absent ← completed prepared (← key program "absent") [] 65536
  match absent.result.native.observation with
  | .failed reason _ =>
      assertTrue (absent.result.diagnostics.diagnostic? reason).isSome
        "compatible uninitialized read lost its diagnostic"
  | observation => throw (IO.userError s!"compatible uninitialized read changed: {reprStr observation}")
  assertTrue (decide (failure.result.diagnostics.additional.map (·.1)).Nodup)
    "compatible dynamic/callable diagnostic reservations overlap"
  IO.println "compatible automatic function artifacts, raw data, dynamic diagnostics and typed resume GREEN"
end Tests.SourceCoreCompatiblePreparedFunctions
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleRuntimeContextValidity
/-! Actual source frames and lexical binder changes supply the runtime context
condition before a Header exists. All rows and residual modes are preserved. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleRuntimeContextValidity
open Solcore Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleRuntimeContextValidity

theorem actual_frame {program : Program} {instantiation : DeclarationInstantiation}
    {body : Dynamic.BodyInstance} {function : Dynamic.Closure} {context : SourceSemantics.Context}
    {types : List TypeSystem.Ty} {solved : List SolvedRequirement}
    (frame : NamedCalls.SourceFrame program instantiation body function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (programTyped : ProgramWellFormed program) (sameLedger : function.context.solvedRequirements = solved) :
    Valid solved context function.evidence :=
  of_frame frame extended programTyped sameLedger

/-- An unused row stays in the complete list after an actual binder extension.
The execution-facing condition cannot silently shorten a template ledger. -/
theorem unused_row_retained {solved : List SolvedRequirement} {source target : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {owner : Resolved.DeclarationId} {binder : TypedBinder}
    (valid : Valid solved source evidence) (extended : BinderExtends owner source binder target)
    {row : SolvedRequirement} (unused : row ∈ solved) : row ∈ target.solvedRequirements := by
  rw [(valid.extend extended).ledger]
  exact unused

theorem residual_mode_retained {source target : SourceSemantics.Context} {owner : Resolved.DeclarationId}
    {parameters : List TypedBinder} {types : List TypeSystem.Ty}
    (extended : MonoBindersExtend owner source parameters types target)
    (actualMode : source.residualTypeVariables = true) : target.residualTypeVariables = true :=
  (RecursiveNamedInitialContextValidity.mono_fields extended).targetResidualVariablesOpen actualMode

abbrev same_ordinary_context := @of_ordinary
abbrev same_context_transport := @Valid.transport

end Tests.SourceCoreCompatibleRuntimeContextValidity
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleSourceInstantiationClosure
/-! Closedness bridges independent source admission to validity without
changing the real residual context. Unused and reordered substitution rows
remain visible. Runtime checks inspect actual retained compiler metadata;
they do not supply source typing or well-formedness proofs. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleSourceInstantiationClosure
open Solcore Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleSourceInstantiationClosure

private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def residual : SourceSemantics.Context :=
  (SourceSemantics.Context.ofSignatures signatures).withResidualTypeVariables

private theorem binders : TypeParameterBindersWellFormed residual := by
  simp [TypeParameterBindersWellFormed, residual, Context.ofSignatures,
    Context.withResidualTypeVariables]

/-- Closed composite types retain staging wrappers and the exact source scope. -/
theorem composite_in_residual :
    TypeWellFormed residual (.comptime (.function (.proxy .bool) (.mapping .bool (.product .word .integer)))) ∧
    residual.residualTypeVariables = true := by
  refine ⟨well_formed ⟨binders, .comptime (.function (.proxy (.builtin .bool))
    (.mapping (.builtin .bool) (.product (.builtin .word) (.builtin .integer))))⟩ rfl rfl, rfl⟩

/-- Full range checking is independent of declaration parameter order. -/
theorem reordered_range (first second : TypeSystem.TypeParameterId) :
    ParameterSubstitution.RangeWellFormed residual [(second, .bool), (first, .comptime .word)] := by
  apply range_well_formed (lexical := rfl)
  · intro parameter replacement member
    rcases List.mem_cons.mp member with same | member
    · cases same; exact ⟨binders, .builtin .bool⟩
    · cases List.mem_singleton.mp member; exact ⟨binders, .comptime (.builtin .word)⟩
  · intro parameter replacement member
    rcases List.mem_cons.mp member with same | member
    · cases same; rfl
    · cases List.mem_singleton.mp member; rfl

/-- An unused residual replacement remains admissible but cannot be hidden by
the fact that applying the substitution leaves a closed result unchanged. -/
theorem unused_open_row (parameter : TypeSystem.TypeParameterId) :
    ParameterSubstitution.RangeAdmissible residual [(parameter, .variable ⟨17⟩)] ∧
    TypeSystem.ParameterSubstitution.apply [(parameter, .variable ⟨17⟩)] .word = .word ∧
    ¬ ClosedParameterRange [(parameter, .variable ⟨17⟩)] ∧
    ¬ ParameterSubstitution.RangeWellFormed residual [(parameter, .variable ⟨17⟩)] := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · intro other replacement member
    simp only [List.mem_singleton] at member
    cases member
    exact TypeAdmissible.variableOfResidual binders rfl ⟨17⟩
  · intro closed
    have impossible := closed parameter (.variable ⟨17⟩) (by simp)
    cases impossible
  · intro valid
    have impossible := TypeWellScoped.variable_iff.mp
      (valid parameter (.variable ⟨17⟩) (by simp)).typeWellScoped
    cases impossible

variable {checked : CallableAncestryPairedLookup.Checked} {base : CallableAncestryPairedLookup.Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context} {definitions : Core.DataEnvironment} {program : SourceSemantics.Program}

/-- The actual named header supplies lexical emptiness, without a false
residual assumption. All declaration metadata is retained by the conclusion. -/
theorem actual_header_declaration (header : RecursiveNamedCatalog.Header prepared values definitions program)
    {instantiation : SourceInference.DeclarationInstantiation}
    (admissible : SourceSemantics.DeclarationInstantiation.Admissible header.context instantiation)
    (closed : ClosedParameterRange instantiation.parameterSubstitution) :
    SourceSemantics.DeclarationInstantiation.Valid header.context instantiation :=
  declaration_valid admissible (RecursiveNamedSourceContextFacts.header_typeVariables header) closed

theorem actual_header_constructor (header : RecursiveNamedCatalog.Header prepared values definitions program)
    {instantiation : SourceInference.DataConstructorInstantiation}
    (admissible : SourceSemantics.DataConstructorInstantiation.Admissible header.context instantiation)
    (closed : ClosedParameterRange instantiation.parameterSubstitution) :
    SourceSemantics.DataConstructorInstantiation.Valid header.context instantiation :=
  constructor_valid admissible (RecursiveNamedSourceContextFacts.header_typeVariables header) closed

private def content : String := String.intercalate "\n" [
  "enum Pair<A, B> { Pair(A, B) }",
  "function choose<A, B>(first: A, second: B) returns (A) { return first; }",
  "function wordRoot() returns (Word) { return choose(7, true); }",
  "function boolRoot() returns (Bool) { return choose(false, 9); }",
  "function dataRoot() returns (Pair<Word, Bool>) { return Pair(choose(11, false), true); }"
]
private def require := SourceCoreUnifiedCorpusSupport.assertTrue

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "source instantiation closure" content
    ["wordRoot", "boolRoot", "dataRoot"]
  let mut functions := 0
  let mut constructors := 0
  for named in compiled.indexed.base.functions do
    let source := CallableIndexedNamedGeneration.source named
    for item in source.nodes do
      match item with
      | .expression node =>
        match node.form with
        | .call _ _ (.declaration instantiation) =>
          let key ← SourceCoreUnifiedCorpusSupport.get "closure exact source key"
            (SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan instantiation)
          let selected ← SourceCoreUnifiedCorpusSupport.get "closure full specialization"
            (SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan key)
          require (decide (instantiation = CallableNamedCanonicalOrder.retainedInstantiation selected))
            "closure full source instantiation changed"
          require (instantiation.parameterSubstitution.length == 2)
            "closure lost generic source parameter rows"
          require (instantiation.parameterSubstitution.all (fun row => SourceCoreDataCatalog.closed row.2))
            "closure retained open source replacement"
          functions := functions + 1
        | .constructor instantiation _ =>
          require (instantiation.parameterSubstitution.length == 2)
            "closure lost generic constructor parameter rows"
          require (instantiation.parameterSubstitution.all (fun row => SourceCoreDataCatalog.closed row.2))
            "closure constructor range retained open replacement"
          constructors := constructors + 1
        | _ => pure ()
      | _ => pure ()
  require (functions == 3 && constructors == 1)
    s!"closure actual metadata coverage changed: functions={functions}, constructors={constructors}"
  IO.println "source instantiation closure: true residual scope, complete ranges, generic source metadata GREEN"

end Tests.SourceCoreCompatibleSourceInstantiationClosure
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleValues
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreCompatibleValues.Encoded.mk
#check_failure Solcore.Frontend.SourceCoreCompatibleValues.Decoded.mk

/-! This separate compatibility profile authenticates raw metadata without
erasing it. Its executable data boundary and ordinary Core mapping operations
are tested here; compiler routing, function handles and initial source heaps
are outside this unit. -/

set_option autoImplicit false

namespace Tests.SourceCoreCompatibleValues
open Solcore Solcore.Frontend
open Solcore.Frontend.SourceInference (DataConstructorInstantiation)
open SourceCoreCompatibleValues

private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "enum Box<T> { Box(T) }",
    "enum Tree<T> { Leaf(T), Branch(Tree<T>, Tree<T>) }",
    "enum Packet<T> { Empty, Only(T), Many(T, Bool, Word) }",
    "function main() returns (Word) { return 7; }"
  ] }] }

private def data (program : CheckedProgram) (name : String) : IO ProgramDataSignature :=
  match program.signatures.dataTypes.filter (·.name == name) with
  | [signature] => pure signature
  | _ => throw (IO.userError s!"compatible signature missing: {name}")

private def metadata (signature : ProgramDataSignature) (arguments : List TypeSystem.Ty)
    (index : Nat := 0) : IO DataConstructorInstantiation := do
  let constructor ← match signature.constructors[index]? with
    | some constructor => pure constructor
    | none => throw (IO.userError "compatible constructor missing")
  let substitution : TypeSystem.ParameterSubstitution := signature.parameters.zip arguments
  pure ⟨constructor.id, substitution, constructor.payloadTypes.map substitution.apply,
    .nominal signature.id arguments⟩

private def encoded (context : Context) (type : TypeSystem.Ty) (value : Value) :
    IO (Encoded 400 context type value) :=
  match encode 400 context type value with
  | .ok receipt => pure receipt
  | .error error => throw (IO.userError s!"compatible encoding failed: {reprStr error}")

private def roundtrip (context : Context) (type : TypeSystem.Ty) (value : Value) :
    IO (Encoded 400 context type value) := do
  let receipt ← encoded context type value
  match decode 400 receipt.context type receipt.value with
  | .ok actual => assertTrue (actual == value) "compatible roundtrip changed raw source data"
  | .error error => throw (IO.userError s!"compatible decoding failed: {reprStr error}")
  let repeated ← encoded receipt.context type value
  assertTrue (repeated.value == receipt.value && repeated.context.registry.length == receipt.context.registry.length)
    "compatible reencoding changed native data or assigned another metadata slot"
  pure receipt

private def rejectDecode (context : Context) (type : TypeSystem.Ty) (core : Core.Value) : IO Error :=
  match decode 400 context type core with
  | .error error => pure error
  | .ok source => throw (IO.userError s!"forged compatible input accepted: {reprStr source}")

private def rejectEncode (context : Context) (type : TypeSystem.Ty) (value : Value) : IO Error :=
  match encode 400 context type value with
  | .error error => pure error
  | .ok _ => throw (IO.userError "forged compatible source metadata accepted")

private def quote : Core.Value → Option Core.Expr
  | .unit => some .unit
  | .bool value => some (.bool value)
  | .word value => some (.word value)
  | .integer value => some (.integer value)
  | .pair left right => do pure (.pair (← quote left) (← quote right))
  | .inLeft type value => do pure (.inLeft type (← quote value))
  | .inRight type value => do pure (.inRight type (← quote value))
  | .constructed constructor value => do pure (.construct constructor (← quote value))
  | _ => none

private def literal (value : Core.Value) : IO Core.Expr :=
  match quote value with
  | some expression => pure expression
  | none => throw (IO.userError "compatible test literal contains a capability")

private def completes (definitions : Core.DataEnvironment) (type : Core.Ty) (body : Core.Expr)
    (expected : Core.Value) : IO Unit := do
  let program : Core.Program := ⟨type, body, definitions⟩
  assertTrue program.check "compatible mapping program failed Core checking"
  match program.runStateful 10000 with
  | .done actual _ => assertTrue (actual == expected) s!"compatible Core result changed: {reprStr actual}"
  | result => throw (IO.userError s!"compatible mapping program failed: {reprStr result}")

private def recursive (leaf branch : DataConstructorInstantiation) : Nat → Value
  | 0 => .constructed leaf [.integer (-(2 ^ 400))]
  | depth + 1 => .constructed branch [recursive leaf branch depth, .constructed leaf [.integer (Int.ofNat depth)]]

example {fuel : Nat} {context : Context} {type : TypeSystem.Ty} {value : Value}
    (receipt : Encoded fuel context type value) :
    decode fuel receipt.context type receipt.value = .ok value := receipt.decode_encode

example {fuel : Nat} {context : Context} {type : TypeSystem.Ty} {value : Value}
    (receipt : Encoded fuel context type value) (world : Core.StoreTyping) :
    Core.RuntimeValueHasType world receipt.value receipt.type context.checked.catalog.definitions := receipt.typed world

example {fuel : Nat} {context : Context} {type : TypeSystem.Ty} {core : Core.Value}
    (receipt : Decoded fuel context type core) :
    ∃ rebuilt : Extended context.registry Core.Value,
      encodeRaw fuel context.checked context.registry type receipt.source = .ok rebuilt ∧ rebuilt.value = core :=
  receipt.reencodes

example {fuel : Nat} {context : Context} {type : TypeSystem.Ty} {value : Value}
    (receipt : Encoded fuel context type value) (id : Core.Word) (metadata : Metadata)
    (found : context.registry.lookup id = some metadata) :
    receipt.context.registry.lookup id = some metadata := receipt.preserves.lookup found

example (fuel : Nat) (type : TypeSystem.Ty) :
    defaultValue? fuel type = none ↔ SourceTypedRuntime.defaultValue? fuel type = none :=
  defaultValue?_absent_iff fuel type

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"compatible fixture checking failed: {reprStr error}")
  let box ← data program "Box"
  let tree ← data program "Tree"
  let packet ← data program "Packet"
  let boxType := TypeSystem.Ty.nominal box.id [.word]
  let treeType := TypeSystem.Ty.nominal tree.id [.integer]
  let packetType := TypeSystem.Ty.nominal packet.id [.integer]
  let proxyType := TypeSystem.Ty.proxy .word
  let proxyMap := TypeSystem.Ty.mapping proxyType .word
  let defaultMap := TypeSystem.Ty.mapping .word proxyType
  let nominalMap := TypeSystem.Ty.mapping .word boxType
  let nestedMap := TypeSystem.Ty.mapping .word (.mapping .word .word)
  let scalarType : TypeSystem.Ty := .product .unit (.product .bool (.product .word .integer))
  let functionType := TypeSystem.Ty.function .word .word
  let checked ← match SourceCoreCompatibleCatalog.prepare program.signatures 200
      [boxType, treeType, packetType, proxyType, .proxy .bool, proxyMap, defaultMap, nominalMap,
        nestedMap, scalarType, functionType, .proxy functionType, .mapping functionType .word,
        .mapping .word functionType] with
    | .ok checked => pure checked
    | .error error => throw (IO.userError s!"compatible catalog preparation failed: {reprStr error}")
  let context := Context.initial checked
  assertTrue (checked.catalog.definitions.isWellFormed) "compatible recursive definitions are not well formed"
  let canonicalBox ← match checked.catalog.project boxType with
    | .ok type => pure type | .error error => throw (IO.userError s!"compatible canonical projection failed: {reprStr error}")
  let stagedBoxType ← match checked.catalog.project (.nominal box.id [.comptime .word]) with
    | .ok type => pure type | .error error => throw (IO.userError s!"compatible staged projection failed: {reprStr error}")
  assertTrue (canonicalBox == stagedBoxType)
    "compatible nominal projection distinguished runtime-equivalent arguments"
  assertTrue (checked.catalog.identity? proxyType == checked.catalog.identity? (.proxy (.comptime .word)))
    "compatible proxy identities are not runtime-type keyed"
  let strict ← match SourceCoreDataCatalog.prepare program.signatures 100 [proxyType, boxType, .nominal box.id [.comptime .word]] with
    | .ok strict => pure strict
    | .error error => throw (IO.userError s!"strict catalog regression preparation failed: {reprStr error}")
  assertTrue (strict.catalog.identity? boxType != strict.catalog.identity? (.nominal box.id [.comptime .word]))
    "separate compatible profile changed strict nominal identity"
  let proxyOwner := (checked.catalog.identity? proxyType).getD ⟨999⟩
  assertTrue (checked.catalog.definitions.lookupConstructorPayloadType? ⟨proxyOwner, 0⟩ == some .word)
    "compatible proxy is missing its raw metadata word"
  let strictProxy := (strict.catalog.identity? proxyType).getD ⟨999⟩
  assertTrue (strict.catalog.definitions.lookupConstructorPayloadType? ⟨strictProxy, 0⟩ == some .unit)
    "strict proxy payload convention changed"

  let scalars : Value := .product .unit (.product (.bool true) (.product (.word (word 17)) (.integer (-(2 ^ 512)))))
  let scalar ← roundtrip context (.comptime scalarType) scalars
  assertTrue (scalar.value == .pair .unit (.pair (.bool true) (.pair (.word (word 17)) (.integer (-(2 ^ 512))))))
    "scalar stage projection or unbounded integer changed"
  let ordinary ← roundtrip scalar.context proxyType (.proxy .word)
  let staged ← roundtrip ordinary.context proxyType (.proxy (.comptime .word))
  assertTrue (ordinary.value != staged.value && staged.context.registry.length == ordinary.context.registry.length + 1)
    "dynamic proxy metadata was erased or not certified as an extension"
  let ordinaryBox ← metadata box [.word]
  let stagedBox ← metadata box [.comptime .word]
  let boxValue ← roundtrip staged.context boxType (.constructed ordinaryBox [.word (word 7)])
  let stagedBoxValue ← roundtrip boxValue.context boxType (.constructed stagedBox [.word (word 7)])
  assertTrue (boxValue.value != stagedBoxValue.value) "nominal raw instantiation metadata collapsed"
  match boxValue.value, stagedBoxValue.value with
  | .constructed left _, .constructed right _ => assertTrue (left == right) "canonical compatible nominal native tag changed"
  | _, _ => throw (IO.userError "compatible nominal metadata was not carried in payloads")
  let leaf ← metadata tree [.integer]
  let branch ← metadata tree [.integer] 1
  let treeValue ← roundtrip stagedBoxValue.context treeType (recursive leaf branch 12)
  let empty ← metadata packet [.integer]
  let only ← metadata packet [.integer] 1
  let many ← metadata packet [.integer] 2
  let packetEmpty ← roundtrip treeValue.context packetType (.constructed empty [])
  let packetOnly ← roundtrip packetEmpty.context packetType (.constructed only [.integer 3])
  let packetMany ← roundtrip packetOnly.context packetType (.constructed many [.integer (-2), .bool true, .word (word 8)])
  let entries : List (Value × Value) := [(.proxy (.comptime .word), .word (word 7)),
    (.proxy (.comptime .word), .word (word 99)), (.proxy .word, .word (word 8))]
  let mapping ← roundtrip packetMany.context proxyMap (.mapping proxyType .word entries)
  let reversed ← roundtrip mapping.context proxyMap (.mapping proxyType .word entries.reverse)
  assertTrue (mapping.value != reversed.value) "compatible mapping sorted or deduplicated entry order"
  let transported ← roundtrip reversed.context defaultMap (.mapping (.comptime .word) (.proxy (.comptime .word)) [])
  let nested ← roundtrip transported.context nestedMap (.mapping .word (.mapping (.comptime .word) (.comptime .word)) [])
  let missing ← roundtrip nested.context nominalMap (.mapping .word boxType [])
  let proxyFunction ← roundtrip missing.context (.proxy functionType) (.proxy functionType)
  let emptyFunctionKeys ← roundtrip proxyFunction.context (.mapping functionType .word) (.mapping functionType .word [])
  let emptyFunctionValues ← roundtrip emptyFunctionKeys.context (.mapping .word functionType) (.mapping .word functionType [])
  let context := emptyFunctionValues.context
  let proxyLayout ← match checked.catalog.mappingLayout proxyType .word with
    | .ok layout => pure layout | .error error => throw (IO.userError s!"compatible proxy layout failed: {reprStr error}")
  let proxyComparator : Core.Expr := .lambda (.product proxyLayout.keyType proxyLayout.keyType) .bool
    (.matchData proxyOwner .bool (.first (.var 0)) [
      .matchData proxyOwner .bool (.second (.var 1)) [.binary .wordEq (.var 1) (.var 0)]])
  let mappingExpression ← literal mapping.value
  let stagedKey ← literal staged.value
  let ordinaryKey ← literal ordinary.value
  completes checked.catalog.definitions (Core.LanguageResult.resultType .word)
    (SourceCoreMappingWithDefault.lookup proxyLayout (word 1000) proxyComparator mappingExpression stagedKey)
    (.inRight .word (.word (word 7)))
  completes checked.catalog.definitions (Core.LanguageResult.resultType .word)
    (SourceCoreMappingWithDefault.lookup proxyLayout (word 1000) proxyComparator mappingExpression ordinaryKey)
    (.inRight .word (.word (word 8)))
  let wordComparator : Core.Expr := .lambda (.product .word .word) .bool
    (.binary .wordEq (.first (.var 0)) (.second (.var 0)))
  let defaultLayout ← match checked.catalog.mappingLayout .word proxyType with
    | .ok layout => pure layout | .error error => throw (IO.userError s!"compatible default layout failed: {reprStr error}")
  completes checked.catalog.definitions (Core.LanguageResult.resultType defaultLayout.valueType)
    (SourceCoreMappingWithDefault.lookup defaultLayout (word 1000) wordComparator (← literal transported.value) (.word (word 4)))
    (.inRight .word staged.value)
  let missingLayout ← match checked.catalog.mappingLayout .word boxType with
    | .ok layout => pure layout | .error error => throw (IO.userError s!"compatible missing layout failed: {reprStr error}")
  let missingHeader ← match missing.value with
    | .pair (.word header) _ => pure header | _ => throw (IO.userError "compatible missing header is malformed")
  completes checked.catalog.definitions (Core.LanguageResult.resultType missingLayout.valueType)
    (SourceCoreMappingWithDefault.lookup missingLayout (word 1000) wordComparator (← literal missing.value) (.word (word 4)))
    (.inLeft missingLayout.valueType (.word ((word 1000).add missingHeader)))

  let changedDefault ← match transported.value with
    | .pair header (.pair _ entries) => pure (.pair header (.pair (.inRight .unit ordinary.value) entries))
    | _ => throw (IO.userError "compatible transported carrier is malformed")
  let tampered ← rejectDecode context defaultMap changedDefault
  assertTrue (tampered.code == .transportedDefaultMismatch) "same-typed forged default was accepted"
  let unknown := Core.Value.constructed ⟨proxyOwner, 0⟩ (.word (word 999999))
  let unknownError ← rejectDecode context proxyType unknown
  assertTrue (unknownError.code == .unknownMetadata (word 999999)) "unknown raw metadata ID accepted"
  let zeroError ← rejectDecode context proxyType (.constructed ⟨proxyOwner, 0⟩ (.word Core.Word.zero))
  assertTrue (zeroError.code == .unknownMetadata Core.Word.zero) "reserved metadata zero was accepted"
  discard <| rejectDecode context proxyType (.constructed ⟨proxyOwner, 1⟩ (.word (word 1)))
  let wrongKind ← match transported.value with
    | .pair header _ => pure (.constructed ⟨proxyOwner, 0⟩ header)
    | _ => throw (IO.userError "compatible mapping header missing")
  discard <| rejectDecode context proxyType wrongKind
  discard <| rejectEncode context boxType (.constructed {stagedBox with payloadTypes := [.bool]} [.bool true])
  discard <| rejectEncode context boxType (.constructed ordinaryBox [])
  discard <| rejectEncode context boxType (.constructed {ordinaryBox with
    parameterSubstitution := ordinaryBox.parameterSubstitution ++ ordinaryBox.parameterSubstitution} [.word (word 7)])
  discard <| rejectEncode context boxType (.constructed ordinaryBox [.bool true])
  discard <| rejectEncode context .word (.bool false)
  discard <| rejectDecode context (.product .word .word) (.pair (.word (word 1)) (.cellRef .word 0))
  discard <| rejectDecode context (.product .word .word) (.pair (.word (word 1)) (.hostFunction .storageRead))
  let nativeBoxForgery ← match boxValue.value with
    | .constructed tag (.pair rawId _) => pure (.constructed tag (.pair rawId (.cellRef .word 0)))
    | _ => throw (IO.userError "compatible Box carrier is malformed")
  discard <| rejectDecode context boxType nativeBoxForgery
  let functionError ← rejectDecode context functionType (.closure .word .word (.var 0) [])
  assertTrue (functionError.code == .functionHandleRequired) "raw closure crossed the data-only compatibility boundary"
  let handleError ← rejectEncode context functionType .unit
  assertTrue (handleError.code == .functionHandleRequired) "function data accepted without an authenticated handle"
  match encode 0 context treeType (recursive leaf branch 0) with
  | .error error => assertTrue (error.code == .exhausted) "codec exhausted with a different error"
  | .ok _ => throw (IO.userError "codec ignored its fuel bound")
  let limited ← match SourceCoreCompatibleCatalog.prepare program.signatures 50 [proxyType] [] {maxEntries := 1} with
    | .ok checked => pure checked | .error error => throw (IO.userError s!"compatible bounded catalog failed: {reprStr error}")
  let budgetError ← rejectEncode (Context.initial limited) proxyType (.proxy (.comptime .word))
  assertTrue (budgetError.code == .metadata (.entryBudgetExhausted 1)) "compatible codec bypassed checked metadata extension budget"
  IO.println "compatible catalog, raw metadata, transported defaults and typed deep codec GREEN"

end Tests.SourceCoreCompatibleValues
end
