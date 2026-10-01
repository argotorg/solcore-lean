import Solcore.SourceSemantics.CoreLowering.TypedStatementMeaning
import Solcore.Frontend.SourceCoreCallableIndexedFrames
import Solcore.Test.SourceCompilerFeatureSupport

#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Repeated indexing crosses a discarded-payload slot and captures a real
ambient closure. The full source statement trace and completed reflection
consume actual lowering receipts, without a child/body semantic premise. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreTypedStatements
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open TypedStatements
open CompatibleStatements (FlowRep BodyRep)
open CompatiblePayload GeneralHeap ReadOnly
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"typed_statements", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "typed_statements.solc"⟩, 0, 4⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def mappingType : TypeSystem.Ty := .mapping .bool .bool
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "table", .mono mappingType, [], false, none⟩
private def baseNode : ExpressionNode := { id := id 0, span, type := mappingType, form := .reference "table" (.local binder.id) }
private def keyNode : ExpressionNode := { id := id 1, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def indexNode : ExpressionNode := { id := id 2, span, type := .bool, form := .index (id 0) (id 1) }
private def statement (index : Nat) : StatementId := ⟨⟨owner, index + 10⟩⟩
private def discarded : StatementNode := ⟨statement 0, span, .unit, .expression (id 2) true⟩
private def returned : StatementNode := ⟨statement 1, span, .bool, .returnStmt (some (id 2))⟩
private def unreachable : StatementNode := ⟨statement 2, span, .unit, .breakStmt⟩
private def statements := [statement 0, statement 1, statement 2]
private def source : TypedSource := {
  owner, inputs := [binder], roots := statements.map .statement,
  nodes := [.expression baseNode, .expression keyNode, .expression indexNode,
    .statement discarded, .statement returned, .statement unreachable] }
private def context : SourceSemantics.Context := (SourceSemantics.Context.ofSignatures signatures).withLocal binder.id binder.scheme
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def compilation : SourceCoreFunctions.Context := ⟨⟨[], [], [], []⟩, ⟨owner, []⟩, [], 0, [], Word.zero⟩
private def noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .ok .unit
private def reason : Word := Word.ofNatModulo 17
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem metadata {expression : ExpressionId} {node : ExpressionNode} (found : source.lookupExpression? expression = some node) :
    node.requirements = CompatibleExpressionLiterals.owned node.form ∧ node.coercions = [] := by
  have member := (lookupExpression?_sound found).1
  simp [source] at member
  rcases member with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
private theorem boolAdmitted : TypeAdmissible context .bool :=
  .bool ((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal binder.id binder.scheme)
private theorem mappingAdmitted : TypeAdmissible context mappingType := .mapping boolAdmitted boolAdmitted
private theorem baseTyped : ExpressionHasType source context (id 0) mappingType := by
  apply ExpressionHasType.ofOrdinary (node := baseNode) (rawType := mappingType) (lookupExpression?_sound (by rfl))
    (.reference (.local (.head) (.head) (.intro (.empty _ _ rfl) (SchemeWellFormed.monoAdmissible mappingAdmitted) []
      .empty (by intro metavariable replacement member; cases member) (by exact SchemeInstantiates.empty_apply mappingType)
      (by simp) (by intro _ member; cases member) (.nil)))) mappingAdmitted mappingAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem keyTyped : ExpressionHasType source context (id 1) .bool := by
  apply ExpressionHasType.ofOrdinary (node := keyNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.reference (.builtinBoolean true)) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem indexTyped : ExpressionHasType source context (id 2) .bool := by
  apply ExpressionHasType.ofOrdinary (node := indexNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.index baseTyped keyTyped) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem indexSyntax : CompatibleExpressionTyped.Syntax source (id 2) :=
  .index (node := indexNode) (keyNode := keyNode) (by cbv) rfl (by cbv) .bool
    (.fragment (.fragment (.fragment (.fragment (.primitive (.product (.read (node := baseNode) rfl rfl)))))))
    (.fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal (node := keyNode) rfl (.bool _ _))))))))
private theorem sourceSyntax : TypedStatements.Syntax source context statements .bool :=
  .discard (node := discarded) (expressionNode := indexNode) rfl rfl rfl rfl rfl indexTyped indexSyntax
    (.returnValue (node := returned) (expressionNode := indexNode) [statement 2] rfl rfl rfl rfl rfl indexTyped indexSyntax)
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
private abbrev expressionPolicy := SourceCoreCompatibleDataExpressions.functionPolicy 100 values
private def policy : SourceCoreLoops.Policy := {
  lowerExpression := fun fuel source scope expression reasonAt =>
    SourceCoreFunctions.lowerExpressionWithPolicy expressionPolicy noBody fuel compilation source scope expression reasonAt
  readStatement := SourceCoreCompatibleDataExpressions.readStatement checked }
private theorem certified {code : Expr}
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy 12 source scope statements .bool (fun _ => reason) reason reason = .ok code) :
    ∃ flow, code = finish .bool flow reason reason ∧ Tree 100 values source context [] (fun _ => reason) scope statements .bool .bool flow := by
  apply tree_of_body rfl ?_ sourceSyntax rfl accepted
  intro budget expression node lowered childSyntax found typed generated
  exact CompatibleExpressionTyped.tree_of_functions unique declarations rfl rfl rfl
    ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩ (fun _ _ _ found => (metadata found).2)
    childSyntax found typed generated

private def compiledResult := SourceCoreLoops.lowerStatementsWithPolicy policy 12 source scope statements
  .bool (fun _ => reason) reason reason
private def frameLayout : SourceCoreCallableIndexedFrames.Layout := ⟨⟨checked.catalog.definitions.length⟩⟩
private def ambient : AmbientDefinitions checked.catalog.definitions := .append _ [frameLayout.definition]
private def functions : FunctionModel checked.catalog ambient where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible
private def model := CompatibleAmbientHeap.payloadModel checked values.registry functions
private def faults : FunctionCalls.FaultRep := fun error token =>
  ((∃ location, error = .uninitializedLocation location) ∧ token = reason) ∨
  (∃ key value tag, MetadataRep values.registry (.mapping key value) tag ∧ error = .missingMappingDefault value ∧ token = reason.add tag)
private theorem uninitialized : ∀ (id : ExpressionId) location, faults (.uninitializedLocation location) ((fun _ => reason) id) :=
  fun _ location => .inl ⟨⟨location, rfl⟩, rfl⟩
private theorem missing : ∀ (id : ExpressionId) key value tag, MetadataRep values.registry (.mapping key value) tag →
    faults (.missingMappingDefault value) (((fun _ => reason) id).add tag) :=
  fun _ key value tag owned => .inr ⟨key, value, tag, owned, rfl, rfl⟩
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
private def after : Dynamic.Heap := ⟨[⟨mappingType, some (.mapping .bool .bool []), none⟩]⟩
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
private theorem initialRead : Dynamic.ExpressionEvaluatesOutcome program context [] source sourceEnvironment before (id 2) (.value (.bool false)) after := by
  apply Dynamic.ExpressionEvaluatesOutcome.value
  apply Dynamic.ExpressionEvaluates.intro (raw := .bool false) (middle := after) (lookupExpression?_sound (node := indexNode) (by cbv))
  · change Dynamic.ExpressionFormEvaluates program context [] source sourceEnvironment before (.index (id 0) (id 1)) [] [] (.bool false) after
    apply Dynamic.ExpressionFormEvaluates.indexDefault (coercions := []) rfl
    · exact .intro (lookupExpression?_sound (node := baseNode) (by rfl))
        (.localEmptyMapping rfl .head (.intro .head) rfl rfl rfl (.intro (.intro .head) .head)) .nil
    · exact .intro (lookupExpression?_sound (node := keyNode) (by cbv)) (.builtinBoolean rfl) .nil
    · exact .nil
    · exact .bool
  · exact .nil

private theorem sourceTrace : Dynamic.FunctionStatementsExecuteOutcome program context [] source sourceEnvironment before
    statements context (.returned (.bool false)) after := by
  have first : Dynamic.ExpressionEvaluates program context [] source sourceEnvironment before (id 2) (.bool false) after := by
    cases initialRead with | value evaluated => exact evaluated
  have second : Dynamic.ExpressionEvaluates program context [] source sourceEnvironment after (id 2) (.bool false) after := by
    apply Dynamic.ExpressionEvaluates.intro (raw := .bool false) (middle := after) (lookupExpression?_sound (node := indexNode) rfl)
    · apply Dynamic.ExpressionFormEvaluates.indexDefault (coercions := []) rfl
      · exact .intro (lookupExpression?_sound (node := baseNode) rfl) (.local rfl .head (.intro .head) rfl rfl) .nil
      · exact .intro (lookupExpression?_sound (node := keyNode) rfl) (.builtinBoolean rfl) .nil
      · exact .nil
      · exact .bool
    · exact .nil
  exact .control (.cons (.expression (lookupStatement?_sound (node := discarded) rfl) rfl first)
    (.terminal (.returnValue (lookupStatement?_sound (node := returned) rfl) rfl second) (.returned _)))

/-- The first discarded index initializes the source mapping. The second
comparator captures its typed discarded value and the original ambient slots. -/
theorem accepted_preserves {code : Expr}
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy 12 source scope statements .bool (fun _ => reason) reason reason = .ok code) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (.integer 99 :: administrativeValue :: environment) store (code.rename ξ) value finalStore ∧
      BodyRep (values := values) (registry := values.registry) functions finalMap finalWorld faults .bool .bool (.returned (.bool false)) value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends [1] finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved [1] store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨flow, rfl, tree⟩ := certified accepted
  exact (Tree.body_preserves (values := values) functions (.refl _) program [] contextValid unique uninitialized missing
    tree reason reason initial.2 initial.1 locals agrees actualTyped sourceTrace).2

/-- Completion alone reconstructs the source statement trace, including
administrative helper allocations and the live mapping read after discard. -/
theorem accepted_reflects {code : Expr}
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy 12 source scope statements .bool (fun _ => reason) reason reason = .ok code)
    {value : Value} {finalStore : Store}
    (completed : Evaluates (.integer 99 :: administrativeValue :: environment) store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.FunctionStatementsExecuteOutcome program context [] source sourceEnvironment before statements context outcome after ∧
      BodyRep (values := values) (registry := values.registry) functions finalMap finalWorld faults .bool .bool outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends [1] finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved [1] store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨flow, rfl, tree⟩ := certified accepted
  exact Tree.body_reflects (values := values) functions (.refl _) program [] contextValid uninitialized missing
    tree reason reason initial.2 initial.1 locals agrees actualTyped completed

private def rawWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Item { Item(Word) }",
    "function repeated(m: mapping(Bool => Bool)) returns (Bool) { m[true]; return m[false]; }",
    "function lazy() returns (Bool) { let m: mapping(Bool => Bool); m[true]; return !m[false]; }",
    "function firstFailure() returns (Bool) { let m: mapping(Bool => Item); let n: mapping(Bool => Bool); m[true]; return n[false]; }",
    "function early() returns (Bool) { let m: mapping(Bool => Item); return true; m[true]; }",
    "function nested(m: mapping(Bool => mapping(Bool => Bool))) returns (Bool) { (m[true][false], !m[false][true]); return m[false][false] ? m[true][true] : !m[true][false]; }"]}] }

def run : IO Unit := do
  let generated ← SourceCompilerFeatureSupport.get "synthetic typed lowering" compiledResult
  let observed := Core.LanguageResult.observeResult (Core.runStateful 30000
    ⟨.eval (generated.rename ξ) (.integer 99 :: administrativeValue :: environment), [], store⟩)
  match observed with
  | .succeeded (.bool false) finalStore =>
      SourceCompilerFeatureSupport.require (finalStore[0]? == some administrativeValue)
        "typed discard changed the ambient closure cell"
  | _ => throw (IO.userError "actual synthetic typed lowering did not complete as false")
  let checked ← SourceCompilerFeatureSupport.get "typed statement checker" (checkProgram rawWorkspace)
  let repeated ← SourceCompilerFeatureSupport.compileNamed checked "repeated"
  let input : SourceCoreExecution.Value := .mapping .bool .bool [(.bool true, .bool false), (.bool false, .bool true)]
  SourceCompilerFeatureSupport.require ((← repeated.run [input]) == .bool true) "repeated index changed result"
  repeated.checkResume [input] (.bool true)
  let lazy ← SourceCompilerFeatureSupport.compileNamed checked "lazy"
  SourceCompilerFeatureSupport.require ((← lazy.run []) == .bool true) "lazy discarded index changed result"
  lazy.checkCells [] [(.mapping .bool .bool, some (.mapping .bool .bool []))]
  let failed ← SourceCompilerFeatureSupport.compileNamed checked "firstFailure"
  let invocation ← failed.invoke []
  match invocation.outcome with
  | .failed token _ =>
      match ← invocation.diagnostic token with
      | some {error := .typeMismatch _ none, span := some _, ..} => pure ()
      | _ => throw (IO.userError "discarded index lost its missing-default metadata/span")
  | _ => throw (IO.userError "discarded missing-default index did not fail")
  let failedState := SourceCompilerFeatureSupport.sourceState (← failed.audit [])
  match failedState.heap with
  | [first, second] =>
      SourceCompilerFeatureSupport.require (second.type == .mapping .bool .bool && second.value.isNone)
        "missing-default failure evaluated the remaining mapping read"
      match first.value with
      | some (.mapping .bool _ []) => pure ()
      | _ => throw (IO.userError "discarded index lost lazy root initialization")
  | _ => throw (IO.userError "discarded index changed source allocation order")
  let early ← SourceCompilerFeatureSupport.compileNamed checked "early"
  SourceCompilerFeatureSupport.require ((← early.run []) == .bool true) "return evaluated the unreachable missing-default index"
  let nested ← SourceCompilerFeatureSupport.compileNamed checked "nested"
  SourceCompilerFeatureSupport.require
    ((← nested.run [.mapping .bool (.mapping .bool .bool) []]) == .bool true) "nested typed expression statement changed result"
  IO.println "typed statements: discarded index captures, ambient closure, actual receipts, lazy default, early return and resume GREEN"
end Tests.SourceCoreTypedStatements
