import Solcore.SourceSemantics.CoreLowering.TypedScopedControlMeaning
import Solcore.Frontend.SourceCoreCallableIndexedFrames
import Solcore.Test.SourceCompilerFeatureSupport

#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Actual scoped block and conditional lowering supplies the full recursive
certificate. The independent trace includes lazy mapping initialization in a
block, a false condition with no else, and a subsequent explicit return. Native
condition and sequence slots carry typed captures and preserve resume effects. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreTypedScopedControl
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open TypedScopedControl
open TypedScopedStatements (Executes FlowRep)
open CompatiblePayload GeneralHeap ReadOnly
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"typed_scoped_control", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "typed_scoped_control.solc"⟩, 0, 4⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def mappingType : TypeSystem.Ty := .mapping .bool .bool
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "table", .mono mappingType, [], false, none⟩
private def baseNode : ExpressionNode := { id := id 0, span, type := mappingType, form := .reference "table" (.local binder.id) }
private def keyNode : ExpressionNode := { id := id 1, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def indexNode : ExpressionNode := { id := id 2, span, type := .bool, form := .index (id 0) (id 1) }
private def statement (index : Nat) : StatementId := ⟨⟨owner, index + 10⟩⟩
private def discarded : StatementNode := ⟨statement 0, span, .unit, .expression (id 2) true⟩
private def scopedBlock : StatementNode := ⟨statement 1, span, .unit, .block [statement 0]⟩
private def branchReturn : StatementNode := ⟨statement 2, span, .bool, .returnStmt (some (id 1))⟩
private def conditional : StatementNode := ⟨statement 3, span, .unit, .ifThen (id 2) [statement 2] none⟩
private def finalReturn : StatementNode := ⟨statement 4, span, .bool, .returnStmt (some (id 1))⟩
private def statements := [statement 1, statement 3, statement 4]
private def source : TypedSource := {
  owner, inputs := [binder], roots := statements.map .statement,
  nodes := [.expression baseNode, .expression keyNode, .expression indexNode, .statement discarded,
    .statement scopedBlock, .statement branchReturn, .statement conditional, .statement finalReturn] }
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
private theorem keySyntax : CompatibleExpressionTyped.Syntax source (id 1) :=
  .fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal (node := keyNode) rfl (.bool _ _)))))))
private theorem sourceSyntax (mode : Bool) : TypedScopedControl.Syntax source context mode statements .bool := by
  apply Syntax.block (node := scopedBlock) rfl rfl rfl
  · exact .fragment (.discard (node := discarded) (expressionNode := indexNode) rfl rfl rfl rfl rfl
      indexTyped indexSyntax (.nil (.inl rfl)))
  · apply Syntax.ifThen (node := conditional) (conditionNode := indexNode) rfl rfl rfl rfl rfl indexTyped indexSyntax
    · exact .fragment (.returnValue (node := branchReturn) (expressionNode := keyNode) [] rfl rfl rfl rfl rfl keyTyped keySyntax)
    · exact .fragment (.nil (.inl rfl))
    · exact .fragment (.returnValue (node := finalReturn) (expressionNode := keyNode) [] rfl rfl rfl rfl rfl keyTyped keySyntax)
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
private theorem certified {mode : Bool} {code : Expr}
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy 12 source scope statements .bool (fun _ => reason) mode reason = .ok code) :
    Tree 100 values source context [] (fun _ => reason) scope mode statements .bool .bool code := by
  apply tree_of_flow rfl ?_ (sourceSyntax mode) rfl accepted
  intro budget expression node lowered childSyntax found typed generated
  exact CompatibleExpressionTyped.tree_of_functions unique declarations rfl rfl rfl
    ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩ (fun _ _ _ found => (metadata found).2)
    childSyntax found typed generated

private def compiledResult (mode : Bool) := SourceCoreLoops.lowerFlowStatementsWithPolicy policy 12 source scope statements
  .bool (fun _ => reason) mode reason
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

private def sourceOutcome (_mode : Bool) : Dynamic.ControlOutcome := .returned (.bool true)
private theorem sourceTrace (mode : Bool) : Executes mode program context [] source sourceEnvironment before
    statements context (sourceOutcome mode) after := by
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
  have returned : Dynamic.ExpressionEvaluates program context [] source sourceEnvironment after (id 1) (.bool true) after :=
    .intro (lookupExpression?_sound (node := keyNode) rfl) (.builtinBoolean rfl) .nil
  have blockTrace : Dynamic.StatementExecutes program context [] source sourceEnvironment before (statement 1)
      context (.fallthrough sourceEnvironment) after :=
    .block (lookupStatement?_sound (node := scopedBlock) rfl) rfl
      (.cons (.expression (lookupStatement?_sound (node := discarded) rfl) rfl first) .nil)
  have ifTrace : Dynamic.StatementExecutes program context [] source sourceEnvironment after (statement 3)
      context (.fallthrough sourceEnvironment) after :=
    .ifFalseWithoutElse (lookupStatement?_sound (node := conditional) rfl) rfl second
  cases mode with
  | false => exact .control (.cons blockTrace (.cons ifTrace
      (.terminal (.returnValue (lookupStatement?_sound (node := finalReturn) rfl) rfl returned) (.returned _))))
  | true => exact .control (.cons blockTrace (.cons ifTrace
      (.singleton (lookupStatement?_sound (node := finalReturn) rfl)
        (by intro expression impossible; cases impossible) (.returnValue (lookupStatement?_sound (node := finalReturn) rfl) rfl returned))))

/-- Actual lowering supplies the entire flow proof in both list modes. -/
theorem accepted_preserves {mode : Bool} {code : Expr}
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy 12 source scope statements .bool (fun _ => reason) mode reason = .ok code) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (.integer 99 :: administrativeValue :: environment) store (code.rename ξ) value finalStore ∧
      FlowRep (values := values) (registry := values.registry) functions finalMap finalWorld faults .bool .bool (sourceOutcome mode) value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends [1] finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved [1] store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  exact (Tree.preserves (values := values) functions (.refl _) program [] contextValid unique uninitialized missing
    (certified accepted) initial.2 initial.1 locals agrees actualTyped (sourceTrace mode)).2

/-- Completed generated flow reconstructs the selected independent judgment. -/
theorem accepted_reflects {mode : Bool} {code : Expr}
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy 12 source scope statements .bool (fun _ => reason) mode reason = .ok code)
    {value : Value} {finalStore : Store}
    (completed : Evaluates (.integer 99 :: administrativeValue :: environment) store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Executes mode program context [] source sourceEnvironment before statements context outcome after ∧
      FlowRep (values := values) (registry := values.registry) functions finalMap finalWorld faults .bool .bool outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends [1] finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved [1] store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  exact Tree.reflects (values := values) functions (.refl _) program [] contextValid uninitialized missing
    (certified accepted) initial.2 initial.1 locals agrees actualTyped completed

private def rawWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Item { Item(Word) }",
    "function blocks() returns (Bool) { let m: mapping(Bool => Bool); { m[true]; } return !m[false]; }",
    "function absent() returns (Bool) { let m: mapping(Bool => Bool); if (m[true]) { return m[false]; } return !m[false]; }",
    "function nominal() returns (Item) { { } return Item(7); }",
    "function branch(m: mapping(Bool => Bool)) returns (Bool) { if (m[true]) { { m[false]; } if (!m[false]) { return m[true]; } else { return false; } } else { { m[true]; } return !m[false]; } }",
    "function elseFault() returns (Bool) { let m: mapping(Bool => Item); if (false) { return true; } else { { m[true]; } } return false; }",
    "function early() returns (Bool) { let m: mapping(Bool => Item); { return true; } m[true]; return false; }"]}] }

def run : IO Unit := do
  for mode in [false, true] do
    let generated ← SourceCompilerFeatureSupport.get "scoped typed lowering" (compiledResult mode)
    let state : Core.State := ⟨.eval (generated.rename ξ) (.integer 99 :: administrativeValue :: environment), [], store⟩
    let expected : Value := .inLeft LocalLoop.transferType (.inRight .unit (.bool true))
    let complete := Core.runStateful 30000 state
    match Core.LanguageResult.observeResult complete with
    | .succeeded value finalStore =>
        SourceCompilerFeatureSupport.require (value == expected) "recursive scoped control changed return value"
        SourceCompilerFeatureSupport.require (finalStore[0]? == some administrativeValue)
          "scoped index changed the ambient closure cell"
    | _ => throw (IO.userError "actual typed scoped lowering did not complete")
    for fuel in [0, 5, 23] do
      match Core.runStateful fuel state with
      | .outOfFuel suspended =>
          SourceCompilerFeatureSupport.require (Core.runStateful 30000 suspended == complete)
            "resuming the scoped flow changed value or store"
      | _ => throw (IO.userError "scoped flow unexpectedly completed at the suspension prefix")
  let checked ← SourceCompilerFeatureSupport.get "typed scoped checker" (checkProgram rawWorkspace)
  for name in ["blocks", "absent", "early"] do
    let compiled ← SourceCompilerFeatureSupport.compileNamed checked name
    SourceCompilerFeatureSupport.require ((← compiled.run []) == .bool true) "typed scoped branch changed result"
    compiled.checkResume [] (.bool true)
  let branch ← SourceCompilerFeatureSupport.compileNamed checked "branch"
  for input in ([.mapping .bool .bool [],
      .mapping .bool .bool [(.bool true, .bool true)]] : List SourceCoreExecution.Value) do
    SourceCompilerFeatureSupport.require ((← branch.run [input]) == .bool true)
      "nested selected branch changed index captures"
    branch.checkResume [input] (.bool true)
  let failed ← SourceCompilerFeatureSupport.compileNamed checked "elseFault"
  let invocation ← failed.invoke []
  match invocation.outcome with
  | .failed token _ =>
      match ← invocation.diagnostic token with
      | some {error := .typeMismatch _ none, span := some _, ..} => pure ()
      | _ => throw (IO.userError "nested else fault lost raw default diagnostic")
  | _ => throw (IO.userError "nested else missing default did not fail")
  let failedState := SourceCompilerFeatureSupport.sourceState (← failed.audit [])
  match failedState.heap with
  | [cell] =>
      match cell.value with
      | some (.mapping .bool _ []) => pure ()
      | _ => throw (IO.userError "nested else fault lost prior lazy initialization")
  | _ => throw (IO.userError "nested else fault changed source allocation order")
  let nominal ← SourceCompilerFeatureSupport.compileNamed checked "nominal"
  match ← nominal.run [] with
  | .constructed _ [.word value] =>
      SourceCompilerFeatureSupport.require (value == Word.ofNatModulo 7) "empty scoped block changed nominal payload"
  | _ => throw (IO.userError "empty scoped block changed nominal return type")
  IO.println "typed scoped control: block/index/absent-else/return, typed captures, nominal blocks and resume GREEN"
end Tests.SourceCoreTypedScopedControl
