import Solcore.SourceSemantics.CoreLowering.CompatibleStatementMeaning
import Solcore.Frontend.SourceCoreCallableIndexedFrames
import Solcore.Test.SourceCompilerFeatureSupport

#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Static production receipts plus full finite sequence proofs. An actual fresh
frame type remains in the ambient store; a discarded local read can fail before
a return. The checked-source integration cases separately audit lazy mapping
effects and early return through the cached public Core artifact. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
set_option linter.unusedSimpArgs false
namespace Tests.SourceCoreCompatibleStatements
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleStatements CompatiblePayload GeneralHeap ReadOnly

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"compatible_statements", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "statements.solc"⟩, 0, 1⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def statement (index : Nat) : StatementId := ⟨⟨owner, index⟩⟩
private def binder : TypedBinder := ⟨⟨owner, 9⟩, "input", .mono .bool, [], false, none⟩
private def localNode : ExpressionNode := { id := id 0, span, type := .bool, form := .reference "input" (.local binder.id) }
private def boolean : ExpressionNode := { id := id 1, span, type := .bool, form := .reference "false" (.builtinBoolean false) }
private def paired : ExpressionNode := { id := id 2, span, type := .product .bool .bool, form := .tuple [id 0, id 1] }
private def discardNode : StatementNode := ⟨statement 10, span, .unit, .expression (id 0) true⟩
private def returnNode : StatementNode := ⟨statement 11, span, .product .bool .bool, .returnStmt (some (id 2))⟩
private def unreachable : StatementNode := ⟨statement 12, span, .unit, .breakStmt⟩
private def tailNode : StatementNode := ⟨statement 13, span, .bool, .expression (id 1) false⟩
private def unitNode : StatementNode := ⟨statement 14, span, .unit, .returnStmt none⟩
private def statements := [statement 10, statement 11, statement 12]
private def source : TypedSource := {
  owner, inputs := [binder], roots := statements.map .statement,
  nodes := [.expression localNode, .expression boolean, .expression paired,
    .statement discardNode, .statement returnNode, .statement unreachable, .statement tailNode, .statement unitNode] }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def context : SourceSemantics.Context := (SourceSemantics.Context.ofSignatures signatures).withLocal binder.id binder.scheme
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def compilation : SourceCoreFunctions.Context := ⟨⟨[], [], [], []⟩, ⟨owner, []⟩, [], 0, [], Word.zero⟩
private def noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .ok .unit
private def reason : Word := Word.ofNatModulo 17
private def faults : FunctionCalls.FaultRep := fun fault token => (∃ location, fault = .uninitializedLocation location) ∧ token = reason
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem boolAdmitted : TypeAdmissible context .bool :=
  .bool ((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal binder.id binder.scheme)
private theorem localTyped : ExpressionHasType source context (id 0) .bool := by
  apply ExpressionHasType.ofOrdinary (node := localNode) (rawType := .bool) (lookupExpression?_sound (by rfl))
    (.reference (.local .head .head (.intro (.empty _ _ rfl) (SchemeWellFormed.monoAdmissible boolAdmitted) []
      .empty (by intro metavariable replacement member; cases member) (SchemeInstantiates.empty_apply _)
      (by simp) (by intro _ member; cases member) .nil))) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem boolTyped : ExpressionHasType source context (id 1) .bool := by
  apply ExpressionHasType.ofOrdinary (node := boolean) (rawType := .bool) (lookupExpression?_sound (by cbv))
    (.reference (.builtinBoolean false)) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem pairTyped : ExpressionHasType source context (id 2) (.product .bool .bool) := by
  apply ExpressionHasType.ofOrdinary (node := paired) (rawType := .product .bool .bool) (lookupExpression?_sound (by cbv))
    (.tuple (.cons localTyped (.cons boolTyped (.nil _)))) (.product boolAdmitted boolAdmitted) (.product boolAdmitted boolAdmitted)
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem localSyntax : CompatibleExpressionConstructors.Syntax source (id 0) :=
  .fragment (.primitive (.product (.read (node := localNode) (by rfl) rfl)))
private theorem boolSyntax : CompatibleExpressionConstructors.Syntax source (id 1) :=
  .fragment (.primitive (.product (.literal (node := boolean) (by cbv) (.bool _ _))))
private theorem pairSyntax : CompatibleExpressionConstructors.Syntax source (id 2) :=
  .fragment (.primitive (.product (.pair (node := paired) (by cbv) rfl
    (.read (node := localNode) (by rfl) rfl) (.literal (node := boolean) (by cbv) (.bool _ _)))))
private theorem sourceSyntax : CompatibleStatements.Syntax source context statements (.product .bool .bool) :=
  .discard (node := discardNode) (expressionNode := localNode) (by cbv) rfl rfl rfl (by rfl) localTyped localSyntax
    (.returnValue (node := returnNode) (expressionNode := paired) [statement 12] (by cbv) rfl rfl (by cbv) rfl pairTyped pairSyntax)
private theorem metadata {expression : ExpressionId} {node : ExpressionNode} (found : source.lookupExpression? expression = some node) :
    node.requirements = CompatibleExpressionLiterals.owned node.form ∧ node.coercions = [] := by
  have member := (lookupExpression?_sound found).1
  simp [source] at member
  rcases member with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
private theorem valid : CompatibleExpressionLiterals.ContextValid [] context [] := by
  refine ⟨rfl, ⟨?_, ?_⟩, ?_⟩
  · simp [RequirementIdsUnique, context, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal]
  · intro requirement member; simp [context, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal] at member
  · constructor
    · intro goal evidence found; cases found
    · intro predicate member; simp [context, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal] at member
private theorem checkExists : (SourceCoreCompatibleCatalog.prepare signatures 10 [.product .bool .bool]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 10 [.product .bool .bool]).toOption.get checkExists
private def values := SourceCoreCompatibleValues.Context.initial checked
private def scope : SourceCoreLocalCell.Scope := [(binder.id, .bool)]
private def expressionPolicy := SourceCoreCompatibleDataExpressions.functionPolicy 20 values
private def policy : SourceCoreLoops.Policy := {
  lowerExpression := fun fuel source scope expression reasonAt =>
    SourceCoreFunctions.lowerExpressionWithPolicy expressionPolicy noBody fuel compilation source scope expression reasonAt
  readStatement := SourceCoreCompatibleDataExpressions.readStatement checked }
private theorem declarations : CompatibleExpressionReads.ScopeDeclarations source scope context := by
  intro localId declared index native selected accepted
  simp only [scope, SourceCoreLocalCell.lookup?] at selected
  split at selected
  · rename_i same
    subst localId
    have actual : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder := by rfl
    rw [actual] at accepted; cases accepted
    exact .head
  · simp at selected
private theorem certify {ids : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (syntaxTree : CompatibleStatements.Syntax source context ids expected)
    (projection : checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy 20 source scope ids type (fun _ => reason) reason reason = .ok code) :
    ∃ flow, code = finish type flow reason reason ∧ Tree 20 values source context [] (fun _ => reason) scope ids expected type flow := by
  apply tree_of_body rfl ?_ syntaxTree projection accepted
  intro budget expression node lowered childSyntax found typed generated
  exact CompatibleExpressionConstructors.tree_of_functions unique declarations rfl rfl
    ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩ (fun _ _ _ found => (metadata found).2)
    childSyntax found typed generated
private def readCode := OptionalCell.read .bool (.var 0) reason
private def pairCode := LocalSequence.pair .bool .bool readCode (LanguageResult.success (.bool false))
private def flow := LocalSequence.discard (LocalLoop.controlType (.product .bool .bool)) readCode
  (LocalLoop.returnValue (.product .bool .bool) pairCode)
private def code := finish (.product .bool .bool) flow reason reason
private theorem localAccepted (fuel : Nat) :
    policy.lowerExpression (fuel + 1) source scope (id 0) (fun _ => reason) = .ok ⟨.bool, readCode⟩ := by
  change SourceCoreFunctions.lowerExpressionWithPolicy expressionPolicy noBody (fuel + 1) compilation source scope (id 0) (fun _ => reason) = _
  rw [SourceCoreFunctions.lowerExpressionWithPolicy]
  rfl
private theorem boolAccepted (fuel : Nat) :
    policy.lowerExpression (fuel + 1) source scope (id 1) (fun _ => reason) = .ok ⟨.bool, LanguageResult.success (.bool false)⟩ := by
  change SourceCoreFunctions.lowerExpressionWithPolicy expressionPolicy noBody (fuel + 1) compilation source scope (id 1) (fun _ => reason) = _
  rw [SourceCoreFunctions.lowerExpressionWithPolicy]
  rfl
private theorem pairAccepted (fuel : Nat) :
    policy.lowerExpression (fuel + 2) source scope (id 2) (fun _ => reason) = .ok ⟨.product .bool .bool, pairCode⟩ := by
  change SourceCoreFunctions.lowerExpressionWithPolicy expressionPolicy noBody (fuel + 2) compilation source scope (id 2) (fun _ => reason) = _
  rw [SourceCoreFunctions.lowerExpressionWithPolicy]
  have ownerEq : (id 2).occurrence.owner = source.owner := rfl
  have found : source.lookupExpression? (id 2) = some paired := rfl
  have read : SourceCoreCompatibleDataExpressions.readExpression values.checked source (id 2) = .ok (paired, .product .bool .bool) := rfl
  simp only [expressionPolicy, SourceCoreCompatibleDataExpressions.functionPolicy, ownerEq, ne_eq, not_true_eq_false,
    ↓reduceIte, found, bind, Except.bind, pure, Except.pure, paired]
  rw [read]
  simp only [bind, Except.bind, paired]
  have first := localAccepted fuel
  have second := boolAccepted fuel
  simp only [policy, expressionPolicy, SourceCoreCompatibleDataExpressions.functionPolicy, pure, Except.pure] at first second
  rw [first]
  simp only [bind, Except.bind]
  rw [second]
  rfl
private theorem accepted : SourceCoreLoops.lowerStatementsWithPolicy policy 20 source scope statements
    (.product .bool .bool) (fun _ => reason) reason reason = .ok code := by
  have readDiscard : policy.readStatement source (statement 10) = .ok (discardNode, .unit) := rfl
  have readReturn : policy.readStatement source (statement 11) = .ok (returnNode, .product .bool .bool) := rfl
  simp only [SourceCoreLoops.lowerStatementsWithPolicy, statements, SourceCoreLoops.lowerFlowStatementsWithPolicy,
    readDiscard, readReturn, bind, Except.bind, pure, Except.pure, discardNode, returnNode]
  rw [localAccepted 18]
  simp only [bind, Except.bind, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  have ensureUnit : SourceCoreBasic.ensureType (.occurrence (statement 10).occurrence) .unit .unit = .ok () := rfl
  have ensurePair : SourceCoreBasic.ensureType (.occurrence (statement 11).occurrence) (.product .bool .bool) (.product .bool .bool) = .ok () := rfl
  rw [ensureUnit]
  simp only [bind, Except.bind]
  rw [ensurePair]
  simp only [bind, Except.bind]
  rw [pairAccepted 16]
  simp only [bind, Except.bind, ensurePair, pure, Except.pure]
  rfl
private theorem certified : Tree 20 values source context [] (fun _ => reason) scope statements (.product .bool .bool) (.product .bool .bool) flow := by
  obtain ⟨generatedFlow, same, tree⟩ := certify sourceSyntax rfl accepted
  have flowSame : generatedFlow = flow := by
    have structural := same
    simp only [code, finish, LocalControl.finish, LocalLoop.toControl, LanguageResult.bind, Expr.caseE.injEq] at structural
    exact structural.1.1.symm
  exact flowSame ▸ tree

/-- The whole source sequence is reconstructed from completed native code.
The actual compiler receipt supplied every child tree; no source execution or
universal body/child meaning is assumed. -/
theorem compiled_reflects {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    {mapping world administrative environment canonical actual before store ξ value finalStore}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents checked values.registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (completed : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.FunctionStatementsExecuteOutcome program context [] source environment before statements context outcome after ∧
      BodyRep (values := values) (registry := values.registry) functions finalMap finalWorld faults
        (.product .bool .bool) (.product .bool .bool) outcome value ∧
      CompatibleAmbientHeap.HeapRepresents checked values.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  Tree.body_reflects (values := values) (ambient := ambient) functions (.refl _) program [] valid (fun _ location => ⟨⟨location, rfl⟩, rfl⟩)
    certified reason reason environments heaps locals agrees completed

private def frameLayout : SourceCoreCallableIndexedFrames.Layout := ⟨⟨checked.catalog.definitions.length⟩⟩
private def ambient : AmbientDefinitions checked.catalog.definitions := .append _ [frameLayout.definition]
private def functions : FunctionModel checked.catalog ambient where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := by intros; contradiction
  runtime_hasType := by intros; contradiction
  source_function := by intros; contradiction
  extend := by intros; contradiction
private def model := CompatibleAmbientHeap.payloadModel checked values.registry functions
private def administrativeType : Ty := .function .unit frameLayout.type
private def administrativeValue : Value := .closure .unit frameLayout.type (.var 1) [SourceCoreCallableIndexedFrames.encode frameLayout .empty]
private theorem frameRegistered : frameLayout.Registered ambient.definitions := by
  constructor
  simp [ambient, AmbientDefinitions.append, frameLayout]
private theorem administrativeTyped : RuntimeValueHasType [] administrativeValue administrativeType ambient.definitions :=
  .closure (.cons (SourceCoreCallableIndexedFrames.encode_runtime_typed [] frameRegistered .empty) .nil) (.var rfl)
private theorem initialHeap : GenericHeap.HeapRepresents model [] [administrativeType] ⟨[]⟩ [administrativeValue] :=
  GenericHeap.HeapRepresents.empty.allocate_administrative administrativeTyped
private def boolHeap (value : Option Dynamic.Value) : Dynamic.Heap := ⟨[⟨.bool, value, none⟩]⟩
private def world : StoreTyping := [administrativeType, OptionalCell.cellType .bool]
private def environment : Environment := [.cellRef (OptionalCell.cellType .bool) 1]
private def sourceEnvironment : Dynamic.Environment := [(binder.id, ⟨0⟩)]
private theorem locals (value : Option Dynamic.Value) : Dynamic.EnvironmentAgrees (boolHeap value) context.locals sourceEnvironment :=
  .cons (.intro .head) rfl (.ordinary rfl rfl) .nil
private theorem visible {sourceValue : Option Dynamic.Value} {native : Value}
    (cell : GenericHeap.CellRepresents model [] [administrativeType] ⟨.bool, sourceValue, none⟩ native .bool) :
    GenericHeap.HeapRepresents model [1] world (boolHeap sourceValue) [administrativeValue, native] ∧
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) [1] world [] scope sourceEnvironment environment ambient.definitions := by
  obtain ⟨heap, reference⟩ := initialHeap.allocate cell Dynamic.Heap.Allocates.append
  exact ⟨heap, .cons reference (.nil .nil)⟩

/-- A failure in the discarded first expression bypasses the pair and return,
keeps the source cell absent, and preserves the fresh ambient closure. -/
theorem discarded_failure_reflects : ∃ outcome after finalMap finalWorld,
    Dynamic.FunctionStatementsExecuteOutcome program context [] source sourceEnvironment (boolHeap none) statements context outcome after ∧
    BodyRep (values := values) (registry := values.registry) functions finalMap finalWorld faults
      (.product .bool .bool) (.product .bool .bool) outcome (.inLeft (.product .bool .bool) (.word reason)) ∧
    CompatibleAmbientHeap.HeapRepresents checked values.registry functions finalMap finalWorld after [administrativeValue, .inLeft .bool .unit] ∧
    LocationMap.Extends [1] finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved [1] [administrativeValue, .inLeft .bool .unit] finalMap [administrativeValue, .inLeft .bool .unit] ∧
    Dynamic.HeapMetadataExtend (boolHeap none) after := by
  obtain ⟨heaps, environments⟩ := visible (.uninitialized (show checked.catalog.project .bool = .ok .bool by rfl))
  have child : Evaluates environment [administrativeValue, .inLeft .bool .unit] readCode
      (.inLeft .bool (.word reason)) [administrativeValue, .inLeft .bool .unit] :=
    OptionalCell.read_failure reason (.var rfl) rfl
  have completed : Evaluates environment [administrativeValue, .inLeft .bool .unit] code
      (.inLeft (.product .bool .bool) (.word reason)) [administrativeValue, .inLeft .bool .unit] :=
    LocalControl.finish_failure _ (LocalLoop.toControl_failure _ reason (LocalSequence.discard_failure _ child))
  exact compiled_reflects functions environments heaps (locals none) (ξ := Renaming.id) (fun {_ _} found => found)
    (by simpa only [Expr.rename_id] using completed)

/-- Independent source execution supplies the forward direction, including the
same local read under both the discarded-payload and pair-payload slots. -/
theorem initialized_preserves : ∃ value finalStore finalMap finalWorld,
    Evaluates environment [administrativeValue, .inRight .unit (.bool true)] code value finalStore ∧
    BodyRep (values := values) (registry := values.registry) functions finalMap finalWorld faults
      (.product .bool .bool) (.product .bool .bool) (.returned (.product (.bool true) (.bool false))) value ∧
    CompatibleAmbientHeap.HeapRepresents checked values.registry functions finalMap finalWorld (boolHeap (some (.bool true))) finalStore ∧
    LocationMap.Extends [1] finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved [1] [administrativeValue, .inRight .unit (.bool true)] finalMap finalStore ∧
    Dynamic.HeapMetadataExtend (boolHeap (some (.bool true))) (boolHeap (some (.bool true))) := by
  obtain ⟨heaps, environments⟩ := visible (.initialized (.bool true))
  have localEvaluation : Dynamic.ExpressionEvaluates program context [] source sourceEnvironment (boolHeap (some (.bool true))) (id 0)
      (.bool true) (boolHeap (some (.bool true))) :=
    .intro (lookupExpression?_sound (show source.lookupExpression? (id 0) = some localNode by rfl))
      (.local rfl .head (.intro .head) rfl rfl) .nil
  have booleanEvaluation : Dynamic.ExpressionEvaluates program context [] source sourceEnvironment (boolHeap (some (.bool true))) (id 1)
      (.bool false) (boolHeap (some (.bool true))) :=
    .intro (lookupExpression?_sound (show source.lookupExpression? (id 1) = some boolean by cbv)) (.builtinBoolean rfl) .nil
  have pairEvaluation : Dynamic.ExpressionEvaluates program context [] source sourceEnvironment (boolHeap (some (.bool true))) (id 2)
      (.product (.bool true) (.bool false)) (boolHeap (some (.bool true))) :=
    .intro (lookupExpression?_sound (show source.lookupExpression? (id 2) = some paired by cbv))
      (.tuple rfl (.cons localEvaluation (.cons booleanEvaluation .nil)) (.cons (.singleton _))) .nil
  have sourceTrace : Dynamic.FunctionStatementsExecuteOutcome program context [] source sourceEnvironment
      (boolHeap (some (.bool true))) statements context (.returned (.product (.bool true) (.bool false))) (boolHeap (some (.bool true))) :=
    .control (.cons (.expression (lookupStatement?_sound (show source.lookupStatement? (statement 10) = some discardNode by cbv)) rfl localEvaluation)
      (.terminal (.returnValue (lookupStatement?_sound (show source.lookupStatement? (statement 11) = some returnNode by cbv)) rfl pairEvaluation) (.returned _)))
  have result := Tree.body_preserves (values := values) (ambient := ambient) functions (.refl _) program [] valid unique
    (faults := faults) (fun _ location => ⟨⟨location, rfl⟩, rfl⟩) certified reason reason
    environments heaps (locals _) (ξ := Renaming.id) (show EnvironmentsAgree Renaming.id environment environment from fun {_ _} found => found) sourceTrace
  simpa only [Expr.rename_id, code, values, SourceCoreCompatibleValues.Context.initial] using result.2

/-- Empty and explicit Unit exits and a semicolon-free tail use the very same
production traversal certificate factory. -/
theorem unit_and_tail_certificates :
    (∃ flow, Tree 20 values source context [] (fun _ => reason) scope [] .unit .unit flow) ∧
    (∃ flow, Tree 20 values source context [] (fun _ => reason) scope [statement 14, statement 12] .unit .unit flow) ∧
    (∃ flow, Tree 20 values source context [] (fun _ => reason) scope [statement 13] .bool .bool flow) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨flow, _, tree⟩ := certify .nil rfl (show SourceCoreLoops.lowerStatementsWithPolicy policy 20 source scope [] .unit (fun _ => reason) reason reason = .ok (finish .unit (LocalLoop.fallthrough .unit) reason reason) by rfl)
    exact ⟨flow, tree⟩
  · obtain ⟨flow, _, tree⟩ := certify (.returnUnit (node := unitNode) [statement 12] (by cbv) rfl rfl) rfl
      (show SourceCoreLoops.lowerStatementsWithPolicy policy 20 source scope [statement 14, statement 12] .unit (fun _ => reason) reason reason = .ok (finish .unit (LocalLoop.returned .unit) reason reason) by rfl)
    exact ⟨flow, tree⟩
  · obtain ⟨flow, _, tree⟩ := certify (.tail (node := tailNode) (expressionNode := boolean) (by cbv) rfl rfl (by cbv) rfl boolTyped boolSyntax) rfl
      (show SourceCoreLoops.lowerStatementsWithPolicy policy 20 source scope [statement 13] .bool (fun _ => reason) reason reason = .ok (finish .bool (LocalLoop.returnValue .bool (LanguageResult.success (.bool false))) reason reason) by
        have read : policy.readStatement source (statement 13) = .ok (tailNode, .bool) := rfl
        simp only [SourceCoreLoops.lowerStatementsWithPolicy, SourceCoreLoops.lowerFlowStatementsWithPolicy,
          read, bind, Except.bind, pure, Except.pure, tailNode]
        rw [boolAccepted 18]
        rfl)
    exact ⟨flow, tree⟩

private def rawWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box { Box(Word) }",
    "function success() returns (Bool, Bool) { true; return (false, true); }",
    "function lazy() returns (Bool) { let m: mapping(Word => Word); m; return true; }",
    "function stopped() returns (Bool) { let missing: Bool; let m: mapping(Word => Word); missing; m; return true; }",
    "function early() returns (Bool) { let missing: Bool; return true; missing; }",
    "function tail() returns (Bool, Bool) { true; (true, false) }",
    "function boxed() returns (Box) { true; return .Box(7); }",
    "function unit() { true; return; }"]}] }

def run : IO Unit := do
  let checked ← SourceCompilerFeatureSupport.get "statement checker" (checkProgram rawWorkspace)
  let success ← SourceCompilerFeatureSupport.compileNamed checked "success"
  SourceCompilerFeatureSupport.require ((← success.run []) == .product (.bool false) (.bool true)) "discard/return pair changed"
  success.checkResume [] (.product (.bool false) (.bool true))
  let lazyEntry ← SourceCompilerFeatureSupport.compileNamed checked "lazy"
  SourceCompilerFeatureSupport.require ((← lazyEntry.run []) == .bool true) "lazy read return changed"
  lazyEntry.checkCells [] [(.mapping .word .word, some (.mapping .word .word []))]
  let stopped ← SourceCompilerFeatureSupport.compileNamed checked "stopped"
  let invocation ← stopped.invoke []
  match invocation.outcome with
  | .failed token _ =>
    let diagnostic ← invocation.diagnostic token
    SourceCompilerFeatureSupport.require (diagnostic.isSome) "discarded failure diagnostic missing"
  | _ => throw (IO.userError "discarded absent read did not stop")
  stopped.checkCells [] [(.bool, none), (.mapping .word .word, none)]
  let early ← SourceCompilerFeatureSupport.compileNamed checked "early"
  SourceCompilerFeatureSupport.require ((← early.run []) == .bool true) "unreachable read ran"
  early.checkCells [] [(.bool, none)]
  let tail ← SourceCompilerFeatureSupport.compileNamed checked "tail"
  SourceCompilerFeatureSupport.require ((← tail.run []) == .product (.bool true) (.bool false)) "tail pair changed"
  let dataEntry ← SourceCompilerFeatureSupport.compileNamed checked "boxed"
  match ← dataEntry.run [] with
  | .constructed _ [.word value] => SourceCompilerFeatureSupport.require (value == Word.ofNatModulo 7) "returned constructor payload changed"
  | _ => throw (IO.userError "returned constructor shape changed")
  let unitEntry ← SourceCompilerFeatureSupport.compileNamed checked "unit"
  SourceCompilerFeatureSupport.require ((← unitEntry.run []) == .unit) "explicit Unit return changed"
  IO.println "compatible statements: compiler certificates, full preservation/reflection, discard fault, lazy effects, early return, tail data and resume GREEN"
end Tests.SourceCoreCompatibleStatements
