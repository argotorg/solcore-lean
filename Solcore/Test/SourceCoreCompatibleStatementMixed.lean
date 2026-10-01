import Solcore.SourceSemantics.CoreLowering.CompatibleStatementMixedMeaning
import Solcore.Test.SourceCompilerFeatureSupport

#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! A mixed prefix reaches three source allocations, then fails in its fourth
initializer. Static receipts and independent semantics agree on the exact
intermediate lexical context; real cached calls exercise longer prefixes. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCompatibleStatementMixed
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleStatementMixed CompatiblePayload GeneralHeap ReadOnly CallableIndexedHistory
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"mixed_binding", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "mixed.solc"⟩, 0, 1⟩
private def expression (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def statement (index : Nat) : StatementId := ⟨⟨owner, index + 10⟩⟩
private def binder (index : Nat) : TypedBinder := ⟨⟨owner, index⟩, "value", .mono .bool, [], false, none⟩
private def inputNode : ExpressionNode := {id := expression 0, span, type := .bool, form := .reference "input" (.local (binder 0).id)}
private def missingNode : ExpressionNode := {id := expression 1, span, type := .bool, form := .reference "missing" (.local (binder 2).id)}
private def first : StatementNode := ⟨statement 0, span, .unit, .letDecl (binder 1) (some (expression 0))⟩
private def second : StatementNode := ⟨statement 1, span, .unit, .letDecl (binder 2) none⟩
private def third : StatementNode := ⟨statement 2, span, .unit, .letDecl (binder 3) (some (expression 0))⟩
private def fourth : StatementNode := ⟨statement 3, span, .unit, .letDecl (binder 4) (some (expression 1))⟩
private def returned : StatementNode := ⟨statement 4, span, .unit, .returnStmt none⟩
private def statements := [statement 0, statement 1, statement 2, statement 3, statement 4]
private def source : TypedSource := {
  owner, inputs := [binder 0], roots := statements.map .statement,
  nodes := [.expression inputNode, .expression missingNode, .statement first, .statement second,
    .statement third, .statement fourth, .statement returned] }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def initial : SourceSemantics.Context := (SourceSemantics.Context.ofSignatures signatures).withLocal (binder 0).id (binder 0).scheme
private def context1 := initial.withLocal (binder 1).id (binder 1).scheme
private def context2 := context1.withLocal (binder 2).id (binder 2).scheme
private def context3 := context2.withLocal (binder 3).id (binder 3).scheme
private def context4 := context3.withLocal (binder 4).id (binder 4).scheme
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def scope : SourceCoreLocalCell.Scope := [((binder 0).id, .bool)]
private def reason := Word.ofNatModulo 37
private theorem extend {context : SourceSemantics.Context} (index : Nat)
    (binders : TypeParameterBindersWellFormed context) (fresh : LocalFresh context (binder index).id) :
    BinderExtends owner context (binder index) (context.withLocal (binder index).id (binder index).scheme) := by
  apply BinderExtends.intro
  · exact {
      owned := rfl
      scheme := {binders, quantified_nodup := by simp [binder, TypeSystem.Scheme.mono], body := .builtin .bool}
      quantified_fresh := by simp [SchemeQuantifiersFresh, binder, TypeSystem.Scheme.mono]
      monomorphic_requirements_empty := by intro; rfl }
  · exact fresh
private theorem extension1 : BinderExtends owner initial (binder 1) context1 := by
  apply extend 1
  · simp [TypeParameterBindersWellFormed, initial, SourceSemantics.Context.ofSignatures,
      SourceSemantics.Context.withLocal, signatures]
  · simp [LocalFresh, initial, SourceSemantics.Context.ofSignatures,
      SourceSemantics.Context.withLocal, binder]
private theorem extension2 : BinderExtends owner context1 (binder 2) context2 := by
  apply extend 2
  · simp [TypeParameterBindersWellFormed, context1, initial, SourceSemantics.Context.ofSignatures,
      SourceSemantics.Context.withLocal, signatures]
  · simp [LocalFresh, context1, initial, SourceSemantics.Context.ofSignatures,
      SourceSemantics.Context.withLocal, binder]
private theorem extension3 : BinderExtends owner context2 (binder 3) context3 := by
  apply extend 3
  · simp [TypeParameterBindersWellFormed, context1, context2, initial, SourceSemantics.Context.ofSignatures,
      SourceSemantics.Context.withLocal, signatures]
  · simp [LocalFresh, context1, context2, initial, SourceSemantics.Context.ofSignatures,
      SourceSemantics.Context.withLocal, binder]
private theorem extension4 : BinderExtends owner context3 (binder 4) context4 := by
  apply extend 4
  · simp [TypeParameterBindersWellFormed, context1, context2, context3, initial, SourceSemantics.Context.ofSignatures,
      SourceSemantics.Context.withLocal, signatures]
  · simp [LocalFresh, context1, context2, context3, initial, SourceSemantics.Context.ofSignatures,
      SourceSemantics.Context.withLocal, binder]
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem localTyped {context : SourceSemantics.Context} {node : ExpressionNode} {index : Nat}
    (found : source.lookupExpression? node.id = some node)
    (form : node.form = .reference "input" (.local (binder index).id) ∨ node.form = .reference "missing" (.local (binder index).id))
    (type : node.type = .bool) (requirements : node.requirements = []) (coercions : node.coercions = [])
    (binders : TypeParameterBindersWellFormed context)
    (lookup : Resolved.LocalScope.Lookup context.locals (binder index).id (binder index).scheme)
    (schemes : context.LocalSchemeRequirementsLookup (binder index).id []) :
    ExpressionHasType source context node.id node.type := by
  have admitted : TypeAdmissible context .bool := .bool binders
  rcases form with form | form
  all_goals
    apply ExpressionHasType.ofOrdinary (rawType := .bool) (owned := []) (lookupExpression?_sound found)
    · rw [form]
      exact .reference (.local lookup schemes (.intro (.empty _ _ rfl) (SchemeWellFormed.monoAdmissible admitted) []
        .empty (by intro metavariable replacement member; cases member) (SchemeInstantiates.empty_apply _)
        (by simp) (by intro _ member; cases member) .nil))
    · exact admitted
    · exact type ▸ admitted
    · intro requirement member; cases member
    · rw [coercions, type]; exact .nil _
    · simp [requirements, coercions, coercionRequirementIds]
private theorem inputInitial : ExpressionHasType source initial (expression 0) .bool := by
  apply localTyped (node := inputNode) (index := 0) rfl (.inl rfl) rfl rfl rfl
  · exact (TypeParameterBindersWellFormed.ofSignatures signatures).withLocal _ _
  · exact .head
  · exact .head
private theorem inputSecond : ExpressionHasType source context2 (expression 0) .bool := by
  apply localTyped (node := inputNode) (index := 0) rfl (.inl rfl) rfl rfl rfl
  · exact (((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal _ _).withLocal _ _).withLocal _ _
  · exact .tail (by decide) (.tail (by decide) .head)
  · exact .tail (by decide) (.tail (by decide) .head)
private theorem missingThird : ExpressionHasType source context3 (expression 1) .bool := by
  apply localTyped (node := missingNode) (index := 2) rfl (.inr rfl) rfl rfl rfl
  · exact ((((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal _ _).withLocal _ _).withLocal _ _).withLocal _ _
  · exact .tail (by decide) .head
  · exact .tail (by decide) .head
private theorem inputSyntax : CompatibleExpressionConstructors.Syntax source (expression 0) :=
  .fragment (.primitive (.product (.read (node := inputNode) rfl rfl)))
private theorem missingSyntax : CompatibleExpressionConstructors.Syntax source (expression 1) :=
  .fragment (.primitive (.product (.read (node := missingNode) rfl rfl)))
private theorem syntaxTree : Syntax source initial statements .unit :=
  .initialized (node := first) (initializerNode := inputNode) rfl rfl rfl rfl extension1 (by decide)
    rfl rfl inputInitial inputSyntax
    (.uninitialized (node := second) rfl rfl rfl rfl extension2 (by decide)
      (.initialized (node := third) (initializerNode := inputNode) rfl rfl rfl rfl extension3 (by decide)
        rfl rfl inputSecond inputSyntax
        (.initialized (node := fourth) (initializerNode := missingNode) rfl rfl rfl rfl extension4 (by decide)
          rfl rfl missingThird missingSyntax (.body (.returnUnit (node := returned) [] rfl rfl rfl)))))
private theorem valid : CompatibleExpressionLiterals.ContextValid [] initial [] := by
  refine ⟨rfl, ⟨?_, ?_⟩, ?_⟩
  · simp [RequirementIdsUnique, initial, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal]
  · intro requirement member
    simp [initial, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal] at member
  · constructor
    · intro goal evidence found; cases found
    · intro predicate member
      simp [initial, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal] at member
private theorem prepared : (SourceCoreCompatibleCatalog.prepare signatures 10 [.bool, .unit]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 10 [.bool, .unit]).toOption.get prepared
private def values := SourceCoreCompatibleValues.Context.initial checked
private def compilation : SourceCoreFunctions.Context := ⟨⟨[], [], [], []⟩, ⟨owner, []⟩, [], 0, [], Word.zero⟩
private def noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .ok .unit
private def expressionPolicy := SourceCoreCompatibleDataExpressions.functionPolicy 10 values
private def onError (_ : SourceCoreAllocationLayouts.Error) : SourceCoreBasic.Error := .traversalExhausted (.declaration owner)
private def policy (layouts : SourceCoreAllocationLayouts.Prepared) (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat) : SourceCoreLoops.Policy := {
  lowerExpression := fun fuel source scope id reasonAt =>
    SourceCoreFunctions.lowerExpressionWithPolicy expressionPolicy noBody fuel compilation source scope id reasonAt
  readStatement := SourceCoreCompatibleDataExpressions.readStatement checked
  lowerBinder := SourceCoreCompatibleDataExpressions.lowerBinder checked
  sourceCells := some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt ⟨owner, []⟩ [] onError)) }
private theorem declarations : CompatibleExpressionReads.ScopeDeclarations source scope initial := by
  intro id declared index type selected authentic
  simp only [scope, SourceCoreLocalCell.lookup?] at selected
  split at selected
  · rename_i same
    subst id
    have found : SourceCoreDataPlaces.rootBinder source (binder 0).id = .ok (binder 0) := rfl
    rw [found] at authentic; cases authentic
    exact .head
  · simp at selected
private theorem metadata {id : ExpressionId} {node : ExpressionNode} (found : source.lookupExpression? id = some node) :
    node.coercions = [] := by
  have member := (lookupExpression?_sound found).1
  simp [source] at member
  rcases member with rfl | rfl <;> rfl

private theorem certified {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals fuel : Nat} {code : Expr}
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy (policy layouts frame globals) fuel source scope
      statements .unit (fun _ => reason) reason reason = .ok code) :
    ∃ flow, code = CompatibleStatements.finish .unit flow reason reason ∧
      Tree layouts ⟨owner, []⟩ [] frame globals onError 10 values source [] (fun _ => reason)
        initial scope statements .unit .unit flow := by
  apply tree_of_body rfl (fun _ _ _ => rfl) rfl ?_ syntaxTree rfl rfl declarations rfl accepted
  intro current closed residual currentScope budget id node lowered declared childSyntax found typed generated
  exact CompatibleExpressionConstructors.tree_of_functions unique declared closed residual
    ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩ (fun _ _ _ found => metadata found)
    childSyntax found typed generated

private def sourceEnvironment : Dynamic.Environment := [((binder 0).id, ⟨0⟩)]
private def environment1 : Dynamic.Environment := ((binder 1).id, ⟨1⟩) :: sourceEnvironment
private def environment2 : Dynamic.Environment := ((binder 2).id, ⟨2⟩) :: environment1
private def environment3 : Dynamic.Environment := ((binder 3).id, ⟨3⟩) :: environment2
private def sourceHeap : Dynamic.Heap := ⟨[⟨.bool, some (.bool true), none⟩]⟩
private def heap1 : Dynamic.Heap := ⟨sourceHeap.cells ++ [⟨.bool, some (.bool true), none⟩]⟩
private def heap2 : Dynamic.Heap := ⟨heap1.cells ++ [⟨.bool, none, none⟩]⟩
private def heap3 : Dynamic.Heap := ⟨heap2.cells ++ [⟨.bool, some (.bool true), none⟩]⟩
private theorem sourceFailure : Dynamic.FunctionStatementsExecuteOutcome program initial [] source sourceEnvironment sourceHeap
    statements context3 (.fault (.uninitializedLocation ⟨2⟩)) heap3 := by
  apply Dynamic.FunctionStatementsExecuteOutcome.fault
  apply Dynamic.FunctionStatementsFault.tail
    (Dynamic.StatementExecutes.letInitialized (node := first) (lookupStatement?_sound rfl) rfl
      (.intro (node := inputNode) (lookupExpression?_sound rfl) (.local rfl .head (.intro .head) rfl rfl) .nil)
      rfl extension1 .append)
  apply Dynamic.FunctionStatementsFault.tail
    (Dynamic.StatementExecutes.letUninitialized (node := second) (lookupStatement?_sound rfl) rfl rfl extension2 .append)
  apply Dynamic.FunctionStatementsFault.tail
    (Dynamic.StatementExecutes.letInitialized (node := third) (lookupStatement?_sound rfl) rfl
      (.intro (node := inputNode) (environment := environment2) (before := heap2) (lookupExpression?_sound rfl)
        (.local rfl (.tail (by decide) (.tail (by decide) .head)) (.intro .head) rfl rfl) .nil)
      rfl extension3 .append)
  apply Dynamic.FunctionStatementsFault.head
  apply Dynamic.StatementFaults.letInitializer (node := fourth) (lookupStatement?_sound rfl) rfl rfl
  apply Dynamic.ExpressionFaults.form (node := missingNode) (lookupExpression?_sound rfl)
  exact .localUninitialized (owned := []) (coercions := []) (cell := ⟨.bool, none, none⟩)
    rfl (.tail (by decide) .head) (.intro (.tail (.tail .head))) rfl rfl
      (by rintro ⟨key, value, impossible⟩; cases impossible)

private theorem failureContext_ne_full : context3 ≠ context4 := by
  intro same
  have impossible : 4 = 5 := congrArg (fun context => context.locals.length) same
  omega

/-- Three successful bindings precede the fault. Reflection recovers that
intermediate context and represented lexical environment from actual code. -/
theorem compiled_reflects {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals fuel : Nat} {code : Expr} {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy (policy layouts frame globals) fuel source scope
      statements .unit (fun _ => reason) reason reason = .ok code)
    {mapping world administrative actualContext canonical actual heap store ξ contextLocation native value finalStore}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world administrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents checked values.registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap initial.locals sourceEnvironment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (completed : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ resultContext outcome after finalMap finalWorld,
      Dynamic.FunctionStatementsExecuteOutcome program initial [] source sourceEnvironment heap
        statements resultContext outcome after ∧
      CompatibleStatements.BodyRep (values := values) (registry := values.registry) functions finalMap finalWorld
        (fun _ token => token = reason) .unit .unit outcome value ∧
      CompatibleAmbientHeap.HeapRepresents checked values.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      LexicalResult checked ambient.definitions finalMap finalWorld administrative source.owner
        initial scope sourceEnvironment resultContext after := by
  obtain ⟨flow, rfl, tree⟩ := certified accepted
  exact Tree.body_reflects (values := values) (ambient := ambient) (faults := fun _ token => token = reason)
    functions definitions registered (.refl _) program [] (fun _ _ => rfl)
    tree valid reason reason environments heaps locals agrees typed reference read unmapped completed

theorem compiled_failure_preserves {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals fuel : Nat} {code : Expr} {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy (policy layouts frame globals) fuel source scope
      statements .unit (fun _ => reason) reason reason = .ok code)
    {mapping world administrative actualContext canonical actual store ξ contextLocation native}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world administrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents checked values.registry functions mapping world sourceHeap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      CompatibleStatements.BodyRep (values := values) (registry := values.registry) functions finalMap finalWorld
        (fun _ token => token = reason) .unit .unit (.fault (.uninitializedLocation ⟨2⟩)) value ∧
      CompatibleAmbientHeap.HeapRepresents checked values.registry functions finalMap finalWorld heap3 finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend sourceHeap heap3 ∧
      LexicalResult checked ambient.definitions finalMap finalWorld administrative source.owner
        initial scope sourceEnvironment context3 heap3 := by
  obtain ⟨flow, rfl, tree⟩ := certified accepted
  exact Tree.body_preserves (values := values) (ambient := ambient) (faults := fun _ token => token = reason)
    functions definitions registered (.refl _) program [] (fun _ _ => rfl)
    tree valid reason reason unique environments heaps (.cons (.intro .head) rfl (.ordinary rfl rfl) .nil)
    agrees typed reference read unmapped sourceFailure

private def rawWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box { Box(Bool) }",
    "function mixed() returns (Bool) { let a = true; let b: Word; let c = a; let d: Bool; let e = c; return e; }",
    "function fail() returns (Bool) { let a = true; let missing: Bool; let c = a; let d = missing; let never = false; return a; }",
    "function effectFailure() returns (Bool) { let a = true; let m: mapping(Word => Word); let c = a; let missing: Bool; let d = (m, missing); let never = false; return a; }",
    "function boxed() returns (Box) { let a: Box = .Box(true); let missing: Bool; let b = a; let c = b; return c; }"]}] }

def run : IO Unit := do
  let checked ← SourceCompilerFeatureSupport.get "mixed checker" (checkProgram rawWorkspace)
  let mixed ← SourceCompilerFeatureSupport.compileNamed checked "mixed"
  SourceCompilerFeatureSupport.require ((← mixed.run []) == .bool true) "mixed local result changed"
  mixed.checkCells [] [(.bool, some (.bool true)), (.word, none), (.bool, some (.bool true)), (.bool, none), (.bool, some (.bool true))]
  mixed.checkResume [] (.bool true)
  let fail ← SourceCompilerFeatureSupport.compileNamed checked "fail"
  let invocation ← fail.invoke []
  match invocation.outcome with
  | .failed token complete =>
      SourceCompilerFeatureSupport.require (← invocation.diagnostic token).isSome "mixed initializer fault diagnostic missing"
      let suspended ← SourceCompilerFeatureSupport.get "mixed fault suspension"
        (← invocation.initial.run invocation.key [] {SourceCompilerFeatureSupport.executionOptions with executionFuel := 10})
      let checkpoint ← match suspended with
        | .outOfFuel checkpoint => pure checkpoint
        | _ => throw (IO.userError "mixed fault fixture did not suspend")
      match ← checkpoint.resume 300000 1024 with
      | .failed resumed finished =>
          SourceCompilerFeatureSupport.require (resumed == token && finished.heapSize == complete.heapSize)
            "resumption changed mixed failure or allocated an unreachable binding"
      | _ => throw (IO.userError "mixed fault checkpoint changed outcome")
  | _ => throw (IO.userError "absent mixed initializer did not fail")
  fail.checkCells [] [(.bool, some (.bool true)), (.bool, none), (.bool, some (.bool true))]
  let effect ← SourceCompilerFeatureSupport.compileNamed checked "effectFailure"
  match (← effect.invoke []).outcome with
  | .failed _ _ => pure ()
  | _ => throw (IO.userError "mixed effectful initializer did not fail")
  effect.checkCells [] [(.bool, some (.bool true)), (.mapping .word .word, some (.mapping .word .word [])),
    (.bool, some (.bool true)), (.bool, none)]
  let boxed ← SourceCompilerFeatureSupport.compileNamed checked "boxed"
  match ← boxed.run [] with
  | .constructed _ [.bool true] => pure ()
  | _ => throw (IO.userError "mixed nominal payload changed")
  IO.println "compatible mixed statements: arbitrary binding induction, intermediate context failure, raw heap order, effects and resume GREEN"
end Tests.SourceCoreCompatibleStatementMixed
