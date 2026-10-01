import Solcore.SourceSemantics.CoreLowering.CompatibleStatementInitializedMeaning
import Solcore.Test.SourceCompilerFeatureSupport

#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! The initializer reads the old scope. Independent success/fault source
traces consume actual lowering receipts; a fault does not reach the binder's
allocation. Public cached runs also test a lazy-read effect before failure. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCompatibleStatementInitialized
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleStatementInitialized CompatiblePayload GeneralHeap ReadOnly CallableIndexedHistory
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"initialized_binding", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "initializer.solc"⟩, 0, 1⟩
private def expression : ExpressionId := ⟨⟨owner, 0⟩⟩
private def statement (index : Nat) : StatementId := ⟨⟨owner, index + 1⟩⟩
private def binder (index : Nat) : TypedBinder := ⟨⟨owner, index⟩, "value", .mono .bool, [], false, none⟩
private def node : ExpressionNode := {id := expression, span, type := .bool, form := .reference "value" (.local (binder 0).id)}
private def initialized : StatementNode := ⟨statement 0, span, .unit, .letDecl (binder 1) (some expression)⟩
private def returned : StatementNode := ⟨statement 1, span, .unit, .returnStmt none⟩
private def source : TypedSource := {
  owner, inputs := [binder 0], roots := [.statement (statement 0), .statement (statement 1)],
  nodes := [.expression node, .statement initialized, .statement returned] }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def initial : SourceSemantics.Context := (SourceSemantics.Context.ofSignatures signatures).withLocal (binder 0).id (binder 0).scheme
private def finalContext := initial.withLocal (binder 1).id (binder 1).scheme
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def scope : SourceCoreLocalCell.Scope := [((binder 0).id, .bool)]
private def reason := Word.ofNatModulo 31
private def faults : FunctionCalls.FaultRep := fun fault token => fault = .uninitializedLocation ⟨0⟩ ∧ token = reason
private theorem extension : BinderExtends owner initial (binder 1) finalContext := by
  apply BinderExtends.intro
  · exact {
      owned := rfl
      scheme := {
        binders := by simp [TypeParameterBindersWellFormed, initial, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal, signatures]
        quantified_nodup := by simp [binder, TypeSystem.Scheme.mono]
        body := .builtin .bool }
      quantified_fresh := by simp [SchemeQuantifiersFresh, binder, TypeSystem.Scheme.mono]
      monomorphic_requirements_empty := by intro; rfl }
  · simp [LocalFresh, initial, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal, binder]
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem boolAdmitted : TypeAdmissible initial .bool :=
  .bool ((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal (binder 0).id (binder 0).scheme)
private theorem localTyped : ExpressionHasType source initial expression .bool := by
  apply ExpressionHasType.ofOrdinary (node := node) (rawType := .bool) (lookupExpression?_sound (by rfl))
    (.reference (.local .head .head (.intro (.empty _ _ rfl) (SchemeWellFormed.monoAdmissible boolAdmitted) []
      .empty (by intro metavariable replacement member; cases member) (SchemeInstantiates.empty_apply _)
      (by simp) (by intro _ member; cases member) .nil))) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem localSyntax : CompatibleExpressionConstructors.Syntax source expression :=
  .fragment (.primitive (.product (.read (node := node) (by rfl) rfl)))
private theorem syntaxTree : Syntax source initial finalContext finalContext (statement 0) [statement 1] .unit :=
  .initialized (node := initialized) (initializerNode := node) (by rfl) rfl (by rfl) rfl extension (by decide)
    (by rfl) rfl localTyped localSyntax (.body (.returnUnit (node := returned) [] (by rfl) rfl rfl))
private theorem valid (context : SourceSemantics.Context) (same : context = initial ∨ context = finalContext) :
    CompatibleExpressionLiterals.ContextValid [] context [] := by
  rcases same with rfl | rfl
  all_goals
    refine ⟨rfl, ⟨?_, ?_⟩, ?_⟩
    · simp [RequirementIdsUnique, finalContext, initial, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal]
    · intro requirement member
      simp [finalContext, initial, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal] at member
    · constructor
      · intro goal evidence found; cases found
      · intro predicate member
        simp [finalContext, initial, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal] at member
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
  subst node
  rfl

private theorem certified {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals fuel : Nat} {code : Expr}
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy (policy layouts frame globals) fuel source scope
      [statement 0, statement 1] .unit (fun _ => reason) reason reason = .ok code) :
    ∃ flow, code = CompatibleStatements.finish .unit flow reason reason ∧
      Tree layouts ⟨owner, []⟩ [] frame globals onError 10 values source initial finalContext finalContext [] (fun _ => reason)
        scope (statement 0) [statement 1] .unit .unit flow := by
  apply tree_of_body rfl (fun _ _ _ => rfl) rfl ?_ syntaxTree declarations rfl accepted
  intro current reachable currentScope budget id node lowered declared childSyntax found typed generated
  have closed : current.typeVariables = [] := by rcases reachable with rfl | rfl <;> rfl
  have residual : current.residualTypeVariables = false := by rcases reachable with rfl | rfl <;> rfl
  exact CompatibleExpressionConstructors.tree_of_functions unique declared closed residual
    ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩ (fun _ _ _ found => metadata found)
    childSyntax found typed generated

private def sourceEnvironment : Dynamic.Environment := [((binder 0).id, ⟨0⟩)]
private def sourceHeap (value : Option Dynamic.Value) : Dynamic.Heap := ⟨[⟨.bool, value, none⟩]⟩
private theorem sourceFailure : Dynamic.FunctionStatementsExecuteOutcome program initial [] source sourceEnvironment (sourceHeap none)
    [statement 0, statement 1] initial (.fault (.uninitializedLocation ⟨0⟩)) (sourceHeap none) := by
  apply Dynamic.FunctionStatementsExecuteOutcome.fault
  apply Dynamic.FunctionStatementsFault.head
  apply Dynamic.StatementFaults.letInitializer (node := initialized) (lookupStatement?_sound (by rfl)) rfl rfl
  apply Dynamic.ExpressionFaults.form (node := node) (lookupExpression?_sound (by rfl))
  exact .localUninitialized (owned := []) (coercions := []) (cell := ⟨.bool, none, none⟩)
    rfl .head (.intro .head) rfl rfl (by rintro ⟨key, value, impossible⟩; cases impossible)

/-- Failure before the marked allocation retains the original lexical context
and source heap; its finite generated execution follows from actual compilation. -/
theorem compiled_failure_preserves {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals fuel : Nat} {code : Expr} {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy (policy layouts frame globals) fuel source scope
      [statement 0, statement 1] .unit (fun _ => reason) reason reason = .ok code)
    {mapping world administrative actualContext canonical actual store ξ contextLocation native}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world administrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents checked values.registry functions mapping world (sourceHeap none) store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      CompatibleStatements.BodyRep (values := values) (registry := values.registry) functions finalMap finalWorld
        (fun _ token => token = reason) .unit .unit (.fault (.uninitializedLocation ⟨0⟩)) value ∧
      CompatibleAmbientHeap.HeapRepresents checked values.registry functions finalMap finalWorld (sourceHeap none) finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend (sourceHeap none) (sourceHeap none) := by
  obtain ⟨flow, rfl, tree⟩ := certified accepted
  exact (Tree.body_preserves (values := values) (ambient := ambient) (faults := fun _ token => token = reason)
    functions definitions registered (.refl _) program [] (valid _ (.inl rfl)) (valid _ (.inr rfl)) (fun _ _ => rfl)
    tree reason reason unique environments heaps (.cons (.intro .head) rfl (.ordinary rfl rfl) .nil)
    agrees typed reference read unmapped sourceFailure).2

/-- Actual completed code reconstructs whether execution reached the binding's
context; the conclusion does not force that context on an early failure. -/
theorem compiled_reflects {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals fuel : Nat} {code : Expr} {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy (policy layouts frame globals) fuel source scope
      [statement 0, statement 1] .unit (fun _ => reason) reason reason = .ok code)
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
      (resultContext = initial ∨ resultContext = finalContext) ∧
      Dynamic.FunctionStatementsExecuteOutcome program initial [] source sourceEnvironment heap
        [statement 0, statement 1] resultContext outcome after ∧
      CompatibleStatements.BodyRep (values := values) (registry := values.registry) functions finalMap finalWorld
        (fun _ token => token = reason) .unit .unit outcome value ∧
      CompatibleAmbientHeap.HeapRepresents checked values.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after := by
  obtain ⟨flow, rfl, tree⟩ := certified accepted
  exact Tree.body_reflects (values := values) (ambient := ambient) (faults := fun _ token => token = reason)
    functions definitions registered (.refl _) program [] (valid _ (.inl rfl)) (valid _ (.inr rfl)) (fun _ _ => rfl)
    tree reason reason environments heaps locals agrees typed reference read unmapped completed

private def rawWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box { Box(Bool) }",
    "function ordered() returns (Bool) { let first = true; let second: Word; return first; }",
    "function fail() returns (Bool) { let missing: Bool; let bound = missing; let never: Word; return true; }",
    "function effectFailure() returns (Bool) { let m: mapping(Word => Word); let missing: Bool; let bound = (m, missing); let never: Word; return true; }",
    "function boxed() returns (Box) { let value: Box = .Box(true); return value; }"]}] }

def run : IO Unit := do
  let checked ← SourceCompilerFeatureSupport.get "initialized checker" (checkProgram rawWorkspace)
  let ordered ← SourceCompilerFeatureSupport.compileNamed checked "ordered"
  SourceCompilerFeatureSupport.require ((← ordered.run []) == .bool true) "initialized local result changed"
  ordered.checkCells [] [(.bool, some (.bool true)), (.word, none)]
  ordered.checkResume [] (.bool true)
  let fail ← SourceCompilerFeatureSupport.compileNamed checked "fail"
  let invocation ← fail.invoke []
  match invocation.outcome with
  | .failed token _ => SourceCompilerFeatureSupport.require (← invocation.diagnostic token).isSome "initializer fault diagnostic missing"
  | _ => throw (IO.userError "absent initializer did not fail")
  fail.checkCells [] [(.bool, none)]
  let partialEntry ← SourceCompilerFeatureSupport.compileNamed checked "effectFailure"
  match (← partialEntry.invoke []).outcome with
  | .failed _ _ => pure ()
  | _ => throw (IO.userError "partial initializer did not fail")
  partialEntry.checkCells [] [(.mapping .word .word, some (.mapping .word .word [])), (.bool, none)]
  let boxed ← SourceCompilerFeatureSupport.compileNamed checked "boxed"
  match ← boxed.run [] with
  | .constructed _ [.bool true] => pure ()
  | _ => throw (IO.userError "initialized nominal payload changed")
  IO.println "compatible initialized statement: old-context failure, initializer effects before allocation, actual receipts, reflection and resume GREEN"
end Tests.SourceCoreCompatibleStatementInitialized
