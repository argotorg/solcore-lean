import Solcore.SourceSemantics.CoreLowering.TypedLexicalWhileMeaning
import Solcore.Test.SourceCompilerFeatureSupport

#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Actual lowering, checker receipts and independent source control connect to
the while theorem under arbitrary typed ambient captures. Runtime fixtures cover
lexical exits, condition/body faults, persistent effects and suspended continue. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
namespace Tests.SourceCoreTypedLexicalWhile
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open TypedLexicalWhile CompatiblePayload GeneralHeap ReadOnly
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"typed_while", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "typed_while.solc"⟩, 0, 1⟩
private def expression : ExpressionId := ⟨⟨owner, 0⟩⟩
private def statement (index : Nat) : StatementId := ⟨⟨owner, index + 1⟩⟩
private def condition : ExpressionNode := {id := expression, span, type := .bool, form := .reference "true" (.builtinBoolean true)}
private def bodyNode : StatementNode := ⟨statement 0, span, .unit, .breakStmt⟩
private def whileNode : StatementNode := ⟨statement 1, span, .unit, .whileLoop expression [statement 0]⟩
private def returnNode : StatementNode := ⟨statement 2, span, .unit, .returnStmt none⟩
private def statements := [statement 1, statement 2]
private def source : TypedSource := {
  owner, inputs := [], roots := statements.map .statement,
  nodes := [.expression condition, .statement bodyNode, .statement whileNode, .statement returnNode]}
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def context : SourceSemantics.Context := SourceSemantics.Context.ofSignatures signatures
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def reason := Word.ofNatModulo 19
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem prepared : (SourceCoreCompatibleCatalog.prepare signatures 10 [.unit, .bool]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 10 [.unit, .bool]).toOption.get prepared
private def values := SourceCoreCompatibleValues.Context.initial checked
private def compilation : SourceCoreFunctions.Context := ⟨⟨[], [], [], []⟩, ⟨owner, []⟩, [], 0, [], Word.zero⟩
private def noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .ok .unit
private def expressionPolicy := SourceCoreCompatibleDataExpressions.functionPolicy 10 values
private def onError (_ : SourceCoreAllocationLayouts.Error) : SourceCoreBasic.Error := .traversalExhausted (.declaration owner)
private def policy (layouts : SourceCoreAllocationLayouts.Prepared) (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat) : SourceCoreLoops.Policy := {
  lowerExpression := fun fuel source scope id reasonAt => SourceCoreFunctions.lowerExpressionWithPolicy expressionPolicy noBody fuel compilation source scope id reasonAt
  readStatement := SourceCoreCompatibleDataExpressions.readStatement checked
  lowerBinder := SourceCoreCompatibleDataExpressions.lowerBinder checked
  sourceCells := some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt ⟨owner, []⟩ [] onError)) }
private def conditionCode := LanguageResult.success (.bool true)
private def loopCode := LocalLoop.whileLoop .unit conditionCode (LocalLoop.breaking .unit) reason
private def code := LocalLoop.sequence .unit loopCode (LocalLoop.returned .unit)
private theorem conditionGenerated : SourceCoreFunctions.lowerExpressionWithPolicy expressionPolicy noBody 4 compilation source [] expression (fun _ => reason) = .ok ⟨.bool, conditionCode⟩ := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy]
  rfl
private theorem generated (layouts : SourceCoreAllocationLayouts.Prepared) (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat) :
    SourceCoreLoops.lowerFlowStatementsWithPolicy (policy layouts frame globals) 5 source [] statements .unit (fun _ => reason) true reason = .ok code := by
  change (do
    let condition ← SourceCoreFunctions.lowerExpressionWithPolicy expressionPolicy noBody 4 compilation source [] expression (fun _ => reason)
    SourceCoreBasic.ensureType (.occurrence (statement 1).occurrence) .bool condition.type
    pure (LocalLoop.sequence .unit (LocalLoop.whileLoop .unit condition.expression (LocalLoop.breaking .unit) reason) (LocalLoop.returned .unit))) = .ok code
  rw [conditionGenerated]
  rfl
private theorem conditionTyped : ExpressionHasType source context expression .bool := by
  apply ExpressionHasType.ofOrdinary (node := condition) (rawType := .bool) (lookupExpression?_sound rfl)
    (.reference (.builtinBoolean true)) (.bool (TypeParameterBindersWellFormed.ofSignatures signatures)) (.bool (TypeParameterBindersWellFormed.ofSignatures signatures))
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem conditionSyntax : CompatibleExpressionTyped.Syntax source expression :=
  .fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal (node := condition) rfl (.bool _ _)))))))
private theorem conditionTree : CompatibleExpressionTyped.Tree 10 values source context [] (fun _ => reason) [] expression ⟨.bool, conditionCode⟩ := by
  exact CompatibleExpressionTyped.tree_of_functions (policy := expressionPolicy) (body := noBody) (context := compilation)
    (values := values) (scope := []) (sourceContext := context) (fuel := 4) unique
    (by intro id binder index type selected; cases selected) rfl rfl rfl
    ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩
    (by
      intro id node _ found
      have member := (lookupExpression?_sound found).1
      simp [source] at member
      rcases member with rfl
      rfl)
    conditionSyntax rfl conditionTyped conditionGenerated

private theorem loopChecked (definitions : DataEnvironment) (administrative : Core.Context) :
    infer? administrative loopCode definitions = some (LocalLoop.resultType .unit) :=
  infer_complete (LocalLoop.whileLoop_hasType reason .unit (LanguageResult.success_hasType .bool) (LocalLoop.breaking_hasType .unit))

/-- Native typing comes from the actual checker at this loop site. The source
condition and body certificates are independently constructed. -/
private theorem certified (layouts : SourceCoreAllocationLayouts.Prepared) (frame : SourceCoreCallableIndexedFrames.Layout)
    (globals : Nat) (definitions : DataEnvironment) (administrative : Core.Context) {actual : Expr}
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy (policy layouts frame globals) 5 source [] statements .unit (fun _ => reason) true reason = .ok actual) :
    Tree layouts ⟨owner, []⟩ [] frame globals onError 10 values source [] (fun _ => reason) definitions administrative
      context [] true statements .unit .unit actual := by
  have same := Except.ok.inj ((generated layouts frame globals).symm.trans accepted)
  subst actual
  exact .whileLoop (node := whileNode) (conditionNode := condition) rfl rfl rfl rfl conditionTree
    (.breaking (node := bodyNode) rfl rfl) (infer_sound (loopChecked definitions administrative))
    (.body (.body (.returnUnit (node := returnNode) [] rfl rfl rfl)) (.body (.returnUnit (node := returnNode) [] rfl rfl)))
private theorem valid : CompatibleExpressionLiterals.ContextValid [] context [] := by
  refine ⟨rfl, ⟨?_, ?_⟩, ?_⟩
  · simp [RequirementIdsUnique, context, SourceSemantics.Context.ofSignatures]
  · intro requirement member; cases member
  · constructor
    · intro goal evidence found; cases found
    · intro predicate member; cases member
private theorem sourceTrace (heap : Dynamic.Heap) : TypedScopedStatements.Executes true program context [] source [] heap statements context (.returned .unit) heap := by
  apply Dynamic.FunctionStatementsExecuteOutcome.control
  apply Dynamic.FunctionStatementsExecute.cons (middleContext := context) (nextEnvironment := []) (middle := heap)
  · apply Dynamic.StatementExecutes.whileLoop (outcome := .fallthrough []) (lookupStatement?_sound (node := whileNode) rfl) rfl
    apply Dynamic.WhileExecutes.breaks
    · exact .intro (lookupExpression?_sound (node := condition) rfl) (.builtinBoolean rfl) .nil
    · exact .terminal (.breakStmt (lookupStatement?_sound (node := bodyNode) rfl) rfl) (.breaking [])
  · exact .singleton (lookupStatement?_sound (node := returnNode) rfl) (by intro expression; simp [returnNode])
      (.returnUnit (lookupStatement?_sound (node := returnNode) rfl) rfl)

private def faults : FunctionCalls.FaultRep := fun _ _ => True

/-- Actual compiled while flow preserves an independent trace, with arbitrary
actual captures/renaming and a genuine live indexed context cell. -/
theorem compiled_preserves {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals : Nat} {actualCode : Expr} {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy (policy layouts frame globals) 5 source [] statements .unit (fun _ => reason) true reason = .ok actualCode)
    {mapping world administrative actualContext canonical actual heap store ξ contextLocation native}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world administrative [] [] canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents checked values.registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap context.locals []) (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (actualCode.rename ξ) value finalStore ∧
      FlowRep (values := values) (registry := values.registry) functions finalMap finalWorld faults .unit .unit (.returned .unit) value ∧
      CompatibleAmbientHeap.HeapRepresents checked values.registry functions finalMap finalWorld heap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap heap ∧
      TypedLexicalControl.LexicalResult checked ambient.definitions finalMap finalWorld administrative source.owner context [] [] context heap :=
  Tree.preserves (values := values) (ambient := ambient) (faults := faults) functions definitions registered (.refl _) program []
    (fun _ _ => trivial) (fun _ _ _ _ _ => trivial) (certified layouts frame globals _ _ accepted) valid unique environments heaps locals agrees typed reference read unmapped (sourceTrace heap)

/-- Completion alone reconstructs source while control and the lexical result;
there is no source-run, condition-run or body-run premise. -/
theorem compiled_reflects {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals : Nat} {actualCode : Expr} {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy (policy layouts frame globals) 5 source [] statements .unit (fun _ => reason) true reason = .ok actualCode)
    {mapping world administrative actualContext canonical actual heap store ξ contextLocation native value finalStore}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world administrative [] [] canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents checked values.registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap context.locals []) (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (completed : Evaluates actual store (actualCode.rename ξ) value finalStore) :
    ∃ finalContext outcome after finalMap finalWorld,
      TypedScopedStatements.Executes true program context [] source [] heap statements finalContext outcome after ∧
      FlowRep (values := values) (registry := values.registry) functions finalMap finalWorld faults .unit .unit outcome value ∧
      CompatibleAmbientHeap.HeapRepresents checked values.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      TypedLexicalControl.LexicalResult checked ambient.definitions finalMap finalWorld administrative source.owner context [] [] finalContext after :=
  Tree.reflects (values := values) (ambient := ambient) (faults := faults) functions definitions registered (.refl _) program []
    (fun _ _ => trivial) (fun _ _ _ _ _ => trivial) (certified layouts frame globals _ _ accepted) valid unique environments heaps locals agrees typed reference read unmapped completed

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function falseLoop() returns (Word) { let x: Word = 7; while (false) { let skip: Word = 8; } return x; }",
    "function nestedBreak(flag: Bool) returns (Word) { let x: Word = 7; while (true) { let x: Word = 8; { let z: Word; if (flag) { break; } else { break; } } let skipped: Word = 9; } return x; }",
    "function earlyReturn() returns (Word) { while (true) { let x: Word = 11; return x; } let skipped: Word = 13; return skipped; }",
    "function conditionFault() returns (Word) { let absent: Bool; while (absent) { return 3; } return 7; }",
    "function bodyFault() returns (Word) { while (true) { let absent: Word; let failed: Word = absent; break; } return 7; }",
    "function lazyCondition() returns (Word) { let m: mapping(Bool => Bool); while (m[true]) { return 3; } return 7; }",
    "function spin() { while (true) { let retained: Word = 5; continue; } }"
  ]}] }

def run : IO Unit := do
  let checked ← SourceCompilerFeatureSupport.get "typed while source checker" (checkProgram workspace)
  let falseLoop ← SourceCompilerFeatureSupport.compileNamed checked "falseLoop"
  SourceCompilerFeatureSupport.require ((← falseLoop.run []) == SourceCompilerFeatureSupport.scalar 7) "false while executed its body"
  falseLoop.checkCells [] [(.word, some (SourceCompilerFeatureSupport.scalar 7))]
  falseLoop.checkResume [] (SourceCompilerFeatureSupport.scalar 7)
  let nested ← SourceCompilerFeatureSupport.compileNamed checked "nestedBreak"
  for flag in [false, true] do
    SourceCompilerFeatureSupport.require ((← nested.run [.bool flag]) == SourceCompilerFeatureSupport.scalar 7) "nested break lost outer scope"
    nested.checkCells [.bool flag] [(.bool, some (.bool flag)), (.word, some (SourceCompilerFeatureSupport.scalar 7)),
      (.word, some (SourceCompilerFeatureSupport.scalar 8)), (.word, none)]
    nested.checkResume [.bool flag] (SourceCompilerFeatureSupport.scalar 7)
  let returned ← SourceCompilerFeatureSupport.compileNamed checked "earlyReturn"
  SourceCompilerFeatureSupport.require ((← returned.run []) == SourceCompilerFeatureSupport.scalar 11) "loop return changed result"
  returned.checkCells [] [(.word, some (SourceCompilerFeatureSupport.scalar 11))]
  returned.checkResume [] (SourceCompilerFeatureSupport.scalar 11)
  let lazy ← SourceCompilerFeatureSupport.compileNamed checked "lazyCondition"
  SourceCompilerFeatureSupport.require ((← lazy.run []) == SourceCompilerFeatureSupport.scalar 7) "lazy loop condition changed default"
  lazy.checkCells [] [(.mapping .bool .bool, some (.mapping .bool .bool []))]
  lazy.checkResume [] (SourceCompilerFeatureSupport.scalar 7)
  for name in ["conditionFault", "bodyFault"] do
    let entry ← SourceCompilerFeatureSupport.compileNamed checked name
    let outcome ← entry.invoke []
    match outcome.outcome with
    | .failed token _ =>
      match ← outcome.diagnostic token with
      | some {error := .uninitializedLocal _, span := some _, ..} => pure ()
      | _ => throw (IO.userError "while fault lost read location")
    | _ => throw (IO.userError "while fault unexpectedly completed")
    entry.checkCells [] [(if name == "conditionFault" then .bool else .word, none)]
  let spin ← SourceCompilerFeatureSupport.compileNamed checked "spin"
  let pending ← spin.invoke [] {executionFuel := 1000}
  match pending.outcome with
  | .outOfFuel checkpoint =>
      let resumed ← checkpoint.resume 1000
      match resumed with
      | .outOfFuel _ => pure ()
      | _ => throw (IO.userError "continue loop terminated after resume")
  | _ => throw (IO.userError "continue loop did not suspend")
  IO.println "typed lexical while: false/break/continue/return, scoped cells, lazy condition effects, faults and resume GREEN"
end Tests.SourceCoreTypedLexicalWhile
