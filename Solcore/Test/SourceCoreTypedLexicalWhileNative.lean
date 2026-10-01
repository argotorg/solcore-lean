import Solcore.SourceSemantics.CoreLowering.TypedLexicalWhileMeaning
import Solcore.SourceSemantics.CoreLowering.TypedLexicalWhileNativeCertificates
import Solcore.Test.SourceCompilerFeatureSupport

#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Actual lowering, checker receipts and independent source control connect to
the while theorem under arbitrary typed ambient captures. Runtime fixtures cover
lexical exits, condition/body faults, persistent effects and suspended continue. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
namespace Tests.SourceCoreTypedLexicalWhileNative
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
private def ifNode : StatementNode := ⟨statement 3, span, .unit, .ifThen expression [statement 1] none⟩
private def blockNode : StatementNode := ⟨statement 4, span, .unit, .block [statement 3]⟩
private def statements := [statement 4, statement 2]
private def source : TypedSource := {
  owner, inputs := [], roots := statements.map .statement,
  nodes := [.expression condition, .statement bodyNode, .statement whileNode, .statement returnNode, .statement ifNode, .statement blockNode]}
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
private def ifCode := LocalLoop.sequence .unit
  (LocalLoop.conditional .unit conditionCode (LocalLoop.sequence .unit loopCode (LocalLoop.fallthrough .unit)) (LocalLoop.fallthrough .unit))
  (LocalLoop.fallthrough .unit)
private def code := LocalLoop.sequence .unit ifCode (LocalLoop.returned .unit)
private theorem conditionGenerated (fuel : Nat) : SourceCoreFunctions.lowerExpressionWithPolicy expressionPolicy noBody (fuel + 1) compilation source [] expression (fun _ => reason) = .ok ⟨.bool, conditionCode⟩ := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy]
  rfl
private theorem loopGenerated (layouts : SourceCoreAllocationLayouts.Prepared) (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat) :
    SourceCoreLoops.lowerFlowStatementsWithPolicy (policy layouts frame globals) 6 source [] [statement 1] .unit (fun _ => reason) false reason =
      .ok (LocalLoop.sequence .unit loopCode (LocalLoop.fallthrough .unit)) := by
  change (do
    let condition ← SourceCoreFunctions.lowerExpressionWithPolicy expressionPolicy noBody 5 compilation source [] expression (fun _ => reason)
    SourceCoreBasic.ensureType (.occurrence (statement 1).occurrence) .bool condition.type
    pure (LocalLoop.sequence .unit (LocalLoop.whileLoop .unit condition.expression (LocalLoop.breaking .unit) reason) (LocalLoop.fallthrough .unit))) = _
  rw [conditionGenerated]
  rfl
private theorem ifGenerated (layouts : SourceCoreAllocationLayouts.Prepared) (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat) :
    SourceCoreLoops.lowerFlowStatementsWithPolicy (policy layouts frame globals) 7 source [] [statement 3] .unit (fun _ => reason) false reason = .ok ifCode := by
  change (do
    let condition ← SourceCoreFunctions.lowerExpressionWithPolicy expressionPolicy noBody 6 compilation source [] expression (fun _ => reason)
    SourceCoreBasic.ensureType (.occurrence (statement 3).occurrence) .bool condition.type
    let yes ← SourceCoreLoops.lowerFlowStatementsWithPolicy (policy layouts frame globals) 6 source [] [statement 1] .unit (fun _ => reason) false reason
    pure (LocalLoop.sequence .unit (LocalLoop.conditional .unit condition.expression yes (LocalLoop.fallthrough .unit)) (LocalLoop.fallthrough .unit))) = _
  rw [conditionGenerated, loopGenerated]
  rfl
private theorem generated (layouts : SourceCoreAllocationLayouts.Prepared) (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat) :
    SourceCoreLoops.lowerFlowStatementsWithPolicy (policy layouts frame globals) 8 source [] statements .unit (fun _ => reason) true reason = .ok code := by
  change (do
    let body ← SourceCoreLoops.lowerFlowStatementsWithPolicy (policy layouts frame globals) 7 source [] [statement 3] .unit (fun _ => reason) false reason
    pure (LocalLoop.sequence .unit body (LocalLoop.returned .unit))) = _
  rw [ifGenerated]
  rfl
private theorem conditionTyped : ExpressionHasType source context expression .bool := by
  apply ExpressionHasType.ofOrdinary (node := condition) (rawType := .bool) (lookupExpression?_sound rfl)
    (.reference (.builtinBoolean true)) (.bool (TypeParameterBindersWellFormed.ofSignatures signatures)) (.bool (TypeParameterBindersWellFormed.ofSignatures signatures))
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem conditionSyntax : CompatibleExpressionTyped.Syntax source expression :=
  .fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal (node := condition) rfl (.bool _ _)))))))
private theorem syntaxTree : TypedLexicalWhile.Syntax source context true statements .unit :=
  .block (node := blockNode) rfl rfl rfl
    (.ifThen (node := ifNode) (conditionNode := condition) rfl rfl rfl rfl rfl conditionTyped conditionSyntax
      (.whileLoop (node := whileNode) (conditionNode := condition) rfl rfl rfl rfl conditionTyped conditionSyntax
        (.breaking (node := bodyNode) rfl rfl) (.body (.body (.nil (.inl rfl)))))
      (.body (.body (.nil (.inl rfl)))) (.body (.body (.nil (.inl rfl)))))
    (.body (.body (.returnUnit (node := returnNode) [] rfl rfl rfl)))
private theorem codeTyped {definitions : DataEnvironment} {administrative : Core.Context} :
    HasType administrative code (LocalLoop.resultType .unit) definitions := by
  apply LocalLoop.sequence_hasType .unit
  · apply LocalLoop.sequence_hasType .unit
    · apply LocalLoop.conditional_hasType .unit (LanguageResult.success_hasType .bool)
      · exact LocalLoop.sequence_hasType .unit (LocalLoop.whileLoop_hasType reason .unit
          (LanguageResult.success_hasType .bool) (LocalLoop.breaking_hasType .unit)) (LocalLoop.fallthrough_hasType .unit)
      · exact LocalLoop.fallthrough_hasType .unit
    · exact LocalLoop.fallthrough_hasType .unit
  · exact LocalLoop.returned_hasType .unit

/-- Only the enclosing checker result is provided; there are no per-loop
native typing hypotheses. Blocks, conditionals and sequencing are inverted. -/
theorem extracted {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals : Nat} {definitions : DataEnvironment} {administrative : Core.Context} {actual : Expr} {nativeType : Ty}
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy (policy layouts frame globals) 8 source [] statements .unit (fun _ => reason) true reason = .ok actual)
    (checked : infer? administrative actual definitions = some nativeType) :
    Tree layouts ⟨owner, []⟩ [] frame globals onError 10 values source [] (fun _ => reason) definitions administrative
      context [] true statements .unit .unit actual := by
  apply tree_of_typed_flow rfl (by intros; rfl) rfl ?_ syntaxTree rfl rfl rfl
    (by intro id binder index type found; cases found) rfl accepted (infer_sound checked)
  intro sourceContext closed residual signatures scope fuel id node lowered declarations syntaxValue found typed generated
  exact CompatibleExpressionTyped.tree_of_functions unique declarations signatures closed residual
    ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩
    (by
      intro id node _ found
      have member := (lookupExpression?_sound found).1
      simp [source] at member
      rcases member with rfl
      rfl)
    syntaxValue found typed generated

/-- The concrete accepted fixture supplies the enclosing checker receipt. -/
theorem concrete (layouts : SourceCoreAllocationLayouts.Prepared) (frame : SourceCoreCallableIndexedFrames.Layout)
    (globals : Nat) (definitions : DataEnvironment) (administrative : Core.Context) :
    Tree layouts ⟨owner, []⟩ [] frame globals onError 10 values source [] (fun _ => reason) definitions administrative
      context [] true statements .unit .unit code :=
  extracted (generated layouts frame globals) (infer_complete codeTyped)

private def finished := LocalControl.finish .unit (LocalLoop.toControl .unit code reason) (LanguageResult.success .unit)

/-- The same automatic extraction also accepts the real finish/toControl body
and uses the enclosing checker result, without a flow or loop typing premise. -/
theorem extracted_finished {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals : Nat} {definitions : DataEnvironment} {administrative : Core.Context} {actual : Expr} {nativeType : Ty}
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy (policy layouts frame globals) 8 source [] statements .unit (fun _ => reason) reason reason = .ok actual)
    (checked : infer? administrative actual definitions = some nativeType) :
    ∃ flow,
      SourceCoreLoops.lowerFlowStatementsWithPolicy (policy layouts frame globals) 8 source [] statements .unit (fun _ => reason) true reason = .ok flow ∧
      Tree layouts ⟨owner, []⟩ [] frame globals onError 10 values source [] (fun _ => reason) definitions administrative
        context [] true statements .unit .unit flow ∧
      actual = LocalControl.finish .unit (LocalLoop.toControl .unit flow reason) (LanguageResult.success .unit) := by
  apply tree_of_typed_body rfl (by intros; rfl) rfl ?_ syntaxTree rfl rfl rfl
    (by intro id binder index type found; cases found) rfl accepted (infer_sound checked)
  intro sourceContext closed residual signatures scope fuel id node lowered declarations syntaxValue found typed generated
  exact CompatibleExpressionTyped.tree_of_functions unique declarations signatures closed residual
    ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩
    (by
      intro id node _ found
      have member := (lookupExpression?_sound found).1
      simp [source] at member
      rcases member with rfl
      rfl)
    syntaxValue found typed generated

theorem concrete_finished (layouts : SourceCoreAllocationLayouts.Prepared) (frame : SourceCoreCallableIndexedFrames.Layout)
    (globals : Nat) (definitions : DataEnvironment) (administrative : Core.Context) :
    ∃ flow,
      SourceCoreLoops.lowerFlowStatementsWithPolicy (policy layouts frame globals) 8 source [] statements .unit (fun _ => reason) true reason = .ok flow ∧
      Tree layouts ⟨owner, []⟩ [] frame globals onError 10 values source [] (fun _ => reason) definitions administrative
        context [] true statements .unit .unit flow ∧
      finished = LocalControl.finish .unit (LocalLoop.toControl .unit flow reason) (LanguageResult.success .unit) := by
  apply extracted_finished
  · unfold SourceCoreLoops.lowerStatementsWithPolicy
    rw [generated]
    rfl
  · exact infer_complete (LocalControl.finish_hasType .unit
      (LocalLoop.toControl_hasType reason .unit codeTyped) (LanguageResult.success_hasType .unit))

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function nested(flag: Bool) returns (Word) { let outer: Word = 17; { let unused: Bool; if (flag) { let inner: Word = 19; while (true) { let shadow: Word = 23; { while (true) { let stopped: Word; break; } } break; } } else { while (false) { let skipped: Word; } } } return outer; }",
    "function early() returns (Word) { let root: Word; { while (true) { let answer: Word = 31; if (true) { return answer; } continue; } } return 1; }"
  ]}] }
def run : IO Unit := do
  let checked ← SourceCompilerFeatureSupport.get "native while source" (checkProgram workspace)
  let nested ← SourceCompilerFeatureSupport.compileNamed checked "nested"
  for flag in [false, true] do
    SourceCompilerFeatureSupport.require ((← nested.run [.bool flag]) == SourceCompilerFeatureSupport.scalar 17) "nested typed loop changed outer value"
    nested.checkResume [.bool flag] (SourceCompilerFeatureSupport.scalar 17)
    nested.checkCells [.bool flag] ([ (.bool, some (.bool flag)), (.word, some (SourceCompilerFeatureSupport.scalar 17)), (.bool, none)] ++
      if flag then [(.word, some (SourceCompilerFeatureSupport.scalar 19)), (.word, some (SourceCompilerFeatureSupport.scalar 23)), (.word, none)] else [])
  let early ← SourceCompilerFeatureSupport.compileNamed checked "early"
  SourceCompilerFeatureSupport.require ((← early.run []) == SourceCompilerFeatureSupport.scalar 31) "nested return changed result"
  early.checkCells [] [(.word, none), (.word, some (SourceCompilerFeatureSupport.scalar 31))]
  early.checkResume [] (SourceCompilerFeatureSupport.scalar 31)
  IO.println "native while extraction: whole checker to loop sites, nested lexical/control wrappers and resume GREEN"
end Tests.SourceCoreTypedLexicalWhileNative
