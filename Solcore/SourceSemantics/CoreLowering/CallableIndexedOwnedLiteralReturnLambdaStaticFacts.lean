import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaSourceFacts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedMixedBodySiteInputs
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedMixedBodyRuntimeBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaScalarNativeTyping
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionLiteralMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderScopeDeclarations

/-! Finite static facts for an actual ordinary lambda with a literal return.
The existing Source typing and accepted compiler actions supply entry, syntax,
and native typing independently of body execution. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLiteralReturnLambdaStaticFacts
open Core Frontend SourceInference

/-- The original lambda typing exposes its genuine parameter context. -/
theorem entry_of_source_facts
    {values : SourceCoreCompatibleValues.Context} {prepared : CallableIndexedLambdaValues.Prepared values.checked}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : CallableIndexedLambdaValues.Code prepared function scope administrative)
    {id : ExpressionId} {node : ExpressionNode}
    (facts : CallableIndexedOwnedOrdinaryLambdaSourceFacts.Facts function id node)
    (kinds : ∀ binding ∈ code.receipt.loweredParameters,
      function.source.inputs.any (fun input => decide (input.id = binding.1.id)) = false)
    (referenceIndex : code.referenceIndex = scope.length + 1 + prepared.base.globals.length) :
    ∃ entry : CallableIndexedLambdaEntryPrefix.Context code, ∃ finalContext bodyFacts,
      StatementsHaveType function.source {returnType := function.resultType}
        entry.context function.body finalContext bodyFacts ∧
      BodyCompletes function.resultType bodyFacts := by
  have typing := facts.typing
  rw [facts.form] at typing
  generalize rawTypeEq : FunctionValues.sourceType function = raw at typing
  cases typing with
  | lambda namesUnique extended bodyTyped completes =>
    exact ⟨⟨_, _, extended, kinds, referenceIndex⟩, _, _, bodyTyped, completes⟩

/-- Lambda binders are declarations at this actual Source occurrence. -/
theorem parameter_declared {function : Dynamic.Closure} {id : ExpressionId} {node : ExpressionNode}
    (facts : CallableIndexedOwnedOrdinaryLambdaSourceFacts.Facts function id node)
    {binder : TypedBinder} (member : binder ∈ function.parameters) :
    binder ∈ SourceCoreDataPlaces.declaredBinders function.source := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨.expression node, facts.contains.1, ?_⟩
  simpa only [facts.form] using member

/-- Parameter installation uses the existing Source declaration producer. -/
theorem entry_declarations
    {values : SourceCoreCompatibleValues.Context} {prepared : CallableIndexedLambdaValues.Prepared values.checked}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : CallableIndexedLambdaValues.Code prepared function scope administrative)
    (entry : CallableIndexedLambdaEntryPrefix.Context code)
    {id : ExpressionId} {node : ExpressionNode}
    (facts : CallableIndexedOwnedOrdinaryLambdaSourceFacts.Facts function id node)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source scope function.context) :
    CompatibleExpressionReads.ScopeDeclarations function.source
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      entry.context := by
  have extended := entry.extended
  rw [CallableIndexedLambdaEntryPrefix.parameters code] at extended
  have declared : ∀ binding, binding ∈ code.receipt.loweredParameters →
      binding.1 ∈ SourceCoreDataPlaces.declaredBinders function.source := by
    intro binding member
    apply parameter_declared facts
    rw [CallableIndexedLambdaEntryPrefix.parameters code]
    exact List.mem_map.mpr ⟨binding, member, rfl⟩
  have installed := RecursiveNamedHeaderScopeDeclarations.parameters declared extended declarations
  simpa only [List.foldl_flip_cons_eq_append, List.map_reverse] using installed

/-- Entry extension retains the full nonlocal context and covering evidence. -/
theorem entry_runtime
    {values : SourceCoreCompatibleValues.Context} {prepared : CallableIndexedLambdaValues.Prepared values.checked}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {code : CallableIndexedLambdaValues.Code prepared function scope administrative}
    (entry : CallableIndexedLambdaEntryPrefix.Context code) {program : Program}
    (frame : Dynamic.ClosureFrame program function) :
    Dynamic.RuntimeContextFields function.context entry.context ∧
      Dynamic.SourceRuntimeValid program entry.context function.source ∧
      function.evidence.Covers entry.context := by
  exact ⟨Dynamic.MonoBindersExtend.runtimeContextFields entry.extended,
    CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters frame entry.extended⟩

private theorem statement_reported {source : TypedSource} {control : ControlContext}
    {context finalContext : SourceSemantics.Context} {statement : StatementId} {facts : StatementFacts}
    (typed : StatementHasType source control context statement finalContext facts) :
    ∃ node, ContainsStatement source statement node ∧ node.type = facts.type := by
  cases typed <;> exact ⟨_, by assumption, by assumption⟩

/-- Singleton return syntax is derived from the original statement judgment. -/
theorem return_syntax {source : TypedSource} {context finalContext : SourceSemantics.Context}
    {statement : StatementId} {node : StatementNode} {expression : ExpressionId}
    {result : TypeSystem.Ty} {bodyFacts : BodyFacts} {approved : ExpressionId → Prop}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? statement = some node)
    (form : node.form = .returnStmt (some expression))
    (typed : StatementsHaveType source {returnType := result} context [statement] finalContext bodyFacts)
    (allowed : approved expression) :
    GenericImperativeMatch.Syntax source approved context (.statements true [statement]) result := by
  cases typed with
  | singleton head =>
    obtain ⟨reported, reportedContains, reportedType⟩ := statement_reported head
    have sameReported : reported = node := Option.some.inj
      ((lookupStatement?_complete unique reportedContains).symm.trans found)
    subst reported
    obtain ⟨controlNode, controlContains, controlTyped⟩ := Dynamic.StatementHasType.controlFormTyping head
    have sameControl : controlNode = node := Option.some.inj
      ((lookupStatement?_complete unique controlContains).symm.trans found)
    subst controlNode
    rw [form] at controlTyped
    cases controlTyped
    obtain ⟨actual, actualContains, actualTyped⟩ := Dynamic.StatementHasType.formTyping head
    have sameActual : actual = node := Option.some.inj
      ((lookupStatement?_complete unique actualContains).symm.trans found)
    subst actual
    rw [form] at actualTyped
    cases actualTyped with
    | returnValue expressionTyped =>
      obtain ⟨expressionNode, expressionContains, expressionType⟩ := expressionTyped.stored_type
      exact .body (.returnValue [] found form reportedType
        (lookupExpression?_complete unique expressionContains) expressionType
        (expressionType.symm ▸ expressionTyped) allowed)

/-- Literal-only approval excludes indirect calls at the same lookup row. -/
theorem literal_not_indirect {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    (found : source.lookupExpression? id = some node)
    (atomic : CompatibleExpressionLiterals.Atomic node.form) :
    CallableIndexedOwnedPreparedMixedBodyRuntimeBounds.NoIndirectOn source (fun candidate => candidate = id) := by
  intro candidate actual callee ids metadata allowed selected
  subst candidate
  have same : actual = node := Option.some.inj (selected.symm.trans found)
  subst actual
  generalize nodeForm : node.form = shape at atomic
  cases atomic <;> intro impossible <;> cases impossible

/-- A real accepted literal child is typed at every administrative context.
The numeric validator and ordinary compiler fields remain authentic inputs. -/
theorem literal_expression_native
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {expressionBudget childBudget : Nat} {compilation : SourceCoreFunctions.Context}
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node)
    (atomic : CompatibleExpressionLiterals.Atomic node.form)
    (unitType : node.form = .tuple [] → node.type = .unit)
    (special : ∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation child budget source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (leafPolicy : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : FunctionCode.children policy lowerBody expressionBudget compilation
      childBudget source scope id reasonAt = .ok lowered)
    (definitions : DataEnvironment) (context : Core.Context) :
    lowered.type.WellFormed definitions ∧
      HasType context lowered.expression (LanguageResult.resultType lowered.type) definitions := by
  obtain ⟨_, _, literal⟩ := CompatibleExpressionLiterals.of_functions
    found atomic unitType special readPolicy leafPolicy accepted
  exact CompatibleExpressionScalarNativeTyping.literal_native literal definitions context

/-- The accepted literal callback supplies native body typing under any actual
administrative context. No scope typing or completed body law is needed. -/
theorem literal_body_native
    {policy : SourceCoreLoops.Policy} {expressions : SourceCoreFunctions.Policy}
    {lowerBody : SourceCoreFunctions.BodyLowerer} {expressionBudget : Nat}
    {compilation : SourceCoreFunctions.Context} {fuel : Nat}
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {statement : StatementId} {node : StatementNode}
    {type : Ty} {expression : ExpressionId} {expressionNode : ExpressionNode} {result : Ty}
    {reasonAt : ExpressionId → Word} {fellThrough escaped : Word} {code : Expr}
    (callback : policy.lowerExpression = FunctionCode.children expressions lowerBody expressionBudget compilation)
    (read : policy.readStatement source statement = .ok (node, type))
    (form : node.form = .returnStmt (some expression))
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope [statement] result reasonAt fellThrough escaped = .ok code)
    (found : source.lookupExpression? expression = some expressionNode)
    (atomic : CompatibleExpressionLiterals.Atomic expressionNode.form)
    (unitType : expressionNode.form = .tuple [] → expressionNode.type = .unit)
    (special : ∀ child budget, (match expressions.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation child budget source scope expression reasonAt) = .ok none)
    (readPolicy : expressions.readExpression source expression =
      SourceCoreCompatibleDataExpressions.readExpression values.checked source expression)
    (leafPolicy : expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (definitions : DataEnvironment) (context : Core.Context) :
    HasType context code (LanguageResult.resultType result) definitions := by
  obtain ⟨budget, lowered, generated, same, emitted⟩ :=
    CallableIndexedLambdaScalarNativeTyping.scalar_body_receipt read (.inl form) accepted
  rw [callback] at generated
  obtain ⟨wellFormed, typed⟩ := literal_expression_native
    found atomic unitType special readPolicy leafPolicy generated definitions context
  rw [same] at wellFormed typed
  rw [emitted]
  apply LocalControl.finish_hasType wellFormed
    (LocalLoop.toControl_hasType escaped wellFormed (LocalLoop.returnValue_hasType wellFormed typed))
  split
  · rename_i unitResult
    simpa only [unitResult] using
      (LanguageResult.success_hasType (HasType.unit (definitions := definitions) (context := context)))
  · exact LanguageResult.failure_hasType wellFormed .word

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLiteralReturnLambdaStaticFacts
