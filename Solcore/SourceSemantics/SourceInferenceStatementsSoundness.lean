import Solcore.SourceSemantics.SourceInferenceSoundness

/-! Fuel-indexed sequencing for the deep statement-inference soundness proof. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceStatementsSoundness

open Frontend SourceInference SourceInferenceSoundness

private theorem child_provenance_through_restore_record
    (state : Frontend.SourceInference.State)
    (scope : Frontend.SourceInference.LexicalScope) (node : Node)
    (roots : List NodeId) :
    TypingSourceExtends (state.toTypedSource roots)
      (((state.restoreLexicalScope scope).recordNode node).toTypedSource
        roots) ∧
    state.integerPatterns ⊆
      ((state.restoreLexicalScope scope).recordNode node).integerPatterns ∧
    state.requirements ⊆
      ((state.restoreLexicalScope scope).recordNode node).requirements := by
  refine ⟨⟨rfl, ?_⟩, ?_, ?_⟩
  · simp only [Frontend.SourceInference.State.toTypedSource,
      Frontend.SourceInference.State.restoreLexicalScope,
      Frontend.SourceInference.State.recordNode]
    exact List.prefix_append _ _
  · intro origin member
    exact member
  · intro requirement member
    exact member

/-- For-item traversal also preserves an anchored typed-source prefix. -/
theorem inferForItemsFuel_success_typingSourceExtends
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {items : List Syntax.ForItem}
    {initial : Frontend.SourceInference.State}
    {result : Detail.InferredForItems}
    (success : Detail.inferForItemsFuel fuel context items initial = .ok result)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (roots : List NodeId := []) :
    TypingSourceExtends (initial.toTypedSource roots)
      (result.state.toTypedSource roots) := by
  constructor
  · exact Detail.inferForItemsFuel_preserves_owner success
  · exact Detail.inferForItemsFuel_preserves_nodesPrefix success
      (nodesPrefix := List.prefix_rfl)
      (baseBelow := initialBelow)
      (cutoffLe := Nat.le_refl _)

/-- The exact metadata needed to type one actual child traversal in the
completed enclosing statement. -/
structure ChildStateProvenance
    (initial childFinal parent : Frontend.SourceInference.State)
    (roots : List NodeId) : Prop where
  initialBelow : initial.NodesBelowNextOccurrence
  sourceExtension : TypingSourceExtends
    (childFinal.toTypedSource roots) (parent.toTypedSource roots)
  integerPatternsSubset :
    childFinal.integerPatterns ⊆ parent.integerPatterns
  requirementsSubset : childFinal.requirements ⊆ parent.requirements

private theorem child_provenance_through_record
    (initial child : Frontend.SourceInference.State)
    (node : Node) (roots : List NodeId)
    (initialBelow : initial.NodesBelowNextOccurrence) :
    ChildStateProvenance initial child (child.recordNode node) roots := by
  refine ⟨initialBelow, ?_, ?_, ?_⟩
  · refine ⟨rfl, ?_⟩
    simp only [Frontend.SourceInference.State.toTypedSource,
      Frontend.SourceInference.State.recordNode]
    exact List.prefix_append _ _
  · intro origin member
    exact member
  · exact Frontend.SourceInference.State.recordNode_requirements_subset
      child node

private theorem child_provenance_through_binder_record
    (initial child : Frontend.SourceInference.State)
    (locals : TypeSystem.Environment) (name : String)
    (scheme : TypeSystem.Scheme) (span : Option Syntax.SourceSpan)
    (schemeRequirements : List LocalSchemeRequirement)
    (node : Node) (roots : List NodeId)
    (initialBelow : initial.NodesBelowNextOccurrence) :
    ChildStateProvenance initial child
      (((child.withLocals locals).allocateBinder name scheme span false
        schemeRequirements).2.recordNode node) roots := by
  refine ⟨initialBelow, ?_, ?_, ?_⟩
  · refine ⟨rfl, ?_⟩
    simp only [Frontend.SourceInference.State.toTypedSource,
      Frontend.SourceInference.State.recordNode,
      Frontend.SourceInference.State.allocateBinder,
      Frontend.SourceInference.State.withLocals]
    exact List.prefix_append _ _
  · intro origin member
    exact member
  · exact List.Subset.trans
      (Frontend.SourceInference.State.withLocals_requirements_subset
        child locals)
      (List.Subset.trans
        (Frontend.SourceInference.State.allocateBinder_requirements_subset
          (child.withLocals locals) name scheme span false
          schemeRequirements)
        (Frontend.SourceInference.State.recordNode_requirements_subset _
          node))

private theorem syntheticMatchTuple_nodesBelow
    (elements : List InferredExpression)
    (elementsState : Frontend.SourceInference.State)
    (span : Syntax.SourceSpan)
    (below : elementsState.NodesBelowNextOccurrence) :
    ((elementsState.allocateExpressionId.2).recordNode (.expression {
      id := elementsState.allocateExpressionId.1
      span
      type := TypeSystem.Ty.productMany (elements.map (·.type))
      form := .tuple (elements.map (·.id))
    })).NodesBelowNextOccurrence := by
  apply Frontend.SourceInference.State.recordNode_preserves_nodesBelowNextOccurrence
  · exact Frontend.SourceInference.State.allocateExpressionId_preserves_nodesBelowNextOccurrence
      elementsState below
  · exact Frontend.SourceInference.State.allocateExpressionId_index_lt_nextOccurrence
      elementsState

/-- The common `match` scrutinee step preserves the occurrence bound for
both the direct singleton and synthetic tuple cases. -/
theorem inferMatchScrutineesFuel_success_nodesBelow
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {span : Syntax.SourceSpan} {sources : List Syntax.Expr}
    {initial final : Frontend.SourceInference.State}
    {scrutinee : InferredExpression}
    (success : inferMatchScrutineesFuel fuel context span sources initial =
      .ok (scrutinee, final))
    (initialBelow : initial.NodesBelowNextOccurrence) :
    final.NodesBelowNextOccurrence := by
  cases sources with
  | nil =>
      unfold inferMatchScrutineesFuel at success
      cases elementsSuccess : Detail.inferExprsFuel fuel context [] initial with
      | error error =>
          simp [elementsSuccess, bind, Except.bind] at success
      | ok elementsPair =>
          rcases elementsPair with ⟨elements, elementsState⟩
          simp only [elementsSuccess, bind, Except.bind, pure, Pure.pure,
            Except.pure] at success
          injection success with resultEq
          cases resultEq
          exact syntheticMatchTuple_nodesBelow elements elementsState span
            ((Detail.inferExprsFuel_occurrenceBoundExtends elementsSuccess
              ).nodesBelowNextOccurrence initialBelow)
  | cons first rest =>
      cases rest with
      | nil =>
          exact (Detail.inferExprFuel_occurrenceBoundExtends
            (by simpa [inferMatchScrutineesFuel] using success)
            ).nodesBelowNextOccurrence initialBelow
      | cons second tail =>
          unfold inferMatchScrutineesFuel at success
          cases elementsSuccess : Detail.inferExprsFuel fuel context
              (first :: second :: tail) initial with
          | error error =>
              simp [elementsSuccess, bind, Except.bind] at success
          | ok elementsPair =>
              rcases elementsPair with ⟨elements, elementsState⟩
              simp only [elementsSuccess, bind, Except.bind, pure, Pure.pure,
                Except.pure] at success
              injection success with resultEq
              cases resultEq
              exact syntheticMatchTuple_nodesBelow elements elementsState span
                ((Detail.inferExprsFuel_occurrenceBoundExtends elementsSuccess
                  ).nodesBelowNextOccurrence initialBelow)

/-- Explicit match-case traversal retains an anchored input source prefix. -/
theorem inferMatchCasesFuel_success_typingSourceExtends
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {scrutineeType expectedReturn : TypeSystem.Ty}
    {outerScope : Frontend.SourceInference.LexicalScope}
    {cases : List Syntax.MatchCase}
    {initial : Frontend.SourceInference.State}
    {result : Detail.MatchCasesResult}
    (success : Detail.inferMatchCasesFuel fuel context scrutineeType
      expectedReturn outerScope cases initial = .ok result)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (roots : List NodeId := []) :
    TypingSourceExtends (initial.toTypedSource roots)
      (result.state.toTypedSource roots) := by
  constructor
  · exact Detail.inferMatchCasesFuel_preserves_owner success
  · exact Detail.inferMatchCasesFuel_preserves_nodesPrefix success
      (nodesPrefix := List.prefix_rfl)
      (baseBelow := initialBelow)
      (cutoffLe := Nat.le_refl _)

/-- The body of the head explicit match arm is an actual subtraversal of the
completed case pass, so it can be typed in the final case source. -/
theorem inferMatchCasesFuel_headBody_provenance
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {scrutineeType expectedReturn : TypeSystem.Ty}
    {outerScope : Frontend.SourceInference.LexicalScope}
    {arm : Syntax.MatchCase} {rest : List Syntax.MatchCase}
    {initial patternState : Frontend.SourceInference.State}
    {pattern : TypedMatchPattern} {body : Detail.BlockResult}
    {result : Detail.MatchCasesResult}
    (patternSuccess : Detail.inferMatchPatternFuel fuel context
      arm.value.pattern scrutineeType initial = .ok (pattern, patternState))
    (bodySuccess : Detail.inferStatementsFuel fuel context
      arm.value.body.value expectedReturn patternState = .ok body)
    (success : Detail.inferMatchCasesFuel (fuel + 1) context scrutineeType
      expectedReturn outerScope (arm :: rest) initial = .ok result)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (roots : List NodeId := []) :
    ChildStateProvenance patternState body.state result.state roots := by
  have patternBelow : patternState.NodesBelowNextOccurrence :=
    (Detail.inferMatchPatternFuel_occurrenceBoundExtends patternSuccess
      ).nodesBelowNextOccurrence initialBelow
  have bodyBelow : body.state.NodesBelowNextOccurrence :=
    (Detail.inferStatementsFuel_occurrenceBoundExtends bodySuccess
      ).nodesBelowNextOccurrence patternBelow
  let tailInput := body.state.restoreLexicalScope outerScope
  have tailInputBelow : tailInput.NodesBelowNextOccurrence :=
    Frontend.SourceInference.State.restoreLexicalScope_preserves_nodesBelowNextOccurrence
      body.state outerScope bodyBelow
  unfold Detail.inferMatchCasesFuel at success
  simp only [bind, Except.bind, patternSuccess, bodySuccess] at success
  cases tailSuccess : Detail.inferMatchCasesFuel fuel context scrutineeType
      expectedReturn outerScope rest tailInput with
  | error error =>
      simp [tailInput, tailSuccess] at success
  | ok tail =>
      simp only [tailInput, tailSuccess, pure, Pure.pure, Except.pure]
        at success
      injection success with resultEq
      have tailInputToTail : TypingSourceExtends
          (tailInput.toTypedSource roots)
          (tail.state.toTypedSource roots) :=
        inferMatchCasesFuel_success_typingSourceExtends tailSuccess
          tailInputBelow roots
      have bodyToTailInput : TypingSourceExtends
          (body.state.toTypedSource roots)
          (tailInput.toTypedSource roots) :=
        ⟨rfl, List.prefix_rfl⟩
      have bodyIntToTail : body.state.integerPatterns ⊆
          tail.state.integerPatterns := by
        simpa [tailInput, Frontend.SourceInference.State.restoreLexicalScope]
          using (Detail.inferMatchCasesFuel_integerPatterns_subset tailSuccess)
      have bodyReqToTail : body.state.requirements ⊆
          tail.state.requirements := by
        simpa [tailInput, Frontend.SourceInference.State.restoreLexicalScope]
          using (Detail.inferMatchCasesFuel_requirements_subset tailSuccess)
      refine ⟨patternBelow, ?_, ?_, ?_⟩
      · simpa [← resultEq] using
          (TypingSourceExtends.trans bodyToTailInput tailInputToTail)
      · simpa [← resultEq] using bodyIntToTail
      · simpa [← resultEq] using bodyReqToTail

/-- A successful default-free `match` retains the complete explicit-case
traversal as a prefix of its final typed source. -/
theorem inferStatementFuel_success_matchWithoutDefault_cases_provenance
    {fuel : Nat}
    {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
    {arms : Syntax.MatchArms} {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    (statementEq : statement.value = .matchWith scrutinees arms)
    (defaultEq : arms.value.defaultBody = none)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (roots : List NodeId := []) :
    ∃ (scrutinee : InferredExpression)
      (hiddenState : Frontend.SourceInference.State)
      (checked : Detail.MatchCasesResult),
      Detail.inferMatchCasesFuel fuel inferenceContext scrutinee.type
        expectedReturn hiddenState.lexicalScope arms.value.cases
        hiddenState = .ok checked ∧
      ChildStateProvenance hiddenState checked.state result.state roots := by
  obtain ⟨scrutinee, scrutineeState, hiddenScrutinee, hiddenState, checked,
    scrutineeSuccess, hiddenAllocation, casesSuccess, _guard, resultEq,
    _contains⟩ :=
    inferStatementFuel_success_matchWithoutDefault_facts statementEq
      defaultEq allocationEq success roots
  have allocatedBelow : allocated.NodesBelowNextOccurrence := by
    have bound :=
      Frontend.SourceInference.State.allocateStatementId_preserves_nodesBelowNextOccurrence
        initial initialBelow
    have eq : (initial.allocateStatementId).2 = allocated :=
      congrArg Prod.snd allocationEq
    simpa [eq] using bound
  have scrutineeBelow : scrutineeState.NodesBelowNextOccurrence :=
    inferMatchScrutineesFuel_success_nodesBelow scrutineeSuccess
      allocatedBelow
  have hiddenBelow : hiddenState.NodesBelowNextOccurrence := by
    have bound :=
      Frontend.SourceInference.State.allocateHiddenLocal_preserves_nodesBelowNextOccurrence
        scrutineeState scrutineeBelow
    have eq : scrutineeState.allocateHiddenLocal.2 = hiddenState :=
      congrArg Prod.snd hiddenAllocation
    simpa [eq] using bound
  have checkedToParent : TypingSourceExtends
      (checked.state.toTypedSource roots)
      (result.state.toTypedSource roots) := by
    rw [resultEq]
    refine ⟨rfl, ?_⟩
    simp only [Frontend.SourceInference.State.toTypedSource,
      Frontend.SourceInference.State.recordNode]
    exact List.prefix_append _ _
  refine ⟨scrutinee, hiddenState, checked, casesSuccess,
    hiddenBelow, checkedToParent, ?_, ?_⟩
  · simp [resultEq]
  · simp [resultEq]

/-- In a successful `match` with a default arm, both the explicit-case
traversal and the default body embed in the final statement source. -/
theorem inferStatementFuel_success_matchWithDefault_children_provenance
    {fuel : Nat}
    {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
    {arms : Syntax.MatchArms} {defaultBody : Syntax.Block}
    {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    (statementEq : statement.value = .matchWith scrutinees arms)
    (defaultEq : arms.value.defaultBody = some defaultBody)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (roots : List NodeId := []) :
    ∃ (scrutinee : InferredExpression)
      (hiddenState : Frontend.SourceInference.State)
      (checked : Detail.MatchCasesResult)
      (defaultResult : Detail.BlockResult),
      Detail.inferMatchCasesFuel fuel inferenceContext scrutinee.type
        expectedReturn hiddenState.lexicalScope arms.value.cases
        hiddenState = .ok checked ∧
      Detail.inferStatementsFuel fuel inferenceContext defaultBody.value
        expectedReturn checked.state = .ok defaultResult ∧
      ChildStateProvenance hiddenState checked.state result.state roots ∧
      ChildStateProvenance checked.state defaultResult.state result.state
        roots := by
  obtain ⟨scrutinee, scrutineeState, hiddenScrutinee, hiddenState, checked,
    defaultResult, scrutineeSuccess, hiddenAllocation, casesSuccess,
    defaultSuccess, _guard, resultEq, _contains⟩ :=
    inferStatementFuel_success_matchWithDefault_facts statementEq defaultEq
      allocationEq success roots
  have allocatedBelow : allocated.NodesBelowNextOccurrence := by
    have bound :=
      Frontend.SourceInference.State.allocateStatementId_preserves_nodesBelowNextOccurrence
        initial initialBelow
    have eq : (initial.allocateStatementId).2 = allocated :=
      congrArg Prod.snd allocationEq
    simpa [eq] using bound
  have scrutineeBelow : scrutineeState.NodesBelowNextOccurrence :=
    inferMatchScrutineesFuel_success_nodesBelow scrutineeSuccess
      allocatedBelow
  have hiddenBelow : hiddenState.NodesBelowNextOccurrence := by
    have bound :=
      Frontend.SourceInference.State.allocateHiddenLocal_preserves_nodesBelowNextOccurrence
        scrutineeState scrutineeBelow
    have eq : scrutineeState.allocateHiddenLocal.2 = hiddenState :=
      congrArg Prod.snd hiddenAllocation
    simpa [eq] using bound
  have checkedBelow : checked.state.NodesBelowNextOccurrence :=
    (Detail.inferMatchCasesFuel_occurrenceBoundExtends casesSuccess
      ).nodesBelowNextOccurrence hiddenBelow
  have checkedToDefault : TypingSourceExtends
      (checked.state.toTypedSource roots)
      (defaultResult.state.toTypedSource roots) :=
    inferStatementsFuel_success_typingSourceExtends defaultSuccess
      checkedBelow roots
  have defaultProvenance :=
    child_provenance_through_restore_record defaultResult.state
      hiddenState.lexicalScope (.statement {
        id
        span := statement.span
        type := if checked.allReturn && defaultResult.sawReturn then
          (defaultResult.state.restoreLexicalScope
            hiddenState.lexicalScope).resolve expectedReturn
        else
          .unit
        form := .matchWith {
          scrutinee := scrutinee.id
          hiddenScrutinee
          cases := checked.cases
          defaultBody := some defaultResult.statements
          requirements := checked.cases.flatMap fun arm =>
            arm.pattern.requirements
        }
      }) roots
  have defaultToParent : TypingSourceExtends
      (defaultResult.state.toTypedSource roots)
      (result.state.toTypedSource roots) := by
    simpa [resultEq] using defaultProvenance.1
  have checkedIntToDefault :=
    Detail.inferStatementsFuel_integerPatterns_subset defaultSuccess
  have checkedReqToDefault :=
    Detail.inferStatementsFuel_requirements_subset defaultSuccess
  have defaultIntToParent : defaultResult.state.integerPatterns ⊆
      result.state.integerPatterns := by
    simp [resultEq]
  have defaultReqToParent : defaultResult.state.requirements ⊆
      result.state.requirements := by
    simp [resultEq]
  exact ⟨scrutinee, hiddenState, checked, defaultResult, casesSuccess,
    defaultSuccess,
    ⟨hiddenBelow,
      TypingSourceExtends.trans checkedToDefault defaultToParent,
      List.Subset.trans checkedIntToDefault defaultIntToParent,
      List.Subset.trans checkedReqToDefault defaultReqToParent⟩,
    ⟨checkedBelow, defaultToParent, defaultIntToParent,
      defaultReqToParent⟩⟩

/-- The actual body of a successful scoped block is an append-only source
prefix of the enclosing statement and retains its inference ledgers. -/
theorem inferStatementFuel_success_block_child_provenance
    {fuel : Nat}
    {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {body : List Syntax.Statement}
    {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    (statementEq : statement.value = .block body)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (roots : List NodeId := []) :
    ∃ bodyResult,
      Detail.inferStatementsFuel fuel inferenceContext body expectedReturn
        allocated = .ok bodyResult ∧
      allocated.NodesBelowNextOccurrence ∧
      TypingSourceExtends (bodyResult.state.toTypedSource roots)
        (result.state.toTypedSource roots) ∧
      bodyResult.state.integerPatterns ⊆ result.state.integerPatterns ∧
      bodyResult.state.requirements ⊆ result.state.requirements := by
  obtain ⟨bodyResult, bodySuccess, resultEq, _contains⟩ :=
    inferStatementFuel_success_block_facts statementEq allocationEq success
      roots
  have allocatedBelow : allocated.NodesBelowNextOccurrence := by
    have bound :=
      Frontend.SourceInference.State.allocateStatementId_preserves_nodesBelowNextOccurrence
        initial initialBelow
    have eq : (initial.allocateStatementId).2 = allocated :=
      congrArg Prod.snd allocationEq
    simpa [eq] using bound
  refine ⟨bodyResult, bodySuccess, allocatedBelow, ?_, ?_, ?_⟩
  · rw [resultEq]
    refine ⟨rfl, ?_⟩
    simp only [Frontend.SourceInference.State.toTypedSource,
      Frontend.SourceInference.State.restoreLexicalScope,
      Frontend.SourceInference.State.recordNode]
    exact List.prefix_append _ _
  · rw [resultEq]
    intro origin member
    exact member
  · rw [resultEq]
    intro requirement member
    exact member

/-- The then-body of a successful conditional without `else` is a genuine
child traversal whose source and ledgers embed in the enclosing result. -/
theorem inferStatementFuel_success_ifWithoutElse_child_provenance
    {fuel : Nat}
    {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {condition : Syntax.Expr}
    {thenBody : Syntax.Block} {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    (statementEq : statement.value = .ifThen condition thenBody none)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (roots : List NodeId := []) :
    ∃ conditionState thenResult,
      (∃ inferredCondition,
        Detail.inferExprFuel fuel inferenceContext condition (some .bool)
          allocated = .ok (inferredCondition, conditionState)) ∧
      Detail.inferStatementsFuel fuel inferenceContext thenBody.value
        expectedReturn conditionState = .ok thenResult ∧
      conditionState.NodesBelowNextOccurrence ∧
      TypingSourceExtends (thenResult.state.toTypedSource roots)
        (result.state.toTypedSource roots) ∧
      thenResult.state.integerPatterns ⊆ result.state.integerPatterns ∧
      thenResult.state.requirements ⊆ result.state.requirements := by
  obtain ⟨inferredCondition, conditionState, thenResult, conditionSuccess,
    thenSuccess, resultEq, _contains⟩ :=
    inferStatementFuel_success_ifWithoutElse_facts statementEq allocationEq
      success roots
  have allocatedBelow : allocated.NodesBelowNextOccurrence := by
    have bound :=
      Frontend.SourceInference.State.allocateStatementId_preserves_nodesBelowNextOccurrence
        initial initialBelow
    have eq : (initial.allocateStatementId).2 = allocated :=
      congrArg Prod.snd allocationEq
    simpa [eq] using bound
  have conditionBelow : conditionState.NodesBelowNextOccurrence :=
    (Detail.inferExprFuel_occurrenceBoundExtends conditionSuccess
      ).nodesBelowNextOccurrence allocatedBelow
  have provenance := child_provenance_through_restore_record thenResult.state
    conditionState.lexicalScope (.statement {
      id
      span := statement.span
      type := .unit
      form := .ifThen inferredCondition.id thenResult.statements none
    }) roots
  refine ⟨conditionState, thenResult, ⟨inferredCondition, conditionSuccess⟩,
    thenSuccess, conditionBelow, ?_, ?_, ?_⟩
  · simpa [resultEq] using provenance.1
  · simp [resultEq]
  · simp [resultEq]

/-- The body of a successful `while` is a genuine child traversal whose
source and ledgers embed in the enclosing result. -/
theorem inferStatementFuel_success_whileLoop_child_provenance
    {fuel : Nat}
    {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {condition : Syntax.Expr}
    {body : Syntax.Block} {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    (statementEq : statement.value = .whileLoop condition body)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (roots : List NodeId := []) :
    ∃ conditionState bodyResult,
      (∃ inferredCondition,
        Detail.inferExprFuel fuel inferenceContext condition (some .bool)
          allocated = .ok (inferredCondition, conditionState)) ∧
      Detail.inferStatementsFuel fuel
        { inferenceContext with
          loopDepth := inferenceContext.loopDepth + 1 }
        body.value expectedReturn conditionState = .ok bodyResult ∧
      conditionState.NodesBelowNextOccurrence ∧
      TypingSourceExtends (bodyResult.state.toTypedSource roots)
        (result.state.toTypedSource roots) ∧
      bodyResult.state.integerPatterns ⊆ result.state.integerPatterns ∧
      bodyResult.state.requirements ⊆ result.state.requirements := by
  obtain ⟨inferredCondition, conditionState, bodyResult, conditionSuccess,
    bodySuccess, resultEq, _contains⟩ :=
    inferStatementFuel_success_whileLoop_facts statementEq allocationEq
      success roots
  have allocatedBelow : allocated.NodesBelowNextOccurrence := by
    have bound :=
      Frontend.SourceInference.State.allocateStatementId_preserves_nodesBelowNextOccurrence
        initial initialBelow
    have eq : (initial.allocateStatementId).2 = allocated :=
      congrArg Prod.snd allocationEq
    simpa [eq] using bound
  have conditionBelow : conditionState.NodesBelowNextOccurrence :=
    (Detail.inferExprFuel_occurrenceBoundExtends conditionSuccess
      ).nodesBelowNextOccurrence allocatedBelow
  have provenance := child_provenance_through_restore_record bodyResult.state
    conditionState.lexicalScope (.statement {
      id
      span := statement.span
      type := .unit
      form := .whileLoop inferredCondition.id bodyResult.statements
    }) roots
  refine ⟨conditionState, bodyResult,
    ⟨inferredCondition, conditionSuccess⟩, bodySuccess, conditionBelow,
    ?_, ?_, ?_⟩
  · simpa [resultEq] using provenance.1
  · simp [resultEq]
  · simp [resultEq]

/-- Both bodies of a successful `if/else` are retained in the enclosing
statement, including the then-body that precedes the else traversal. -/
theorem inferStatementFuel_success_ifWithElse_child_provenance
    {fuel : Nat}
    {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {condition : Syntax.Expr}
    {thenBody elseBody : Syntax.Block} {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    (statementEq : statement.value =
      .ifThen condition thenBody (some elseBody))
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (roots : List NodeId := []) :
    ∃ conditionState thenResult elseResult,
      (∃ inferredCondition,
        Detail.inferExprFuel fuel inferenceContext condition (some .bool)
          allocated = .ok (inferredCondition, conditionState)) ∧
      Detail.inferStatementsFuel fuel inferenceContext thenBody.value
        expectedReturn conditionState = .ok thenResult ∧
      Detail.inferStatementsFuel fuel inferenceContext elseBody.value
        expectedReturn
        (thenResult.state.restoreLexicalScope conditionState.lexicalScope) =
          .ok elseResult ∧
      conditionState.NodesBelowNextOccurrence ∧
      (thenResult.state.restoreLexicalScope
        conditionState.lexicalScope).NodesBelowNextOccurrence ∧
      TypingSourceExtends (thenResult.state.toTypedSource roots)
        (result.state.toTypedSource roots) ∧
      TypingSourceExtends (elseResult.state.toTypedSource roots)
        (result.state.toTypedSource roots) ∧
      thenResult.state.integerPatterns ⊆ result.state.integerPatterns ∧
      elseResult.state.integerPatterns ⊆ result.state.integerPatterns ∧
      thenResult.state.requirements ⊆ result.state.requirements ∧
      elseResult.state.requirements ⊆ result.state.requirements := by
  obtain ⟨inferredCondition, conditionState, thenResult, elseResult,
    conditionSuccess, thenSuccess, elseSuccess, resultEq, _contains⟩ :=
    inferStatementFuel_success_ifWithElse_facts statementEq allocationEq
      success roots
  have allocatedBelow : allocated.NodesBelowNextOccurrence := by
    have bound :=
      Frontend.SourceInference.State.allocateStatementId_preserves_nodesBelowNextOccurrence
        initial initialBelow
    have eq : (initial.allocateStatementId).2 = allocated :=
      congrArg Prod.snd allocationEq
    simpa [eq] using bound
  have conditionBelow : conditionState.NodesBelowNextOccurrence :=
    (Detail.inferExprFuel_occurrenceBoundExtends conditionSuccess
      ).nodesBelowNextOccurrence allocatedBelow
  have thenBelow : thenResult.state.NodesBelowNextOccurrence :=
    (Detail.inferStatementsFuel_occurrenceBoundExtends thenSuccess
      ).nodesBelowNextOccurrence conditionBelow
  have elseInputBelow : (thenResult.state.restoreLexicalScope
      conditionState.lexicalScope).NodesBelowNextOccurrence := by
    exact (Frontend.SourceInference.State.OccurrenceBoundExtends.of_nodes_eq_nextOccurrence_eq
      rfl rfl).nodesBelowNextOccurrence thenBelow
  have elseInputToElseResult : TypingSourceExtends
      (((thenResult.state.restoreLexicalScope
        conditionState.lexicalScope).toTypedSource roots))
      (elseResult.state.toTypedSource roots) :=
    inferStatementsFuel_success_typingSourceExtends elseSuccess
      elseInputBelow roots
  have thenToElseInput : TypingSourceExtends
      (thenResult.state.toTypedSource roots)
      ((thenResult.state.restoreLexicalScope
        conditionState.lexicalScope).toTypedSource roots) :=
    ⟨rfl, List.prefix_rfl⟩
  have elseProvenance :=
    child_provenance_through_restore_record elseResult.state
      conditionState.lexicalScope (.statement {
        id
        span := statement.span
        type := if thenResult.sawReturn && elseResult.sawReturn then
          elseResult.state.resolve expectedReturn
        else
          .unit
        form := .ifThen inferredCondition.id thenResult.statements
          (some elseResult.statements)
      }) roots
  have elseToParent : TypingSourceExtends
      (elseResult.state.toTypedSource roots)
      (result.state.toTypedSource roots) := by
    simpa [resultEq] using elseProvenance.1
  have thenToParent : TypingSourceExtends
      (thenResult.state.toTypedSource roots)
      (result.state.toTypedSource roots) :=
    TypingSourceExtends.trans thenToElseInput
      (TypingSourceExtends.trans elseInputToElseResult elseToParent)
  have thenIntegerSubset : thenResult.state.integerPatterns ⊆
      elseResult.state.integerPatterns := by
    simpa [Frontend.SourceInference.State.restoreLexicalScope] using
      (Detail.inferStatementsFuel_integerPatterns_subset elseSuccess)
  have thenRequirementSubset : thenResult.state.requirements ⊆
      elseResult.state.requirements := by
    simpa [Frontend.SourceInference.State.restoreLexicalScope] using
      (Detail.inferStatementsFuel_requirements_subset elseSuccess)
  have elseIntegerSubset : elseResult.state.integerPatterns ⊆
      result.state.integerPatterns := by
    simp [resultEq]
  have elseRequirementSubset : elseResult.state.requirements ⊆
      result.state.requirements := by
    simp [resultEq]
  exact ⟨conditionState, thenResult, elseResult,
    ⟨inferredCondition, conditionSuccess⟩, thenSuccess, elseSuccess,
    conditionBelow, elseInputBelow, thenToParent, elseToParent,
    List.Subset.trans thenIntegerSubset elseIntegerSubset,
    elseIntegerSubset,
    List.Subset.trans thenRequirementSubset elseRequirementSubset,
    elseRequirementSubset⟩

/-- The initializer, body, and post-item traversals of a successful `for`
all embed in the final statement source.  Their initial occurrence bounds
follow the actual source-ordered execution chain. -/
theorem inferStatementFuel_success_forLoop_child_provenance
    {fuel : Nat}
    {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {headerSpan : Syntax.SourceSpan}
    {initializer post : List Syntax.ForItem} {condition : Syntax.Expr}
    {body : Syntax.Block} {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    (statementEq : statement.value =
      .forLoop headerSpan initializer condition post body)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (roots : List NodeId := []) :
    ∃ initializerResult inferredCondition conditionState bodyResult postResult,
      Detail.inferForItemsFuel fuel inferenceContext initializer allocated =
        .ok initializerResult ∧
      Detail.inferExprFuel fuel inferenceContext condition (some .bool)
        initializerResult.state = .ok (inferredCondition, conditionState) ∧
      Detail.inferStatementsFuel fuel
        { inferenceContext with
          loopDepth := inferenceContext.loopDepth + 1 }
        body.value expectedReturn conditionState = .ok bodyResult ∧
      Detail.inferForItemsFuel fuel
        { inferenceContext with
          loopDepth := inferenceContext.loopDepth + 1 }
        post (bodyResult.state.restoreLexicalScope
          initializerResult.state.lexicalScope) = .ok postResult ∧
      ChildStateProvenance allocated initializerResult.state result.state roots ∧
      ChildStateProvenance conditionState bodyResult.state result.state roots ∧
      ChildStateProvenance
        (bodyResult.state.restoreLexicalScope
          initializerResult.state.lexicalScope)
        postResult.state result.state roots := by
  obtain ⟨initializerResult, inferredCondition, conditionState, bodyResult,
    postResult, initializerSuccess, conditionSuccess, bodySuccess,
    postSuccess, resultEq, _contains⟩ :=
    inferStatementFuel_success_forLoop_facts statementEq allocationEq
      success roots
  have allocatedBelow : allocated.NodesBelowNextOccurrence := by
    have bound :=
      Frontend.SourceInference.State.allocateStatementId_preserves_nodesBelowNextOccurrence
        initial initialBelow
    have eq : (initial.allocateStatementId).2 = allocated :=
      congrArg Prod.snd allocationEq
    simpa [eq] using bound
  have initializerBelow :
      initializerResult.state.NodesBelowNextOccurrence :=
    (Detail.inferForItemsFuel_occurrenceBoundExtends initializerSuccess
      ).nodesBelowNextOccurrence allocatedBelow
  have conditionBelow : conditionState.NodesBelowNextOccurrence :=
    (Detail.inferExprFuel_occurrenceBoundExtends conditionSuccess
      ).nodesBelowNextOccurrence initializerBelow
  have bodyBelow : bodyResult.state.NodesBelowNextOccurrence :=
    (Detail.inferStatementsFuel_occurrenceBoundExtends bodySuccess
      ).nodesBelowNextOccurrence conditionBelow
  let postInput := bodyResult.state.restoreLexicalScope
    initializerResult.state.lexicalScope
  have postInputBelow : postInput.NodesBelowNextOccurrence :=
    (Frontend.SourceInference.State.OccurrenceBoundExtends.of_nodes_eq_nextOccurrence_eq
      rfl rfl).nodesBelowNextOccurrence bodyBelow
  have initializerToCondition : TypingSourceExtends
      (initializerResult.state.toTypedSource roots)
      (conditionState.toTypedSource roots) :=
    inferExprFuel_success_typingSourceExtends conditionSuccess
      initializerBelow roots
  have conditionToBody : TypingSourceExtends
      (conditionState.toTypedSource roots)
      (bodyResult.state.toTypedSource roots) :=
    inferStatementsFuel_success_typingSourceExtends bodySuccess
      conditionBelow roots
  have bodyToPostInput : TypingSourceExtends
      (bodyResult.state.toTypedSource roots)
      (postInput.toTypedSource roots) :=
    ⟨rfl, List.prefix_rfl⟩
  have postInputToPost : TypingSourceExtends
      (postInput.toTypedSource roots)
      (postResult.state.toTypedSource roots) :=
    inferForItemsFuel_success_typingSourceExtends postSuccess
      postInputBelow roots
  have postProvenance :=
    child_provenance_through_restore_record postResult.state
      allocated.lexicalScope (.statement {
        id
        span := statement.span
        type := .unit
        form := .forLoop initializerResult.items inferredCondition.id
          postResult.items bodyResult.statements
      }) roots
  have postToParent : TypingSourceExtends
      (postResult.state.toTypedSource roots)
      (result.state.toTypedSource roots) := by
    simpa [resultEq] using postProvenance.1
  have bodyToParent : TypingSourceExtends
      (bodyResult.state.toTypedSource roots)
      (result.state.toTypedSource roots) :=
    TypingSourceExtends.trans bodyToPostInput
      (TypingSourceExtends.trans postInputToPost postToParent)
  have initializerToParent : TypingSourceExtends
      (initializerResult.state.toTypedSource roots)
      (result.state.toTypedSource roots) :=
    TypingSourceExtends.trans initializerToCondition
      (TypingSourceExtends.trans conditionToBody bodyToParent)
  have initializerIntToCondition :=
    Detail.inferExprFuel_integerPatterns_subset conditionSuccess
  have conditionIntToBody :=
    Detail.inferStatementsFuel_integerPatterns_subset bodySuccess
  have bodyIntToPost : bodyResult.state.integerPatterns ⊆
      postResult.state.integerPatterns := by
    simpa [postInput, Frontend.SourceInference.State.restoreLexicalScope]
      using (Detail.inferForItemsFuel_integerPatterns_subset postSuccess)
  have postIntToParent : postResult.state.integerPatterns ⊆
      result.state.integerPatterns := by
    simp [resultEq]
  have initializerReqToCondition :=
    Detail.inferExprFuel_requirements_subset conditionSuccess
  have conditionReqToBody :=
    Detail.inferStatementsFuel_requirements_subset bodySuccess
  have bodyReqToPost : bodyResult.state.requirements ⊆
      postResult.state.requirements := by
    simpa [postInput, Frontend.SourceInference.State.restoreLexicalScope]
      using (Detail.inferForItemsFuel_requirements_subset postSuccess)
  have postReqToParent : postResult.state.requirements ⊆
      result.state.requirements := by
    simp [resultEq]
  refine ⟨initializerResult, inferredCondition, conditionState, bodyResult,
    postResult, initializerSuccess, conditionSuccess, bodySuccess, postSuccess,
    ?_, ?_, ?_⟩
  · exact ⟨allocatedBelow, initializerToParent,
      List.Subset.trans initializerIntToCondition
        (List.Subset.trans conditionIntToBody
          (List.Subset.trans bodyIntToPost postIntToParent)),
      List.Subset.trans initializerReqToCondition
        (List.Subset.trans conditionReqToBody
          (List.Subset.trans bodyReqToPost postReqToParent))⟩
  · exact ⟨conditionBelow, bodyToParent,
      List.Subset.trans bodyIntToPost postIntToParent,
      List.Subset.trans bodyReqToPost postReqToParent⟩
  · exact ⟨postInputBelow, postToParent, postIntToParent, postReqToParent⟩

/-- Statement-list sequencing under a fixed ambient typed source only needs
one-statement soundness at strictly smaller fuel.  In contrast to the
unbounded callback variant, this premise is suitable for a mutual fuel
induction with `inferStatementFuel`. -/
theorem inferStatementsFuel_success_statementsHaveType_under_ambient_bounded
    (invariant : Frontend.SourceInference.State →
      SourceSemantics.Context → Prop)
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statements : List Syntax.Statement}
    {expectedReturn : TypeSystem.Ty}
    {state : Frontend.SourceInference.State} {result : Detail.BlockResult}
    {evidenceState : Frontend.SourceInference.State}
    {ambientSource : TypedSource} {control : ControlContext}
    {substitution : TypeSystem.Substitution}
    {semanticContext : SourceSemantics.Context}
    (roots : List NodeId := [])
    (initialInvariant : invariant state semanticContext)
    (initialBelow : state.NodesBelowNextOccurrence)
    (resultExtension : TypingSourceExtends
      ((result.state.toTypedSource roots).applySubstitution substitution)
      ambientSource)
    (integerPatternsSubset :
      result.state.integerPatterns ⊆ evidenceState.integerPatterns)
    (requirementsSubset :
      result.state.requirements ⊆ evidenceState.requirements)
    (statementSound :
      ∀ {childFuel : Nat} {input : Frontend.SourceInference.State}
        {inputContext : SourceSemantics.Context}
        {statement : Syntax.Statement} {head : Detail.StatementResult},
        childFuel < fuel →
        invariant input inputContext →
        Detail.inferStatementFuel childFuel inferenceContext statement
          expectedReturn input = .ok head →
        TypingSourceExtends
          ((head.state.toTypedSource roots).applySubstitution substitution)
          ambientSource →
        head.state.integerPatterns ⊆ evidenceState.integerPatterns →
        head.state.requirements ⊆ evidenceState.requirements →
        ∃ outputContext facts,
          invariant head.state outputContext ∧
          StatementHasType
            ((head.state.toTypedSource roots).applySubstitution substitution)
            control inputContext head.id outputContext facts ∧
          StatementResultMatchesFactsAfterSubstitution substitution head facts)
    (success : Detail.inferStatementsFuel fuel inferenceContext statements
      expectedReturn state = .ok result) :
    ∃ finalContext facts,
      invariant result.state finalContext ∧
      StatementsHaveType ambientSource control semanticContext
        result.statements finalContext facts ∧
      BlockResultMatchesFactsAfterSubstitution substitution result facts := by
  induction fuel generalizing statements state semanticContext result with
  | zero =>
      simp [Detail.inferStatementsFuel] at success
  | succ fuel induction =>
      cases statements with
      | nil =>
          have resultEq := inferStatementsFuel_success_nil_facts success
          subst result
          exact ⟨semanticContext, .empty, initialInvariant,
            .nil control semanticContext,
            BlockResultMatchesFactsAfterSubstitution.empty substitution state⟩
      | cons statement rest =>
          cases rest with
          | nil =>
              obtain ⟨head, headSuccess, resultEq⟩ :=
                inferStatementsFuel_success_singleton_facts success
              subst result
              obtain ⟨finalContext, headFacts, finalInvariant, headTyping,
                  headMatches⟩ :=
                statementSound (Nat.lt_succ_self fuel) initialInvariant
                  headSuccess resultExtension integerPatternsSubset
                  requirementsSubset
              have headTypingAmbient :=
                StatementHasType.weakenSource resultExtension headTyping
              exact ⟨finalContext, .singleton headFacts, finalInvariant,
                .singleton headTypingAmbient,
                BlockResultMatchesFactsAfterSubstitution.singleton headMatches⟩
          | cons next rest =>
              obtain ⟨head, tail, headSuccess, tailSuccess, resultEq⟩ :=
                inferStatementsFuel_success_cons_facts success
              subst result
              have headBelow : head.state.NodesBelowNextOccurrence :=
                (Detail.inferStatementFuel_occurrenceBoundExtends headSuccess
                  ).nodesBelowNextOccurrence initialBelow
              have headToTail : TypingSourceExtends
                  ((head.state.toTypedSource roots).applySubstitution
                    substitution)
                  ((tail.state.toTypedSource roots).applySubstitution
                    substitution) :=
                (inferStatementsFuel_success_typingSourceExtends tailSuccess
                  headBelow roots).applySubstitution substitution
              have headExtension : TypingSourceExtends
                  ((head.state.toTypedSource roots).applySubstitution
                    substitution)
                  ambientSource :=
                TypingSourceExtends.trans headToTail resultExtension
              have headIntegerPatternsSubset :
                  head.state.integerPatterns ⊆
                    evidenceState.integerPatterns :=
                List.Subset.trans
                  (Detail.inferStatementsFuel_integerPatterns_subset
                    tailSuccess)
                  integerPatternsSubset
              have headRequirementsSubset :
                  head.state.requirements ⊆ evidenceState.requirements :=
                List.Subset.trans
                  (Detail.inferStatementsFuel_requirements_subset tailSuccess)
                  requirementsSubset
              obtain ⟨middleContext, headFacts, middleInvariant, headTyping,
                  headMatches⟩ :=
                statementSound (Nat.lt_succ_self fuel) initialInvariant
                  headSuccess headExtension headIntegerPatternsSubset
                  headRequirementsSubset
              obtain ⟨finalContext, tailFacts, finalInvariant, tailTyping,
                  tailMatches⟩ :=
                induction (statements := next :: rest)
                  (state := head.state) (result := tail)
                  (semanticContext := middleContext)
                  middleInvariant headBelow resultExtension
                  integerPatternsSubset requirementsSubset
                  (fun childBound childInvariant childSuccess childExtension
                    childIntegerPatternsSubset childRequirementsSubset =>
                    statementSound (Nat.lt_trans childBound
                      (Nat.lt_succ_self fuel)) childInvariant childSuccess
                      childExtension childIntegerPatternsSubset
                      childRequirementsSubset)
                  tailSuccess
              have headTypingAmbient :=
                StatementHasType.weakenSource headExtension headTyping
              obtain ⟨tailHead, tailRest, tailStatementsEq⟩ :=
                inferStatementsFuel_success_statements_eq_cons tailSuccess
              have sequenceTyping : StatementsHaveType ambientSource control
                  semanticContext (head.id :: tail.statements) finalContext
                  (.cons headFacts tailFacts) := by
                rw [tailStatementsEq]
                exact .cons headTypingAmbient
                  (by simpa [tailStatementsEq] using tailTyping)
              exact ⟨finalContext, .cons headFacts tailFacts, finalInvariant,
                sequenceTyping,
                BlockResultMatchesFactsAfterSubstitution.cons headMatches
                  tailMatches⟩

/-- The scoped-block constructor closes its recursive body callback using
bounded soundness of the statements inside that body.  No typing premise for
an unrelated child block is required. -/
theorem inferStatementFuel_success_block_sound_bounded
    {fuel : Nat}
    {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {body : List Syntax.Statement}
    {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    {outer : TypeSystem.Substitution} {control : ControlContext}
    {target : SourceSemantics.Context}
    (statementEq : statement.value = .block body)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (invariant : ActiveLocalContextInvariant initial outer target)
    (roots : List NodeId := [])
    (childStatementSound :
      ∀ {childFuel : Nat} {input : Frontend.SourceInference.State}
        {inputContext : SourceSemantics.Context}
        {childStatement : Syntax.Statement}
        {head : Detail.StatementResult},
        childFuel < fuel →
        ActiveLocalContextInvariant input outer inputContext →
        Detail.inferStatementFuel childFuel inferenceContext childStatement
          expectedReturn input = .ok head →
        TypingSourceExtends
          ((head.state.toTypedSource roots).applySubstitution outer)
          ((result.state.toTypedSource roots).applySubstitution outer) →
        head.state.integerPatterns ⊆ result.state.integerPatterns →
        head.state.requirements ⊆ result.state.requirements →
        ∃ outputContext facts,
          ActiveLocalContextInvariant head.state outer outputContext ∧
          StatementHasType
            ((head.state.toTypedSource roots).applySubstitution outer)
            control inputContext head.id outputContext facts ∧
          StatementResultMatchesFactsAfterSubstitution outer head facts) :
    ∃ facts,
      ActiveLocalContextInvariant result.state outer target ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution outer)
        control target result.id target facts ∧
      StatementResultMatchesFactsAfterSubstitution outer result facts := by
  obtain ⟨bodyResult, bodySuccess, allocatedBelow, bodyExtension,
    bodyIntegerPatternsSubset, bodyRequirementsSubset⟩ :=
    inferStatementFuel_success_block_child_provenance statementEq allocationEq
      success initialBelow roots
  have allocatedInvariant : ActiveLocalContextInvariant allocated outer target :=
    invariant.allocateStatementId allocationEq
  have bodyTyping :=
    inferStatementsFuel_success_statementsHaveType_under_ambient_bounded
      (fun state context => ActiveLocalContextInvariant state outer context)
      (roots := roots) allocatedInvariant allocatedBelow
      (bodyExtension.applySubstitution outer)
      bodyIntegerPatternsSubset bodyRequirementsSubset
      childStatementSound bodySuccess
  apply inferStatementFuel_success_block_sound statementEq allocationEq
    success invariant roots
  intro childResult childSuccess
  have childEq : childResult = bodyResult := by
    rw [bodySuccess] at childSuccess
    exact (Except.ok.inj childSuccess).symm
  subst childResult
  exact bodyTyping

/-- Conditional-without-else soundness closes its actual then-body using
bounded statement-list sequencing. -/
theorem inferStatementFuel_success_ifWithoutElse_sound_bounded
    {fuel : Nat}
    {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {condition : Syntax.Expr}
    {thenBody : Syntax.Block} {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    {outer : TypeSystem.Substitution} {target : SourceSemantics.Context}
    (statementEq : statement.value = .ifThen condition thenBody none)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (signatureFormation :
      Frontend.ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ signature ∈ inferenceContext.signatures.functions,
      signature.scheme.body = .function
        (TypeSystem.Ty.productMany signature.parameterTypes)
        (TypeSystem.Ty.productMany signature.returnTypes))
    (ready : initial.InferenceReady)
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (invariant : ActiveLocalContextInvariant initial outer target)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (outerExtension : outer.SemanticallyExtends
      result.state.inference.substitution)
    (roots : List NodeId := [])
    (conditionSound :
      ∀ {inferredCondition : InferredExpression}
        {conditionState : Frontend.SourceInference.State},
        Detail.inferExprFuel fuel inferenceContext condition (some .bool)
          allocated = .ok (inferredCondition, conditionState) →
        ExpressionHasType
          ((result.state.toTypedSource roots).applySubstitution outer)
          target inferredCondition.id (outer.apply inferredCondition.type))
    (childStatementSound :
      ∀ {childFuel : Nat} {input : Frontend.SourceInference.State}
        {inputContext : SourceSemantics.Context}
        {childStatement : Syntax.Statement}
        {head : Detail.StatementResult},
        childFuel < fuel →
        ActiveLocalContextInvariant input outer inputContext →
        Detail.inferStatementFuel childFuel inferenceContext childStatement
          expectedReturn input = .ok head →
        TypingSourceExtends
          ((head.state.toTypedSource roots).applySubstitution outer)
          ((result.state.toTypedSource roots).applySubstitution outer) →
        head.state.integerPatterns ⊆ result.state.integerPatterns →
        head.state.requirements ⊆ result.state.requirements →
        ∃ outputContext facts,
          ActiveLocalContextInvariant head.state outer outputContext ∧
          StatementHasType
            ((head.state.toTypedSource roots).applySubstitution outer) {
              returnType := outer.apply expectedReturn
              loopDepth := inferenceContext.loopDepth
            } inputContext head.id outputContext facts ∧
          StatementResultMatchesFactsAfterSubstitution outer head facts) :
    ∃ facts,
      ActiveLocalContextInvariant result.state outer target ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution outer) {
          returnType := outer.apply expectedReturn
          loopDepth := inferenceContext.loopDepth
        } target result.id target facts ∧
      StatementResultMatchesFactsAfterSubstitution outer result facts := by
  have allocatedInvariant : ActiveLocalContextInvariant allocated outer target :=
    invariant.allocateStatementId allocationEq
  have allocatedReady : allocated.InferenceReady := by
    have preserved :=
      Frontend.SourceInference.State.InferenceReady.allocateStatementId ready
    have finalEq : (initial.allocateStatementId).2 = allocated :=
      congrArg Prod.snd allocationEq
    simpa [finalEq] using preserved
  have allocatedReturnBelow :
      expectedReturn.VariablesBelow allocated.inference.next := by
    have finalEq : (initial.allocateStatementId).2 = allocated :=
      congrArg Prod.snd allocationEq
    rw [← finalEq]
    exact returnBelow
  obtain ⟨inferredCondition, conditionState, thenResult, conditionSuccess,
    thenSuccess, resultEq, contains⟩ :=
    inferStatementFuel_success_ifWithoutElse_facts statementEq allocationEq
      success roots
  have conditionProperties :=
    Detail.inferExprFuel_inferenceProperties allocatedReady signatureFormation
      functionsCanonical (by
        intro expected member
        simp only [Option.mem_def] at member
        injection member with expectedEq
        subst expected
        simp [TypeSystem.Ty.bool]) conditionSuccess
  have conditionInvariant :
      ActiveLocalContextInvariant conditionState outer target :=
    allocatedInvariant.inferExprFuel conditionSuccess
  have conditionTyping := conditionSound conditionSuccess
  have conditionReturnBelow :
      expectedReturn.VariablesBelow conditionState.inference.next :=
    allocatedReturnBelow.weaken conditionProperties.1.next_le
  have thenProperties :=
    Detail.inferStatementsFuel_inferenceProperties conditionProperties.2.1
      signatureFormation functionsCanonical conditionReturnBelow thenSuccess
  obtain ⟨_actualConditionState, _actualThenResult,
    ⟨_actualCondition, _actualConditionSuccess⟩, _actualThenSuccess,
    conditionBelow, thenSourceExtension, thenIntegerPatternsSubset,
    thenRequirementsSubset⟩ :=
    inferStatementFuel_success_ifWithoutElse_child_provenance statementEq
      allocationEq success initialBelow roots
  -- The branch provenance theorem and the operational facts select the same
  -- deterministic condition and then-body results.
  have conditionStateEq : _actualConditionState = conditionState := by
    rw [conditionSuccess] at _actualConditionSuccess
    exact (congrArg Prod.snd (Except.ok.inj _actualConditionSuccess)).symm
  subst _actualConditionState
  have thenResultEq : _actualThenResult = thenResult := by
    rw [thenSuccess] at _actualThenSuccess
    exact (Except.ok.inj _actualThenSuccess).symm
  subst _actualThenResult
  have thenTyping :=
    inferStatementsFuel_success_statementsHaveType_under_ambient_bounded
      (fun state context => ActiveLocalContextInvariant state outer context)
      (roots := roots) conditionInvariant conditionBelow
      (thenSourceExtension.applySubstitution outer)
      thenIntegerPatternsSubset thenRequirementsSubset
      childStatementSound thenSuccess
  obtain ⟨thenFinal, thenFacts, _thenInvariant, thenBodyTyping,
    thenAgreement⟩ := thenTyping
  subst result
  have thenExtension : outer.SemanticallyExtends
      thenResult.state.inference.substitution := by
    change outer.SemanticallyExtends
      thenResult.state.inference.substitution at outerExtension
    exact outerExtension
  have conditionExtension : outer.SemanticallyExtends
      conditionState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans thenExtension
      thenProperties.1.substitution_extends
  have conditionEq : outer.apply inferredCondition.type = .bool := by
    simpa using Detail.inferExprFuel_expected_type_apply_eq conditionSuccess
      conditionExtension
  refine ⟨{
      type := .unit
      hasValue := false
      sawReturn := false
      control := thenFacts.control.branches (.ordinary .unit)
    }, conditionInvariant.restoreLexicalScope_recordNode _, ?_, ?_⟩
  · exact ifWithoutElseStatementHasType_afterSubstitution contains
      conditionTyping conditionEq thenBodyTyping
  · exact StatementResultMatchesFactsAfterSubstitution.ifWithoutElse outer
      thenFacts id _

/-- `while` soundness closes the actual loop body at smaller fuel. -/
theorem inferStatementFuel_success_whileLoop_sound_bounded
    {fuel : Nat}
    {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {condition : Syntax.Expr}
    {body : Syntax.Block} {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    {outer : TypeSystem.Substitution} {target : SourceSemantics.Context}
    (statementEq : statement.value = .whileLoop condition body)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (signatureFormation :
      Frontend.ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ signature ∈ inferenceContext.signatures.functions,
      signature.scheme.body = .function
        (TypeSystem.Ty.productMany signature.parameterTypes)
        (TypeSystem.Ty.productMany signature.returnTypes))
    (ready : initial.InferenceReady)
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (invariant : ActiveLocalContextInvariant initial outer target)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (outerExtension : outer.SemanticallyExtends
      result.state.inference.substitution)
    (roots : List NodeId := [])
    (conditionSound :
      ∀ {inferredCondition : InferredExpression}
        {conditionState : Frontend.SourceInference.State},
        Detail.inferExprFuel fuel inferenceContext condition (some .bool)
          allocated = .ok (inferredCondition, conditionState) →
        ExpressionHasType
          ((result.state.toTypedSource roots).applySubstitution outer)
          target inferredCondition.id (outer.apply inferredCondition.type))
    (childStatementSound :
      ∀ {childFuel : Nat} {input : Frontend.SourceInference.State}
        {inputContext : SourceSemantics.Context}
        {childStatement : Syntax.Statement}
        {head : Detail.StatementResult},
        childFuel < fuel →
        ActiveLocalContextInvariant input outer inputContext →
        Detail.inferStatementFuel childFuel
          { inferenceContext with
            loopDepth := inferenceContext.loopDepth + 1 }
          childStatement expectedReturn input = .ok head →
        TypingSourceExtends
          ((head.state.toTypedSource roots).applySubstitution outer)
          ((result.state.toTypedSource roots).applySubstitution outer) →
        head.state.integerPatterns ⊆ result.state.integerPatterns →
        head.state.requirements ⊆ result.state.requirements →
        ∃ outputContext facts,
          ActiveLocalContextInvariant head.state outer outputContext ∧
          StatementHasType
            ((head.state.toTypedSource roots).applySubstitution outer)
            (({
              returnType := outer.apply expectedReturn
              loopDepth := inferenceContext.loopDepth
            } : ControlContext).enterLoop)
            inputContext head.id outputContext facts ∧
          StatementResultMatchesFactsAfterSubstitution outer head facts) :
    ∃ facts,
      ActiveLocalContextInvariant result.state outer target ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution outer) {
          returnType := outer.apply expectedReturn
          loopDepth := inferenceContext.loopDepth
        } target result.id target facts ∧
      StatementResultMatchesFactsAfterSubstitution outer result facts := by
  have allocatedInvariant : ActiveLocalContextInvariant allocated outer target :=
    invariant.allocateStatementId allocationEq
  have allocatedReady : allocated.InferenceReady := by
    have preserved :=
      Frontend.SourceInference.State.InferenceReady.allocateStatementId ready
    have finalEq : (initial.allocateStatementId).2 = allocated :=
      congrArg Prod.snd allocationEq
    simpa [finalEq] using preserved
  have allocatedReturnBelow :
      expectedReturn.VariablesBelow allocated.inference.next := by
    have finalEq : (initial.allocateStatementId).2 = allocated :=
      congrArg Prod.snd allocationEq
    rw [← finalEq]
    exact returnBelow
  obtain ⟨inferredCondition, conditionState, bodyResult, conditionSuccess,
    bodySuccess, resultEq, contains⟩ :=
    inferStatementFuel_success_whileLoop_facts statementEq allocationEq
      success roots
  have conditionProperties :=
    Detail.inferExprFuel_inferenceProperties allocatedReady signatureFormation
      functionsCanonical (by
        intro expected member
        simp only [Option.mem_def] at member
        injection member with expectedEq
        subst expected
        simp [TypeSystem.Ty.bool]) conditionSuccess
  have conditionInvariant :
      ActiveLocalContextInvariant conditionState outer target :=
    allocatedInvariant.inferExprFuel conditionSuccess
  have conditionTyping := conditionSound conditionSuccess
  have conditionReturnBelow :
      expectedReturn.VariablesBelow conditionState.inference.next :=
    allocatedReturnBelow.weaken conditionProperties.1.next_le
  have bodyProperties :=
    Detail.inferStatementsFuel_inferenceProperties
      (context := {
        inferenceContext with
        loopDepth := inferenceContext.loopDepth + 1
      }) conditionProperties.2.1 signatureFormation functionsCanonical
      conditionReturnBelow bodySuccess
  obtain ⟨_actualConditionState, _actualBodyResult,
    ⟨_actualCondition, _actualConditionSuccess⟩, _actualBodySuccess,
    conditionBelow, bodySourceExtension, bodyIntegerPatternsSubset,
    bodyRequirementsSubset⟩ :=
    inferStatementFuel_success_whileLoop_child_provenance statementEq
      allocationEq success initialBelow roots
  have conditionStateEq : _actualConditionState = conditionState := by
    rw [conditionSuccess] at _actualConditionSuccess
    exact (congrArg Prod.snd (Except.ok.inj _actualConditionSuccess)).symm
  subst _actualConditionState
  have bodyResultEq : _actualBodyResult = bodyResult := by
    rw [bodySuccess] at _actualBodySuccess
    exact (Except.ok.inj _actualBodySuccess).symm
  subst _actualBodyResult
  obtain ⟨bodyFinal, bodyFacts, _bodyInvariant, bodyTyping,
    bodyAgreement⟩ :=
    inferStatementsFuel_success_statementsHaveType_under_ambient_bounded
      (fun state context => ActiveLocalContextInvariant state outer context)
      (roots := roots) conditionInvariant conditionBelow
      (bodySourceExtension.applySubstitution outer)
      bodyIntegerPatternsSubset bodyRequirementsSubset
      childStatementSound bodySuccess
  subst result
  have bodyExtension : outer.SemanticallyExtends
      bodyResult.state.inference.substitution := by
    change outer.SemanticallyExtends
      bodyResult.state.inference.substitution at outerExtension
    exact outerExtension
  have conditionExtension : outer.SemanticallyExtends
      conditionState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans bodyExtension
      bodyProperties.1.substitution_extends
  have conditionEq : outer.apply inferredCondition.type = .bool := by
    simpa using Detail.inferExprFuel_expected_type_apply_eq conditionSuccess
      conditionExtension
  refine ⟨{
      type := .unit
      hasValue := false
      sawReturn := false
      control := .loop bodyFacts.control
    }, conditionInvariant.restoreLexicalScope_recordNode _, ?_, ?_⟩
  · exact whileLoopStatementHasType_afterSubstitution contains conditionTyping
      conditionEq bodyTyping
  · exact StatementResultMatchesFactsAfterSubstitution.whileLoop outer
      bodyFacts id _

/-- Both actual branches of a successful `if/else` are typed by bounded
statement-list induction in their source-ordered final state. -/
theorem inferStatementFuel_success_ifWithElse_sound_bounded
    {fuel : Nat}
    {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {condition : Syntax.Expr}
    {thenBody elseBody : Syntax.Block}
    {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    {outer : TypeSystem.Substitution} {target : SourceSemantics.Context}
    (statementEq : statement.value =
      .ifThen condition thenBody (some elseBody))
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (signatureFormation :
      Frontend.ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ signature ∈ inferenceContext.signatures.functions,
      signature.scheme.body = .function
        (TypeSystem.Ty.productMany signature.parameterTypes)
        (TypeSystem.Ty.productMany signature.returnTypes))
    (ready : initial.InferenceReady)
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (invariant : ActiveLocalContextInvariant initial outer target)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (outerExtension : outer.SemanticallyExtends
      result.state.inference.substitution)
    (roots : List NodeId := [])
    (conditionSound :
      ∀ {inferredCondition : InferredExpression}
        {conditionState : Frontend.SourceInference.State},
        Detail.inferExprFuel fuel inferenceContext condition (some .bool)
          allocated = .ok (inferredCondition, conditionState) →
        ExpressionHasType
          ((result.state.toTypedSource roots).applySubstitution outer)
          target inferredCondition.id (outer.apply inferredCondition.type))
    (childStatementSound :
      ∀ {childFuel : Nat} {input : Frontend.SourceInference.State}
        {inputContext : SourceSemantics.Context}
        {childStatement : Syntax.Statement}
        {head : Detail.StatementResult},
        childFuel < fuel →
        ActiveLocalContextInvariant input outer inputContext →
        Detail.inferStatementFuel childFuel inferenceContext childStatement
          expectedReturn input = .ok head →
        TypingSourceExtends
          ((head.state.toTypedSource roots).applySubstitution outer)
          ((result.state.toTypedSource roots).applySubstitution outer) →
        head.state.integerPatterns ⊆ result.state.integerPatterns →
        head.state.requirements ⊆ result.state.requirements →
        ∃ outputContext facts,
          ActiveLocalContextInvariant head.state outer outputContext ∧
          StatementHasType
            ((head.state.toTypedSource roots).applySubstitution outer) {
              returnType := outer.apply expectedReturn
              loopDepth := inferenceContext.loopDepth
            } inputContext head.id outputContext facts ∧
          StatementResultMatchesFactsAfterSubstitution outer head facts) :
    ∃ facts,
      ActiveLocalContextInvariant result.state outer target ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution outer) {
          returnType := outer.apply expectedReturn
          loopDepth := inferenceContext.loopDepth
        } target result.id target facts ∧
      StatementResultMatchesFactsAfterSubstitution outer result facts := by
  have allocatedInvariant : ActiveLocalContextInvariant allocated outer target :=
    invariant.allocateStatementId allocationEq
  have allocatedReady : allocated.InferenceReady := by
    have preserved :=
      Frontend.SourceInference.State.InferenceReady.allocateStatementId ready
    have finalEq : (initial.allocateStatementId).2 = allocated :=
      congrArg Prod.snd allocationEq
    simpa [finalEq] using preserved
  have allocatedReturnBelow :
      expectedReturn.VariablesBelow allocated.inference.next := by
    have finalEq : (initial.allocateStatementId).2 = allocated :=
      congrArg Prod.snd allocationEq
    rw [← finalEq]
    exact returnBelow
  obtain ⟨inferredCondition, conditionState, thenResult, elseResult,
    conditionSuccess, thenSuccess, elseSuccess, resultEq, contains⟩ :=
    inferStatementFuel_success_ifWithElse_facts statementEq allocationEq
      success roots
  have conditionProperties :=
    Detail.inferExprFuel_inferenceProperties allocatedReady signatureFormation
      functionsCanonical (by
        intro expected member
        simp only [Option.mem_def] at member
        injection member with expectedEq
        subst expected
        simp [TypeSystem.Ty.bool]) conditionSuccess
  have conditionInvariant :
      ActiveLocalContextInvariant conditionState outer target :=
    allocatedInvariant.inferExprFuel conditionSuccess
  have conditionTyping := conditionSound conditionSuccess
  have conditionReturnBelow :
      expectedReturn.VariablesBelow conditionState.inference.next :=
    allocatedReturnBelow.weaken conditionProperties.1.next_le
  have thenProperties :=
    Detail.inferStatementsFuel_inferenceProperties conditionProperties.2.1
      signatureFormation functionsCanonical conditionReturnBelow thenSuccess
  obtain ⟨_actualConditionState, _actualThenResult, _actualElseResult,
    ⟨_actualCondition, _actualConditionSuccess⟩, _actualThenSuccess,
    _actualElseSuccess, conditionBelow, elseInputBelow,
    thenSourceExtension, elseSourceExtension,
    thenIntegerPatternsSubset, elseIntegerPatternsSubset,
    thenRequirementsSubset, elseRequirementsSubset⟩ :=
    inferStatementFuel_success_ifWithElse_child_provenance statementEq
      allocationEq success initialBelow roots
  have conditionStateEq : _actualConditionState = conditionState := by
    rw [conditionSuccess] at _actualConditionSuccess
    exact (congrArg Prod.snd (Except.ok.inj _actualConditionSuccess)).symm
  subst _actualConditionState
  have thenResultEq : _actualThenResult = thenResult := by
    rw [thenSuccess] at _actualThenSuccess
    exact (Except.ok.inj _actualThenSuccess).symm
  subst _actualThenResult
  have elseResultEq : _actualElseResult = elseResult := by
    rw [elseSuccess] at _actualElseSuccess
    exact (Except.ok.inj _actualElseSuccess).symm
  subst _actualElseResult
  obtain ⟨thenFinal, thenFacts, _thenInvariant, thenTyping,
    thenAgreement⟩ :=
    inferStatementsFuel_success_statementsHaveType_under_ambient_bounded
      (fun state context => ActiveLocalContextInvariant state outer context)
      (roots := roots) conditionInvariant conditionBelow
      (thenSourceExtension.applySubstitution outer)
      thenIntegerPatternsSubset thenRequirementsSubset
      childStatementSound thenSuccess
  have restoredProperties :=
    Frontend.SourceInference.State.restoreLexicalScope_inferenceProperties
      conditionProperties.2.1 thenProperties.1
  have elseInputInvariant : ActiveLocalContextInvariant
      (thenResult.state.restoreLexicalScope conditionState.lexicalScope) outer
      target := conditionInvariant.restoreLexicalScope
  have elseReturnBelow : expectedReturn.VariablesBelow
      (thenResult.state.restoreLexicalScope
        conditionState.lexicalScope).inference.next :=
    conditionReturnBelow.weaken restoredProperties.1.next_le
  have elseProperties :=
    Detail.inferStatementsFuel_inferenceProperties restoredProperties.2
      signatureFormation functionsCanonical elseReturnBelow elseSuccess
  obtain ⟨elseFinal, elseFacts, _elseInvariant, elseTyping,
    elseAgreement⟩ :=
    inferStatementsFuel_success_statementsHaveType_under_ambient_bounded
      (fun state context => ActiveLocalContextInvariant state outer context)
      (roots := roots) elseInputInvariant elseInputBelow
      (elseSourceExtension.applySubstitution outer)
      elseIntegerPatternsSubset elseRequirementsSubset
      childStatementSound elseSuccess
  subst result
  have elseExtension : outer.SemanticallyExtends
      elseResult.state.inference.substitution := by
    change outer.SemanticallyExtends
      elseResult.state.inference.substitution at outerExtension
    exact outerExtension
  have restoredExtension : outer.SemanticallyExtends
      (thenResult.state.restoreLexicalScope
        conditionState.lexicalScope).inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans elseExtension
      elseProperties.1.substitution_extends
  have conditionExtension : outer.SemanticallyExtends
      conditionState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans restoredExtension
      restoredProperties.1.substitution_extends
  have conditionEq : outer.apply inferredCondition.type = .bool := by
    simpa using Detail.inferExprFuel_expected_type_apply_eq conditionSuccess
      conditionExtension
  refine ⟨{
      type := if thenFacts.sawReturn && elseFacts.sawReturn then
        outer.apply expectedReturn
      else
        .unit
      hasValue := thenFacts.sawReturn && elseFacts.sawReturn
      sawReturn := thenFacts.sawReturn && elseFacts.sawReturn
      control := thenFacts.control.branches elseFacts.control
    }, conditionInvariant.restoreLexicalScope_recordNode _, ?_, ?_⟩
  · exact ifWithElseStatementHasType_afterSubstitution contains
      conditionTyping conditionEq thenTyping elseTyping thenAgreement
      elseAgreement elseExtension
  · exact StatementResultMatchesFactsAfterSubstitution.ifWithElse
      thenAgreement elseAgreement elseExtension id _

/-- A `for` statement closes its recursive body by fuel induction while its
initializer, condition, and post-items are typed in their actual local
sources and weakened to the completed statement source. -/
theorem inferStatementFuel_success_forLoop_sound_bounded
    {fuel : Nat}
    {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {headerSpan : Syntax.SourceSpan}
    {initializer post : List Syntax.ForItem} {condition : Syntax.Expr}
    {body : Syntax.Block} {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    {outer : TypeSystem.Substitution} {target : SourceSemantics.Context}
    (statementEq : statement.value =
      .forLoop headerSpan initializer condition post body)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (invariant : ActiveLocalContextInvariant initial outer target)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (roots : List NodeId := [])
    (initializerSound :
      ∀ {initializerResult : Detail.InferredForItems},
        Detail.inferForItemsFuel fuel inferenceContext initializer allocated =
          .ok initializerResult →
        ∃ loopContext,
          ActiveLocalContextInvariant initializerResult.state outer
            loopContext ∧
          ForItemsHaveType
            ((initializerResult.state.toTypedSource roots
              ).applySubstitution outer) {
              returnType := outer.apply expectedReturn
              loopDepth := inferenceContext.loopDepth
            } target
              (initializerResult.items.map
                (ForItemForm.applySubstitution outer)) loopContext)
    (conditionSound :
      ∀ {initializerResult : Detail.InferredForItems}
        {conditionState : Frontend.SourceInference.State}
        {inferredCondition : InferredExpression}
        {loopContext : SourceSemantics.Context},
        Detail.inferForItemsFuel fuel inferenceContext initializer allocated =
          .ok initializerResult →
        ActiveLocalContextInvariant initializerResult.state outer
          loopContext →
        Detail.inferExprFuel fuel inferenceContext condition (some .bool)
          initializerResult.state = .ok (inferredCondition, conditionState) →
        ExpressionHasType
          ((conditionState.toTypedSource roots).applySubstitution outer)
          loopContext inferredCondition.id .bool)
    (postSound :
      ∀ {initializerResult : Detail.InferredForItems}
        {conditionState : Frontend.SourceInference.State}
        {bodyResult : Detail.BlockResult}
        {postResult : Detail.InferredForItems}
        {loopContext : SourceSemantics.Context},
        Detail.inferForItemsFuel fuel inferenceContext initializer allocated =
          .ok initializerResult →
        Detail.inferStatementsFuel fuel
          { inferenceContext with
            loopDepth := inferenceContext.loopDepth + 1 }
          body.value expectedReturn conditionState = .ok bodyResult →
        ActiveLocalContextInvariant
          (bodyResult.state.restoreLexicalScope
            initializerResult.state.lexicalScope) outer loopContext →
        Detail.inferForItemsFuel fuel
          { inferenceContext with
            loopDepth := inferenceContext.loopDepth + 1 }
          post (bodyResult.state.restoreLexicalScope
            initializerResult.state.lexicalScope) = .ok postResult →
        ∃ postContext,
          ActiveLocalContextInvariant postResult.state outer postContext ∧
          ForItemsHaveType
            ((postResult.state.toTypedSource roots).applySubstitution outer)
            (({
              returnType := outer.apply expectedReturn
              loopDepth := inferenceContext.loopDepth
            } : ControlContext).enterLoop) loopContext
              (postResult.items.map (ForItemForm.applySubstitution outer))
              postContext)
    (childStatementSound :
      ∀ {childFuel : Nat} {input : Frontend.SourceInference.State}
        {inputContext : SourceSemantics.Context}
        {childStatement : Syntax.Statement}
        {head : Detail.StatementResult},
        childFuel < fuel →
        ActiveLocalContextInvariant input outer inputContext →
        Detail.inferStatementFuel childFuel
          { inferenceContext with
            loopDepth := inferenceContext.loopDepth + 1 }
          childStatement expectedReturn input = .ok head →
        TypingSourceExtends
          ((head.state.toTypedSource roots).applySubstitution outer)
          ((result.state.toTypedSource roots).applySubstitution outer) →
        head.state.integerPatterns ⊆ result.state.integerPatterns →
        head.state.requirements ⊆ result.state.requirements →
        ∃ outputContext facts,
          ActiveLocalContextInvariant head.state outer outputContext ∧
          StatementHasType
            ((head.state.toTypedSource roots).applySubstitution outer)
            (({
              returnType := outer.apply expectedReturn
              loopDepth := inferenceContext.loopDepth
            } : ControlContext).enterLoop)
            inputContext head.id outputContext facts ∧
          StatementResultMatchesFactsAfterSubstitution outer head facts) :
    ∃ facts,
      ActiveLocalContextInvariant result.state outer target ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution outer) {
          returnType := outer.apply expectedReturn
          loopDepth := inferenceContext.loopDepth
        } target result.id target facts ∧
      StatementResultMatchesFactsAfterSubstitution outer result facts := by
  have allocatedInvariant : ActiveLocalContextInvariant allocated outer target :=
    invariant.allocateStatementId allocationEq
  obtain ⟨initializerResult, inferredCondition, conditionState, bodyResult,
    postResult, initializerSuccess, conditionSuccess, bodySuccess,
    postSuccess, resultEq, contains⟩ :=
    inferStatementFuel_success_forLoop_facts statementEq allocationEq success
      roots
  obtain ⟨_actualInitializerResult, _actualCondition,
    _actualConditionState, _actualBodyResult, _actualPostResult,
    _actualInitializerSuccess, _actualConditionSuccess, _actualBodySuccess,
    _actualPostSuccess, initializerProvenance, bodyProvenance,
    postProvenance⟩ :=
    inferStatementFuel_success_forLoop_child_provenance statementEq
      allocationEq success initialBelow roots
  have initializerResultEq : _actualInitializerResult = initializerResult := by
    rw [initializerSuccess] at _actualInitializerSuccess
    exact (Except.ok.inj _actualInitializerSuccess).symm
  subst _actualInitializerResult
  have conditionPairEq : (_actualCondition, _actualConditionState) =
      (inferredCondition, conditionState) := by
    rw [conditionSuccess] at _actualConditionSuccess
    exact (Except.ok.inj _actualConditionSuccess).symm
  have conditionStateEq : _actualConditionState = conditionState :=
    congrArg Prod.snd conditionPairEq
  subst _actualConditionState
  have bodyResultEq : _actualBodyResult = bodyResult := by
    rw [bodySuccess] at _actualBodySuccess
    exact (Except.ok.inj _actualBodySuccess).symm
  subst _actualBodyResult
  have postResultEq : _actualPostResult = postResult := by
    rw [postSuccess] at _actualPostSuccess
    exact (Except.ok.inj _actualPostSuccess).symm
  subst _actualPostResult
  obtain ⟨loopContext, initializerInvariant, initializerTypingLocal⟩ :=
    initializerSound initializerSuccess
  have initializerTyping := ForItemsHaveType.weakenSource
    (initializerProvenance.sourceExtension.applySubstitution outer)
    initializerTypingLocal
  have conditionInvariant :
      ActiveLocalContextInvariant conditionState outer loopContext :=
    initializerInvariant.inferExprFuel conditionSuccess
  have conditionTypingLocal := conditionSound initializerSuccess
    initializerInvariant conditionSuccess
  have conditionToBody : TypingSourceExtends
      (conditionState.toTypedSource roots)
      (bodyResult.state.toTypedSource roots) :=
    inferStatementsFuel_success_typingSourceExtends bodySuccess
      bodyProvenance.initialBelow roots
  have conditionToParent := TypingSourceExtends.trans conditionToBody
    bodyProvenance.sourceExtension
  have conditionTyping := ExpressionHasType.weakenSource
    (conditionToParent.applySubstitution outer) conditionTypingLocal
  obtain ⟨bodyFinal, bodyFacts, _bodyInvariant, bodyTyping,
    _bodyAgreement⟩ :=
    inferStatementsFuel_success_statementsHaveType_under_ambient_bounded
      (fun state context => ActiveLocalContextInvariant state outer context)
      (roots := roots) conditionInvariant bodyProvenance.initialBelow
      (bodyProvenance.sourceExtension.applySubstitution outer)
      bodyProvenance.integerPatternsSubset
      bodyProvenance.requirementsSubset childStatementSound bodySuccess
  have postInputInvariant : ActiveLocalContextInvariant
      (bodyResult.state.restoreLexicalScope
        initializerResult.state.lexicalScope) outer loopContext :=
    initializerInvariant.restoreLexicalScope
  obtain ⟨postContext, _postInvariant, postTypingLocal⟩ :=
    postSound initializerSuccess bodySuccess postInputInvariant postSuccess
  have postTyping := ForItemsHaveType.weakenSource
    (postProvenance.sourceExtension.applySubstitution outer)
    postTypingLocal
  subst result
  refine ⟨{
      type := .unit
      hasValue := false
      sawReturn := false
      control := .loop bodyFacts.control
    }, allocatedInvariant.restoreLexicalScope_recordNode _, ?_, ?_⟩
  · exact forLoopStatementHasType_afterSubstitution contains
      initializerTyping conditionTyping bodyTyping postTyping
  · exact StatementResultMatchesFactsAfterSubstitution.forLoop outer
      bodyFacts id _

/-- Explicit match arms are sound from one-step soundness at strictly smaller
fuel.  The bounded case theorem supplies provenance for each actual arm body;
the statement-list theorem then types that body in the enclosing source. -/
theorem inferMatchCasesFuel_success_sound_of_bounded_statements
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {scrutineeType expectedReturn : TypeSystem.Ty}
    {outerScope : Frontend.SourceInference.LexicalScope}
    {cases : List Syntax.MatchCase}
    {state : Frontend.SourceInference.State}
    {result : Detail.MatchCasesResult}
    {source : TypedSource} {control : ControlContext}
    {outer : TypeSystem.Substitution}
    {semanticContext : SourceSemantics.Context}
    {evidenceState : Frontend.SourceInference.State} {occurrence : NodeId}
    {roots : List NodeId}
    (validated : ProgramSignatureFormationValidated
      inferenceContext.signatures)
    (functionsCanonical : ∀ signature ∈
      inferenceContext.signatures.functions,
      signature.scheme.body = .function
        (TypeSystem.Ty.productMany signature.parameterTypes)
        (TypeSystem.Ty.productMany signature.returnTypes))
    (catalog : SignatureCatalogWellFormed semanticContext.signatures)
    (semanticSignaturesEq :
      semanticContext.signatures = inferenceContext.signatures)
    (evidence : IntegerPatternEvidenceAt source semanticContext outer
      evidenceState occurrence)
    (ready : state.InferenceReady)
    (scrutineeBelow :
      scrutineeType.VariablesBelow state.inference.next)
    (returnBelow : expectedReturn.VariablesBelow state.inference.next)
    (below : state.LocalBindersBelowNextLocal)
    (initialBelow : state.NodesBelowNextOccurrence)
    (ownerEq : source.owner = state.owner)
    (semanticOwner : semanticContext.currentDeclaration = some source.owner)
    (scrutineeAdmissible :
      TypeAdmissible semanticContext (outer.apply scrutineeType))
    (initialInvariant :
      ActiveLocalContextInvariant state outer semanticContext)
    (scopeEq : state.lexicalScope = outerScope)
    (outerExtension : outer.SemanticallyExtends
      result.state.inference.substitution)
    (resultSourceExtension : TypingSourceExtends
      ((result.state.toTypedSource roots).applySubstitution outer) source)
    (integerPatternsSubset :
      result.state.integerPatterns ⊆ evidenceState.integerPatterns)
    (requirementsSubset :
      result.state.requirements ⊆ evidenceState.requirements)
    (requirementsOccur : ∀ matchCase,
      matchCase ∈ result.cases →
      ∀ requirement, requirement ∈ matchCase.pattern.requirements →
        PrimaryRequirementOccursAt source occurrence requirement)
    (statementSound :
      ∀ {childFuel : Nat} {input : Frontend.SourceInference.State}
        {inputContext : SourceSemantics.Context}
        {statement : Syntax.Statement} {head : Detail.StatementResult},
        childFuel < fuel →
        ActiveLocalContextInvariant input outer inputContext →
        Detail.inferStatementFuel childFuel inferenceContext statement
          expectedReturn input = .ok head →
        TypingSourceExtends
          ((head.state.toTypedSource roots).applySubstitution outer) source →
        head.state.integerPatterns ⊆ evidenceState.integerPatterns →
        head.state.requirements ⊆ evidenceState.requirements →
        ∃ outputContext facts,
          ActiveLocalContextInvariant head.state outer outputContext ∧
          StatementHasType
            ((head.state.toTypedSource roots).applySubstitution outer)
            control inputContext head.id outputContext facts ∧
          StatementResultMatchesFactsAfterSubstitution outer head facts)
    (success : Detail.inferMatchCasesFuel fuel inferenceContext scrutineeType
      expectedReturn outerScope cases state = .ok result) :
    ∃ caseFacts,
      MatchCasesHaveType source control semanticContext
        (outer.apply scrutineeType)
        (result.cases.map (TypedMatchCase.applySubstitution outer)) caseFacts ∧
      allBodiesSawReturn caseFacts = result.allReturn := by
  apply inferMatchCasesFuel_success_sound_at_bounded validated
    functionsCanonical catalog semanticSignaturesEq evidence ready
    scrutineeBelow returnBelow below initialBelow ownerEq semanticOwner
    scrutineeAdmissible initialInvariant scopeEq outerExtension
    resultSourceExtension integerPatternsSubset requirementsSubset
    requirementsOccur ?_ success
  intro childFuel statements childInitial childResult childContext
    childBound childInvariant childSuccess childBelow childExtension
    childIntegerSubset childRequirementSubset
  exact inferStatementsFuel_success_statementsHaveType_under_ambient_bounded
    (fun state context => ActiveLocalContextInvariant state outer context)
    (roots := roots) childInvariant childBelow childExtension
    childIntegerSubset childRequirementSubset
    (fun headBound headInvariant headSuccess headExtension
      headIntegerSubset headRequirementSubset =>
      statementSound (Nat.lt_trans headBound childBound) headInvariant
        headSuccess headExtension headIntegerSubset headRequirementSubset)
    childSuccess

theorem inferStatementFuel_success_matchWithoutDefault_bounded_sound
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
    {arms : Syntax.MatchArms} {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    {outer : TypeSystem.Substitution} {target : SourceSemantics.Context}
    {evidenceState : Frontend.SourceInference.State}
    (statementEq : statement.value = .matchWith scrutinees arms)
    (defaultEq : arms.value.defaultBody = none)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ signature ∈
      inferenceContext.signatures.functions,
      signature.scheme.body = .function
        (TypeSystem.Ty.productMany signature.parameterTypes)
        (TypeSystem.Ty.productMany signature.returnTypes))
    (catalog : SignatureCatalogWellFormed target.signatures)
    (signatures_eq : target.signatures = inferenceContext.signatures)
    (ready : initial.InferenceReady)
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (below : initial.LocalBindersBelowNextLocal)
    (invariant : ActiveLocalContextInvariant initial outer target)
    (outerExtension : outer.SemanticallyExtends
      result.state.inference.substitution)
    (roots : List NodeId := [])
    (initialBelow : initial.NodesBelowNextOccurrence)
    (semanticOwner : target.currentDeclaration = some
      ((result.state.toTypedSource roots).applySubstitution outer).owner)
    (evidence : IntegerPatternEvidenceAt
      ((result.state.toTypedSource roots).applySubstitution outer) target outer
      evidenceState (.statement result.id))
    (integerPatternsSubset :
      result.state.integerPatterns ⊆ evidenceState.integerPatterns)
    (requirementsSubset :
      result.state.requirements ⊆ evidenceState.requirements)
    (statementSound :
      ∀ {childFuel : Nat}
        {input : Frontend.SourceInference.State}
        {inputContext : SourceSemantics.Context}
        {childStatement : Syntax.Statement}
        {head : Detail.StatementResult},
        childFuel < fuel →
        ActiveLocalContextInvariant input outer inputContext →
        Detail.inferStatementFuel childFuel inferenceContext childStatement
          expectedReturn input = .ok head →
        TypingSourceExtends
          ((head.state.toTypedSource roots).applySubstitution outer)
          ((result.state.toTypedSource roots).applySubstitution outer) →
        head.state.integerPatterns ⊆ evidenceState.integerPatterns →
        head.state.requirements ⊆ evidenceState.requirements →
        ∃ outputContext facts,
          ActiveLocalContextInvariant head.state outer outputContext ∧
          StatementHasType
            ((head.state.toTypedSource roots).applySubstitution outer) {
              returnType := outer.apply expectedReturn
              loopDepth := inferenceContext.loopDepth
            } inputContext head.id outputContext facts ∧
          StatementResultMatchesFactsAfterSubstitution outer head facts)
    (casesPresent : arms.value.cases ≠ [])
    (scrutineeSound :
      ∀ {scrutinee : InferredExpression}
        {scrutineeState : Frontend.SourceInference.State},
        inferMatchScrutineesFuel fuel inferenceContext statement.span
            scrutinees.elements.toList allocated =
              .ok (scrutinee, scrutineeState) →
          ExpressionHasType
            ((result.state.toTypedSource roots).applySubstitution outer)
            target scrutinee.id (outer.apply scrutinee.type)) :
    ∃ facts,
      ActiveLocalContextInvariant result.state outer target ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution outer) {
          returnType := outer.apply expectedReturn
          loopDepth := inferenceContext.loopDepth
        } target result.id target facts ∧
      StatementResultMatchesFactsAfterSubstitution outer result facts := by
  have allocatedInvariant :
      ActiveLocalContextInvariant allocated outer target :=
    invariant.allocateStatementId allocationEq
  have allocatedReady : allocated.InferenceReady := by
    have retained :=
      Frontend.SourceInference.State.InferenceReady.allocateStatementId ready
    have allocatedEq : initial.allocateStatementId.2 = allocated :=
      congrArg Prod.snd allocationEq
    rw [allocatedEq] at retained
    exact retained
  have allocatedReturnBelow :
      expectedReturn.VariablesBelow allocated.inference.next := by
    have allocatedEq : initial.allocateStatementId.2 = allocated :=
      congrArg Prod.snd allocationEq
    rw [← allocatedEq]
    exact returnBelow
  have allocatedBelow : allocated.LocalBindersBelowNextLocal := by
    have retained :=
      Frontend.SourceInference.State.allocateStatementId_preserves_localBindersBelowNextLocal
        initial below
    have allocatedEq : initial.allocateStatementId.2 = allocated :=
      congrArg Prod.snd allocationEq
    rw [allocatedEq] at retained
    exact retained
  obtain ⟨scrutinee, scrutineeState, hiddenScrutinee, hiddenState, checked,
      scrutineeSuccess, hiddenAllocation, casesSuccess,
      guardPassed, resultEq, contains⟩ :=
    inferStatementFuel_success_matchWithoutDefault_facts statementEq defaultEq
      allocationEq success roots
  have scrutineeProperties := inferMatchScrutineesFuel_inferenceProperties
    allocatedReady signatureFormation functionsCanonical scrutineeSuccess
  have scrutineeInvariant :
      ActiveLocalContextInvariant scrutineeState outer target :=
    allocatedInvariant.inferMatchScrutineesFuel scrutineeSuccess
  have scrutineeLocalBelow :
      scrutineeState.LocalBindersBelowNextLocal :=
    inferMatchScrutineesFuel_preserves_localBindersBelowNextLocal
      allocatedBelow scrutineeSuccess
  have hiddenInvariant : ActiveLocalContextInvariant hiddenState outer target :=
    scrutineeInvariant.allocateHiddenLocal hiddenAllocation
  have hiddenReady : hiddenState.InferenceReady := by
    have retained :=
      Frontend.SourceInference.State.InferenceReady.allocateHiddenLocal
        scrutineeProperties.2.1
    have hiddenEq : scrutineeState.allocateHiddenLocal.2 = hiddenState :=
      congrArg Prod.snd hiddenAllocation
    rw [hiddenEq] at retained
    exact retained
  have hiddenScrutineeBelow :
      scrutinee.type.VariablesBelow hiddenState.inference.next := by
    have hiddenEq : scrutineeState.allocateHiddenLocal.2 = hiddenState :=
      congrArg Prod.snd hiddenAllocation
    rw [← hiddenEq]
    exact scrutineeProperties.2.2
  have hiddenReturnBelow :
      expectedReturn.VariablesBelow hiddenState.inference.next := by
    have atScrutinee :=
      allocatedReturnBelow.weaken scrutineeProperties.1.next_le
    have hiddenEq : scrutineeState.allocateHiddenLocal.2 = hiddenState :=
      congrArg Prod.snd hiddenAllocation
    rw [← hiddenEq]
    exact atScrutinee
  have hiddenBelow : hiddenState.LocalBindersBelowNextLocal := by
    have retained :=
      Frontend.SourceInference.State.allocateHiddenLocal_preserves_localBindersBelowNextLocal
        scrutineeState scrutineeLocalBelow
    have hiddenEq : scrutineeState.allocateHiddenLocal.2 = hiddenState :=
      congrArg Prod.snd hiddenAllocation
    rw [hiddenEq] at retained
    exact retained
  have checkedInvariant : ActiveLocalContextInvariant checked.state outer
      target := hiddenInvariant.inferMatchCasesFuel casesSuccess
  have scrutineeTyping := scrutineeSound scrutineeSuccess
  have checkedIntegerPatternsSubset :
      checked.state.integerPatterns ⊆ result.state.integerPatterns := by
    rw [resultEq]
    intro origin member
    exact member
  have checkedRequirementsSubset :
      checked.state.requirements ⊆ result.state.requirements := by
    rw [resultEq]
    exact Frontend.SourceInference.State.recordNode_requirements_subset
      checked.state _
  have checkedRequirementsOccur : ∀ matchCase,
      matchCase ∈ checked.cases →
      ∀ requirement, requirement ∈ matchCase.pattern.requirements →
        PrimaryRequirementOccursAt
          ((result.state.toTypedSource roots).applySubstitution outer)
          (.statement result.id) requirement := by
    intro matchCase caseMember requirement requirementMember
    rw [FlexibleSubstitution.primaryRequirementOccursAt_applySubstitution]
    exact contains.matchCasePatternRequirementOccursAt rfl caseMember
      requirementMember
  have allocatedNodesBelow : allocated.NodesBelowNextOccurrence := by
    have bound :=
      Frontend.SourceInference.State.allocateStatementId_preserves_nodesBelowNextOccurrence
        initial initialBelow
    have eq : initial.allocateStatementId.2 = allocated :=
      congrArg Prod.snd allocationEq
    simpa [eq] using bound
  have scrutineeNodesBelow :
      scrutineeState.NodesBelowNextOccurrence :=
    inferMatchScrutineesFuel_success_nodesBelow scrutineeSuccess
      allocatedNodesBelow
  have hiddenNodesBelow : hiddenState.NodesBelowNextOccurrence := by
    have bound :=
      Frontend.SourceInference.State.allocateHiddenLocal_preserves_nodesBelowNextOccurrence
        scrutineeState scrutineeNodesBelow
    have eq : scrutineeState.allocateHiddenLocal.2 = hiddenState :=
      congrArg Prod.snd hiddenAllocation
    simpa [eq] using bound
  have checkedToResult : TypingSourceExtends
      ((checked.state.toTypedSource roots).applySubstitution outer)
      ((result.state.toTypedSource roots).applySubstitution outer) := by
    have raw : TypingSourceExtends
        (checked.state.toTypedSource roots)
        (result.state.toTypedSource roots) := by
      rw [resultEq]
      refine ⟨rfl, ?_⟩
      simp only [Frontend.SourceInference.State.toTypedSource,
        Frontend.SourceInference.State.recordNode]
      exact List.prefix_append _ _
    exact raw.applySubstitution outer
  subst result
  have checkedExtension : outer.SemanticallyExtends
      checked.state.inference.substitution := by
    change outer.SemanticallyExtends
      checked.state.inference.substitution at outerExtension
    exact outerExtension
  have checkedOwner : checked.state.owner = hiddenState.owner :=
    Detail.inferMatchCasesFuel_preserves_owner casesSuccess
  obtain ⟨caseFacts, casesTyping, allReturnEq⟩ :=
    inferMatchCasesFuel_success_sound_of_bounded_statements
      signatureFormation functionsCanonical catalog signatures_eq evidence
      hiddenReady hiddenScrutineeBelow hiddenReturnBelow hiddenBelow
      hiddenNodesBelow (by
        simpa [Frontend.SourceInference.State.toTypedSource,
          Frontend.SourceInference.State.recordNode,
          TypedSource.applySubstitution] using checkedOwner)
      semanticOwner scrutineeTyping.type_admissible hiddenInvariant rfl
      checkedExtension checkedToResult
      (List.Subset.trans checkedIntegerPatternsSubset integerPatternsSubset)
      (List.Subset.trans checkedRequirementsSubset requirementsSubset)
      checkedRequirementsOccur statementSound casesSuccess
  have exhaustive :=
    matchExhaustiveWithoutDefault_of_guard catalog signatures_eq casesSuccess
      casesTyping scrutineeTyping.type_admissible checkedExtension guardPassed
  have checkedCasesPresent : checked.cases ≠ [] := by
    intro checkedCasesEq
    have lengthEq := Detail.inferMatchCasesFuel_success_cases_length
      casesSuccess
    rw [checkedCasesEq] at lengthEq
    apply casesPresent
    simpa using lengthEq.symm
  have caseFactsPresent : caseFacts ≠ [] :=
    matchCasesHaveType_facts_ne_nil_of_cases_ne_nil casesTyping (by
      simpa using checkedCasesPresent)
  obtain ⟨summary, merged⟩ :=
    mergeBodyControls_withoutDefault_eq_some_of_ne_nil caseFacts
      caseFactsPresent
  refine ⟨{
      type := if allBodiesSawReturn caseFacts then
        outer.apply expectedReturn
      else
        .unit
      hasValue := allBodiesSawReturn caseFacts
      sawReturn := allBodiesSawReturn caseFacts
      control := summary.eraseValue
    }, checkedInvariant.recordNode _, ?_, ?_⟩
  · exact matchWithoutDefaultStatementHasType_afterSubstitution contains
      scrutineeTyping casesTyping exhaustive allReturnEq merged
      checkedExtension
  · exact StatementResultMatchesFactsAfterSubstitution.matchWithoutDefault
      allReturnEq checkedExtension id _


theorem inferStatementFuel_success_matchWithDefault_bounded_sound
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
    {arms : Syntax.MatchArms} {defaultBody : Syntax.Block}
    {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    {outer : TypeSystem.Substitution} {target : SourceSemantics.Context}
    {evidenceState : Frontend.SourceInference.State}
    (statementEq : statement.value = .matchWith scrutinees arms)
    (defaultEq : arms.value.defaultBody = some defaultBody)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ signature ∈
      inferenceContext.signatures.functions,
      signature.scheme.body = .function
        (TypeSystem.Ty.productMany signature.parameterTypes)
        (TypeSystem.Ty.productMany signature.returnTypes))
    (catalog : SignatureCatalogWellFormed target.signatures)
    (signatures_eq : target.signatures = inferenceContext.signatures)
    (ready : initial.InferenceReady)
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (below : initial.LocalBindersBelowNextLocal)
    (invariant : ActiveLocalContextInvariant initial outer target)
    (outerExtension : outer.SemanticallyExtends
      result.state.inference.substitution)
    (roots : List NodeId := [])
    (initialBelow : initial.NodesBelowNextOccurrence)
    (semanticOwner : target.currentDeclaration = some
      ((result.state.toTypedSource roots).applySubstitution outer).owner)
    (evidence : IntegerPatternEvidenceAt
      ((result.state.toTypedSource roots).applySubstitution outer) target outer
      evidenceState (.statement result.id))
    (integerPatternsSubset :
      result.state.integerPatterns ⊆ evidenceState.integerPatterns)
    (requirementsSubset :
      result.state.requirements ⊆ evidenceState.requirements)
    (scrutineeSound :
      ∀ {scrutinee : InferredExpression}
        {scrutineeState : Frontend.SourceInference.State},
        inferMatchScrutineesFuel fuel inferenceContext statement.span
            scrutinees.elements.toList allocated =
              .ok (scrutinee, scrutineeState) →
          ExpressionHasType
            ((result.state.toTypedSource roots).applySubstitution outer)
            target scrutinee.id (outer.apply scrutinee.type))
    (statementSound :
      ∀ {childFuel : Nat}
        {input : Frontend.SourceInference.State}
        {inputContext : SourceSemantics.Context}
        {childStatement : Syntax.Statement}
        {head : Detail.StatementResult},
        childFuel < fuel →
        ActiveLocalContextInvariant input outer inputContext →
        Detail.inferStatementFuel childFuel inferenceContext childStatement
          expectedReturn input = .ok head →
        TypingSourceExtends
          ((head.state.toTypedSource roots).applySubstitution outer)
          ((result.state.toTypedSource roots).applySubstitution outer) →
        head.state.integerPatterns ⊆ evidenceState.integerPatterns →
        head.state.requirements ⊆ evidenceState.requirements →
        ∃ outputContext facts,
          ActiveLocalContextInvariant head.state outer outputContext ∧
          StatementHasType
            ((head.state.toTypedSource roots).applySubstitution outer) {
              returnType := outer.apply expectedReturn
              loopDepth := inferenceContext.loopDepth
            } inputContext head.id outputContext facts ∧
          StatementResultMatchesFactsAfterSubstitution outer head facts) :
    ∃ facts,
      ActiveLocalContextInvariant result.state outer target ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution outer) {
          returnType := outer.apply expectedReturn
          loopDepth := inferenceContext.loopDepth
        } target result.id target facts ∧
      StatementResultMatchesFactsAfterSubstitution outer result facts := by
  have allocatedInvariant :
      ActiveLocalContextInvariant allocated outer target :=
    invariant.allocateStatementId allocationEq
  have allocatedReady : allocated.InferenceReady := by
    have retained :=
      Frontend.SourceInference.State.InferenceReady.allocateStatementId ready
    have allocatedEq : initial.allocateStatementId.2 = allocated :=
      congrArg Prod.snd allocationEq
    rw [allocatedEq] at retained
    exact retained
  have allocatedReturnBelow :
      expectedReturn.VariablesBelow allocated.inference.next := by
    have allocatedEq : initial.allocateStatementId.2 = allocated :=
      congrArg Prod.snd allocationEq
    rw [← allocatedEq]
    exact returnBelow
  have allocatedBelow : allocated.LocalBindersBelowNextLocal := by
    have retained :=
      Frontend.SourceInference.State.allocateStatementId_preserves_localBindersBelowNextLocal
        initial below
    have allocatedEq : initial.allocateStatementId.2 = allocated :=
      congrArg Prod.snd allocationEq
    rw [allocatedEq] at retained
    exact retained
  obtain ⟨scrutinee, scrutineeState, hiddenScrutinee, hiddenState, checked,
      defaultResult, scrutineeSuccess, hiddenAllocation, casesSuccess,
      defaultSuccess, _guardPassed, resultEq, contains⟩ :=
    inferStatementFuel_success_matchWithDefault_facts statementEq defaultEq
      allocationEq success roots
  have scrutineeProperties := inferMatchScrutineesFuel_inferenceProperties
    allocatedReady signatureFormation functionsCanonical scrutineeSuccess
  have scrutineeInvariant :
      ActiveLocalContextInvariant scrutineeState outer target :=
    allocatedInvariant.inferMatchScrutineesFuel scrutineeSuccess
  have scrutineeLocalBelow :
      scrutineeState.LocalBindersBelowNextLocal :=
    inferMatchScrutineesFuel_preserves_localBindersBelowNextLocal
      allocatedBelow scrutineeSuccess
  have hiddenInvariant : ActiveLocalContextInvariant hiddenState outer target :=
    scrutineeInvariant.allocateHiddenLocal hiddenAllocation
  have hiddenReady : hiddenState.InferenceReady := by
    have retained :=
      Frontend.SourceInference.State.InferenceReady.allocateHiddenLocal
        scrutineeProperties.2.1
    have hiddenEq : scrutineeState.allocateHiddenLocal.2 = hiddenState :=
      congrArg Prod.snd hiddenAllocation
    rw [hiddenEq] at retained
    exact retained
  have hiddenScrutineeBelow :
      scrutinee.type.VariablesBelow hiddenState.inference.next := by
    have hiddenEq : scrutineeState.allocateHiddenLocal.2 = hiddenState :=
      congrArg Prod.snd hiddenAllocation
    rw [← hiddenEq]
    exact scrutineeProperties.2.2
  have hiddenReturnBelow :
      expectedReturn.VariablesBelow hiddenState.inference.next := by
    have atScrutinee :=
      allocatedReturnBelow.weaken scrutineeProperties.1.next_le
    have hiddenEq : scrutineeState.allocateHiddenLocal.2 = hiddenState :=
      congrArg Prod.snd hiddenAllocation
    rw [← hiddenEq]
    exact atScrutinee
  have hiddenBelow : hiddenState.LocalBindersBelowNextLocal := by
    have retained :=
      Frontend.SourceInference.State.allocateHiddenLocal_preserves_localBindersBelowNextLocal
        scrutineeState scrutineeLocalBelow
    have hiddenEq : scrutineeState.allocateHiddenLocal.2 = hiddenState :=
      congrArg Prod.snd hiddenAllocation
    rw [hiddenEq] at retained
    exact retained
  have checkedProperties := Detail.inferMatchCasesFuel_inferenceProperties
    hiddenReady signatureFormation functionsCanonical hiddenScrutineeBelow
      hiddenReturnBelow rfl casesSuccess
  have checkedInvariant : ActiveLocalContextInvariant checked.state outer
      target := hiddenInvariant.inferMatchCasesFuel casesSuccess
  have checkedReturnBelow :=
    hiddenReturnBelow.weaken checkedProperties.1.next_le
  have defaultProperties := Detail.inferStatementsFuel_inferenceProperties
    checkedProperties.2.1 signatureFormation functionsCanonical
      checkedReturnBelow defaultSuccess
  have scrutineeTyping := scrutineeSound scrutineeSuccess
  have checkedIntegerPatternsSubset :
      checked.state.integerPatterns ⊆ result.state.integerPatterns := by
    rw [resultEq]
    have throughDefault : checked.state.integerPatterns ⊆
        defaultResult.state.integerPatterns :=
      Detail.inferStatementsFuel_integerPatterns_subset defaultSuccess
    have throughRestore : defaultResult.state.integerPatterns ⊆
        (defaultResult.state.restoreLexicalScope
          hiddenState.lexicalScope).integerPatterns := by
      intro origin member
      exact member
    apply List.Subset.trans throughDefault
    apply List.Subset.trans throughRestore
    intro origin member
    exact member
  have checkedRequirementsSubset :
      checked.state.requirements ⊆ result.state.requirements := by
    rw [resultEq]
    exact List.Subset.trans
      (Detail.inferStatementsFuel_requirements_subset defaultSuccess)
      (List.Subset.trans
        (Frontend.SourceInference.State.restoreLexicalScope_requirements_subset
          defaultResult.state hiddenState.lexicalScope)
        (Frontend.SourceInference.State.recordNode_requirements_subset
          (defaultResult.state.restoreLexicalScope hiddenState.lexicalScope)
          _))
  have checkedRequirementsOccur : ∀ matchCase,
      matchCase ∈ checked.cases →
      ∀ requirement, requirement ∈ matchCase.pattern.requirements →
        PrimaryRequirementOccursAt
          ((result.state.toTypedSource roots).applySubstitution outer)
          (.statement result.id) requirement := by
    intro matchCase caseMember requirement requirementMember
    rw [FlexibleSubstitution.primaryRequirementOccursAt_applySubstitution]
    exact contains.matchCasePatternRequirementOccursAt rfl caseMember
      requirementMember
  have allocatedNodesBelow : allocated.NodesBelowNextOccurrence := by
    have bound :=
      Frontend.SourceInference.State.allocateStatementId_preserves_nodesBelowNextOccurrence
        initial initialBelow
    have eq : initial.allocateStatementId.2 = allocated :=
      congrArg Prod.snd allocationEq
    simpa [eq] using bound
  have scrutineeNodesBelow :
      scrutineeState.NodesBelowNextOccurrence :=
    inferMatchScrutineesFuel_success_nodesBelow scrutineeSuccess
      allocatedNodesBelow
  have hiddenNodesBelow : hiddenState.NodesBelowNextOccurrence := by
    have bound :=
      Frontend.SourceInference.State.allocateHiddenLocal_preserves_nodesBelowNextOccurrence
        scrutineeState scrutineeNodesBelow
    have eq : scrutineeState.allocateHiddenLocal.2 = hiddenState :=
      congrArg Prod.snd hiddenAllocation
    simpa [eq] using bound
  have checkedNodesBelow : checked.state.NodesBelowNextOccurrence :=
    (Detail.inferMatchCasesFuel_occurrenceBoundExtends casesSuccess
      ).nodesBelowNextOccurrence hiddenNodesBelow
  have defaultToResultRaw : TypingSourceExtends
      (defaultResult.state.toTypedSource roots)
      (result.state.toTypedSource roots) := by
    rw [resultEq]
    exact (child_provenance_through_restore_record
      defaultResult.state hiddenState.lexicalScope _ roots).1
  have defaultToResult : TypingSourceExtends
      ((defaultResult.state.toTypedSource roots).applySubstitution outer)
      ((result.state.toTypedSource roots).applySubstitution outer) :=
    defaultToResultRaw.applySubstitution outer
  have checkedToDefault : TypingSourceExtends
      (checked.state.toTypedSource roots)
      (defaultResult.state.toTypedSource roots) :=
    inferStatementsFuel_success_typingSourceExtends defaultSuccess
      checkedNodesBelow roots
  have checkedToResult : TypingSourceExtends
      ((checked.state.toTypedSource roots).applySubstitution outer)
      ((result.state.toTypedSource roots).applySubstitution outer) :=
    (TypingSourceExtends.trans checkedToDefault defaultToResultRaw
      ).applySubstitution outer
  have defaultIntegerPatternsSubset :
      defaultResult.state.integerPatterns ⊆
        evidenceState.integerPatterns := by
    apply List.Subset.trans ?_ integerPatternsSubset
    rw [resultEq]
    exact (child_provenance_through_restore_record
      defaultResult.state hiddenState.lexicalScope _ roots).2.1
  have defaultRequirementsSubset :
      defaultResult.state.requirements ⊆
        evidenceState.requirements := by
    apply List.Subset.trans ?_ requirementsSubset
    rw [resultEq]
    exact (child_provenance_through_restore_record
      defaultResult.state hiddenState.lexicalScope _ roots).2.2
  subst result
  have defaultExtension : outer.SemanticallyExtends
      defaultResult.state.inference.substitution := by
    change outer.SemanticallyExtends
      defaultResult.state.inference.substitution at outerExtension
    exact outerExtension
  have checkedExtension : outer.SemanticallyExtends
      checked.state.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans defaultExtension
      defaultProperties.1.substitution_extends
  have checkedOwner : checked.state.owner = hiddenState.owner :=
    Detail.inferMatchCasesFuel_preserves_owner casesSuccess
  have defaultOwner : defaultResult.state.owner = checked.state.owner :=
    Detail.inferStatementsFuel_preserves_owner defaultSuccess
  obtain ⟨caseFacts, casesTyping, caseReturnEq⟩ :=
    inferMatchCasesFuel_success_sound_of_bounded_statements
      signatureFormation functionsCanonical catalog signatures_eq evidence
      hiddenReady hiddenScrutineeBelow hiddenReturnBelow hiddenBelow
      hiddenNodesBelow (by
        simpa [Frontend.SourceInference.State.toTypedSource,
          Frontend.SourceInference.State.restoreLexicalScope,
          Frontend.SourceInference.State.recordNode,
          TypedSource.applySubstitution] using
            defaultOwner.trans checkedOwner)
      semanticOwner scrutineeTyping.type_admissible hiddenInvariant rfl
      checkedExtension checkedToResult
      (List.Subset.trans checkedIntegerPatternsSubset integerPatternsSubset)
      (List.Subset.trans checkedRequirementsSubset requirementsSubset)
      checkedRequirementsOccur statementSound casesSuccess
  obtain ⟨defaultFinal, defaultFacts, _defaultInvariant, defaultTyping,
      defaultAgreement⟩ :=
    inferStatementsFuel_success_statementsHaveType_under_ambient_bounded
      (fun state context => ActiveLocalContextInvariant state outer context)
      (roots := roots) checkedInvariant checkedNodesBelow defaultToResult
      defaultIntegerPatternsSubset defaultRequirementsSubset
      statementSound defaultSuccess
  obtain ⟨summary, merged⟩ :=
    mergeBodyControls_withDefault_eq_some caseFacts defaultFacts
  refine ⟨{
      type := if allBodiesSawReturn caseFacts && defaultFacts.sawReturn then
        outer.apply expectedReturn
      else
        .unit
      hasValue := allBodiesSawReturn caseFacts && defaultFacts.sawReturn
      sawReturn := allBodiesSawReturn caseFacts && defaultFacts.sawReturn
      control := summary.eraseValue
    }, hiddenInvariant.restoreLexicalScope_recordNode _, ?_, ?_⟩
  · exact matchWithDefaultStatementHasType_afterSubstitution contains
      scrutineeTyping casesTyping defaultTyping caseReturnEq defaultAgreement
      merged defaultExtension
  · exact StatementResultMatchesFactsAfterSubstitution.matchWithDefault
      caseReturnEq defaultAgreement defaultExtension id _


/-- The actual child of an expression statement remains in the parent source. -/
theorem inferStatementFuel_success_expression_child_provenance
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expression : Syntax.Expr}
    {trailingSemicolon : Bool} {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    (statementEq : statement.value =
      .expression expression trailingSemicolon)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (roots : List NodeId := []) :
    ∃ inferred expressionState,
      Detail.inferExprFuel fuel inferenceContext expression none allocated =
        .ok (inferred, expressionState) ∧
      ChildStateProvenance allocated expressionState result.state roots := by
  obtain ⟨inferred, expressionState, expressionSuccess, resultEq, _contains⟩ :=
    inferStatementFuel_success_expression_facts statementEq allocationEq
      success roots
  have allocatedBelow : allocated.NodesBelowNextOccurrence := by
    have bound :=
      Frontend.SourceInference.State.allocateStatementId_preserves_nodesBelowNextOccurrence
        initial initialBelow
    have eq : initial.allocateStatementId.2 = allocated :=
      congrArg Prod.snd allocationEq
    simpa [eq] using bound
  refine ⟨inferred, expressionState, expressionSuccess, ?_⟩
  rw [resultEq]
  exact child_provenance_through_record allocated expressionState _ roots
    allocatedBelow

/-- The actual child of a value return remains in the parent source. -/
theorem inferStatementFuel_success_returnValue_child_provenance
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {value : Syntax.Expr}
    {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    (statementEq : statement.value = .returnStmt (some value))
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (roots : List NodeId := []) :
    ∃ inferred valueState,
      Detail.inferExprFuel fuel inferenceContext value
        (some expectedReturn) allocated = .ok (inferred, valueState) ∧
      ChildStateProvenance allocated valueState result.state roots := by
  obtain ⟨inferred, valueState, valueSuccess, resultEq, _contains⟩ :=
    inferStatementFuel_success_returnValue_facts statementEq allocationEq
      success roots
  have allocatedBelow : allocated.NodesBelowNextOccurrence := by
    have bound :=
      Frontend.SourceInference.State.allocateStatementId_preserves_nodesBelowNextOccurrence
        initial initialBelow
    have eq : initial.allocateStatementId.2 = allocated :=
      congrArg Prod.snd allocationEq
    simpa [eq] using bound
  refine ⟨inferred, valueState, valueSuccess, ?_⟩
  rw [resultEq]
  exact child_provenance_through_record allocated valueState _ roots
    allocatedBelow

/-- An expression statement only needs semantic typing in its child's own
completed source; the actual parent trace transports it to the statement. -/
theorem inferStatementFuel_success_expression_sound_local
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expression : Syntax.Expr}
    {trailingSemicolon : Bool} {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    {outer : TypeSystem.Substitution} {control : ControlContext}
    {target : SourceSemantics.Context}
    (statementEq : statement.value =
      .expression expression trailingSemicolon)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (invariant : ActiveLocalContextInvariant initial outer target)
    (roots : List NodeId := [])
    (localExpressionSound :
      ∀ {inferred : InferredExpression}
        {expressionState : Frontend.SourceInference.State},
        Detail.inferExprFuel fuel inferenceContext expression none allocated =
          .ok (inferred, expressionState) →
        ExpressionHasType
          ((expressionState.toTypedSource roots).applySubstitution outer)
          target inferred.id (outer.apply inferred.type)) :
    ∃ facts,
      ActiveLocalContextInvariant result.state outer target ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution outer)
        control target result.id target facts ∧
      StatementResultMatchesFactsAfterSubstitution outer result facts := by
  obtain ⟨actualInferred, actualState, actualSuccess, provenance⟩ :=
    inferStatementFuel_success_expression_child_provenance statementEq
      allocationEq success initialBelow roots
  apply inferStatementFuel_success_expression_sound statementEq allocationEq
    success invariant roots
  intro inferred expressionState expressionSuccess
  have pairEq : (inferred, expressionState) =
      (actualInferred, actualState) := by
    rw [actualSuccess] at expressionSuccess
    exact (Except.ok.inj expressionSuccess).symm
  cases pairEq
  exact ExpressionHasType.weakenSource
    (provenance.sourceExtension.applySubstitution outer)
    (localExpressionSound actualSuccess)

/-- A value return has the same local-expression-to-parent transport. -/
theorem inferStatementFuel_success_returnValue_sound_local
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {value : Syntax.Expr}
    {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    {outer : TypeSystem.Substitution} {target : SourceSemantics.Context}
    (statementEq : statement.value = .returnStmt (some value))
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (invariant : ActiveLocalContextInvariant initial outer target)
    (outerExtension : outer.SemanticallyExtends
      result.state.inference.substitution)
    (roots : List NodeId := [])
    (localExpressionSound :
      ∀ {inferred : InferredExpression}
        {valueState : Frontend.SourceInference.State},
        Detail.inferExprFuel fuel inferenceContext value
            (some expectedReturn) allocated = .ok (inferred, valueState) →
        ExpressionHasType
          ((valueState.toTypedSource roots).applySubstitution outer)
          target inferred.id (outer.apply inferred.type)) :
    ActiveLocalContextInvariant result.state outer target ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution outer) {
          returnType := outer.apply expectedReturn
          loopDepth := inferenceContext.loopDepth
        } target result.id target {
          type := outer.apply expectedReturn
          hasValue := true
          sawReturn := true
          control := .returned
        } ∧
      StatementResultMatchesFactsAfterSubstitution outer result {
        type := outer.apply expectedReturn
        hasValue := true
        sawReturn := true
        control := .returned
      } := by
  obtain ⟨actualInferred, actualState, actualSuccess, provenance⟩ :=
    inferStatementFuel_success_returnValue_child_provenance statementEq
      allocationEq success initialBelow roots
  apply inferStatementFuel_success_returnValue_sound statementEq allocationEq
    success invariant outerExtension roots
  intro inferred valueState valueSuccess
  have pairEq : (inferred, valueState) =
      (actualInferred, actualState) := by
    rw [actualSuccess] at valueSuccess
    exact (Except.ok.inj valueSuccess).symm
  cases pairEq
  exact ExpressionHasType.weakenSource
    (provenance.sourceExtension.applySubstitution outer)
    (localExpressionSound actualSuccess)

/-- An initialized annotated binder retains its initializer expression node
through local-binder allocation and the final statement record. -/
theorem inferStatementFuel_success_letAnnotatedInitialized_child_provenance
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {name : Syntax.Identifier}
    {sourceType : Syntax.TypeExpr} {initializer : Syntax.Expr}
    {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    (statementEq : statement.value =
      .letDecl name (some sourceType) (some initializer))
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (roots : List NodeId := []) :
    ∃ resolvedType inferred initializerState,
      Detail.resolveSourceType inferenceContext sourceType = .ok resolvedType ∧
      Detail.inferExprFuel fuel inferenceContext initializer
        (some resolvedType) allocated = .ok (inferred, initializerState) ∧
      ChildStateProvenance allocated initializerState result.state roots := by
  obtain ⟨resolvedType, inferred, initializerState, locals, valueType,
    generalized, binding, resolution, initializerSuccess, _localsEq,
    _valueTypeEq, _generalizedEq, bindingEq, resultEq, _contains⟩ :=
    inferStatementFuel_success_letAnnotatedInitialized_facts statementEq
      allocationEq success roots
  have allocatedBelow : allocated.NodesBelowNextOccurrence := by
    have bound :=
      Frontend.SourceInference.State.allocateStatementId_preserves_nodesBelowNextOccurrence
        initial initialBelow
    have eq : initial.allocateStatementId.2 = allocated :=
      congrArg Prod.snd allocationEq
    simpa [eq] using bound
  refine ⟨resolvedType, inferred, initializerState, resolution,
    initializerSuccess, ?_⟩
  rw [resultEq, ← bindingEq]
  exact child_provenance_through_binder_record allocated initializerState
    locals name.value generalized.scheme (some name.span)
      generalized.requirements _ roots allocatedBelow

/-- The unannotated initialized binder has the same source and ledger
provenance, independent of its separate generalization obligations. -/
theorem inferStatementFuel_success_letUnannotatedInitialized_child_provenance
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {name : Syntax.Identifier}
    {initializer : Syntax.Expr} {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    (statementEq : statement.value =
      .letDecl name none (some initializer))
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (roots : List NodeId := []) :
    ∃ inferred initializerState,
      Detail.inferExprFuel fuel inferenceContext initializer none allocated =
        .ok (inferred, initializerState) ∧
      ChildStateProvenance allocated initializerState result.state roots := by
  obtain ⟨inferred, initializerState, locals, valueType, generalized,
    binding, initializerSuccess, _localsEq, _valueTypeEq, _generalizedEq,
    bindingEq, resultEq, _contains⟩ :=
    inferStatementFuel_success_letUnannotatedInitialized_facts statementEq
      allocationEq success roots
  have allocatedBelow : allocated.NodesBelowNextOccurrence := by
    have bound :=
      Frontend.SourceInference.State.allocateStatementId_preserves_nodesBelowNextOccurrence
        initial initialBelow
    have eq : initial.allocateStatementId.2 = allocated :=
      congrArg Prod.snd allocationEq
    simpa [eq] using bound
  refine ⟨inferred, initializerState, initializerSuccess, ?_⟩
  rw [resultEq, ← bindingEq]
  exact child_provenance_through_binder_record allocated initializerState
    locals name.value generalized.scheme (some name.span)
      generalized.requirements _ roots allocatedBelow

/-- The annotated-let branch consumes initializer typing in the actual
initializer source and weakens it through binder allocation. -/
theorem inferStatementFuel_success_letAnnotatedInitialized_sound_local
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {name : Syntax.Identifier}
    {sourceType : Syntax.TypeExpr} {initializer : Syntax.Expr}
    {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    {outer : TypeSystem.Substitution} {control : ControlContext}
    {target : SourceSemantics.Context}
    (statementEq : statement.value =
      .letDecl name (some sourceType) (some initializer))
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (signatureFormation :
      Frontend.ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ signature ∈
      inferenceContext.signatures.functions,
      signature.scheme.body = .function
        (TypeSystem.Ty.productMany signature.parameterTypes)
        (TypeSystem.Ty.productMany signature.returnTypes))
    (canonical : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (signaturesEq : target.signatures = inferenceContext.signatures)
    (parametersEq : target.typeParameters = inferenceContext.typeParameters)
    (declarationEq : target.currentDeclaration =
      some inferenceContext.scope.genericOwner)
    (ready : initial.InferenceReady)
    (invariant : ActiveLocalContextInvariant initial outer target)
    (below : initial.LocalBindersBelowNextLocal)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (outerExtension : outer.SemanticallyExtends
      result.state.inference.substitution)
    (roots : List NodeId := [])
    (localInitializerSound :
      ∀ {resolvedType : TypeSystem.Ty}
        {inferred : InferredExpression}
        {initializerState : Frontend.SourceInference.State},
        Detail.resolveSourceType inferenceContext sourceType =
          .ok resolvedType →
        Detail.inferExprFuel fuel inferenceContext initializer
            (some resolvedType) allocated = .ok (inferred, initializerState) →
        ExpressionHasType
          ((initializerState.toTypedSource roots).applySubstitution outer)
          target inferred.id (outer.apply inferred.type)) :
    ∃ finalContext facts,
      ActiveLocalContextInvariant result.state outer finalContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution outer)
        control target result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution outer result facts := by
  obtain ⟨actualType, actualInferred, actualState, actualResolution,
    actualSuccess, provenance⟩ :=
    inferStatementFuel_success_letAnnotatedInitialized_child_provenance
      statementEq allocationEq success initialBelow roots
  apply inferStatementFuel_success_letAnnotatedInitialized_sound statementEq
    allocationEq success signatureFormation functionsCanonical canonical
    signaturesEq parametersEq declarationEq ready invariant below
    outerExtension roots
  intro resolvedType inferred initializerState resolution initializerSuccess
  have typeEq : resolvedType = actualType := by
    rw [actualResolution] at resolution
    exact (Except.ok.inj resolution).symm
  subst resolvedType
  have pairEq : (inferred, initializerState) =
      (actualInferred, actualState) := by
    rw [actualSuccess] at initializerSuccess
    exact (Except.ok.inj initializerSuccess).symm
  cases pairEq
  exact ExpressionHasType.weakenSource
    (provenance.sourceExtension.applySubstitution outer)
    (localInitializerSound actualResolution actualSuccess)

end Solcore.SourceSemantics.SourceInferenceStatementsSoundness
