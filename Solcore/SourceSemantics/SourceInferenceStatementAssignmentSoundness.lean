import Solcore.SourceSemantics.SourceInferenceSoundness

/-!
Operational provenance for assignable-place and assignment inference.  The
lemmas in this file expose the exact recursive states used by a successful
assignment; they do not assume soundness of unrelated expressions.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem

/-- Place inference only appends to a node table whose existing occurrences
were allocated before its input cutoff. -/
theorem inferPlaceFuel_success_typingSourceExtends_under_bound
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {target : Syntax.Expr} {initial final : Frontend.SourceInference.State}
    {place : PlaceResolution}
    (success : Detail.inferPlaceFuel fuel inferenceContext target initial =
      .ok (place, final))
    (below : initial.NodesBelowNextOccurrence)
    (roots : List NodeId := []) :
    TypingSourceExtends (initial.toTypedSource roots)
      (final.toTypedSource roots) := by
  constructor
  · exact Detail.inferPlaceFuel_preserves_owner success
  · exact Detail.inferPlaceFuel_preserves_nodesPrefix success
      List.prefix_rfl below (Nat.le_refl _)

/-- The compound assignment traversal likewise retains its anchored input
table; a selected call inside a new RHS cannot rewrite an older place node. -/
theorem inferAssignedValueFuel_success_typingSourceExtends_under_bound
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {target value : Syntax.Expr} {operator : Syntax.ValueAssignOp}
    {initial final : Frontend.SourceInference.State}
    {assignment : AssignmentResolution}
    {inferred : InferredExpression}
    (success : Detail.inferAssignedValueFuel fuel inferenceContext target
      operator value initial = .ok (assignment, inferred, final))
    (below : initial.NodesBelowNextOccurrence)
    (roots : List NodeId := []) :
    TypingSourceExtends (initial.toTypedSource roots)
      (final.toTypedSource roots) := by
  constructor
  · exact Detail.inferAssignedValueFuel_preserves_owner success
  · exact Detail.inferAssignedValueFuel_preserves_nodesPrefix success
      List.prefix_rfl below (Nat.le_refl _)

/-- A successful value-assignment statement records only one fresh statement
node after its actual delegated assignment traversal. -/
theorem inferStatementFuel_success_assignValue_child_provenance
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {targetExpression value : Syntax.Expr}
    {operator : Syntax.Located Syntax.ValueAssignOp}
    {expectedReturn : Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    {outer : Substitution}
    (statementEq : statement.value =
      .assignValue targetExpression operator value)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (roots : List NodeId := []) :
    ∃ assignment inferred assignmentState,
      Detail.inferAssignedValueFuel fuel inferenceContext targetExpression
        operator.value value allocated =
          .ok (assignment, inferred, assignmentState) ∧
      allocated.NodesBelowNextOccurrence ∧
      TypingSourceExtends
        ((assignmentState.toTypedSource roots).applySubstitution outer)
        ((result.state.toTypedSource roots).applySubstitution outer) ∧
      assignmentState.integerPatterns ⊆ result.state.integerPatterns ∧
      assignmentState.requirements ⊆ result.state.requirements := by
  obtain ⟨assignment, inferred, assignmentState, assignmentSuccess,
      resultEq, _⟩ :=
    inferStatementFuel_success_assignValue_facts statementEq allocationEq
      success roots
  have allocatedBelow : allocated.NodesBelowNextOccurrence :=
    by
      have nextBelow :=
        (Frontend.SourceInference.State.OccurrenceBoundExtends.allocateStatementId
          initial).nodesBelowNextOccurrence initialBelow
      simpa only [allocationEq] using nextBelow
  subst result
  refine ⟨assignment, inferred, assignmentState, assignmentSuccess,
    allocatedBelow, ?_, ?_, ?_⟩
  · apply TypingSourceExtends.applySubstitution outer
    constructor
    · rfl
    · exact Frontend.SourceInference.State.recordNode_nodesPrefix
        assignmentState _
  · intro pattern member
    exact member
  · intro requirement member
    exact member

/-- Bit-not assignment uses exactly one place traversal, one unification to
`Word`, and one fresh statement node.  All indexed key expressions therefore
remain in the parent source and both evidence ledgers are preserved. -/
theorem inferStatementFuel_success_assignBitNot_child_provenance
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {targetExpression : Syntax.Expr}
    {operatorSpan : Syntax.SourceSpan} {expectedReturn : Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    {outer : Substitution}
    (statementEq : statement.value =
      .assignBitNot targetExpression operatorSpan)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (roots : List NodeId := []) :
    ∃ place placeState unified,
      Detail.inferPlaceFuel fuel inferenceContext targetExpression allocated =
        .ok (place, placeState) ∧
      Detail.unify placeState place.type .word = .ok unified ∧
      allocated.NodesBelowNextOccurrence ∧
      TypingSourceExtends
        ((placeState.toTypedSource roots).applySubstitution outer)
        ((result.state.toTypedSource roots).applySubstitution outer) ∧
      placeState.integerPatterns ⊆ result.state.integerPatterns ∧
      placeState.requirements ⊆ result.state.requirements := by
  obtain ⟨place, placeState, unified, placeSuccess, unifiedSuccess, _,
      resultEq, _⟩ :=
    inferStatementFuel_success_assignBitNot_facts statementEq allocationEq
      success roots
  have allocatedBelow : allocated.NodesBelowNextOccurrence := by
    have nextBelow :=
      (Frontend.SourceInference.State.OccurrenceBoundExtends.allocateStatementId
        initial).nodesBelowNextOccurrence initialBelow
    simpa only [allocationEq] using nextBelow
  have placeToUnified : TypingSourceExtends
      (placeState.toTypedSource roots) (unified.toTypedSource roots) := by
    constructor
    · have headerEq := Detail.unify_state_header unifiedSuccess
      have ownerEq := congrArg Frontend.SourceInference.State.Header.owner
        headerEq
      simpa [Frontend.SourceInference.State.toTypedSource,
        Frontend.SourceInference.State.header] using ownerEq
    · have nodesEq := (Detail.unify_occurrenceState_eq unifiedSuccess).1
      change placeState.nodes <+: unified.nodes
      rw [nodesEq]
      exact List.prefix_rfl
  have unifiedToRecorded : TypingSourceExtends
      (unified.toTypedSource roots)
      ((unified.recordNode (.statement {
          id
          span := statement.span
          type := .unit
          form := .assignBitNot {
            target := { place with type := unified.resolve place.type }
          }
        })).toTypedSource roots) := by
    constructor
    · rfl
    · exact Frontend.SourceInference.State.recordNode_nodesPrefix unified _
  subst result
  refine ⟨place, placeState, unified, placeSuccess, unifiedSuccess,
    allocatedBelow, ?_, ?_, ?_⟩
  · exact (placeToUnified.trans unifiedToRecorded).applySubstitution outer
  · intro pattern member
    change pattern ∈ unified.integerPatterns
    rw [Detail.unify_integerPatterns unifiedSuccess]
    exact member
  · intro requirement member
    change requirement ∈ unified.requirements
    rw [Detail.unify_requirements_eq unifiedSuccess]
    exact member

/-- Once the one actual delegated assignment has been typed, the enclosing
statement needs no hypothesis about any other place or RHS computation. -/
theorem inferStatementFuel_success_assignValue_sound_of_actual_child
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {targetExpression value : Syntax.Expr}
    {operator : Syntax.Located Syntax.ValueAssignOp}
    {expectedReturn : Ty}
    {initial allocated assignmentState : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    {assignment : AssignmentResolution} {inferred : InferredExpression}
    {outer : Substitution} {control : ControlContext}
    {target : SourceSemantics.Context}
    (statementEq : statement.value =
      .assignValue targetExpression operator value)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (invariant : ActiveLocalContextInvariant initial outer target)
    (roots : List NodeId := [])
    (assignmentSuccess : Detail.inferAssignedValueFuel fuel inferenceContext
      targetExpression operator.value value allocated =
        .ok (assignment, inferred, assignmentState))
    (assignmentTyped : SourceAssignmentHasType
      ((result.state.toTypedSource roots).applySubstitution outer) target
      (assignment.applySubstitution outer) operator.value inferred.id) :
    ActiveLocalContextInvariant result.state outer target ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution outer)
        control target result.id target {
          type := .unit
          hasValue := false
          sawReturn := false
          control := .ordinary .unit
        } ∧
      StatementResultMatchesFactsAfterSubstitution outer result {
        type := .unit
        hasValue := false
        sawReturn := false
        control := .ordinary .unit
      } := by
  apply inferStatementFuel_success_assignValue_sound statementEq allocationEq
    success invariant roots
  intro actualAssignment actualValue actualState actualSuccess
  rw [assignmentSuccess] at actualSuccess
  obtain ⟨rfl, rfl, rfl⟩ := (Except.ok.inj actualSuccess).symm
  exact assignmentTyped

/-- The bit-not statement consumes only the place returned by its actual
delegated place inference. -/
theorem inferStatementFuel_success_assignBitNot_sound_of_actual_child
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {targetExpression : Syntax.Expr}
    {operatorSpan : Syntax.SourceSpan} {expectedReturn : Ty}
    {initial allocated placeState : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    {place : PlaceResolution}
    {outer : Substitution} {control : ControlContext}
    {target : SourceSemantics.Context}
    (statementEq : statement.value =
      .assignBitNot targetExpression operatorSpan)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (invariant : ActiveLocalContextInvariant initial outer target)
    (outerExtension : outer.SemanticallyExtends
      result.state.inference.substitution)
    (roots : List NodeId := [])
    (placeSuccess : Detail.inferPlaceFuel fuel inferenceContext
      targetExpression allocated = .ok (place, placeState))
    (placeTyped : SourcePlaceHasType
      ((result.state.toTypedSource roots).applySubstitution outer)
      target (place.applySubstitution outer) (outer.apply place.type)) :
    ActiveLocalContextInvariant result.state outer target ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution outer)
        control target result.id target {
          type := .unit
          hasValue := false
          sawReturn := false
          control := .ordinary .unit
        } ∧
      StatementResultMatchesFactsAfterSubstitution outer result {
        type := .unit
        hasValue := false
        sawReturn := false
        control := .ordinary .unit
      } := by
  apply inferStatementFuel_success_assignBitNot_sound statementEq allocationEq
    success invariant outerExtension roots
  intro actualPlace actualState actualSuccess
  rw [placeSuccess] at actualSuccess
  obtain ⟨rfl, rfl⟩ := (Except.ok.inj actualSuccess).symm
  exact placeTyped

/-- Assignment inference needs only the typing of the place and value it
actually returned.  The executable expectation and unification checks
identify their finalized types; no global expression-soundness callback is
needed at this boundary. -/
theorem inferAssignedValueFuel_success_sound_of_typed_result
    {source : TypedSource} {outer : Substitution}
    {target : SourceSemantics.Context}
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {targetExpression value : Syntax.Expr}
    {operator : Syntax.ValueAssignOp}
    {initial final : Frontend.SourceInference.State}
    {assignment : AssignmentResolution}
    {inferredValue : InferredExpression}
    (ready : initial.InferenceReady)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical :
      ∀ signature ∈ inferenceContext.signatures.functions,
        signature.scheme.body = .function
          (Ty.productMany signature.parameterTypes)
          (Ty.productMany signature.returnTypes))
    (outerExtension : outer.SemanticallyExtends
      final.inference.substitution)
    (placeTyped : SourcePlaceHasType (source.applySubstitution outer) target
      (assignment.target.applySubstitution outer)
      (outer.apply assignment.target.type))
    (valueTyped : ExpressionHasType (source.applySubstitution outer) target
      inferredValue.id (outer.apply inferredValue.type))
    (success : Detail.inferAssignedValueFuel fuel inferenceContext
      targetExpression operator value initial =
        .ok (assignment, inferredValue, final)) :
    SourceAssignmentHasType (source.applySubstitution outer) target
      (assignment.applySubstitution outer) operator inferredValue.id := by
  unfold Detail.inferAssignedValueFuel at success
  cases placeResult : Detail.inferPlaceFuel fuel inferenceContext
      targetExpression initial with
  | error error =>
      simp [placeResult, bind, Except.bind] at success
  | ok placePair =>
      rcases placePair with ⟨place, placeState⟩
      simp only [placeResult, bind, Except.bind, Prod.eta] at success
      have placeProperties := Detail.inferPlaceFuel_inferenceProperties ready
        signatureFormation functionsCanonical placeResult
      have finishNonEqual
          (operatorKind : WordCompoundAssignmentOperator operator)
          (tailSuccess :
            (do
              let fittedState ← Detail.unify placeState place.type .word
              let (inferredValue, finalState) ←
                Detail.inferExprFuel fuel inferenceContext value (some .word)
                  fittedState
              pure (({ target := { place with
                type := finalState.resolve place.type } } :
                  AssignmentResolution), inferredValue, finalState)) =
                .ok (assignment, inferredValue, final)) :
          SourceAssignmentHasType (source.applySubstitution outer) target
            (assignment.applySubstitution outer) operator inferredValue.id := by
        cases unifyResult : Detail.unify placeState place.type .word with
        | error error =>
            simp [unifyResult, bind, Except.bind] at tailSuccess
        | ok fittedState =>
            simp only [unifyResult, bind, Except.bind] at tailSuccess
            have fitProgress := Detail.unify_inferenceProgress
              placeProperties.2.1.solved placeProperties.2.2
              (Ty.variablesBelow_constructor _ _) unifyResult
            have fittedReady := Detail.unify_preserves_inferenceReady
              placeProperties.2.1 placeProperties.2.2
              (Ty.variablesBelow_constructor _ _) unifyResult
            cases valueResult : Detail.inferExprFuel fuel inferenceContext
                value (some .word) fittedState with
            | error error =>
                simp [valueResult] at tailSuccess
            | ok valuePair =>
                rcases valuePair with ⟨inferred, finalState⟩
                simp only [valueResult, pure, Pure.pure, Except.pure]
                  at tailSuccess
                injection tailSuccess with resultEq
                injection resultEq with assignmentEq valueStateEq
                injection valueStateEq with inferredEq finalEq
                subst assignment
                subst inferredValue
                subst final
                have valueProperties :=
                  Detail.inferExprFuel_inferenceProperties fittedReady
                    signatureFormation functionsCanonical (by
                      intro expectedType member
                      simp only [Option.mem_def] at member
                      injection member with typeEq
                      subst expectedType
                      exact Ty.variablesBelow_constructor _ _)
                    valueResult
                have outerFitted : outer.SemanticallyExtends
                    fittedState.inference.substitution :=
                  Substitution.SemanticallyExtends.trans outerExtension
                    valueProperties.1.substitution_extends
                have resolvedWord : fittedState.resolve place.type = .word :=
                  (Detail.unify_resolve_eq unifyResult).trans (by rfl)
                have placeWordEq : outer.apply place.type = .word := by
                  calc
                    outer.apply place.type =
                        outer.apply (fittedState.resolve place.type) := by
                      simpa [Frontend.SourceInference.State.resolve,
                        TypeSystem.InferState.resolve] using
                          (outerFitted place.type).symm
                    _ = outer.apply .word := congrArg outer.apply resolvedWord
                    _ = .word := rfl
                have storedWordEq :
                    outer.apply (finalState.resolve place.type) = .word := by
                  calc
                    outer.apply (finalState.resolve place.type) =
                        outer.apply place.type := by
                      simpa [Frontend.SourceInference.State.resolve,
                        TypeSystem.InferState.resolve] using
                          outerExtension place.type
                    _ = .word := placeWordEq
                have placeWord : SourcePlaceHasType
                    (source.applySubstitution outer) target
                    (({ place with type := finalState.resolve place.type } :
                      PlaceResolution).applySubstitution outer) .word := by
                  rw [← storedWordEq]
                  exact placeTyped
                have valueWordEq : outer.apply inferred.type = .word := by
                  simpa using
                    (Detail.inferExprFuel_expected_type_apply_eq valueResult
                      outerExtension)
                have valueWord : ExpressionHasType
                    (source.applySubstitution outer) target inferred.id
                    .word := by
                  rw [← valueWordEq]
                  exact valueTyped
                exact .wordCompound operatorKind placeWord valueWord rfl
      cases operator with
      | equal =>
          simp only [pure, Pure.pure, Except.pure] at success
          cases valueResult : Detail.inferExprFuel fuel inferenceContext value
              (some (placeState.resolve place.type)) placeState with
          | error error =>
              simp [valueResult] at success
          | ok valuePair =>
              rcases valuePair with ⟨inferred, finalState⟩
              simp only [valueResult] at success
              injection success with resultEq
              injection resultEq with assignmentEq valueStateEq
              injection valueStateEq with inferredEq finalEq
              subst assignment
              subst inferredValue
              subst final
              have expectedBelow :
                  (placeState.resolve place.type).VariablesBelow
                    placeState.inference.next :=
                placeProperties.2.1.solved.variablesBelow_apply
                  placeProperties.2.2
              have valueProperties :=
                Detail.inferExprFuel_inferenceProperties
                  placeProperties.2.1 signatureFormation functionsCanonical
                  (by
                    intro expectedType member
                    simp only [Option.mem_def] at member
                    injection member with typeEq
                    subst expectedType
                    exact expectedBelow) valueResult
              have outerPlace : outer.SemanticallyExtends
                  placeState.inference.substitution :=
                Substitution.SemanticallyExtends.trans outerExtension
                  valueProperties.1.substitution_extends
              have valueEq : outer.apply inferred.type =
                  outer.apply (finalState.resolve place.type) := by
                calc
                  outer.apply inferred.type =
                      outer.apply (placeState.resolve place.type) :=
                    Detail.inferExprFuel_expected_type_apply_eq valueResult
                      outerExtension
                  _ = outer.apply place.type := by
                    simpa [Frontend.SourceInference.State.resolve,
                      TypeSystem.InferState.resolve] using
                        outerPlace place.type
                  _ = outer.apply (finalState.resolve place.type) := by
                    simpa [Frontend.SourceInference.State.resolve,
                      TypeSystem.InferState.resolve] using
                        (outerExtension place.type).symm
              have valueAtPlace : ExpressionHasType
                  (source.applySubstitution outer) target inferred.id
                  (outer.apply (finalState.resolve place.type)) := by
                rw [← valueEq]
                exact valueTyped
              exact .equal placeTyped valueAtPlace rfl
      | add => exact finishNonEqual .add success
      | subtract => exact finishNonEqual .subtract success
      | multiply => exact finishNonEqual .multiply success
      | divide => exact finishNonEqual .divide success
      | modulo => exact finishNonEqual .modulo success
      | bitAnd => exact finishNonEqual .bitAnd success
      | bitXor => exact finishNonEqual .bitXor success
      | bitOr => exact finishNonEqual .bitOr success

/-- The indexed-place branch is compositional in just its actual recursive
base place and actual mapping-key expression.  This is the one-step rule
needed by the closed place/expression induction. -/
theorem inferPlaceFuel_success_index_sound_of_actual_children
    {source : TypedSource} {outer : Substitution}
    {target : SourceSemantics.Context}
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {targetExpression base key : Syntax.Expr}
    {brackets : Syntax.SourceSpan}
    {initial final : Frontend.SourceInference.State}
    {place : PlaceResolution}
    (targetEq : targetExpression.value = .index base brackets key)
    (ready : initial.InferenceReady)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical :
      ∀ signature ∈ inferenceContext.signatures.functions,
        signature.scheme.body = .function
          (Ty.productMany signature.parameterTypes)
          (Ty.productMany signature.returnTypes))
    (outerExtension : outer.SemanticallyExtends
      final.inference.substitution)
    (baseSound :
      ∀ {basePlace : PlaceResolution}
        {baseState : Frontend.SourceInference.State},
        Detail.inferPlaceFuel fuel inferenceContext base initial =
          .ok (basePlace, baseState) →
        SourcePlaceHasType (source.applySubstitution outer) target
          (basePlace.applySubstitution outer) (outer.apply basePlace.type))
    (keySound :
      ∀ {expected : Ty} {keyInitial keyFinal : Frontend.SourceInference.State}
        {inferred : InferredExpression},
        Detail.inferExprFuel fuel inferenceContext key (some expected)
          keyInitial = .ok (inferred, keyFinal) →
        ExpressionHasType (source.applySubstitution outer) target
          inferred.id (outer.apply inferred.type))
    (success : Detail.inferPlaceFuel (fuel + 1) inferenceContext
      targetExpression initial = .ok (place, final)) :
    SourcePlaceHasType (source.applySubstitution outer) target
      (place.applySubstitution outer) (outer.apply place.type) := by
  unfold Detail.inferPlaceFuel at success
  simp only [targetEq, bind, Except.bind] at success
  cases baseResult : Detail.inferPlaceFuel fuel inferenceContext base
      initial with
  | error error =>
      simp [baseResult] at success
  | ok basePair =>
      rcases basePair with ⟨basePlace, baseState⟩
      simp only [baseResult] at success
      let keyAllocation := baseState.fresh
      let valueAllocation := keyAllocation.2.fresh
      cases unifyResult : Detail.unify valueAllocation.2 basePlace.type
          (.mapping keyAllocation.1 valueAllocation.1) with
      | error error =>
          simp [keyAllocation, valueAllocation, unifyResult] at success
      | ok unifiedState =>
          simp only [keyAllocation, valueAllocation, unifyResult] at success
          cases keyResult : Detail.inferExprFuel fuel inferenceContext key
              (some (unifiedState.resolve keyAllocation.1)) unifiedState with
          | error error =>
              simp [keyAllocation, keyResult] at success
          | ok keyPair =>
              rcases keyPair with ⟨inferredKey, keyState⟩
              simp only [keyAllocation, keyResult, pure, Pure.pure,
                Except.pure] at success
              injection success with resultEq
              injection resultEq with placeEq finalEq
              subst place
              subst final
              have baseProperties :=
                Detail.inferPlaceFuel_inferenceProperties ready
                  signatureFormation functionsCanonical baseResult
              have keyProperties :=
                Detail.fresh_eq_inferenceProperties
                  baseProperties.2.1
                  (initial := baseState) (type := keyAllocation.1)
                  (next := keyAllocation.2) rfl
              have valueProperties :=
                Detail.fresh_eq_inferenceProperties
                  keyProperties.2.1
                  (initial := keyAllocation.2)
                  (type := valueAllocation.1)
                  (next := valueAllocation.2) rfl
              have baseAtValue : basePlace.type.VariablesBelow
                  valueAllocation.2.inference.next :=
                baseProperties.2.2.weaken
                  (keyProperties.1.trans valueProperties.1).next_le
              have keyAtValue : keyAllocation.1.VariablesBelow
                  valueAllocation.2.inference.next :=
                keyProperties.2.2.weaken valueProperties.1.next_le
              have mappingBelow :
                  (Ty.mapping keyAllocation.1 valueAllocation.1).VariablesBelow
                    valueAllocation.2.inference.next :=
                (Ty.variablesBelow_mapping_iff _ _ _).2
                  ⟨keyAtValue, valueProperties.2.2⟩
              have unifyProgress := Detail.unify_inferenceProgress
                valueProperties.2.1.solved baseAtValue mappingBelow
                unifyResult
              have unifiedReady := Detail.unify_preserves_inferenceReady
                valueProperties.2.1 baseAtValue mappingBelow unifyResult
              have keyAtUnified : keyAllocation.1.VariablesBelow
                  unifiedState.inference.next :=
                keyAtValue.weaken unifyProgress.next_le
              have resolvedKeyBelow :
                  (unifiedState.resolve keyAllocation.1).VariablesBelow
                    unifiedState.inference.next :=
                unifiedReady.solved.variablesBelow_apply keyAtUnified
              have keyExpressionProperties :=
                Detail.inferExprFuel_inferenceProperties unifiedReady
                  signatureFormation functionsCanonical (by
                    intro expectedType member
                    simp only [Option.mem_def] at member
                    injection member with typeEq
                    subst expectedType
                    exact resolvedKeyBelow) keyResult
              have outerUnified : outer.SemanticallyExtends
                  unifiedState.inference.substitution :=
                Substitution.SemanticallyExtends.trans outerExtension
                  keyExpressionProperties.1.substitution_extends
              have mappingEq : outer.apply basePlace.type =
                  .mapping (outer.apply keyAllocation.1)
                    (outer.apply valueAllocation.1) := by
                calc
                  outer.apply basePlace.type =
                      outer.apply (unifiedState.resolve basePlace.type) := by
                    simpa [Frontend.SourceInference.State.resolve,
                      TypeSystem.InferState.resolve] using
                        (outerUnified basePlace.type).symm
                  _ = outer.apply (unifiedState.resolve
                        (.mapping keyAllocation.1 valueAllocation.1)) :=
                    congrArg outer.apply (Detail.unify_resolve_eq unifyResult)
                  _ = outer.apply
                        (.mapping keyAllocation.1 valueAllocation.1) := by
                    simpa [Frontend.SourceInference.State.resolve,
                      TypeSystem.InferState.resolve] using
                        outerUnified
                          (.mapping keyAllocation.1 valueAllocation.1)
                  _ = .mapping (outer.apply keyAllocation.1)
                        (outer.apply valueAllocation.1) := rfl
              have baseMapping : SourcePlaceHasType
                  (source.applySubstitution outer) target
                  (basePlace.applySubstitution outer)
                  (.mapping (outer.apply keyAllocation.1)
                    (outer.apply valueAllocation.1)) := by
                rw [← mappingEq]
                exact baseSound baseResult
              have keyExpectedEq : outer.apply inferredKey.type =
                  outer.apply keyAllocation.1 := by
                calc
                  outer.apply inferredKey.type =
                      outer.apply
                        (unifiedState.resolve keyAllocation.1) :=
                    Detail.inferExprFuel_expected_type_apply_eq keyResult
                      outerExtension
                  _ = outer.apply keyAllocation.1 := by
                    simpa [Frontend.SourceInference.State.resolve,
                      TypeSystem.InferState.resolve] using
                        outerUnified keyAllocation.1
              have keyType : ExpressionHasType
                  (source.applySubstitution outer) target inferredKey.id
                  (outer.apply keyAllocation.1) := by
                rw [← keyExpectedEq]
                exact keySound keyResult
              have indexed := SourcePlaceHasType.snocIndex baseMapping
                keyType
              have resolvedValueEq :
                  outer.apply (keyState.resolve valueAllocation.1) =
                    outer.apply valueAllocation.1 := by
                simpa [Frontend.SourceInference.State.resolve,
                  TypeSystem.InferState.resolve] using
                    outerExtension valueAllocation.1
              simpa [keyAllocation, valueAllocation,
                PlaceResolution.applySubstitution, resolvedValueEq]
                using indexed

/-- Once a place has been inferred, the remaining RHS traversal cannot
rewrite its already allocated nodes.  This exposes the intermediate place
state used by an actual successful assignment together with its retained
source and evidence ledgers. -/
theorem inferAssignedValueFuel_success_place_state_provenance
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {targetExpression value : Syntax.Expr}
    {operator : Syntax.ValueAssignOp}
    {initial final : Frontend.SourceInference.State}
    {assignment : AssignmentResolution}
    {inferredValue : InferredExpression}
    (success : Detail.inferAssignedValueFuel fuel inferenceContext
      targetExpression operator value initial =
        .ok (assignment, inferredValue, final))
    (below : initial.NodesBelowNextOccurrence)
    (roots : List NodeId := []) :
    ∃ place placeState,
      Detail.inferPlaceFuel fuel inferenceContext targetExpression initial =
        .ok (place, placeState) ∧
      placeState.NodesBelowNextOccurrence ∧
      TypingSourceExtends (placeState.toTypedSource roots)
        (final.toTypedSource roots) ∧
      placeState.integerPatterns ⊆ final.integerPatterns ∧
      placeState.requirements ⊆ final.requirements := by
  unfold Detail.inferAssignedValueFuel at success
  cases placeResult : Detail.inferPlaceFuel fuel inferenceContext
      targetExpression initial with
  | error error =>
      simp [placeResult, bind, Except.bind] at success
  | ok placePair =>
      rcases placePair with ⟨place, placeState⟩
      simp only [placeResult, bind, Except.bind, Prod.eta] at success
      have placeBelow : placeState.NodesBelowNextOccurrence :=
        (Detail.inferPlaceFuel_occurrenceBoundExtends
          placeResult).nodesBelowNextOccurrence below
      have finishNonEqual
          (tailSuccess :
            (do
              let fittedState ← Detail.unify placeState place.type .word
              let (inferredValue, finalState) ←
                Detail.inferExprFuel fuel inferenceContext value (some .word)
                  fittedState
              pure (({ target := { place with
                type := finalState.resolve place.type } } :
                  AssignmentResolution), inferredValue, finalState)) =
                .ok (assignment, inferredValue, final)) :
          ∃ actualPlace actualState,
            (Except.ok (place, placeState) : Except Frontend.SourceInference.Error
              (PlaceResolution × Frontend.SourceInference.State)) =
                .ok (actualPlace, actualState) ∧
            actualState.NodesBelowNextOccurrence ∧
            TypingSourceExtends (actualState.toTypedSource roots)
              (final.toTypedSource roots) ∧
            actualState.integerPatterns ⊆ final.integerPatterns ∧
            actualState.requirements ⊆ final.requirements := by
        cases unifyResult : Detail.unify placeState place.type .word with
        | error error =>
            simp [unifyResult, bind, Except.bind] at tailSuccess
        | ok fittedState =>
            simp only [unifyResult, bind, Except.bind] at tailSuccess
            cases valueResult : Detail.inferExprFuel fuel inferenceContext
                value (some .word) fittedState with
            | error error =>
                simp [valueResult] at tailSuccess
            | ok valuePair =>
                rcases valuePair with ⟨inferred, finalState⟩
                simp only [valueResult, pure, Pure.pure, Except.pure]
                  at tailSuccess
                injection tailSuccess with resultEq
                injection resultEq with assignmentEq valueStateEq
                injection valueStateEq with inferredEq finalEq
                subst assignment
                subst inferredValue
                subst final
                have fittedBelow : fittedState.NodesBelowNextOccurrence :=
                  (Detail.unify_occurrenceBoundExtends
                    unifyResult).nodesBelowNextOccurrence placeBelow
                have placeToFitted : TypingSourceExtends
                    (placeState.toTypedSource roots)
                    (fittedState.toTypedSource roots) := by
                  constructor
                  · have headerEq := Detail.unify_state_header unifyResult
                    have ownerEq :=
                      congrArg Frontend.SourceInference.State.Header.owner
                        headerEq
                    simpa [Frontend.SourceInference.State.toTypedSource,
                      Frontend.SourceInference.State.header] using ownerEq
                  · have nodesEq :=
                      (Detail.unify_occurrenceState_eq unifyResult).1
                    change placeState.nodes <+: fittedState.nodes
                    rw [nodesEq]
                    exact List.prefix_rfl
                refine ⟨place, placeState, rfl, placeBelow,
                  placeToFitted.trans
                    (inferExprFuel_success_typingSourceExtends valueResult
                      fittedBelow roots), ?_, ?_⟩
                · rw [← Detail.unify_integerPatterns unifyResult]
                  exact Detail.inferExprFuel_integerPatterns_subset valueResult
                · exact (Detail.unify_requirements_subset unifyResult).trans
                    (Detail.inferExprFuel_requirements_subset valueResult)
      cases operator with
      | equal =>
          simp only [pure, Pure.pure, Except.pure] at success
          cases valueResult : Detail.inferExprFuel fuel inferenceContext value
              (some (placeState.resolve place.type)) placeState with
          | error error =>
              simp [valueResult] at success
          | ok valuePair =>
              rcases valuePair with ⟨inferred, finalState⟩
              simp only [valueResult] at success
              injection success with resultEq
              injection resultEq with assignmentEq valueStateEq
              injection valueStateEq with inferredEq finalEq
              subst assignment
              subst inferredValue
              subst final
              exact ⟨place, placeState, rfl, placeBelow,
                inferExprFuel_success_typingSourceExtends valueResult
                  placeBelow roots,
                Detail.inferExprFuel_integerPatterns_subset valueResult,
                Detail.inferExprFuel_requirements_subset valueResult⟩
      | add => exact finishNonEqual success
      | subtract => exact finishNonEqual success
      | multiply => exact finishNonEqual success
      | divide => exact finishNonEqual success
      | modulo => exact finishNonEqual success
      | bitAnd => exact finishNonEqual success
      | bitXor => exact finishNonEqual success
      | bitOr => exact finishNonEqual success

/-- In an indexed place, the recursive base traversal is an anchored prefix
of the whole place traversal.  In particular, a selected call used as the new
mapping key may refine only nodes allocated after that base prefix. -/
theorem inferPlaceFuel_success_index_base_state_provenance
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {targetExpression base key : Syntax.Expr}
    {brackets : Syntax.SourceSpan}
    {initial final : Frontend.SourceInference.State}
    {place : PlaceResolution}
    (targetEq : targetExpression.value = .index base brackets key)
    (success : Detail.inferPlaceFuel (fuel + 1) inferenceContext
      targetExpression initial = .ok (place, final))
    (below : initial.NodesBelowNextOccurrence)
    (roots : List NodeId := []) :
    ∃ basePlace baseState,
      Detail.inferPlaceFuel fuel inferenceContext base initial =
        .ok (basePlace, baseState) ∧
      baseState.NodesBelowNextOccurrence ∧
      TypingSourceExtends (baseState.toTypedSource roots)
        (final.toTypedSource roots) ∧
      baseState.integerPatterns ⊆ final.integerPatterns ∧
      baseState.requirements ⊆ final.requirements := by
  unfold Detail.inferPlaceFuel at success
  simp only [targetEq, bind, Except.bind] at success
  cases baseResult : Detail.inferPlaceFuel fuel inferenceContext base
      initial with
  | error error =>
      simp [baseResult] at success
  | ok basePair =>
      rcases basePair with ⟨basePlace, baseState⟩
      simp only [baseResult] at success
      let keyAllocation := baseState.fresh
      let valueAllocation := keyAllocation.2.fresh
      cases unifyResult : Detail.unify valueAllocation.2 basePlace.type
          (.mapping keyAllocation.1 valueAllocation.1) with
      | error error =>
          simp [keyAllocation, valueAllocation, unifyResult] at success
      | ok unifiedState =>
          simp only [keyAllocation, valueAllocation, unifyResult] at success
          cases keyResult : Detail.inferExprFuel fuel inferenceContext key
              (some (unifiedState.resolve keyAllocation.1)) unifiedState with
          | error error =>
              simp [keyAllocation, keyResult] at success
          | ok keyPair =>
              rcases keyPair with ⟨inferredKey, keyState⟩
              simp only [keyAllocation, keyResult, pure, Pure.pure,
                Except.pure] at success
              injection success with resultEq
              injection resultEq with placeEq finalEq
              subst place
              subst final
              have baseBelow : baseState.NodesBelowNextOccurrence :=
                (Detail.inferPlaceFuel_occurrenceBoundExtends
                  baseResult).nodesBelowNextOccurrence below
              have keyAllocatedBelow :
                  keyAllocation.2.NodesBelowNextOccurrence :=
                (Frontend.SourceInference.State.OccurrenceBoundExtends.fresh
                  baseState).nodesBelowNextOccurrence baseBelow
              have valueAllocatedBelow :
                  valueAllocation.2.NodesBelowNextOccurrence :=
                (Frontend.SourceInference.State.OccurrenceBoundExtends.fresh
                  keyAllocation.2).nodesBelowNextOccurrence
                    keyAllocatedBelow
              have unifiedBelow : unifiedState.NodesBelowNextOccurrence :=
                (Detail.unify_occurrenceBoundExtends
                  unifyResult).nodesBelowNextOccurrence valueAllocatedBelow
              have baseToUnified : TypingSourceExtends
                  (baseState.toTypedSource roots)
                  (unifiedState.toTypedSource roots) := by
                constructor
                · have headerEq := Detail.unify_state_header unifyResult
                  have ownerEq :=
                    congrArg Frontend.SourceInference.State.Header.owner
                      headerEq
                  simpa [Frontend.SourceInference.State.toTypedSource,
                    Frontend.SourceInference.State.header,
                    Frontend.SourceInference.State.fresh,
                    keyAllocation, valueAllocation] using ownerEq
                · have nodesEq :=
                    (Detail.unify_occurrenceState_eq unifyResult).1
                  change baseState.nodes <+: unifiedState.nodes
                  rw [nodesEq]
                  simp [keyAllocation, valueAllocation,
                    Frontend.SourceInference.State.fresh]
              refine ⟨basePlace, baseState, rfl, baseBelow,
                baseToUnified.trans
                  (inferExprFuel_success_typingSourceExtends keyResult
                    unifiedBelow roots), ?_, ?_⟩
              · intro pattern member
                have inUnified : pattern ∈ unifiedState.integerPatterns := by
                  rw [Detail.unify_integerPatterns unifyResult]
                  simpa [keyAllocation, valueAllocation,
                    Frontend.SourceInference.State.fresh] using member
                exact Detail.inferExprFuel_integerPatterns_subset keyResult
                  inUnified
              · intro requirement member
                have inUnified : requirement ∈ unifiedState.requirements := by
                  rw [Detail.unify_requirements_eq unifyResult]
                  simpa [keyAllocation, valueAllocation,
                    Frontend.SourceInference.State.fresh] using member
                exact Detail.inferExprFuel_requirements_subset keyResult
                  inUnified

end Solcore.SourceSemantics.SourceInferenceSoundness
