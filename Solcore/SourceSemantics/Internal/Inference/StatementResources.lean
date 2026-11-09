import Solcore.SourceSemantics.Internal.Inference.Soundness
import Solcore.SourceSemantics.InferenceSoundness
import Solcore.SourceSemantics.Internal.Inference.StatementSequences
import Solcore.SourceSemantics.Internal.Inference.LetCertificates

/-!
# Statement resources

Assignment provenance, stable local bounds, the interface of the recursive proof, and the
non-recursive assembly of loops.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceStatementAssignmentSoundness
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
      assignmentState.integerLiterals ⊆ result.state.integerLiterals ∧
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
    allocatedBelow, ?_, ?_, ?_, ?_⟩
  · apply TypingSourceExtends.applySubstitution outer
    constructor
    · rfl
    · exact Frontend.SourceInference.State.recordNode_nodesPrefix
        assignmentState _
  · intro literal member
    exact member
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
      placeState.integerLiterals ⊆ result.state.integerLiterals ∧
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
    allocatedBelow, ?_, ?_, ?_, ?_⟩
  · exact (placeToUnified.trans unifiedToRecorded).applySubstitution outer
  · intro literal member
    change literal ∈ unified.integerLiterals
    rw [Detail.unify_integerLiterals unifiedSuccess]
    exact member
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
      | shiftLeft => exact finishNonEqual .shiftLeft success
      | shiftRight => exact finishNonEqual .shiftRight success
      | uncheckedAdd => exact finishNonEqual .uncheckedAdd success
      | uncheckedSubtract => exact finishNonEqual .uncheckedSubtract success
      | uncheckedMultiply => exact finishNonEqual .uncheckedMultiply success
      | uncheckedDivide => exact finishNonEqual .uncheckedDivide success
      | uncheckedModulo => exact finishNonEqual .uncheckedModulo success

/-- Once the actual place and RHS are typed in the completed statement
source, executable assignment inference supplies every remaining premise of
the declarative statement rule. -/
theorem inferStatementFuel_success_assignValue_sound_of_typed_children
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
    (assignmentSuccess : Detail.inferAssignedValueFuel fuel inferenceContext
      targetExpression operator.value value allocated =
        .ok (assignment, inferred, assignmentState))
    (ready : initial.InferenceReady)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical :
      ∀ signature ∈ inferenceContext.signatures.functions,
        signature.scheme.body = .function
          (Ty.productMany signature.parameterTypes)
          (Ty.productMany signature.returnTypes))
    (invariant : ActiveLocalContextInvariant initial outer target)
    (outerExtension : outer.SemanticallyExtends
      result.state.inference.substitution)
    (roots : List NodeId := [])
    (placeTyped : SourcePlaceHasType
      ((result.state.toTypedSource roots).applySubstitution outer) target
      (assignment.target.applySubstitution outer)
      (outer.apply assignment.target.type))
    (valueTyped : ExpressionHasType
      ((result.state.toTypedSource roots).applySubstitution outer) target
      inferred.id (outer.apply inferred.type)) :
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
  have allocatedReady : allocated.InferenceReady := by
    have preserved :=
      Frontend.SourceInference.State.InferenceReady.allocateStatementId ready
    rw [allocationEq] at preserved
    exact preserved
  obtain ⟨actualAssignment, actualInferred, actualState, actualSuccess,
      resultEq, _⟩ :=
    inferStatementFuel_success_assignValue_facts statementEq allocationEq
      success roots
  rw [assignmentSuccess] at actualSuccess
  obtain ⟨rfl, rfl, rfl⟩ := (Except.ok.inj actualSuccess).symm
  have assignmentExtension : outer.SemanticallyExtends
      assignmentState.inference.substitution := by
    rw [resultEq] at outerExtension
    simpa [Frontend.SourceInference.State.recordNode] using outerExtension
  have assignmentTyped :=
    inferAssignedValueFuel_success_sound_of_typed_result allocatedReady
      signatureFormation functionsCanonical assignmentExtension placeTyped
      valueTyped assignmentSuccess
  exact inferStatementFuel_success_assignValue_sound_of_actual_child
    statementEq allocationEq success invariant roots assignmentSuccess
    assignmentTyped

/-- The assignment statement's final rule consumes only its *actual*
delegated traversal.  Its recorded parent covers every indexed key and the
RHS in the whole finalized graph; the callback receives the corresponding
source/evidence prefix facts rather than an assumption about unrelated
expression calls. -/
theorem inferStatementFuel_success_assignValue_bounded_scoped
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {targetExpression value : Syntax.Expr}
    {operator : Syntax.Located Syntax.ValueAssignOp}
    {expectedReturn : Ty}
    {initial allocated evidenceState : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    {outer : Substitution} {control : ControlContext}
    {target : SourceSemantics.Context} {coverageSource : TypedSource}
    (statementEq : statement.value =
      .assignValue targetExpression operator value)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (ready : initial.InferenceReady)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical :
      ∀ signature ∈ inferenceContext.signatures.functions,
        signature.scheme.body = .function
          (Ty.productMany signature.parameterTypes)
          (Ty.productMany signature.returnTypes))
    (invariant : ActiveLocalContextInvariant initial outer target)
    (outerExtension : outer.SemanticallyExtends
      result.state.inference.substitution)
    (roots : List NodeId := [])
    (parentCovered : TemplateScopeCovered coverageSource target
      (.statement result.id))
    (closed : OccurrenceGraphClosed coverageSource)
    (resultExtension : TypingSourceExtends
      ((result.state.toTypedSource roots).applySubstitution outer)
      coverageSource)
    (resultIntegerPatternsSubset :
      result.state.integerPatterns ⊆ evidenceState.integerPatterns)
    (resultIntegerLiteralsSubset :
      result.state.integerLiterals ⊆ evidenceState.integerLiterals)
    (resultRequirementsSubset :
      result.state.requirements ⊆ evidenceState.requirements)
    (actualChildrenSound :
      ∀ {assignment : AssignmentResolution}
        {inferred : InferredExpression}
        {assignmentState : Frontend.SourceInference.State},
        Detail.inferAssignedValueFuel fuel inferenceContext targetExpression
          operator.value value allocated =
            .ok (assignment, inferred, assignmentState) →
        TypingSourceExtends
          ((assignmentState.toTypedSource roots).applySubstitution outer)
          coverageSource →
        assignmentState.integerPatterns ⊆ evidenceState.integerPatterns →
        assignmentState.integerLiterals ⊆ evidenceState.integerLiterals →
        assignmentState.requirements ⊆ evidenceState.requirements →
        (∀ key, .expression key ∈ assignment.references →
          TemplateScopeCovered coverageSource target (.expression key)) →
        TemplateScopeCovered coverageSource target
          (.expression inferred.id) →
        SourcePlaceHasType
          ((result.state.toTypedSource roots).applySubstitution outer)
          target (assignment.target.applySubstitution outer)
          (outer.apply assignment.target.type) ∧
        ExpressionHasType
          ((result.state.toTypedSource roots).applySubstitution outer)
          target inferred.id (outer.apply inferred.type)) :
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
  obtain ⟨assignment, inferred, assignmentState, assignmentSuccess,
      resultEq, containsRaw⟩ :=
    inferStatementFuel_success_assignValue_facts statementEq allocationEq
      success roots
  obtain ⟨assignment', inferred', assignmentState', assignmentSuccess',
      _, assignmentToResult, literalsToResult, patternsToResult,
      requirementsToResult⟩ :=
    inferStatementFuel_success_assignValue_child_provenance statementEq
      allocationEq success initialBelow roots
  rw [assignmentSuccess] at assignmentSuccess'
  obtain ⟨rfl, rfl, rfl⟩ := (Except.ok.inj assignmentSuccess').symm
  have assignmentExtension : TypingSourceExtends
      ((assignmentState.toTypedSource roots).applySubstitution outer)
      coverageSource :=
    assignmentToResult.trans resultExtension
  have patternsSubset :
      assignmentState.integerPatterns ⊆ evidenceState.integerPatterns :=
    List.Subset.trans patternsToResult resultIntegerPatternsSubset
  have literalsSubset :
      assignmentState.integerLiterals ⊆ evidenceState.integerLiterals :=
    List.Subset.trans literalsToResult resultIntegerLiteralsSubset
  have requirementsSubset :
      assignmentState.requirements ⊆ evidenceState.requirements :=
    List.Subset.trans requirementsToResult resultRequirementsSubset
  have containsFinal : ContainsStatement coverageSource result.id
      (({
        id := result.id
        span := statement.span
        type := result.type
        form := .assignValue assignment operator.value inferred.id
      } : StatementNode).applySubstitution outer) :=
    resultExtension.containsStatement
      (FlexibleSubstitution.ContainsStatement.applySubstitution outer
        containsRaw)
  have keysCovered : ∀ key,
      .expression key ∈ assignment.references →
        TemplateScopeCovered coverageSource target (.expression key) := by
    intro key member
    apply TemplateScopeCovered.statementExpressionChild_of_noBindings_and_reference
      parentCovered closed containsFinal
    · simp [StatementNode.applySubstitution,
        StatementForm.applySubstitution, statementInitializedLetBindings]
    · have appended : .expression key ∈
          assignment.references ++ [.expression inferred.id] :=
        List.mem_append.mpr (Or.inl member)
      simpa [StatementNode.applySubstitution,
        StatementForm.applySubstitution, StatementForm.references,
        AssignmentResolution.references,
        AssignmentResolution.applySubstitution,
        PlaceResolution.applySubstitution, PlaceResolution.references]
        using appended
  have rhsCovered : TemplateScopeCovered coverageSource target
      (.expression inferred.id) := by
    apply TemplateScopeCovered.statementExpressionChild_of_noBindings_and_reference
      parentCovered closed containsFinal
    · simp [StatementNode.applySubstitution,
        StatementForm.applySubstitution, statementInitializedLetBindings]
    · simp [StatementNode.applySubstitution,
        StatementForm.applySubstitution, StatementForm.references]
  obtain ⟨placeTyped, valueTyped⟩ :=
    actualChildrenSound assignmentSuccess assignmentExtension patternsSubset
      literalsSubset requirementsSubset keysCovered rhsCovered
  exact inferStatementFuel_success_assignValue_sound_of_typed_children
    statementEq allocationEq success assignmentSuccess ready
    signatureFormation functionsCanonical invariant outerExtension roots
    placeTyped valueTyped

/-- Bit-not assignment has only the actual place traversal as a recursive
child.  Its indexed keys inherit the final graph's template scope from the
recorded statement, and all child evidence rows remain in the final ledger. -/
theorem inferStatementFuel_success_assignBitNot_bounded_scoped
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {targetExpression : Syntax.Expr}
    {operatorSpan : Syntax.SourceSpan} {expectedReturn : Ty}
    {initial allocated evidenceState : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    {outer : Substitution} {control : ControlContext}
    {target : SourceSemantics.Context} {coverageSource : TypedSource}
    (statementEq : statement.value =
      .assignBitNot targetExpression operatorSpan)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (invariant : ActiveLocalContextInvariant initial outer target)
    (outerExtension : outer.SemanticallyExtends
      result.state.inference.substitution)
    (roots : List NodeId := [])
    (parentCovered : TemplateScopeCovered coverageSource target
      (.statement result.id))
    (closed : OccurrenceGraphClosed coverageSource)
    (resultExtension : TypingSourceExtends
      ((result.state.toTypedSource roots).applySubstitution outer)
      coverageSource)
    (resultIntegerPatternsSubset :
      result.state.integerPatterns ⊆ evidenceState.integerPatterns)
    (resultIntegerLiteralsSubset :
      result.state.integerLiterals ⊆ evidenceState.integerLiterals)
    (resultRequirementsSubset :
      result.state.requirements ⊆ evidenceState.requirements)
    (actualPlaceSound :
      ∀ {place : PlaceResolution}
        {placeState : Frontend.SourceInference.State},
        Detail.inferPlaceFuel fuel inferenceContext targetExpression allocated =
          .ok (place, placeState) →
        TypingSourceExtends
          ((placeState.toTypedSource roots).applySubstitution outer)
          coverageSource →
        placeState.integerPatterns ⊆ evidenceState.integerPatterns →
        placeState.integerLiterals ⊆ evidenceState.integerLiterals →
        placeState.requirements ⊆ evidenceState.requirements →
        (∀ key, .expression key ∈ place.references →
          TemplateScopeCovered coverageSource target (.expression key)) →
        SourcePlaceHasType
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
  obtain ⟨place, placeState, unified, placeSuccess, _, _, resultEq,
      containsRaw⟩ :=
    inferStatementFuel_success_assignBitNot_facts statementEq allocationEq
      success roots
  obtain ⟨place', placeState', unified', placeSuccess', _, _,
      placeToResult, literalsToResult, patternsToResult,
      requirementsToResult⟩ :=
    inferStatementFuel_success_assignBitNot_child_provenance statementEq
      allocationEq success initialBelow roots
  rw [placeSuccess] at placeSuccess'
  obtain ⟨rfl, rfl⟩ := (Except.ok.inj placeSuccess').symm
  have placeExtension : TypingSourceExtends
      ((placeState.toTypedSource roots).applySubstitution outer)
      coverageSource :=
    placeToResult.trans resultExtension
  have patternsSubset :
      placeState.integerPatterns ⊆ evidenceState.integerPatterns :=
    List.Subset.trans patternsToResult resultIntegerPatternsSubset
  have literalsSubset :
      placeState.integerLiterals ⊆ evidenceState.integerLiterals :=
    List.Subset.trans literalsToResult resultIntegerLiteralsSubset
  have requirementsSubset :
      placeState.requirements ⊆ evidenceState.requirements :=
    List.Subset.trans requirementsToResult resultRequirementsSubset
  have containsFinal : ContainsStatement coverageSource result.id
      (({
        id := result.id
        span := statement.span
        type := result.type
        form := .assignBitNot {
          target := { place with type := unified.resolve place.type }
        }
      } : StatementNode).applySubstitution outer) :=
    resultExtension.containsStatement
      (FlexibleSubstitution.ContainsStatement.applySubstitution outer
        containsRaw)
  have keysCovered : ∀ key,
      .expression key ∈ place.references →
        TemplateScopeCovered coverageSource target (.expression key) := by
    intro key member
    apply TemplateScopeCovered.statementExpressionChild_of_noBindings_and_reference
      parentCovered closed containsFinal
    · simp [StatementNode.applySubstitution,
        StatementForm.applySubstitution, statementInitializedLetBindings]
    · simpa [StatementNode.applySubstitution,
        StatementForm.applySubstitution, StatementForm.references,
        AssignmentResolution.references,
        AssignmentResolution.applySubstitution,
        PlaceResolution.applySubstitution, PlaceResolution.references]
        using member
  have placeTyped := actualPlaceSound placeSuccess placeExtension
    patternsSubset literalsSubset requirementsSubset keysCovered
  exact inferStatementFuel_success_assignBitNot_sound_of_actual_child
    statementEq allocationEq success invariant outerExtension roots
    placeSuccess placeTyped

/-- The assignment branch does not introduce a visible binder; the actual
place/RHS traversal preserves the declaration-local binder cutoff. -/
theorem inferStatementFuel_success_assignValue_localBindersBelow
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {targetExpression value : Syntax.Expr}
    {operator : Syntax.Located Syntax.ValueAssignOp}
    {expectedReturn : Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    (statementEq : statement.value =
      .assignValue targetExpression operator value)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (below : initial.LocalBindersBelowNextLocal) :
    result.state.LocalBindersBelowNextLocal := by
  obtain ⟨assignment, inferred, assignmentState, assignmentSuccess,
      resultEq, _⟩ :=
    inferStatementFuel_success_assignValue_facts statementEq allocationEq
      success
  have allocatedBelow : allocated.LocalBindersBelowNextLocal := by
    have preserved :=
      Frontend.SourceInference.State.allocateStatementId_preserves_localBindersBelowNextLocal
        initial below
    simpa only [allocationEq] using preserved
  have assignmentBelow : assignmentState.LocalBindersBelowNextLocal :=
    Detail.inferAssignedValueFuel_preserves_localBindersBelowNextLocal
      allocatedBelow assignmentSuccess
  rw [resultEq]
  exact Frontend.SourceInference.State.recordNode_preserves_localBindersBelowNextLocal
    assignmentState _ assignmentBelow

/-- Bit-not assignment has the same stable-binder guarantee, including its
forced `Word` unification after place inference. -/
theorem inferStatementFuel_success_assignBitNot_localBindersBelow
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {targetExpression : Syntax.Expr}
    {operatorSpan : Syntax.SourceSpan} {expectedReturn : Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    (statementEq : statement.value =
      .assignBitNot targetExpression operatorSpan)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (below : initial.LocalBindersBelowNextLocal) :
    result.state.LocalBindersBelowNextLocal := by
  obtain ⟨place, placeState, unified, placeSuccess, unifySuccess, _,
      resultEq, _⟩ :=
    inferStatementFuel_success_assignBitNot_facts statementEq allocationEq
      success
  have allocatedBelow : allocated.LocalBindersBelowNextLocal := by
    have preserved :=
      Frontend.SourceInference.State.allocateStatementId_preserves_localBindersBelowNextLocal
        initial below
    simpa only [allocationEq] using preserved
  have placeBelow : placeState.LocalBindersBelowNextLocal :=
    Detail.inferPlaceFuel_preserves_localBindersBelowNextLocal allocatedBelow
      placeSuccess
  have unifiedBelow : unified.LocalBindersBelowNextLocal :=
    Detail.unify_preserves_localBindersBelowNextLocal placeBelow unifySuccess
  rw [resultEq]
  exact Frontend.SourceInference.State.recordNode_preserves_localBindersBelowNextLocal
    unified _ unifiedBelow

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
      placeState.integerLiterals ⊆ final.integerLiterals ∧
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
            actualState.integerLiterals ⊆ final.integerLiterals ∧
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
                      fittedBelow roots), ?_, ?_, ?_⟩
                · rw [← Detail.unify_integerLiterals unifyResult]
                  exact Detail.inferExprFuel_integerLiterals_subset valueResult
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
                Detail.inferExprFuel_integerLiterals_subset valueResult,
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
      | shiftLeft => exact finishNonEqual success
      | shiftRight => exact finishNonEqual success
      | uncheckedAdd => exact finishNonEqual success
      | uncheckedSubtract => exact finishNonEqual success
      | uncheckedMultiply => exact finishNonEqual success
      | uncheckedDivide => exact finishNonEqual success
      | uncheckedModulo => exact finishNonEqual success

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
      baseState.integerLiterals ⊆ final.integerLiterals ∧
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
                    unifiedBelow roots), ?_, ?_, ?_⟩
              · intro literal member
                have inUnified : literal ∈ unifiedState.integerLiterals := by
                  rw [Detail.unify_integerLiterals unifyResult]
                  simpa [keyAllocation, valueAllocation,
                    Frontend.SourceInference.State.fresh] using member
                exact Detail.inferExprFuel_integerLiterals_subset keyResult
                  inUnified
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

/-- The key used by a successful indexed place is exactly the expression
inference performed by that branch, and its occurrence is retained as a
direct place reference. -/
theorem inferPlaceFuel_success_index_key_provenance
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
    ∃ expected keyInitial inferredKey,
      Detail.inferExprFuel fuel inferenceContext key (some expected)
        keyInitial = .ok (inferredKey, final) ∧
      keyInitial.NodesBelowNextOccurrence ∧
      .expression inferredKey.id ∈ place.references ∧
      TypingSourceExtends (keyInitial.toTypedSource roots)
        (final.toTypedSource roots) ∧
      keyInitial.integerLiterals ⊆ final.integerLiterals ∧
      keyInitial.integerPatterns ⊆ final.integerPatterns ∧
      keyInitial.requirements ⊆ final.requirements := by
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
              refine ⟨unifiedState.resolve keyAllocation.1, unifiedState,
                inferredKey, keyResult, unifiedBelow, ?_,
                inferExprFuel_success_typingSourceExtends keyResult
                  unifiedBelow roots,
                Detail.inferExprFuel_integerLiterals_subset keyResult,
                Detail.inferExprFuel_integerPatterns_subset keyResult,
                Detail.inferExprFuel_requirements_subset keyResult⟩
              simp [PlaceResolution.references,
                PlaceProjection.references]

/-- The RHS of a successful assignment is one actual expected-type expression
traversal, whether or not the operator first unified the place with `Word`.
The returned RHS state is exactly the assignment's final state. -/
theorem inferAssignedValueFuel_success_value_provenance
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
    ∃ expected valueInitial,
      Detail.inferExprFuel fuel inferenceContext value (some expected)
        valueInitial = .ok (inferredValue, final) ∧
      valueInitial.NodesBelowNextOccurrence ∧
      TypingSourceExtends (valueInitial.toTypedSource roots)
        (final.toTypedSource roots) ∧
      valueInitial.integerLiterals ⊆ final.integerLiterals ∧
      valueInitial.integerPatterns ⊆ final.integerPatterns ∧
      valueInitial.requirements ⊆ final.requirements := by
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
          ∃ expected valueInitial,
            Detail.inferExprFuel fuel inferenceContext value (some expected)
              valueInitial = .ok (inferredValue, final) ∧
            valueInitial.NodesBelowNextOccurrence ∧
            TypingSourceExtends (valueInitial.toTypedSource roots)
              (final.toTypedSource roots) ∧
            valueInitial.integerLiterals ⊆ final.integerLiterals ∧
            valueInitial.integerPatterns ⊆ final.integerPatterns ∧
            valueInitial.requirements ⊆ final.requirements := by
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
                exact ⟨.word, fittedState, valueResult, fittedBelow,
                  inferExprFuel_success_typingSourceExtends valueResult
                    fittedBelow roots,
                  Detail.inferExprFuel_integerLiterals_subset valueResult,
                  Detail.inferExprFuel_integerPatterns_subset valueResult,
                  Detail.inferExprFuel_requirements_subset valueResult⟩
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
              exact ⟨placeState.resolve place.type, placeState, valueResult,
                placeBelow,
                inferExprFuel_success_typingSourceExtends valueResult
                  placeBelow roots,
                Detail.inferExprFuel_integerLiterals_subset valueResult,
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
      | shiftLeft => exact finishNonEqual success
      | shiftRight => exact finishNonEqual success
      | uncheckedAdd => exact finishNonEqual success
      | uncheckedSubtract => exact finishNonEqual success
      | uncheckedMultiply => exact finishNonEqual success
      | uncheckedDivide => exact finishNonEqual success
      | uncheckedModulo => exact finishNonEqual success

/-- The assignment's final type refinement changes no place projection
edges.  Every indexed key of the actual inferred place is still a direct
child of the recorded assignment statement. -/
theorem inferAssignedValueFuel_success_target_references_eq
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {targetExpression value : Syntax.Expr}
    {operator : Syntax.ValueAssignOp}
    {initial placeState final : Frontend.SourceInference.State}
    {place : PlaceResolution}
    {assignment : AssignmentResolution}
    {inferredValue : InferredExpression}
    (placeSuccess : Detail.inferPlaceFuel fuel inferenceContext
      targetExpression initial = .ok (place, placeState))
    (success : Detail.inferAssignedValueFuel fuel inferenceContext
      targetExpression operator value initial =
        .ok (assignment, inferredValue, final)) :
    assignment.target.references = place.references := by
  unfold Detail.inferAssignedValueFuel at success
  simp only [placeSuccess, bind, Except.bind] at success
  cases operator <;>
    simp only [pure, Pure.pure, Except.pure] at success <;>
    repeat' (split at success) <;>
    simp_all [PlaceResolution.references]
  all_goals
    rcases success with ⟨assignmentEq, _, _⟩
    subst assignment
    rfl

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceStatementLocalBound
/-!
Stable local-binder allocation bounds for the actual statement traversal.
The semantic statement induction needs this bound after every sequential
head, independently of expression typing or finalization.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem

/-- Any successful statement which retains its incoming visible binder stack
preserves that stack's allocation bound. -/
theorem inferStatementFuel_localBindersBelow_of_sameBinders
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    (below : initial.LocalBindersBelowNextLocal)
    (success : Detail.inferStatementFuel fuel inferenceContext statement
      expectedReturn initial = .ok result)
    (same : result.state.localBinders = initial.localBinders) :
    result.state.LocalBindersBelowNextLocal :=
  State.LocalBindersBelowNextLocal.transport same
    (Detail.inferStatementFuel_nextLocal_le success) below

private theorem inferStatementFuel_localBindersBelow_of_sameScope
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    (below : initial.LocalBindersBelowNextLocal)
    (success : Detail.inferStatementFuel fuel inferenceContext statement
      expectedReturn initial = .ok result)
    (same : result.state.lexicalScope = initial.lexicalScope) :
    result.state.LocalBindersBelowNextLocal :=
  inferStatementFuel_localBindersBelow_of_sameBinders below success
    (by simpa only [State.lexicalScope] using
      congrArg LexicalScope.binders same)

/-- A real `let` binder is allocated after an initializer state whose visible
binders are already bounded; recording the statement does not alter locals. -/
private theorem letBinding_recordNode_localBindersBelow
    {name : Syntax.Identifier} {initial : State}
    {locals : TypeSystem.Environment} {generalized : Detail.GeneralizedValue}
    {binding : TypedBinder × State} {node : StatementNode}
    (below : initial.LocalBindersBelowNextLocal)
    (allocated : (initial.withLocals locals).allocateBinder name.value
      generalized.scheme (some name.span) false generalized.requirements =
        binding) :
    (binding.2.recordNode (.statement node)).LocalBindersBelowNextLocal := by
  have withLocalsBelow :
      (initial.withLocals locals).LocalBindersBelowNextLocal :=
    State.withLocals_preserves_localBindersBelowNextLocal initial locals below
  have bindingBelow :=
    State.allocateBinder_preserves_localBindersBelowNextLocal
      (initial.withLocals locals) name.value generalized.scheme
      (some name.span) false generalized.requirements withLocalsBelow
  rw [allocated] at bindingBelow
  exact State.recordNode_preserves_localBindersBelowNextLocal
    binding.2 (.statement node) bindingBelow

/-- The uninitialized annotated declaration allocates exactly one visible
binder after the statement-ID step. -/
theorem inferStatementFuel_success_letAnnotatedUninitialized_localBindersBelow
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {name : Syntax.Identifier}
    {sourceType : Syntax.TypeExpr} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult}
    (statementEq : statement.value =
      .letDecl name (some sourceType) none)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (below : initial.LocalBindersBelowNextLocal) :
    result.state.LocalBindersBelowNextLocal := by
  obtain ⟨_, locals, _, generalized, binding, _, _, _, _, bindingEq,
      resultEq, _⟩ :=
    inferStatementFuel_success_letAnnotatedUninitialized_facts statementEq
      allocationEq success
  have allocatedBelow : allocated.LocalBindersBelowNextLocal := by
    have preserved :=
      State.allocateStatementId_preserves_localBindersBelowNextLocal
        initial below
    simpa only [allocationEq] using preserved
  rw [resultEq]
  exact letBinding_recordNode_localBindersBelow allocatedBelow bindingEq

/-- Inferred-value declarations preserve the binder bound through the actual
initializer traversal before allocating their one visible binder. -/
theorem inferStatementFuel_success_letUnannotatedInitialized_localBindersBelow
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {name : Syntax.Identifier}
    {initializer : Syntax.Expr} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult}
    (statementEq : statement.value =
      .letDecl name none (some initializer))
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (below : initial.LocalBindersBelowNextLocal) :
    result.state.LocalBindersBelowNextLocal := by
  obtain ⟨inferred, initializerState, locals, _, generalized, binding,
      initializerSuccess, _, _, _, bindingEq, resultEq, _⟩ :=
    inferStatementFuel_success_letUnannotatedInitialized_facts statementEq
      allocationEq success
  have allocatedBelow : allocated.LocalBindersBelowNextLocal := by
    have preserved :=
      State.allocateStatementId_preserves_localBindersBelowNextLocal
        initial below
    simpa only [allocationEq] using preserved
  have initializerBelow : initializerState.LocalBindersBelowNextLocal :=
    Detail.inferExprFuel_preserves_localBindersBelowNextLocal allocatedBelow
      initializerSuccess
  rw [resultEq]
  exact letBinding_recordNode_localBindersBelow initializerBelow bindingEq

/-- An annotated initialized declaration has the same allocation behavior:
source-type resolution does not mutate the state, and initializer inference
preserves the incoming visible binder stack. -/
theorem inferStatementFuel_success_letAnnotatedInitialized_localBindersBelow
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {name : Syntax.Identifier}
    {sourceType : Syntax.TypeExpr} {initializer : Syntax.Expr}
    {expectedReturn : Ty} {initial allocated : State}
    {id : StatementId} {result : Detail.StatementResult}
    (statementEq : statement.value =
      .letDecl name (some sourceType) (some initializer))
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (below : initial.LocalBindersBelowNextLocal) :
    result.state.LocalBindersBelowNextLocal := by
  obtain ⟨resolvedType, inferred, initializerState, locals, _, generalized,
      binding, _, initializerSuccess, _, _, _, bindingEq, resultEq, _⟩ :=
    inferStatementFuel_success_letAnnotatedInitialized_facts statementEq
      allocationEq success
  have allocatedBelow : allocated.LocalBindersBelowNextLocal := by
    have preserved :=
      State.allocateStatementId_preserves_localBindersBelowNextLocal
        initial below
    simpa only [allocationEq] using preserved
  have initializerBelow : initializerState.LocalBindersBelowNextLocal :=
    Detail.inferExprFuel_preserves_localBindersBelowNextLocal allocatedBelow
      initializerSuccess
  rw [resultEq]
  exact letBinding_recordNode_localBindersBelow initializerBelow bindingEq

/-- A match without a default leaves its hidden scrutinee binder visible in
the inference state.  The case traversal restores exactly that scope and
advances the shared binder cutoff monotonically. -/
theorem inferStatementFuel_success_matchWithoutDefault_localBindersBelow
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
    {arms : Syntax.MatchArms} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult}
    (statementEq : statement.value = .matchWith scrutinees arms)
    (defaultEq : arms.value.defaultBody = none)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (below : initial.LocalBindersBelowNextLocal) :
    result.state.LocalBindersBelowNextLocal := by
  obtain ⟨scrutinee, scrutineeState, hiddenScrutinee, hiddenState, checked,
      scrutineeSuccess, hiddenEq, casesSuccess, _, resultEq, _⟩ :=
    inferStatementFuel_success_matchWithoutDefault_facts statementEq defaultEq
      allocationEq success
  have allocatedBelow : allocated.LocalBindersBelowNextLocal := by
    have preserved := State.allocateStatementId_preserves_localBindersBelowNextLocal
      initial below
    simpa only [allocationEq] using preserved
  have scrutineeBelow : scrutineeState.LocalBindersBelowNextLocal :=
    inferMatchScrutineesFuel_preserves_localBindersBelowNextLocal
      allocatedBelow scrutineeSuccess
  have hiddenBelow : hiddenState.LocalBindersBelowNextLocal := by
    have preserved := State.allocateHiddenLocal_preserves_localBindersBelowNextLocal
      scrutineeState scrutineeBelow
    simpa only [hiddenEq] using preserved
  have checkedScope :=
    Detail.inferMatchCasesFuel_success_lexicalScope_eq rfl casesSuccess
  have sameBinders : checked.state.localBinders = hiddenState.localBinders := by
    simpa only [State.lexicalScope] using
      congrArg LexicalScope.binders checkedScope
  have checkedBelow : checked.state.LocalBindersBelowNextLocal :=
    State.LocalBindersBelowNextLocal.transport sameBinders
      (Detail.inferMatchCasesFuel_nextLocal_le casesSuccess) hiddenBelow
  rw [resultEq]
  exact State.recordNode_preserves_localBindersBelowNextLocal checked.state _
    checkedBelow

/-- A default match restores the hidden-binder scope after its default block;
the same allocation bound therefore holds at the retained statement. -/
theorem inferStatementFuel_success_matchWithDefault_localBindersBelow
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
    {arms : Syntax.MatchArms} {defaultBody : Syntax.Block}
    {expectedReturn : Ty} {initial allocated : State}
    {id : StatementId} {result : Detail.StatementResult}
    (statementEq : statement.value = .matchWith scrutinees arms)
    (defaultEq : arms.value.defaultBody = some defaultBody)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (below : initial.LocalBindersBelowNextLocal) :
    result.state.LocalBindersBelowNextLocal := by
  obtain ⟨scrutinee, scrutineeState, hiddenScrutinee, hiddenState, checked,
      defaultResult, scrutineeSuccess, hiddenEq, casesSuccess, defaultSuccess,
      _, resultEq, _⟩ :=
    inferStatementFuel_success_matchWithDefault_facts statementEq defaultEq
      allocationEq success
  have allocatedBelow : allocated.LocalBindersBelowNextLocal := by
    have preserved := State.allocateStatementId_preserves_localBindersBelowNextLocal
      initial below
    simpa only [allocationEq] using preserved
  have scrutineeBelow : scrutineeState.LocalBindersBelowNextLocal :=
    inferMatchScrutineesFuel_preserves_localBindersBelowNextLocal
      allocatedBelow scrutineeSuccess
  have hiddenBelow : hiddenState.LocalBindersBelowNextLocal := by
    have preserved := State.allocateHiddenLocal_preserves_localBindersBelowNextLocal
      scrutineeState scrutineeBelow
    simpa only [hiddenEq] using preserved
  have restoredBelow :
      (defaultResult.state.restoreLexicalScope hiddenState.lexicalScope)
        |>.LocalBindersBelowNextLocal :=
    State.restoreLexicalScope_preserves_localBindersBelowNextLocal hiddenBelow
      (Nat.le_trans (Detail.inferMatchCasesFuel_nextLocal_le casesSuccess)
        (Detail.inferStatementsFuel_nextLocal_le defaultSuccess))
  rw [resultEq]
  exact State.recordNode_preserves_localBindersBelowNextLocal _ _ restoredBelow

/-- Ordinary statement branches, including nested blocks and loops, restore
the incoming visible binder stack.  Only `let` and `match` create a binder
that remains in the statement result.  The recursive soundness dispatcher
uses this to transport active-scheme isolation across nonbinding branches. -/
theorem inferStatementFuel_success_nonbinding_sameScope
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult}
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (notLet : ∀ name sourceType initializer,
      statement.value ≠ .letDecl name sourceType initializer)
    (notMatch : ∀ scrutinees arms,
      statement.value ≠ .matchWith scrutinees arms) :
    result.state.lexicalScope = initial.lexicalScope := by
  have allocatedScope : allocated.lexicalScope = initial.lexicalScope :=
    Detail.allocateStatementId_success_lexicalScope allocationEq
  cases statementEq : statement.value with
  | letDecl name sourceType initializer =>
      exact False.elim (notLet name sourceType initializer statementEq)
  | matchWith scrutinees arms =>
      exact False.elim (notMatch scrutinees arms statementEq)
  | expression expression trailingSemicolon =>
      obtain ⟨_, expressionState, expressionSuccess, resultEq, _⟩ :=
        inferStatementFuel_success_expression_facts statementEq allocationEq
          success
      rw [resultEq]
      exact (Detail.inferExprFuel_success_lexicalScope_eq
        expressionSuccess).trans allocatedScope
  | assignValue target operator value =>
      obtain ⟨assignment, inferredValue, assignmentState,
          assignmentSuccess, resultEq, _⟩ :=
        inferStatementFuel_success_assignValue_facts statementEq allocationEq
          success
      rw [resultEq]
      exact (Detail.inferAssignedValueFuel_success_lexicalScope_eq
        assignmentSuccess).trans allocatedScope
  | assignBitNot target operatorSpan =>
      obtain ⟨place, placeState, unified, placeSuccess, unifySuccess, _,
          resultEq, _⟩ :=
        inferStatementFuel_success_assignBitNot_facts statementEq allocationEq
          success
      rw [resultEq]
      exact (Detail.unify_preserves_lexicalScope unifySuccess).trans
        ((Detail.inferPlaceFuel_success_lexicalScope_eq placeSuccess).trans
          allocatedScope)
  | returnStmt value =>
      cases value with
      | none =>
          obtain ⟨unified, unifySuccess, _, resultEq, _⟩ :=
            inferStatementFuel_success_returnUnit_facts statementEq
              allocationEq success
          rw [resultEq]
          exact (Detail.unify_preserves_lexicalScope unifySuccess).trans
            allocatedScope
      | some value =>
          obtain ⟨inferred, valueState, valueSuccess, resultEq, _⟩ :=
            inferStatementFuel_success_returnValue_facts statementEq
              allocationEq success
          rw [resultEq]
          exact (Detail.inferExprFuel_success_lexicalScope_eq
            valueSuccess).trans allocatedScope
  | ifThen condition thenBody elseBody =>
      cases elseBody with
      | none =>
          obtain ⟨inferredCondition, conditionState, thenResult,
              conditionSuccess, thenSuccess, resultEq, _⟩ :=
            inferStatementFuel_success_ifWithoutElse_facts statementEq
              allocationEq success
          rw [resultEq]
          exact (Detail.inferExprFuel_success_lexicalScope_eq
            conditionSuccess).trans allocatedScope
      | some elseBody =>
          obtain ⟨inferredCondition, conditionState, thenResult, elseResult,
              conditionSuccess, thenSuccess, elseSuccess, resultEq, _⟩ :=
            inferStatementFuel_success_ifWithElse_facts statementEq
              allocationEq success
          rw [resultEq]
          exact (Detail.inferExprFuel_success_lexicalScope_eq
            conditionSuccess).trans allocatedScope
  | block body =>
      obtain ⟨bodyResult, bodySuccess, resultEq, _⟩ :=
        inferStatementFuel_success_block_facts statementEq allocationEq success
      rw [resultEq]
      exact allocatedScope
  | forLoop headerSpan initializer condition post body =>
      obtain ⟨initializerResult, inferredCondition, conditionState,
          bodyResult, postResult, initializerSuccess, conditionSuccess,
          bodySuccess, postSuccess, resultEq, _⟩ :=
        inferStatementFuel_success_forLoop_facts statementEq allocationEq
          success
      rw [resultEq]
      exact allocatedScope
  | whileLoop condition body =>
      obtain ⟨inferredCondition, conditionState, bodyResult, conditionSuccess,
          bodySuccess, resultEq, _⟩ :=
        inferStatementFuel_success_whileLoop_facts statementEq allocationEq
          success
      rw [resultEq]
      exact (Detail.inferExprFuel_success_lexicalScope_eq
        conditionSuccess).trans allocatedScope
  | breakStmt =>
      obtain ⟨_, resultEq, _⟩ :=
        inferStatementFuel_success_break_facts statementEq allocationEq
          success
      rw [resultEq]
      exact allocatedScope
  | continueStmt =>
      obtain ⟨_, resultEq, _⟩ :=
        inferStatementFuel_success_continue_facts statementEq allocationEq
          success
      rw [resultEq]
      exact allocatedScope
  | assembly body =>
      simp [Detail.inferStatementFuel, statementEq] at success
  | error =>
      simp [Detail.inferStatementFuel, statementEq] at success

/-- Every successful statement inference result has bounded visible local
identities.  This combines ordinary lexical restoration with the two forms
that allocate a binder retained in the inference result. -/
theorem inferStatementFuel_preserves_localBindersBelowNextLocal
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    (below : initial.LocalBindersBelowNextLocal)
    (success : Detail.inferStatementFuel fuel inferenceContext statement
      expectedReturn initial = .ok result) :
    result.state.LocalBindersBelowNextLocal := by
  cases fuel with
  | zero => simp [Detail.inferStatementFuel] at success
  | succ fuel =>
      rcases allocationEq : initial.allocateStatementId with ⟨id, allocated⟩
      cases statementEq : statement.value
      case letDecl name sourceType initializer =>
          cases sourceType with
          | none =>
              cases initializer with
              | none =>
                  simp [Detail.inferStatementFuel, allocationEq, statementEq,
                    bind, Except.bind]
                    at success
              | some initializer =>
                  exact inferStatementFuel_success_letUnannotatedInitialized_localBindersBelow
                    statementEq allocationEq success below
          | some sourceType =>
              cases initializer with
              | none =>
                  exact inferStatementFuel_success_letAnnotatedUninitialized_localBindersBelow
                    statementEq allocationEq success below
              | some initializer =>
                  exact inferStatementFuel_success_letAnnotatedInitialized_localBindersBelow
                    statementEq allocationEq success below
      case matchWith scrutinees arms =>
          cases defaultEq : arms.value.defaultBody with
          | none =>
              exact inferStatementFuel_success_matchWithoutDefault_localBindersBelow
                statementEq defaultEq allocationEq success below
          | some defaultBody =>
              exact inferStatementFuel_success_matchWithDefault_localBindersBelow
                statementEq defaultEq allocationEq success below
      all_goals
        apply inferStatementFuel_localBindersBelow_of_sameScope below success
        apply inferStatementFuel_success_nonbinding_sameScope allocationEq
          success
        · intro name sourceType initializer
          simp [statementEq]
        · intro scrutinees arms
          simp [statementEq]

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceRecursiveSoundness
/-!
An actual-success interface for the remaining mutually recursive inference
proof.  The final evidence source is fixed by one successful finalization;
each statement is typed in its own append-only local source.  No callback
asserts soundness of an arbitrary child computation unrelated to a successful
parent trace.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem
open SourceInferenceStatementsSoundness

/-- Facts that remain available at every sequential statement boundary.  In
particular the final substitution extends the current inference substitution,
while the semantic context may gain local binders but retains the finalized
whole-body requirement environment. -/
structure RecursiveStatementInvariant
    (inferenceContext : Frontend.SourceInference.Context)
    (expectedReturn : Ty) (finalized : Frontend.SourceInference.Result)
    (state : State) (semanticContext : SourceSemantics.Context) : Prop where
  active : ActiveLocalContextInvariant state finalized.substitution
    semanticContext
  ready : state.InferenceReady
  returnBelow : expectedReturn.VariablesBelow state.inference.next
  bindersBelow : state.LocalBindersBelowNextLocal
  nodesBelow : state.NodesBelowNextOccurrence
  schemeIsolation : ActiveSchemeQuantifierIsolation state
  substitutionExtension : finalized.substitution.SemanticallyExtends
    state.inference.substitution
  signaturesEq : semanticContext.signatures =
    (finalizedRequirementContext inferenceContext finalized).signatures
  typeParametersEq : semanticContext.typeParameters =
    inferenceContext.typeParameters
  declarationEq : semanticContext.currentDeclaration =
    some inferenceContext.scope.genericOwner
  residual : semanticContext.residualTypeVariables = true
  solvedRequirementsEq : semanticContext.solvedRequirements =
    (finalizedRequirementContext inferenceContext finalized
      ).solvedRequirements
  assumptionsMono :
    (finalizedRequirementContext inferenceContext finalized).assumptions ⊆
      semanticContext.assumptions

/-- Reserving the statement occurrence leaves every recursive semantic and
inference premise intact, apart from advancing the occurrence bound. -/
theorem RecursiveStatementInvariant.allocateStatementId
    {wholeContext : Frontend.SourceInference.Context}
    {expectedReturn : Ty}
    {finalized : Frontend.SourceInference.Result}
    {initial allocated : State}
    {id : StatementId}
    {semanticContext : SourceSemantics.Context}
    (invariant : RecursiveStatementInvariant wholeContext expectedReturn
      finalized initial semanticContext)
    (allocationEq : initial.allocateStatementId = (id, allocated)) :
    RecursiveStatementInvariant wholeContext expectedReturn finalized
      allocated semanticContext := by
  have allocatedEq : initial.allocateStatementId.2 = allocated :=
    congrArg Prod.snd allocationEq
  subst allocated
  refine {
    active := invariant.active.allocateStatementId allocationEq
    ready := ?_
    returnBelow := ?_
    bindersBelow := ?_
    nodesBelow := ?_
    schemeIsolation := ?_
    substitutionExtension := ?_
    signaturesEq := invariant.signaturesEq
    typeParametersEq := invariant.typeParametersEq
    declarationEq := invariant.declarationEq
    residual := invariant.residual
    solvedRequirementsEq := invariant.solvedRequirementsEq
    assumptionsMono := invariant.assumptionsMono
  }
  · exact invariant.ready.allocateStatementId
  · exact invariant.returnBelow
  · exact State.allocateStatementId_preserves_localBindersBelowNextLocal
      initial invariant.bindersBelow
  · exact State.allocateStatementId_preserves_nodesBelowNextOccurrence
      initial invariant.nodesBelow
  · exact activeSchemeQuantifierIsolation_allocateStatementId
      invariant.schemeIsolation allocationEq
  · exact invariant.substitutionExtension

/-- An actual expression traversal may refine types and append expression
nodes, but it does not change the active lexical context.  This is the common
state step before `if`, `while`, and `for` bodies. -/
theorem RecursiveStatementInvariant.inferExprFuel
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {expectedReturn : Ty}
    {expression : Syntax.Expr} {expected : Option Ty}
    {initial resultState : State} {inferred : InferredExpression}
    {finalized : Frontend.SourceInference.Result}
    {semanticContext : SourceSemantics.Context}
    (invariant : RecursiveStatementInvariant wholeContext expectedReturn
      finalized initial semanticContext)
    (success : Detail.inferExprFuel fuel inferenceContext expression expected
      initial = .ok (inferred, resultState))
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈
      inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (expectedBelow : ∀ type ∈ expected,
      type.VariablesBelow initial.inference.next)
    (resultSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        resultState.inference.substitution) :
    RecursiveStatementInvariant wholeContext expectedReturn finalized
      resultState semanticContext := by
  have properties := Detail.inferExprFuel_inferenceProperties invariant.ready
    signatureFormation functionsCanonical expectedBelow success
  refine {
    active := invariant.active.inferExprFuel success
    ready := properties.2.1
    returnBelow := invariant.returnBelow.weaken properties.1.next_le
    bindersBelow := Detail.inferExprFuel_preserves_localBindersBelowNextLocal
      invariant.bindersBelow success
    nodesBelow := (Detail.inferExprFuel_occurrenceBoundExtends success
      ).nodesBelowNextOccurrence invariant.nodesBelow
    schemeIsolation := ?_
    substitutionExtension := resultSubstitutionExtension
    signaturesEq := invariant.signaturesEq
    typeParametersEq := invariant.typeParametersEq
    declarationEq := invariant.declarationEq
    residual := invariant.residual
    solvedRequirementsEq := invariant.solvedRequirementsEq
    assumptionsMono := invariant.assumptionsMono
  }
  have bindersEq : resultState.localBinders = initial.localBinders := by
    simpa [State.lexicalScope] using
      congrArg LexicalScope.binders
        (Detail.inferExprFuel_success_lexicalScope_eq success)
  exact activeSchemeQuantifierIsolation_transport
    invariant.schemeIsolation bindersEq

/-- Leaving a branch restores the outer lexical binders while retaining all
allocator and substitution progress of the inner traversal. -/
theorem RecursiveStatementInvariant.restoreLexicalScope
    {wholeContext : Frontend.SourceInference.Context}
    {expectedReturn : Ty}
    {finalized : Frontend.SourceInference.Result}
    {outer inner : State}
    {semanticContext : SourceSemantics.Context}
    (invariant : RecursiveStatementInvariant wholeContext expectedReturn
      finalized outer semanticContext)
    (progress : outer.InferenceProgress inner)
    (innerBelow : inner.NodesBelowNextOccurrence)
    (nextLocalLe : outer.nextLocal ≤ inner.nextLocal)
    (substitutionExtension : finalized.substitution.SemanticallyExtends
      inner.inference.substitution) :
    RecursiveStatementInvariant wholeContext expectedReturn finalized
      (inner.restoreLexicalScope outer.lexicalScope) semanticContext := by
  have restoredProperties := State.restoreLexicalScope_inferenceProperties
    invariant.ready progress
  refine {
    active := invariant.active.restoreLexicalScope
    ready := restoredProperties.2
    returnBelow := invariant.returnBelow.weaken restoredProperties.1.next_le
    bindersBelow := State.restoreLexicalScope_preserves_localBindersBelowNextLocal
      invariant.bindersBelow nextLocalLe
    nodesBelow := State.restoreLexicalScope_preserves_nodesBelowNextOccurrence
      inner outer.lexicalScope innerBelow
    schemeIsolation := ?_
    substitutionExtension := ?_
    signaturesEq := invariant.signaturesEq
    typeParametersEq := invariant.typeParametersEq
    declarationEq := invariant.declarationEq
    residual := invariant.residual
    solvedRequirementsEq := invariant.solvedRequirementsEq
    assumptionsMono := invariant.assumptionsMono
  }
  · apply activeSchemeQuantifierIsolation_transport invariant.schemeIsolation
    rfl
  exact substitutionExtension

/-- Once a branch has produced its actual semantic typing, the generic
frontend progress facts and lexical-only context change reconstruct the
invariant for the next source-ordered statement. -/
theorem RecursiveStatementInvariant.of_statement_typing
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {finalized : Frontend.SourceInference.Result}
    {initialContext finalContext : SourceSemantics.Context}
    {roots : List NodeId} {facts : StatementFacts}
    (initialInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initial initialContext)
    (success : Detail.inferStatementFuel fuel inferenceContext statement
      expectedReturn initial = .ok result)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈
      inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (resultActive : ActiveLocalContextInvariant result.state
      finalized.substitution finalContext)
    (resultBindersBelow : result.state.LocalBindersBelowNextLocal)
    (resultSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        result.state.inference.substitution)
    (resultSchemeIsolation : ActiveSchemeQuantifierIsolation result.state)
    (typing : StatementHasType
      ((result.state.toTypedSource roots).applySubstitution
        finalized.substitution)
      { returnType := finalized.substitution.apply expectedReturn
        loopDepth := inferenceContext.loopDepth }
      initialContext result.id finalContext facts) :
    RecursiveStatementInvariant wholeContext expectedReturn finalized
      result.state finalContext := by
  have properties := Detail.inferStatementFuel_inferenceProperties
    initialInvariant.ready signatureFormation functionsCanonical
    initialInvariant.returnBelow success
  have fields := statementHasType_nonlocal_fields_eq typing
  refine {
    active := resultActive
    ready := properties.2.1
    returnBelow := initialInvariant.returnBelow.weaken properties.1.next_le
    bindersBelow := resultBindersBelow
    nodesBelow := (Detail.inferStatementFuel_occurrenceBoundExtends success
      ).nodesBelowNextOccurrence initialInvariant.nodesBelow
    schemeIsolation := resultSchemeIsolation
    substitutionExtension := resultSubstitutionExtension
    signaturesEq := fields.1.trans initialInvariant.signaturesEq
    typeParametersEq := fields.2.1.trans initialInvariant.typeParametersEq
    declarationEq := fields.2.2.1.trans initialInvariant.declarationEq
    residual := fields.2.2.2.1.trans initialInvariant.residual
    solvedRequirementsEq := fields.2.2.2.2.1.trans
      initialInvariant.solvedRequirementsEq
    assumptionsMono := ?_
  }
  rw [fields.2.2.2.2.2]
  exact initialInvariant.assumptionsMono

/-- Package a branch-local soundness proof as the recursive successor
invariant.  All state progress is supplied by the concrete successful
statement inference, so branch proofs need only establish the declarative
judgment and its result facts. -/
theorem RecursiveStatementInvariant.close_statement_branch
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {finalized : Frontend.SourceInference.Result}
    {initialContext : SourceSemantics.Context}
    {roots : List NodeId}
    (initialInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initial initialContext)
    (success : Detail.inferStatementFuel fuel inferenceContext statement
      expectedReturn initial = .ok result)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈
      inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (resultBindersBelow : result.state.LocalBindersBelowNextLocal)
    (resultSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        result.state.inference.substitution)
    (resultSchemeIsolation : ActiveSchemeQuantifierIsolation result.state)
    (branch : ∃ finalContext facts,
      ActiveLocalContextInvariant result.state finalized.substitution
        finalContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        initialContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts) :
    ∃ finalContext facts,
      RecursiveStatementInvariant wholeContext expectedReturn finalized
        result.state finalContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        initialContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts := by
  obtain ⟨finalContext, facts, resultActive, typing, agreement⟩ := branch
  exact ⟨finalContext, facts,
    RecursiveStatementInvariant.of_statement_typing initialInvariant success
      signatureFormation functionsCanonical resultActive resultBindersBelow
      resultSubstitutionExtension resultSchemeIsolation typing,
    typing, agreement⟩

/-- The one-statement obligation for a fuel-indexed proof.  Its only dynamic
premise is the actual successful inference being typed; the retained source,
ledgers, and root coverage come from that same result and finalization. -/
def InferStatementFuelSoundness (fuel : Nat) : Prop :=
  ∀ {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {evidenceState : State} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticContext : SourceSemantics.Context},
    Detail.inferStatementFuel fuel inferenceContext statement expectedReturn
      initial = .ok result →
    FinalInferenceResources inferenceContext expectedReturn evidenceState roots
      finalized →
    ProgramSignatureFormationValidated inferenceContext.signatures →
    (∀ candidate ∈ inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes)) →
    SignatureCatalogWellFormed inferenceContext.signatures →
    SignatureParametersWellFormed inferenceContext.scope.genericOwner
      inferenceContext.typeParameters →
    RecursiveStatementInvariant inferenceContext expectedReturn finalized
      initial semanticContext →
    finalized.substitution.SemanticallyExtends
      result.state.inference.substitution →
    TypingSourceExtends
      ((result.state.toTypedSource roots).applySubstitution
        finalized.substitution) finalized.typedSource →
    result.state.integerPatterns ⊆ evidenceState.integerPatterns →
    result.state.integerLiterals ⊆ evidenceState.integerLiterals →
    result.state.requirements ⊆ evidenceState.requirements →
    TemplateScopeCovered finalized.typedSource semanticContext
      (.statement result.id) →
    ∃ finalContext facts,
      RecursiveStatementInvariant inferenceContext expectedReturn finalized
        result.state finalContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts

/-- Once the one-statement theorem is proved at every smaller fuel, list
sequencing needs no separate semantic callback.  This is the exact proposition
consumed by the checker-body bridge. -/
theorem inferStatementsFuelSoundness_of_statementSoundness
    {fuel : Nat}
    (statementSound : ∀ childFuel, childFuel < fuel →
      InferStatementFuelSoundness childFuel) :
    InferStatementsFuelSoundness fuel := by
  intro inferenceContext statements expectedReturn initial result
    evidenceState roots finalized semanticContext success resources
    signatureFormation functionsCanonical catalog signatureParameters
    initialActive initialSchemeIsolation ready returnBelow bindersBelow
    initialBelow
    finalSubstitutionExtension rawResultExtension resultExtension
    integerPatternsSubset
    integerLiteralsSubset requirementsSubset signaturesEq typeParametersEq
    declarationEq residual solvedRequirementsEq assumptionsMono covered
  have progress := Detail.inferStatementsFuel_inferenceProperties ready
    signatureFormation functionsCanonical returnBelow success
  have initialSubstitutionExtension : finalized.substitution.SemanticallyExtends
      initial.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans
      finalSubstitutionExtension progress.1.substitution_extends
  have initialInvariant : RecursiveStatementInvariant inferenceContext
      expectedReturn finalized initial semanticContext := {
    active := initialActive
    ready
    returnBelow
    bindersBelow
    nodesBelow := initialBelow
    schemeIsolation := initialSchemeIsolation
    substitutionExtension := initialSubstitutionExtension
    signaturesEq
    typeParametersEq
    declarationEq
    residual
    solvedRequirementsEq
    assumptionsMono
  }
  obtain ⟨finalContext, facts, finalInvariant, typing, agreement⟩ :=
    inferStatementsFuel_success_statementsHaveType_under_ambient_bounded_scoped_evidence_with_extra
      (fun state context => RecursiveStatementInvariant inferenceContext
        expectedReturn finalized state context)
      (fun state => finalized.substitution.SemanticallyExtends
        state.inference.substitution ∧
        state.integerLiterals ⊆ evidenceState.integerLiterals)
      (roots := roots) initialInvariant initialBelow resultExtension
      integerPatternsSubset requirementsSubset
      ⟨finalSubstitutionExtension, integerLiteralsSubset⟩
      (fun headInvariant headSuccess tailSuccess tailExtra => by
        have headProperties := Detail.inferStatementFuel_inferenceProperties
          headInvariant.ready signatureFormation functionsCanonical
          headInvariant.returnBelow headSuccess
        have tailProperties := Detail.inferStatementsFuel_inferenceProperties
          headProperties.2.1 signatureFormation functionsCanonical
          (headInvariant.returnBelow.weaken headProperties.1.next_le)
          tailSuccess
        exact ⟨TypeSystem.Substitution.SemanticallyExtends.trans
            tailExtra.1 tailProperties.1.substitution_extends,
          List.Subset.trans
            (Detail.inferStatementsFuel_integerLiterals_subset tailSuccess)
            tailExtra.2⟩)
      covered
      (fun childBound childInvariant childSuccess childExtension
        childIntegerPatternsSubset childRequirementsSubset childExtra
        childCovered =>
        statementSound _ childBound childSuccess resources
          signatureFormation functionsCanonical catalog signatureParameters
          childInvariant childExtra.1 childExtension childIntegerPatternsSubset
          childExtra.2 childRequirementsSubset childCovered)
      success
  exact ⟨finalContext, facts, finalInvariant.active, typing, agreement⟩

/-- The remaining branch proof can be supplied one fuel layer at a time.  A
single statement at fuel `n` may invoke a statement list only at smaller
fuel; the sequencing theorem above then closes all source-ordered lists. -/
theorem inferStatementsFuelSoundness_of_recursive_statement_step
    (step : ∀ fuel,
      (∀ childFuel, childFuel < fuel →
        InferStatementsFuelSoundness childFuel) →
      InferStatementFuelSoundness fuel) :
    ∀ fuel, InferStatementsFuelSoundness fuel := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel induction =>
      apply inferStatementsFuelSoundness_of_statementSoundness
      intro childFuel childBound
      apply step childFuel
      intro nestedFuel nestedBound
      exact induction nestedFuel (Nat.lt_trans nestedBound childBound)

/-- Strong, two-source one-statement theorem needed by nested blocks and
lambda bodies.  `semanticSource` is the enclosing construct's completed local
source; `finalized.typedSource` is only the whole-body evidence source.  The
resource index deliberately belongs to the whole checker body, not the
possibly different return type or loop depth of this local traversal. -/
def InferStatementFuelScopedSoundness (fuel : Nat) : Prop :=
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {initial : State}
    {result : Detail.StatementResult} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {semanticContext : SourceSemantics.Context},
    Detail.inferStatementFuel fuel inferenceContext statement expectedReturn
      initial = .ok result →
    FinalInferenceResources wholeContext wholeReturn evidenceState roots
      finalized →
    inferenceContext.signatures = wholeContext.signatures →
    inferenceContext.scope.genericOwner = wholeContext.scope.genericOwner →
    inferenceContext.typeParameters = wholeContext.typeParameters →
    inferenceContext.assumptions = wholeContext.assumptions →
    ProgramSignatureFormationValidated inferenceContext.signatures →
    (∀ candidate ∈ inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes)) →
    SignatureCatalogWellFormed inferenceContext.signatures →
    SignatureParametersWellFormed inferenceContext.scope.genericOwner
      inferenceContext.typeParameters →
    RecursiveStatementInvariant wholeContext expectedReturn finalized
      initial semanticContext →
    finalized.substitution.SemanticallyExtends
      result.state.inference.substitution →
    TypingSourceExtends
      ((result.state.toTypedSource roots).applySubstitution
        finalized.substitution) semanticSource →
    TypingSourceExtends semanticSource finalized.typedSource →
    TypingSourceExtends (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots) →
    result.state.integerPatterns ⊆ evidenceState.integerPatterns →
    result.state.integerLiterals ⊆ evidenceState.integerLiterals →
    result.state.requirements ⊆ evidenceState.requirements →
    TemplateScopeCovered finalized.typedSource semanticContext
      (.statement result.id) →
    ∃ finalContext facts,
      RecursiveStatementInvariant wholeContext expectedReturn finalized
        result.state finalContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts

/-- Source-ordered sequencing for the strong two-source contract.  Unlike the
checker specialization, this can be instantiated with a block or lambda's
local parent source while its proof obligations still consult whole-body
coverage and ledgers. -/
def InferStatementsFuelScopedSoundness (fuel : Nat) : Prop :=
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statements : List Syntax.Statement} {initial : State}
    {result : Detail.BlockResult} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {semanticContext : SourceSemantics.Context},
    Detail.inferStatementsFuel fuel inferenceContext statements expectedReturn
      initial = .ok result →
    FinalInferenceResources wholeContext wholeReturn evidenceState roots
      finalized →
    inferenceContext.signatures = wholeContext.signatures →
    inferenceContext.scope.genericOwner = wholeContext.scope.genericOwner →
    inferenceContext.typeParameters = wholeContext.typeParameters →
    inferenceContext.assumptions = wholeContext.assumptions →
    ProgramSignatureFormationValidated inferenceContext.signatures →
    (∀ candidate ∈ inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes)) →
    SignatureCatalogWellFormed inferenceContext.signatures →
    SignatureParametersWellFormed inferenceContext.scope.genericOwner
      inferenceContext.typeParameters →
    RecursiveStatementInvariant wholeContext expectedReturn finalized
      initial semanticContext →
    finalized.substitution.SemanticallyExtends
      result.state.inference.substitution →
    TypingSourceExtends
      ((result.state.toTypedSource roots).applySubstitution
        finalized.substitution) semanticSource →
    TypingSourceExtends semanticSource finalized.typedSource →
    TypingSourceExtends (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots) →
    result.state.integerPatterns ⊆ evidenceState.integerPatterns →
    result.state.integerLiterals ⊆ evidenceState.integerLiterals →
    result.state.requirements ⊆ evidenceState.requirements →
    (∀ statement ∈ result.statements,
      TemplateScopeCovered finalized.typedSource semanticContext
        (.statement statement)) →
    ∃ finalContext facts,
      RecursiveStatementInvariant wholeContext expectedReturn finalized
        result.state finalContext ∧
      StatementsHaveType semanticSource
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.statements finalContext facts ∧
      BlockResultMatchesFactsAfterSubstitution finalized.substitution result
        facts

theorem inferStatementsFuelScopedSoundness_of_statementSoundness
    {fuel : Nat}
    (statementSound : ∀ childFuel, childFuel < fuel →
      InferStatementFuelScopedSoundness childFuel) :
    InferStatementsFuelScopedSoundness fuel := by
  intro wholeContext inferenceContext wholeReturn expectedReturn statements
    initial result evidenceState roots finalized semanticSource semanticContext
    success resources signaturesEq ownerEq parametersEq assumptionsEq
    signatureFormation functionsCanonical catalog signatureParameters
    initialInvariant finalSubstitutionExtension resultExtension
    semanticSourceExtension rawResultExtension integerPatternsSubset
    integerLiteralsSubset requirementsSubset covered
  obtain ⟨finalContext, facts, finalInvariant, typing, agreement⟩ :=
    inferStatementsFuel_success_statementsHaveType_under_ambient_bounded_scoped_evidence_with_extra
      (fun state context => RecursiveStatementInvariant wholeContext
        expectedReturn finalized state context)
      (fun state => finalized.substitution.SemanticallyExtends
        state.inference.substitution ∧
        state.integerLiterals ⊆ evidenceState.integerLiterals ∧
        TypingSourceExtends (state.toTypedSource roots)
          (evidenceState.toTypedSource roots))
      (roots := roots) initialInvariant initialInvariant.nodesBelow
      resultExtension integerPatternsSubset requirementsSubset
      ⟨finalSubstitutionExtension, integerLiteralsSubset,
        rawResultExtension⟩
      (by
        intro headFuel childFuel headInitial headContext headStatement head
          tail remaining headInvariant headSuccess tailSuccess tailExtra
        have headProperties := Detail.inferStatementFuel_inferenceProperties
          headInvariant.ready signatureFormation functionsCanonical
          headInvariant.returnBelow headSuccess
        have tailProperties := Detail.inferStatementsFuel_inferenceProperties
          headProperties.2.1 signatureFormation functionsCanonical
          (headInvariant.returnBelow.weaken headProperties.1.next_le)
          tailSuccess
        have headNodesBelow : head.state.NodesBelowNextOccurrence :=
          (Detail.inferStatementFuel_occurrenceBoundExtends headSuccess
            ).nodesBelowNextOccurrence headInvariant.nodesBelow
        have headToTail : TypingSourceExtends
            (head.state.toTypedSource roots)
            (tail.state.toTypedSource roots) :=
          inferStatementsFuel_success_typingSourceExtends tailSuccess
            headNodesBelow roots
        exact ⟨TypeSystem.Substitution.SemanticallyExtends.trans
            tailExtra.1 tailProperties.1.substitution_extends,
          List.Subset.trans
            (Detail.inferStatementsFuel_integerLiterals_subset tailSuccess)
            tailExtra.2.1,
          TypingSourceExtends.trans headToTail tailExtra.2.2⟩)
      covered
      (fun childBound childInvariant childSuccess childExtension
        childIntegerPatternsSubset childRequirementsSubset childExtra
        childCovered =>
        statementSound _ childBound childSuccess resources signaturesEq
          ownerEq parametersEq assumptionsEq signatureFormation
          functionsCanonical catalog signatureParameters childInvariant
          childExtra.1 childExtension semanticSourceExtension
          childExtra.2.2 childIntegerPatternsSubset childExtra.2.1
          childRequirementsSubset childCovered)
      success
  exact ⟨finalContext, facts, finalInvariant, typing, agreement⟩

/-- The local-source statement and block judgments close by strong fuel
induction once the syntax-directed one-statement step is supplied. -/
theorem inferStatementsFuelScopedSoundness_of_recursive_statement_step
    (step : ∀ fuel,
      (∀ childFuel, childFuel < fuel →
        InferStatementsFuelScopedSoundness childFuel) →
      InferStatementFuelScopedSoundness fuel) :
    ∀ fuel, InferStatementsFuelScopedSoundness fuel := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel induction =>
      apply inferStatementsFuelScopedSoundness_of_statementSoundness
      intro childFuel childBound
      apply step childFuel
      intro nestedFuel nestedBound
      exact induction nestedFuel (Nat.lt_trans nestedBound childBound)

/-- The checker-facing statement theorem is the whole-body specialization of
the two-source recursive theorem.  The initial substitution invariant follows
from the actual successful list inference and its final substitution
extension; no extra callback is assumed at this boundary. -/
theorem inferStatementsFuelSoundness_of_scopedSoundness
    {fuel : Nat}
    (scopedSound : InferStatementsFuelScopedSoundness fuel) :
    InferStatementsFuelSoundness fuel := by
  intro inferenceContext statements expectedReturn initial result
    evidenceState roots finalized semanticContext success resources
    signatureFormation functionsCanonical catalog signatureParameters
    initialActive initialSchemeIsolation ready returnBelow bindersBelow
    initialBelow
    finalSubstitutionExtension rawResultExtension resultExtension
    integerPatternsSubset integerLiteralsSubset requirementsSubset
    signaturesEq typeParametersEq declarationEq residual
    solvedRequirementsEq assumptionsMono covered
  have progress := Detail.inferStatementsFuel_inferenceProperties ready
    signatureFormation functionsCanonical returnBelow success
  have initialSubstitutionExtension : finalized.substitution.SemanticallyExtends
      initial.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans
      finalSubstitutionExtension progress.1.substitution_extends
  have initialInvariant : RecursiveStatementInvariant inferenceContext
      expectedReturn finalized initial semanticContext := {
    active := initialActive
    ready
    returnBelow
    bindersBelow
    nodesBelow := initialBelow
    schemeIsolation := initialSchemeIsolation
    substitutionExtension := initialSubstitutionExtension
    signaturesEq
    typeParametersEq
    declarationEq
    residual
    solvedRequirementsEq
    assumptionsMono
  }
  obtain ⟨finalContext, facts, finalInvariant, typing, agreement⟩ :=
    scopedSound (wholeContext := inferenceContext)
      (wholeReturn := expectedReturn)
      (semanticSource := finalized.typedSource)
      success resources rfl rfl rfl rfl signatureFormation
      functionsCanonical catalog signatureParameters initialInvariant
      finalSubstitutionExtension resultExtension
      (TypingSourceExtends.refl _) rawResultExtension
      integerPatternsSubset integerLiteralsSubset requirementsSubset covered
  exact ⟨finalContext, facts, finalInvariant.active, typing, agreement⟩

/-- A successful block consumes the scoped soundness theorem for its actual
body traversal.  The recorded block node supplies each body root's coverage;
the body source and three ledgers are prefixes of the enclosing statement's
successful result. -/
theorem inferStatementFuel_success_block_of_scoped_body
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {body : List Syntax.Statement}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticContext : SourceSemantics.Context}
    (statementEq : statement.value = .block body)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (ownerEq : inferenceContext.scope.genericOwner =
      wholeContext.scope.genericOwner)
    (parametersEq : inferenceContext.typeParameters =
      wholeContext.typeParameters)
    (assumptionsEq : inferenceContext.assumptions =
      wholeContext.assumptions)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈
      inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signatureParameters : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (initialInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initial semanticContext)
    (resultSubstitutionExtension : finalized.substitution.SemanticallyExtends
      result.state.inference.substitution)
    (resultExtension : TypingSourceExtends
      ((result.state.toTypedSource roots).applySubstitution
        finalized.substitution) finalized.typedSource)
    (rawResultExtension : TypingSourceExtends
      (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots))
    (integerPatternsSubset : result.state.integerPatterns ⊆
      evidenceState.integerPatterns)
    (integerLiteralsSubset : result.state.integerLiterals ⊆
      evidenceState.integerLiterals)
    (requirementsSubset : result.state.requirements ⊆
      evidenceState.requirements)
    (parentCovered : TemplateScopeCovered finalized.typedSource
      semanticContext (.statement result.id))
    (bodySound : InferStatementsFuelScopedSoundness fuel) :
    ∃ finalContext facts,
      RecursiveStatementInvariant wholeContext expectedReturn finalized
        result.state finalContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts := by
  obtain ⟨bodyResult, bodySuccess, resultEq, parentNode⟩ :=
    inferStatementFuel_success_block_facts statementEq allocationEq success
      roots
  obtain ⟨bodyResult', bodySuccess', _allocatedBelow, bodyExtension,
      bodyIntegerPatternsSubset, bodyRequirementsSubset⟩ :=
    inferStatementFuel_success_block_child_provenance statementEq allocationEq
      success initialInvariant.nodesBelow roots
  have bodyResultEq : bodyResult' = bodyResult := by
    rw [bodySuccess] at bodySuccess'
    exact (Except.ok.inj bodySuccess').symm
  subst bodyResult'
  have allocatedInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized allocated semanticContext :=
    initialInvariant.allocateStatementId allocationEq
  have bodySubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        bodyResult.state.inference.substitution := by
    simpa [resultEq, State.restoreLexicalScope, State.recordNode] using
      resultSubstitutionExtension
  have bodyIntegerLiteralsSubset :
      bodyResult.state.integerLiterals ⊆ result.state.integerLiterals := by
    rw [resultEq]
    intro literal member
    simpa [State.restoreLexicalScope, State.recordNode] using member
  have bodyCovered : ∀ child, child ∈ bodyResult.statements →
      TemplateScopeCovered finalized.typedSource semanticContext
        (.statement child) := by
    intro child member
    have childEdge : DirectChild (result.state.toTypedSource roots)
        (.statement result.id) (.statement child) := by
      refine ⟨.statement {
        id := result.id
        span := statement.span
        type := result.type
        form := .block bodyResult.statements
      }, ?_, ?_⟩
      · refine ⟨parentNode.1, ?_⟩
        exact congrArg NodeId.statement parentNode.2
      · simpa [nodeChildIds, Node.references, StatementForm.references] using
          (List.mem_map.mpr ⟨child, member, rfl⟩ :
            NodeId.statement child ∈
              bodyResult.statements.map NodeId.statement)
    have coveredEdge : DirectChild finalized.typedSource
        (.statement result.id) (.statement child) :=
      DirectChild.ofTypingSourceExtends resultExtension
        (FlexibleSubstitution.directChild_applySubstitution
          finalized.substitution childEdge)
    exact TemplateScopeCovered.statementChild parentCovered
      resources.graph_closed coveredEdge (fun _ membership => membership)
  have branch : ∃ finalContext facts,
      ActiveLocalContextInvariant result.state finalized.substitution
        finalContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts := by
    have blockSound := inferStatementFuel_success_block_sound
      statementEq allocationEq success initialInvariant.active roots
      (by
        intro actualBody actualSuccess
        have actualEq : actualBody = bodyResult := by
          rw [bodySuccess] at actualSuccess
          exact (Except.ok.inj actualSuccess).symm
        subst actualBody
        obtain ⟨bodyContext, bodyFacts, bodyInvariant, bodyTyping,
            bodyAgreement⟩ :=
          bodySound bodySuccess resources signaturesEq ownerEq parametersEq
            assumptionsEq signatureFormation functionsCanonical catalog
            signatureParameters allocatedInvariant bodySubstitutionExtension
            (bodyExtension.applySubstitution finalized.substitution)
            resultExtension
            (TypingSourceExtends.trans bodyExtension rawResultExtension)
            (List.Subset.trans bodyIntegerPatternsSubset integerPatternsSubset)
            (List.Subset.trans bodyIntegerLiteralsSubset integerLiteralsSubset)
            (List.Subset.trans bodyRequirementsSubset requirementsSubset)
            bodyCovered
        exact ⟨bodyContext, bodyFacts, bodyInvariant.active, bodyTyping,
          bodyAgreement⟩)
    obtain ⟨facts, active, typing, agreement⟩ := blockSound
    exact ⟨semanticContext, facts, active, typing, agreement⟩
  have resultSchemeIsolation : ActiveSchemeQuantifierIsolation
      result.state := by
    apply activeSchemeQuantifierIsolation_transport
      allocatedInvariant.schemeIsolation
    simp [resultEq, State.restoreLexicalScope, State.recordNode,
      State.lexicalScope]
  exact RecursiveStatementInvariant.close_statement_branch initialInvariant
    success signatureFormation functionsCanonical
    (inferStatementFuel_preserves_localBindersBelowNextLocal
      initialInvariant.bindersBelow success)
    resultSubstitutionExtension resultSchemeIsolation branch

/-- The while-loop body is checked at the actual condition-result state and
typed under the loop-depth increment.  Its semantic source is the completed
while statement, while coverage and requirements remain anchored to the
whole finalized body. -/
theorem inferStatementFuel_success_whileLoop_of_scoped_body
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {condition : Syntax.Expr}
    {body : Syntax.Block}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticContext : SourceSemantics.Context}
    (statementEq : statement.value = .whileLoop condition body)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (ownerEq : inferenceContext.scope.genericOwner =
      wholeContext.scope.genericOwner)
    (parametersEq : inferenceContext.typeParameters =
      wholeContext.typeParameters)
    (assumptionsEq : inferenceContext.assumptions =
      wholeContext.assumptions)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈
      inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signatureParameters : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (initialInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initial semanticContext)
    (resultSubstitutionExtension : finalized.substitution.SemanticallyExtends
      result.state.inference.substitution)
    (resultExtension : TypingSourceExtends
      ((result.state.toTypedSource roots).applySubstitution
        finalized.substitution) finalized.typedSource)
    (rawResultExtension : TypingSourceExtends
      (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots))
    (integerPatternsSubset : result.state.integerPatterns ⊆
      evidenceState.integerPatterns)
    (integerLiteralsSubset : result.state.integerLiterals ⊆
      evidenceState.integerLiterals)
    (requirementsSubset : result.state.requirements ⊆
      evidenceState.requirements)
    (parentCovered : TemplateScopeCovered finalized.typedSource
      semanticContext (.statement result.id))
    (conditionSound : ∀ {inferredCondition : InferredExpression}
      {conditionState : State},
      Detail.inferExprFuel fuel inferenceContext condition (some .bool)
        allocated = .ok (inferredCondition, conditionState) →
      ExpressionHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        semanticContext inferredCondition.id
        (finalized.substitution.apply inferredCondition.type))
    (bodySound : InferStatementsFuelScopedSoundness fuel) :
    ∃ finalContext facts,
      RecursiveStatementInvariant wholeContext expectedReturn finalized
        result.state finalContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts := by
  let loopContext : Frontend.SourceInference.Context := {
    inferenceContext with loopDepth := inferenceContext.loopDepth + 1 }
  obtain ⟨inferredCondition, conditionState, bodyResult, conditionSuccess,
      actualBodySuccess, resultEq, contains⟩ :=
    inferStatementFuel_success_whileLoop_facts statementEq allocationEq
      success roots
  obtain ⟨actualConditionState, actualBodyResult,
      ⟨actualCondition, actualConditionSuccess⟩, actualBodySuccess',
      conditionBelow, bodySourceExtension, bodyIntegerPatternsSubset,
      bodyRequirementsSubset⟩ :=
    inferStatementFuel_success_whileLoop_child_provenance statementEq
      allocationEq success initialInvariant.nodesBelow roots
  have conditionStateEq : actualConditionState = conditionState := by
    rw [conditionSuccess] at actualConditionSuccess
    exact (congrArg Prod.snd
      (Except.ok.inj actualConditionSuccess)).symm
  subst actualConditionState
  have bodyResultEq : actualBodyResult = bodyResult := by
    rw [actualBodySuccess] at actualBodySuccess'
    exact (Except.ok.inj actualBodySuccess').symm
  subst actualBodyResult
  have allocatedInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized allocated semanticContext :=
    initialInvariant.allocateStatementId allocationEq
  have conditionProperties := Detail.inferExprFuel_inferenceProperties
    allocatedInvariant.ready signatureFormation functionsCanonical (by
      intro expected member
      simp only [Option.mem_def] at member
      injection member with expectedEq
      subst expected
      simp [Ty.bool]) conditionSuccess
  have conditionReturnBelow :
      expectedReturn.VariablesBelow conditionState.inference.next :=
    allocatedInvariant.returnBelow.weaken conditionProperties.1.next_le
  have bodyProperties := Detail.inferStatementsFuel_inferenceProperties
    (context := loopContext) conditionProperties.2.1 signatureFormation
    functionsCanonical conditionReturnBelow actualBodySuccess
  have bodySubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        bodyResult.state.inference.substitution := by
    simpa [resultEq, State.restoreLexicalScope, State.recordNode] using
      resultSubstitutionExtension
  have conditionSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        conditionState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans
      bodySubstitutionExtension bodyProperties.1.substitution_extends
  have conditionInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized conditionState semanticContext :=
    allocatedInvariant.inferExprFuel conditionSuccess signatureFormation
      functionsCanonical (by
        intro expected member
        simp only [Option.mem_def] at member
        injection member with expectedEq
        subst expected
        simp [Ty.bool]) conditionSubstitutionExtension
  have bodyIntegerLiteralsSubset :
      bodyResult.state.integerLiterals ⊆ result.state.integerLiterals := by
    rw [resultEq]
    intro literal member
    simpa [State.restoreLexicalScope, State.recordNode] using member
  have bodyCovered : ∀ child, child ∈ bodyResult.statements →
      TemplateScopeCovered finalized.typedSource semanticContext
        (.statement child) := by
    intro child member
    have childReference : (.statement child : NodeId) ∈
        (StatementForm.whileLoop inferredCondition.id
          bodyResult.statements).references := by
      simp [StatementForm.references, member]
    exact TemplateScopeCovered.statementChild_of_recorded_reference
      contains childReference resultExtension parentCovered
      resources.graph_closed (fun _ membership => membership)
  obtain ⟨bodyFinal, bodyFacts, bodyInvariant, bodyTyping,
      bodyAgreement⟩ :=
    bodySound actualBodySuccess resources (by simpa [loopContext] using signaturesEq)
      (by simpa [loopContext] using ownerEq)
      (by simpa [loopContext] using parametersEq)
      (by simpa [loopContext] using assumptionsEq)
      signatureFormation functionsCanonical catalog signatureParameters
      conditionInvariant bodySubstitutionExtension
      (bodySourceExtension.applySubstitution finalized.substitution)
      resultExtension
      (TypingSourceExtends.trans bodySourceExtension rawResultExtension)
      (List.Subset.trans bodyIntegerPatternsSubset integerPatternsSubset)
      (List.Subset.trans bodyIntegerLiteralsSubset integerLiteralsSubset)
      (List.Subset.trans bodyRequirementsSubset requirementsSubset)
      bodyCovered
  have branch : ∃ finalContext facts,
      ActiveLocalContextInvariant result.state finalized.substitution
        finalContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts := by
    have conditionTyping := conditionSound conditionSuccess
    have conditionEq : finalized.substitution.apply inferredCondition.type =
        .bool := by
      simpa using Detail.inferExprFuel_expected_type_apply_eq
        conditionSuccess conditionSubstitutionExtension
    subst result
    refine ⟨semanticContext, {
        type := .unit
        hasValue := false
        sawReturn := false
        control := .loop bodyFacts.control
      }, conditionInvariant.active.restoreLexicalScope_recordNode _, ?_, ?_⟩
    · exact whileLoopStatementHasType_afterSubstitution contains
        conditionTyping conditionEq bodyTyping
    · exact StatementResultMatchesFactsAfterSubstitution.whileLoop
        finalized.substitution bodyFacts id _
  have resultSchemeIsolation : ActiveSchemeQuantifierIsolation
      result.state := by
    apply activeSchemeQuantifierIsolation_transport
      conditionInvariant.schemeIsolation
    simp [resultEq, State.restoreLexicalScope, State.recordNode,
      State.lexicalScope]
  exact RecursiveStatementInvariant.close_statement_branch initialInvariant
    success signatureFormation functionsCanonical
    (inferStatementFuel_preserves_localBindersBelowNextLocal
      initialInvariant.bindersBelow success)
    resultSubstitutionExtension resultSchemeIsolation branch

/-- The no-else conditional consumes only its actual then-body traversal;
the missing else branch contributes the ordinary unit control fact. -/
theorem inferStatementFuel_success_ifWithoutElse_of_scoped_body
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {condition : Syntax.Expr}
    {thenBody : Syntax.Block}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticContext : SourceSemantics.Context}
    (statementEq : statement.value = .ifThen condition thenBody none)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (ownerEq : inferenceContext.scope.genericOwner =
      wholeContext.scope.genericOwner)
    (parametersEq : inferenceContext.typeParameters =
      wholeContext.typeParameters)
    (assumptionsEq : inferenceContext.assumptions =
      wholeContext.assumptions)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈
      inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signatureParameters : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (initialInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initial semanticContext)
    (resultSubstitutionExtension : finalized.substitution.SemanticallyExtends
      result.state.inference.substitution)
    (resultExtension : TypingSourceExtends
      ((result.state.toTypedSource roots).applySubstitution
        finalized.substitution) finalized.typedSource)
    (rawResultExtension : TypingSourceExtends
      (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots))
    (integerPatternsSubset : result.state.integerPatterns ⊆
      evidenceState.integerPatterns)
    (integerLiteralsSubset : result.state.integerLiterals ⊆
      evidenceState.integerLiterals)
    (requirementsSubset : result.state.requirements ⊆
      evidenceState.requirements)
    (parentCovered : TemplateScopeCovered finalized.typedSource
      semanticContext (.statement result.id))
    (conditionSound : ∀ {inferredCondition : InferredExpression}
      {conditionState : State},
      Detail.inferExprFuel fuel inferenceContext condition (some .bool)
        allocated = .ok (inferredCondition, conditionState) →
      ExpressionHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        semanticContext inferredCondition.id
        (finalized.substitution.apply inferredCondition.type))
    (thenSound : InferStatementsFuelScopedSoundness fuel) :
    ∃ finalContext facts,
      RecursiveStatementInvariant wholeContext expectedReturn finalized
        result.state finalContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts := by
  obtain ⟨inferredCondition, conditionState, thenResult, conditionSuccess,
      thenSuccess, resultEq, contains⟩ :=
    inferStatementFuel_success_ifWithoutElse_facts statementEq allocationEq
      success roots
  obtain ⟨actualConditionState, actualThenResult,
      ⟨actualCondition, actualConditionSuccess⟩, actualThenSuccess,
      _conditionBelow, thenSourceExtension, thenIntegerPatternsSubset,
      thenRequirementsSubset⟩ :=
    inferStatementFuel_success_ifWithoutElse_child_provenance statementEq
      allocationEq success initialInvariant.nodesBelow roots
  have conditionStateEq : actualConditionState = conditionState := by
    rw [conditionSuccess] at actualConditionSuccess
    exact (congrArg Prod.snd
      (Except.ok.inj actualConditionSuccess)).symm
  subst actualConditionState
  have thenResultEq : actualThenResult = thenResult := by
    rw [thenSuccess] at actualThenSuccess
    exact (Except.ok.inj actualThenSuccess).symm
  subst actualThenResult
  have allocatedInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized allocated semanticContext :=
    initialInvariant.allocateStatementId allocationEq
  have conditionProperties := Detail.inferExprFuel_inferenceProperties
    allocatedInvariant.ready signatureFormation functionsCanonical (by
      intro expected member
      simp only [Option.mem_def] at member
      injection member with expectedEq
      subst expected
      simp [Ty.bool]) conditionSuccess
  have conditionReturnBelow :
      expectedReturn.VariablesBelow conditionState.inference.next :=
    allocatedInvariant.returnBelow.weaken conditionProperties.1.next_le
  have thenProperties := Detail.inferStatementsFuel_inferenceProperties
    conditionProperties.2.1 signatureFormation functionsCanonical
    conditionReturnBelow thenSuccess
  have thenSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        thenResult.state.inference.substitution := by
    simpa [resultEq, State.restoreLexicalScope, State.recordNode] using
      resultSubstitutionExtension
  have conditionSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        conditionState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans
      thenSubstitutionExtension thenProperties.1.substitution_extends
  have conditionInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized conditionState semanticContext :=
    allocatedInvariant.inferExprFuel conditionSuccess signatureFormation
      functionsCanonical (by
        intro expected member
        simp only [Option.mem_def] at member
        injection member with expectedEq
        subst expected
        simp [Ty.bool]) conditionSubstitutionExtension
  have thenIntegerLiteralsSubset :
      thenResult.state.integerLiterals ⊆ result.state.integerLiterals := by
    rw [resultEq]
    intro literal member
    simpa [State.restoreLexicalScope, State.recordNode] using member
  have thenCovered : ∀ child, child ∈ thenResult.statements →
      TemplateScopeCovered finalized.typedSource semanticContext
        (.statement child) := by
    intro child member
    have childReference : (.statement child : NodeId) ∈
        (StatementForm.ifThen inferredCondition.id thenResult.statements
          none).references := by
      simp [StatementForm.references, member]
    exact TemplateScopeCovered.statementChild_of_recorded_reference
      contains childReference resultExtension parentCovered
      resources.graph_closed (fun _ membership => membership)
  obtain ⟨thenFinal, thenFacts, thenInvariant, thenTyping,
      thenAgreement⟩ :=
    thenSound thenSuccess resources signaturesEq ownerEq parametersEq
      assumptionsEq signatureFormation functionsCanonical catalog
      signatureParameters conditionInvariant thenSubstitutionExtension
      (thenSourceExtension.applySubstitution finalized.substitution)
      resultExtension
      (TypingSourceExtends.trans thenSourceExtension rawResultExtension)
      (List.Subset.trans thenIntegerPatternsSubset integerPatternsSubset)
      (List.Subset.trans thenIntegerLiteralsSubset integerLiteralsSubset)
      (List.Subset.trans thenRequirementsSubset requirementsSubset)
      thenCovered
  have branch : ∃ finalContext facts,
      ActiveLocalContextInvariant result.state finalized.substitution
        finalContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts := by
    have conditionTyping := conditionSound conditionSuccess
    have conditionEq : finalized.substitution.apply inferredCondition.type =
        .bool := by
      simpa using Detail.inferExprFuel_expected_type_apply_eq
        conditionSuccess conditionSubstitutionExtension
    subst result
    refine ⟨semanticContext, {
        type := .unit
        hasValue := false
        sawReturn := false
        control := thenFacts.control.branches (.ordinary .unit)
      }, conditionInvariant.active.restoreLexicalScope_recordNode _, ?_, ?_⟩
    · exact ifWithoutElseStatementHasType_afterSubstitution contains
        conditionTyping conditionEq thenTyping
    · exact StatementResultMatchesFactsAfterSubstitution.ifWithoutElse
        finalized.substitution thenFacts id _
  have resultSchemeIsolation : ActiveSchemeQuantifierIsolation
      result.state := by
    apply activeSchemeQuantifierIsolation_transport
      conditionInvariant.schemeIsolation
    simp [resultEq, State.restoreLexicalScope, State.recordNode,
      State.lexicalScope]
  exact RecursiveStatementInvariant.close_statement_branch initialInvariant
    success signatureFormation functionsCanonical
    (inferStatementFuel_preserves_localBindersBelowNextLocal
      initialInvariant.bindersBelow success)
    resultSubstitutionExtension resultSchemeIsolation branch

/-- Both branches of a successful conditional are typed from their concrete
traces.  The second branch starts from the restored condition scope, while
both branches' roots remain direct children of the completed parent node. -/
theorem inferStatementFuel_success_ifWithElse_of_scoped_bodies
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {condition : Syntax.Expr}
    {thenBody elseBody : Syntax.Block}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticContext : SourceSemantics.Context}
    (statementEq : statement.value = .ifThen condition thenBody
      (some elseBody))
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (ownerEq : inferenceContext.scope.genericOwner =
      wholeContext.scope.genericOwner)
    (parametersEq : inferenceContext.typeParameters =
      wholeContext.typeParameters)
    (assumptionsEq : inferenceContext.assumptions =
      wholeContext.assumptions)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈
      inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signatureParameters : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (initialInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initial semanticContext)
    (resultSubstitutionExtension : finalized.substitution.SemanticallyExtends
      result.state.inference.substitution)
    (resultExtension : TypingSourceExtends
      ((result.state.toTypedSource roots).applySubstitution
        finalized.substitution) finalized.typedSource)
    (rawResultExtension : TypingSourceExtends
      (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots))
    (integerPatternsSubset : result.state.integerPatterns ⊆
      evidenceState.integerPatterns)
    (integerLiteralsSubset : result.state.integerLiterals ⊆
      evidenceState.integerLiterals)
    (requirementsSubset : result.state.requirements ⊆
      evidenceState.requirements)
    (parentCovered : TemplateScopeCovered finalized.typedSource
      semanticContext (.statement result.id))
    (conditionSound : ∀ {inferredCondition : InferredExpression}
      {conditionState : State},
      Detail.inferExprFuel fuel inferenceContext condition (some .bool)
        allocated = .ok (inferredCondition, conditionState) →
      ExpressionHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        semanticContext inferredCondition.id
        (finalized.substitution.apply inferredCondition.type))
    (branchSound : InferStatementsFuelScopedSoundness fuel) :
    ∃ finalContext facts,
      RecursiveStatementInvariant wholeContext expectedReturn finalized
        result.state finalContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts := by
  obtain ⟨inferredCondition, conditionState, thenResult, elseResult,
      conditionSuccess, thenSuccess, elseSuccess, resultEq, contains⟩ :=
    inferStatementFuel_success_ifWithElse_facts statementEq allocationEq
      success roots
  obtain ⟨actualConditionState, actualThenResult, actualElseResult,
      ⟨actualCondition, actualConditionSuccess⟩, actualThenSuccess,
      actualElseSuccess, _conditionBelow, _elseInputBelow,
      thenSourceExtension, elseSourceExtension,
      thenIntegerPatternsSubset, elseIntegerPatternsSubset,
      thenRequirementsSubset, elseRequirementsSubset⟩ :=
    inferStatementFuel_success_ifWithElse_child_provenance statementEq
      allocationEq success initialInvariant.nodesBelow roots
  have conditionStateEq : actualConditionState = conditionState := by
    rw [conditionSuccess] at actualConditionSuccess
    exact (congrArg Prod.snd
      (Except.ok.inj actualConditionSuccess)).symm
  subst actualConditionState
  have thenResultEq : actualThenResult = thenResult := by
    rw [thenSuccess] at actualThenSuccess
    exact (Except.ok.inj actualThenSuccess).symm
  subst actualThenResult
  have elseResultEq : actualElseResult = elseResult := by
    rw [elseSuccess] at actualElseSuccess
    exact (Except.ok.inj actualElseSuccess).symm
  subst actualElseResult
  have allocatedInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized allocated semanticContext :=
    initialInvariant.allocateStatementId allocationEq
  have conditionProperties := Detail.inferExprFuel_inferenceProperties
    allocatedInvariant.ready signatureFormation functionsCanonical (by
      intro expected member
      simp only [Option.mem_def] at member
      injection member with expectedEq
      subst expected
      simp [Ty.bool]) conditionSuccess
  have conditionReturnBelow :
      expectedReturn.VariablesBelow conditionState.inference.next :=
    allocatedInvariant.returnBelow.weaken conditionProperties.1.next_le
  have thenProperties := Detail.inferStatementsFuel_inferenceProperties
    conditionProperties.2.1 signatureFormation functionsCanonical
    conditionReturnBelow thenSuccess
  have thenBelow : thenResult.state.NodesBelowNextOccurrence :=
    (Detail.inferStatementsFuel_occurrenceBoundExtends thenSuccess
      ).nodesBelowNextOccurrence
        ((Detail.inferExprFuel_occurrenceBoundExtends conditionSuccess
          ).nodesBelowNextOccurrence allocatedInvariant.nodesBelow)
  have restoredProperties := State.restoreLexicalScope_inferenceProperties
    conditionProperties.2.1 thenProperties.1
  have elseReturnBelow : expectedReturn.VariablesBelow
      (thenResult.state.restoreLexicalScope
        conditionState.lexicalScope).inference.next :=
    conditionReturnBelow.weaken restoredProperties.1.next_le
  have elseProperties := Detail.inferStatementsFuel_inferenceProperties
    restoredProperties.2 signatureFormation functionsCanonical
    elseReturnBelow elseSuccess
  have elseSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        elseResult.state.inference.substitution := by
    simpa [resultEq, State.restoreLexicalScope, State.recordNode] using
      resultSubstitutionExtension
  have elseInputSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        (thenResult.state.restoreLexicalScope
          conditionState.lexicalScope).inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans
      elseSubstitutionExtension elseProperties.1.substitution_extends
  have conditionSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        conditionState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans
      elseInputSubstitutionExtension restoredProperties.1.substitution_extends
  have conditionInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized conditionState semanticContext :=
    allocatedInvariant.inferExprFuel conditionSuccess signatureFormation
      functionsCanonical (by
        intro expected member
        simp only [Option.mem_def] at member
        injection member with expectedEq
        subst expected
        simp [Ty.bool]) conditionSubstitutionExtension
  have elseInputInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized
      (thenResult.state.restoreLexicalScope conditionState.lexicalScope)
      semanticContext :=
    conditionInvariant.restoreLexicalScope thenProperties.1 thenBelow
      (Detail.inferStatementsFuel_nextLocal_le thenSuccess)
      elseInputSubstitutionExtension
  have thenSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        thenResult.state.inference.substitution := by
    simpa [State.restoreLexicalScope] using
      elseInputSubstitutionExtension
  have elseIntegerLiteralsSubset :
      elseResult.state.integerLiterals ⊆ result.state.integerLiterals := by
    rw [resultEq]
    intro literal member
    simpa [State.restoreLexicalScope, State.recordNode] using member
  have thenIntegerLiteralsSubset :
      thenResult.state.integerLiterals ⊆ result.state.integerLiterals := by
    have throughElse : thenResult.state.integerLiterals ⊆
        elseResult.state.integerLiterals := by
      simpa [State.restoreLexicalScope] using
        (Detail.inferStatementsFuel_integerLiterals_subset elseSuccess)
    exact List.Subset.trans throughElse elseIntegerLiteralsSubset
  have thenCovered : ∀ child, child ∈ thenResult.statements →
      TemplateScopeCovered finalized.typedSource semanticContext
        (.statement child) := by
    intro child member
    have childReference : (.statement child : NodeId) ∈
        (StatementForm.ifThen inferredCondition.id thenResult.statements
          (some elseResult.statements)).references := by
      simp [StatementForm.references, member]
    exact TemplateScopeCovered.statementChild_of_recorded_reference
      contains childReference resultExtension parentCovered
      resources.graph_closed (fun _ membership => membership)
  obtain ⟨thenFinal, thenFacts, thenInvariant, thenTyping,
      thenAgreement⟩ :=
    branchSound thenSuccess resources signaturesEq ownerEq parametersEq
      assumptionsEq signatureFormation functionsCanonical catalog
      signatureParameters conditionInvariant thenSubstitutionExtension
      (thenSourceExtension.applySubstitution finalized.substitution)
      resultExtension
      (TypingSourceExtends.trans thenSourceExtension rawResultExtension)
      (List.Subset.trans thenIntegerPatternsSubset integerPatternsSubset)
      (List.Subset.trans thenIntegerLiteralsSubset integerLiteralsSubset)
      (List.Subset.trans thenRequirementsSubset requirementsSubset)
      thenCovered
  have elseIntegerPatternsSubset' :=
    List.Subset.trans elseIntegerPatternsSubset integerPatternsSubset
  have elseIntegerLiteralsSubset' :=
    List.Subset.trans elseIntegerLiteralsSubset integerLiteralsSubset
  have elseRequirementsSubset' :=
    List.Subset.trans elseRequirementsSubset requirementsSubset
  have elseCovered : ∀ child, child ∈ elseResult.statements →
      TemplateScopeCovered finalized.typedSource semanticContext
        (.statement child) := by
    intro child member
    have childReference : (.statement child : NodeId) ∈
        (StatementForm.ifThen inferredCondition.id thenResult.statements
          (some elseResult.statements)).references := by
      simp [StatementForm.references, member]
    exact TemplateScopeCovered.statementChild_of_recorded_reference
      contains childReference resultExtension parentCovered
      resources.graph_closed (fun _ membership => membership)
  obtain ⟨elseFinal, elseFacts, elseInvariant, elseTyping,
      elseAgreement⟩ :=
    branchSound elseSuccess resources signaturesEq ownerEq parametersEq
      assumptionsEq signatureFormation functionsCanonical catalog
      signatureParameters elseInputInvariant elseSubstitutionExtension
      (elseSourceExtension.applySubstitution finalized.substitution)
      resultExtension
      (TypingSourceExtends.trans elseSourceExtension rawResultExtension)
      elseIntegerPatternsSubset' elseIntegerLiteralsSubset'
      elseRequirementsSubset' elseCovered
  have branch : ∃ finalContext facts,
      ActiveLocalContextInvariant result.state finalized.substitution
        finalContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts := by
    have conditionTyping := conditionSound conditionSuccess
    have conditionEq : finalized.substitution.apply inferredCondition.type =
        .bool := by
      simpa using Detail.inferExprFuel_expected_type_apply_eq
        conditionSuccess conditionSubstitutionExtension
    subst result
    refine ⟨semanticContext, {
        type := if thenFacts.sawReturn && elseFacts.sawReturn then
          finalized.substitution.apply expectedReturn
        else
          .unit
        hasValue := thenFacts.sawReturn && elseFacts.sawReturn
        sawReturn := thenFacts.sawReturn && elseFacts.sawReturn
        control := thenFacts.control.branches elseFacts.control
      }, conditionInvariant.active.restoreLexicalScope_recordNode _, ?_, ?_⟩
    · exact ifWithElseStatementHasType_afterSubstitution contains
        conditionTyping conditionEq thenTyping elseTyping thenAgreement
        elseAgreement elseSubstitutionExtension
    · exact StatementResultMatchesFactsAfterSubstitution.ifWithElse
        thenAgreement elseAgreement elseSubstitutionExtension id _
  have resultSchemeIsolation : ActiveSchemeQuantifierIsolation
      result.state := by
    apply activeSchemeQuantifierIsolation_transport
      conditionInvariant.schemeIsolation
    simp [resultEq, State.restoreLexicalScope, State.recordNode,
      State.lexicalScope]
  exact RecursiveStatementInvariant.close_statement_branch initialInvariant
    success signatureFormation functionsCanonical
    (inferStatementFuel_preserves_localBindersBelowNextLocal
      initialInvariant.bindersBelow success)
    resultSubstitutionExtension resultSchemeIsolation branch

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceStatementAtomicSoundness
/-!
Closed typing branches for source statements with no recursively inferred
child.  Each theorem consumes an actual successful frontend trace and returns
the exact result shape expected by the recursive statement dispatcher.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem

/-- A bare return is sound after its actual unit/return-type unification. -/
theorem inferStatementFuel_returnUnit_atomicBranch
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult}
    {outer : TypeSystem.Substitution} {target : SourceSemantics.Context}
    {roots : List NodeId}
    (statementEq : statement.value = .returnStmt none)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (invariant : ActiveLocalContextInvariant initial outer target)
    (outerExtension : outer.SemanticallyExtends
      result.state.inference.substitution) :
    ∃ finalContext facts,
      ActiveLocalContextInvariant result.state outer finalContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution outer)
        { returnType := outer.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        target result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution outer result facts := by
  exact ⟨target, _, inferStatementFuel_success_returnUnit_sound statementEq
    allocationEq success invariant outerExtension roots⟩

/-- The successful loop-depth guard supplies precisely the declarative
`break` premise. -/
theorem inferStatementFuel_break_atomicBranch
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult}
    {outer : TypeSystem.Substitution} {target : SourceSemantics.Context}
    {roots : List NodeId}
    (statementEq : statement.value = .breakStmt)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (invariant : ActiveLocalContextInvariant initial outer target) :
    ∃ finalContext facts,
      ActiveLocalContextInvariant result.state outer finalContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution outer)
        { returnType := outer.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        target result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution outer result facts := by
  exact ⟨target, _, inferStatementFuel_success_break_sound statementEq
    allocationEq success invariant roots⟩

/-- Successful `continue` uses the same loop-depth guard while preserving its
distinct control outcome. -/
theorem inferStatementFuel_continue_atomicBranch
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult}
    {outer : TypeSystem.Substitution} {target : SourceSemantics.Context}
    {roots : List NodeId}
    (statementEq : statement.value = .continueStmt)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (invariant : ActiveLocalContextInvariant initial outer target) :
    ∃ finalContext facts,
      ActiveLocalContextInvariant result.state outer finalContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution outer)
        { returnType := outer.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        target result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution outer result facts := by
  exact ⟨target, _, inferStatementFuel_success_continue_sound statementEq
    allocationEq success invariant roots⟩

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceStatementForLoopAssembly
/-!
The `for` statement's non-recursive semantic assembly.  The child-typing
premise is indexed by the actual successful initializer, condition, body,
and post traversals of one successful parent; it does not assert anything
about unrelated child computations.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem

/-- Assemble a scoped `for` statement once its actual four child traversals
have been typed in the completed parent source.  The loop's lexical binders
are restored before returning to the enclosing semantic context. -/
theorem inferStatementFuel_success_forLoop_of_actual_typed_children
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {expectedReturn : Ty}
    {statement : Syntax.Statement} {headerSpan : Syntax.SourceSpan}
    {initializer post : List Syntax.ForItem} {condition : Syntax.Expr}
    {body : Syntax.Block}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticContext : SourceSemantics.Context}
    (statementEq : statement.value =
      .forLoop headerSpan initializer condition post body)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈
      inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (initialInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initial semanticContext)
    (resultSubstitutionExtension : finalized.substitution.SemanticallyExtends
      result.state.inference.substitution)
    (typedChildren :
      ∀ {initializerResult : Detail.InferredForItems}
        {inferredCondition : InferredExpression}
        {conditionState : State} {bodyResult : Detail.BlockResult}
        {postResult : Detail.InferredForItems},
        Detail.inferForItemsFuel fuel inferenceContext initializer allocated =
          .ok initializerResult →
        Detail.inferExprFuel fuel inferenceContext condition (some .bool)
          initializerResult.state = .ok (inferredCondition, conditionState) →
        Detail.inferStatementsFuel fuel
          { inferenceContext with
            loopDepth := inferenceContext.loopDepth + 1 }
          body.value expectedReturn conditionState = .ok bodyResult →
        Detail.inferForItemsFuel fuel
          { inferenceContext with
            loopDepth := inferenceContext.loopDepth + 1 } post
          (bodyResult.state.restoreLexicalScope
            initializerResult.state.lexicalScope) = .ok postResult →
        ∃ loopContext bodyFinal bodyFacts postContext,
          ForItemsHaveType
            ((result.state.toTypedSource roots).applySubstitution
              finalized.substitution)
            { returnType := finalized.substitution.apply expectedReturn
              loopDepth := inferenceContext.loopDepth }
            semanticContext
            (initializerResult.items.map
              (ForItemForm.applySubstitution finalized.substitution))
            loopContext ∧
          ExpressionHasType
            ((result.state.toTypedSource roots).applySubstitution
              finalized.substitution)
            loopContext inferredCondition.id .bool ∧
          StatementsHaveType
            ((result.state.toTypedSource roots).applySubstitution
              finalized.substitution)
            ({ returnType := finalized.substitution.apply expectedReturn
               loopDepth := inferenceContext.loopDepth } :
              ControlContext).enterLoop
            loopContext bodyResult.statements bodyFinal bodyFacts ∧
          ForItemsHaveType
            ((result.state.toTypedSource roots).applySubstitution
              finalized.substitution)
            ({ returnType := finalized.substitution.apply expectedReturn
               loopDepth := inferenceContext.loopDepth } :
              ControlContext).enterLoop
            loopContext
            (postResult.items.map
              (ForItemForm.applySubstitution finalized.substitution))
            postContext) :
    ∃ finalContext facts,
      RecursiveStatementInvariant wholeContext expectedReturn finalized
        result.state finalContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts := by
  obtain ⟨initializerResult, inferredCondition, conditionState, bodyResult,
    postResult, initializerSuccess, conditionSuccess, bodySuccess,
    postSuccess, resultEq, contains⟩ :=
    inferStatementFuel_success_forLoop_facts statementEq allocationEq success
      roots
  obtain ⟨loopContext, bodyFinal, bodyFacts, postContext,
    initializerTyping, conditionTyping, bodyTyping, postTyping⟩ :=
    typedChildren initializerSuccess conditionSuccess bodySuccess postSuccess
  have allocatedInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized allocated semanticContext :=
    initialInvariant.allocateStatementId allocationEq
  have resultSchemeIsolation : ActiveSchemeQuantifierIsolation result.state := by
    apply activeSchemeQuantifierIsolation_transport
      allocatedInvariant.schemeIsolation
    simp [resultEq, State.restoreLexicalScope, State.recordNode,
      State.lexicalScope]
  have branch : ∃ finalContext facts,
      ActiveLocalContextInvariant result.state finalized.substitution
        finalContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts := by
    subst result
    refine ⟨semanticContext, {
      type := .unit
      hasValue := false
      sawReturn := false
      control := .loop bodyFacts.control
    }, allocatedInvariant.active.restoreLexicalScope_recordNode _, ?_, ?_⟩
    · exact forLoopStatementHasType_afterSubstitution contains
        initializerTyping conditionTyping bodyTyping postTyping
    · exact StatementResultMatchesFactsAfterSubstitution.forLoop
        finalized.substitution bodyFacts id _
  exact RecursiveStatementInvariant.close_statement_branch initialInvariant
    success signatureFormation functionsCanonical
    (inferStatementFuel_preserves_localBindersBelowNextLocal
      initialInvariant.bindersBelow success)
    resultSubstitutionExtension resultSchemeIsolation branch

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceStatementForLoopResources
/-!
Actual-source provenance for the four source-ordered traversals in a `for`
statement.  In particular, later post-header inference may refine the
condition's substitution, so the condition must be transported through the
whole trace before its typing theorem can use finalization.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem
open SourceInferenceStatementsSoundness

/-- The actual `for` condition's final state is an append-only prefix of its
completed statement source, with all three evidence ledgers retained and the
whole-body substitution extending its inference substitution. -/
theorem inferStatementFuel_success_forLoop_condition_resources
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {headerSpan : Syntax.SourceSpan}
    {initializer post : List Syntax.ForItem} {condition : Syntax.Expr}
    {body : Syntax.Block} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticContext : SourceSemantics.Context}
    (statementEq : statement.value =
      .forLoop headerSpan initializer condition post body)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈
      inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (initialInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initial semanticContext)
    (resultSubstitutionExtension : finalized.substitution.SemanticallyExtends
      result.state.inference.substitution)
    (integerPatternsSubset : result.state.integerPatterns ⊆
      evidenceState.integerPatterns)
    (integerLiteralsSubset : result.state.integerLiterals ⊆
      evidenceState.integerLiterals)
    (requirementsSubset : result.state.requirements ⊆
      evidenceState.requirements) :
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
          loopDepth := inferenceContext.loopDepth + 1 } post
        (bodyResult.state.restoreLexicalScope
          initializerResult.state.lexicalScope) = .ok postResult ∧
      initializerResult.state.NodesBelowNextOccurrence ∧
      finalized.substitution.SemanticallyExtends
        conditionState.inference.substitution ∧
      TypingSourceExtends (conditionState.toTypedSource roots)
        (result.state.toTypedSource roots) ∧
      conditionState.integerPatterns ⊆ evidenceState.integerPatterns ∧
      conditionState.integerLiterals ⊆ evidenceState.integerLiterals ∧
      conditionState.requirements ⊆ evidenceState.requirements := by
  obtain ⟨initializerResult, inferredCondition, conditionState, bodyResult,
    postResult, initializerSuccess, conditionSuccess, bodySuccess,
    postSuccess, resultEq, _contains⟩ :=
    inferStatementFuel_success_forLoop_facts statementEq allocationEq success
      roots
  obtain ⟨provenanceInitializer, provenanceCondition,
    provenanceConditionState, provenanceBody, provenancePost,
    provenanceInitializerSuccess, provenanceConditionSuccess,
    provenanceBodySuccess, provenancePostSuccess,
    initializerProvenance, bodyProvenance,
    postProvenance⟩ :=
    inferStatementFuel_success_forLoop_child_provenance statementEq
      allocationEq success initialInvariant.nodesBelow roots
  have initializerEq : provenanceInitializer = initializerResult := by
    rw [initializerSuccess] at provenanceInitializerSuccess
    exact (Except.ok.inj provenanceInitializerSuccess).symm
  subst provenanceInitializer
  have conditionPairEq :
      (provenanceCondition, provenanceConditionState) =
        (inferredCondition, conditionState) := by
    rw [conditionSuccess] at provenanceConditionSuccess
    exact (Except.ok.inj provenanceConditionSuccess).symm
  obtain ⟨rfl, rfl⟩ := conditionPairEq
  have bodyEq : provenanceBody = bodyResult := by
    rw [bodySuccess] at provenanceBodySuccess
    exact (Except.ok.inj provenanceBodySuccess).symm
  subst provenanceBody
  have allocatedInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized allocated semanticContext :=
    initialInvariant.allocateStatementId allocationEq
  have initializerProperties := Detail.inferForItemsFuel_inferenceProperties
    allocatedInvariant.ready signatureFormation functionsCanonical
    initializerSuccess
  have conditionProperties := Detail.inferExprFuel_inferenceProperties
    initializerProperties.2 signatureFormation functionsCanonical
    (by
      intro expected member
      simp only [Option.mem_def] at member
      injection member with expectedEq
      subst expected
      simp [Ty.bool]) conditionSuccess
  have initializerReturnBelow : expectedReturn.VariablesBelow
      initializerResult.state.inference.next :=
    allocatedInvariant.returnBelow.weaken initializerProperties.1.next_le
  have conditionReturnBelow : expectedReturn.VariablesBelow
      conditionState.inference.next :=
    initializerReturnBelow.weaken conditionProperties.1.next_le
  have bodyProperties := Detail.inferStatementsFuel_inferenceProperties
    (context := { inferenceContext with
      loopDepth := inferenceContext.loopDepth + 1 })
    conditionProperties.2.1 signatureFormation functionsCanonical
    conditionReturnBelow bodySuccess
  have postInputProperties := State.restoreLexicalScope_inferenceProperties
    initializerProperties.2
    (conditionProperties.1.trans bodyProperties.1)
  have postProperties := Detail.inferForItemsFuel_inferenceProperties
    (context := { inferenceContext with
      loopDepth := inferenceContext.loopDepth + 1 })
    postInputProperties.2 signatureFormation functionsCanonical postSuccess
  have postSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        postResult.state.inference.substitution := by
    simpa [resultEq, State.restoreLexicalScope, State.recordNode] using
      resultSubstitutionExtension
  have bodySubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        bodyResult.state.inference.substitution := by
    have postInputSubstitutionExtension :=
      Substitution.SemanticallyExtends.trans postSubstitutionExtension
        postProperties.1.substitution_extends
    simpa [State.restoreLexicalScope] using postInputSubstitutionExtension
  have conditionSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        conditionState.inference.substitution :=
    Substitution.SemanticallyExtends.trans bodySubstitutionExtension
      bodyProperties.1.substitution_extends
  have conditionToBody : TypingSourceExtends
      (conditionState.toTypedSource roots)
      (bodyResult.state.toTypedSource roots) :=
    inferStatementsFuel_success_typingSourceExtends bodySuccess
      bodyProvenance.initialBelow roots
  have conditionToResult : TypingSourceExtends
      (conditionState.toTypedSource roots)
      (result.state.toTypedSource roots) :=
    conditionToBody.trans bodyProvenance.sourceExtension
  have bodyLiteralsSubset : bodyResult.state.integerLiterals ⊆
      result.state.integerLiterals := by
    rw [resultEq]
    intro literal member
    simpa [State.restoreLexicalScope, State.recordNode] using
      (Detail.inferForItemsFuel_integerLiterals_subset postSuccess
        (by simpa [State.restoreLexicalScope] using member))
  have conditionLiteralsSubset : conditionState.integerLiterals ⊆
      result.state.integerLiterals :=
    List.Subset.trans
      (Detail.inferStatementsFuel_integerLiterals_subset bodySuccess)
      bodyLiteralsSubset
  refine ⟨initializerResult, inferredCondition, conditionState, bodyResult,
    postResult, initializerSuccess, conditionSuccess, bodySuccess,
    postSuccess, ?_, conditionSubstitutionExtension, conditionToResult,
    ?_, ?_, ?_⟩
  · exact (Detail.inferForItemsFuel_occurrenceBoundExtends
      initializerSuccess).nodesBelowNextOccurrence
      initializerProvenance.initialBelow
  · exact List.Subset.trans
      (List.Subset.trans
        (Detail.inferStatementsFuel_integerPatterns_subset bodySuccess)
        bodyProvenance.integerPatternsSubset)
      integerPatternsSubset
  · exact List.Subset.trans conditionLiteralsSubset integerLiteralsSubset
  · exact List.Subset.trans
      (List.Subset.trans
        (Detail.inferStatementsFuel_requirements_subset bodySuccess)
        bodyProvenance.requirementsSubset)
      requirementsSubset

end Solcore.SourceSemantics.SourceInferenceSoundness
end
