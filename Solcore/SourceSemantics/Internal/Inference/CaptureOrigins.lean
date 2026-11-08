import Solcore.SourceSemantics.Internal.Inference.Soundness

/-!
# Capture origins

Operational provenance for polymorphic lexical binders, and its one-statement preservation.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceCaptureOrigins
/-!
Operational provenance for polymorphic lexical binders.  The no-capture
certificate produced by finalization is indexed by the raw, final source;
these lemmas keep each active binder connected to that source while inference
enters and leaves lexical scopes.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem

/-- Monomorphic function parameters have no capture obligation, regardless of
which later state is used as the final evidence carrier. -/
theorem activeBinderCaptureOrigins_initial_mono
    (owner : Resolved.DeclarationId) (locals : Environment)
    (inputComptime : List Bool) (wholeSource : TypedSource)
    (monomorphic : ∀ entry, entry ∈ locals → entry.2.quantified = []) :
    ActiveBinderCaptureOrigins
      (State.initial owner locals inputComptime) wholeSource := by
  apply ActiveBinderCaptureOrigins.of_monomorphic
  intro binder binderMember
  rw [← State.initial_inputs_eq_localBinders,
    State.initial_inputs_definition] at binderMember
  obtain ⟨index, indexLt, binderEq⟩ :=
    List.exists_of_mem_mapIdx binderMember
  subst binder
  exact monomorphic locals[index] (List.getElem_mem indexLt)

/-- An initialized let's recorded statement provides the exact raw-source
origin needed when its generalized binder becomes active.  The enclosing
source may be a later state, including the state finalized for the body. -/
theorem ActiveBinderCaptureOrigins.allocateBinder_recordInitialized
    {before after : State} {wholeSource : TypedSource}
    {name : String} {scheme : Scheme} {span : Option Syntax.SourceSpan}
    {comptime : Bool} {schemeRequirements : List LocalSchemeRequirement}
    {binder : TypedBinder} {recordedSource : TypedSource}
    {id : StatementId} {node : StatementNode}
    (origins : ActiveBinderCaptureOrigins before wholeSource)
    (allocated : before.allocateBinder name scheme span comptime
      schemeRequirements = (binder, after))
    (contains : ContainsStatement recordedSource id node)
    (initialized : binder ∈ node.form.initializedLetBinders)
    (recordedToWhole : TypingSourceExtends recordedSource wholeSource) :
    ActiveBinderCaptureOrigins after wholeSource := by
  have retained : binder ∈ wholeSource.initializedLetBinders :=
    recordedToWhole.initializedLetBinders_subset
      (contains.initializedLetBinder_mem initialized)
  exact origins.allocateBinder allocated (.inr retained)

/-- A contained initialized declaration remains a capture origin after the
recording step itself; the record operation does not change lexical binders. -/
theorem ActiveBinderCaptureOrigins.recordInitializedLet
    {before after : State} {wholeSource : TypedSource}
    {name : String} {scheme : Scheme} {span : Option Syntax.SourceSpan}
    {comptime : Bool} {schemeRequirements : List LocalSchemeRequirement}
    {binder : TypedBinder} {id : StatementId} {statementSpan : Syntax.SourceSpan}
    {initializer : ExpressionId} {roots : List NodeId}
    (origins : ActiveBinderCaptureOrigins before wholeSource)
    (allocated : before.allocateBinder name scheme span comptime
      schemeRequirements = (binder, after))
    (recordedToWhole : TypingSourceExtends
      ((after.recordNode (.statement {
        id, span := statementSpan, type := .unit,
        form := .letDecl binder (some initializer)
      })).toTypedSource roots) wholeSource) :
    ActiveBinderCaptureOrigins
      (after.recordNode (.statement {
        id, span := statementSpan, type := .unit,
        form := .letDecl binder (some initializer)
      })) wholeSource := by
  have contains : ContainsStatement
      ((after.recordNode (.statement {
        id, span := statementSpan, type := .unit,
        form := .letDecl binder (some initializer)
      })).toTypedSource roots) id {
        id, span := statementSpan, type := .unit,
        form := .letDecl binder (some initializer)
      } := recordNode_containsStatement after _ roots
  have entered : ActiveBinderCaptureOrigins after wholeSource :=
    origins.allocateBinder_recordInitialized allocated contains
      (by simp [StatementForm.initializedLetBinders]) recordedToWhole
  exact entered.recordNode _

/-- A successful unannotated initialized declaration keeps the binder's
capture origin in the raw final evidence source.  Its initializer expression
cannot change the previously active binder stack. -/
theorem inferStatementFuel_letUnannotatedInitialized_captureOrigins
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {name : Syntax.Identifier}
    {initializer : Syntax.Expr} {expectedReturn : Ty}
    {initial allocated evidenceState : State}
    {id : StatementId} {result : Detail.StatementResult}
    {roots : List NodeId}
    (statementEq : statement.value = .letDecl name none (some initializer))
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (initialOrigins : ActiveBinderCaptureOrigins initial
      (evidenceState.toTypedSource roots))
    (resultToEvidence : TypingSourceExtends
      (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots)) :
    ActiveBinderCaptureOrigins result.state
      (evidenceState.toTypedSource roots) := by
  obtain ⟨inferred, initializerState, locals, valueType, generalized,
      ⟨binder, bindingState⟩, initializerSuccess, _, _, _, bindingEq,
      resultEq, _⟩ :=
    inferStatementFuel_success_letUnannotatedInitialized_facts statementEq
      allocationEq success roots
  have allocatedOrigins : ActiveBinderCaptureOrigins allocated
      (evidenceState.toTypedSource roots) :=
    initialOrigins.allocateStatementId allocationEq
  have initializerOrigins : ActiveBinderCaptureOrigins initializerState
      (evidenceState.toTypedSource roots) :=
    allocatedOrigins.inferExprFuel initializerSuccess
  have bindingOrigins : ActiveBinderCaptureOrigins
      (bindingState.recordNode (.statement {
        id, span := statement.span, type := .unit,
        form := .letDecl binder (some inferred.id)
      })) (evidenceState.toTypedSource roots) :=
    (initializerOrigins.withLocals locals).recordInitializedLet bindingEq
      (by simpa only [resultEq] using resultToEvidence)
  simpa only [resultEq] using bindingOrigins

/-- The annotated initialized declaration uses the same recorded-binder
origin, after its source annotation has selected the initializer expectation. -/
theorem inferStatementFuel_letAnnotatedInitialized_captureOrigins
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {name : Syntax.Identifier}
    {sourceType : Syntax.TypeExpr} {initializer : Syntax.Expr}
    {expectedReturn : Ty} {initial allocated evidenceState : State}
    {id : StatementId} {result : Detail.StatementResult}
    {roots : List NodeId}
    (statementEq : statement.value =
      .letDecl name (some sourceType) (some initializer))
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (initialOrigins : ActiveBinderCaptureOrigins initial
      (evidenceState.toTypedSource roots))
    (resultToEvidence : TypingSourceExtends
      (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots)) :
    ActiveBinderCaptureOrigins result.state
      (evidenceState.toTypedSource roots) := by
  obtain ⟨resolvedType, inferred, initializerState, locals, valueType,
      generalized, ⟨binder, bindingState⟩, _, initializerSuccess, _, _, _,
      bindingEq, resultEq, _⟩ :=
    inferStatementFuel_success_letAnnotatedInitialized_facts statementEq
      allocationEq success roots
  have allocatedOrigins : ActiveBinderCaptureOrigins allocated
      (evidenceState.toTypedSource roots) :=
    initialOrigins.allocateStatementId allocationEq
  have initializerOrigins : ActiveBinderCaptureOrigins initializerState
      (evidenceState.toTypedSource roots) :=
    allocatedOrigins.inferExprFuel initializerSuccess
  have bindingOrigins : ActiveBinderCaptureOrigins
      (bindingState.recordNode (.statement {
        id, span := statement.span, type := .unit,
        form := .letDecl binder (some inferred.id)
      })) (evidenceState.toTypedSource roots) :=
    (initializerOrigins.withLocals locals).recordInitializedLet bindingEq
      (by simpa only [resultEq] using resultToEvidence)
  simpa only [resultEq] using bindingOrigins

/-- A source annotation resolves to a rigid type.  Consequently an
uninitialized annotated declaration enters a monomorphic binder, which needs
no initialized-let origin in the final evidence source. -/
theorem inferStatementFuel_letAnnotatedUninitialized_captureOrigins
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {name : Syntax.Identifier}
    {sourceType : Syntax.TypeExpr} {expectedReturn : Ty}
    {initial allocated evidenceState : State}
    {id : StatementId} {result : Detail.StatementResult}
    {roots : List NodeId}
    (statementEq : statement.value = .letDecl name (some sourceType) none)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (initialOrigins : ActiveBinderCaptureOrigins initial
      (evidenceState.toTypedSource roots)) :
    ActiveBinderCaptureOrigins result.state
      (evidenceState.toTypedSource roots) := by
  obtain ⟨resolvedType, locals, valueType, generalized,
      ⟨binder, bindingState⟩, resolution, _, valueTypeEq,
      generalizedEq, bindingEq, resultEq, _⟩ :=
    inferStatementFuel_success_letAnnotatedUninitialized_facts statementEq
      allocationEq success roots
  have resolvedClosed : resolvedType.freeVariables = [] := by
    cases variablesEq : resolvedType.freeVariables with
    | nil => rfl
    | cons metavariable rest =>
        have impossible : metavariable.index < 0 :=
          (Detail.resolveSourceType_success_variablesBelow resolution 0)
            metavariable (by simp [variablesEq])
        exact False.elim ((Nat.not_lt_zero _) impossible)
  have resolvedByState : allocated.resolve resolvedType = resolvedType := by
    simpa [State.resolve, InferState.resolve] using
      (Detail.resolveSourceType_success_apply_eq_self
        allocated.inference.substitution resolution)
  have valueClosed : valueType.freeVariables = [] := by
    rw [valueTypeEq, resolvedByState]
    exact resolvedClosed
  have generalizedMono : generalized.scheme.quantified = [] := by
    rw [generalizedEq, Detail.generalizeValue_scheme_quantified, valueClosed]
    rfl
  have binderEq :
      ((allocated.withLocals locals).allocateBinder name.value
        generalized.scheme (some name.span) false
        generalized.requirements).1 = binder :=
    congrArg Prod.fst bindingEq
  have binderMono : binder.scheme.quantified = [] := by
    rw [← binderEq]
    exact generalizedMono
  have allocatedOrigins : ActiveBinderCaptureOrigins allocated
      (evidenceState.toTypedSource roots) :=
    initialOrigins.allocateStatementId allocationEq
  have entered : ActiveBinderCaptureOrigins bindingState
      (evidenceState.toTypedSource roots) :=
    (allocatedOrigins.withLocals locals).allocateBinder bindingEq
      (.inl binderMono)
  have recorded := entered.recordNode (.statement {
    id, span := statement.span, type := .unit,
    form := .letDecl binder none
  })
  simpa only [resultEq] using recorded

/-- An expression statement changes no visible binder stack. -/
theorem inferStatementFuel_expression_captureOrigins
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expression : Syntax.Expr}
    {trailingSemicolon : Bool} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult} {wholeSource : TypedSource}
    (statementEq : statement.value =
      .expression expression trailingSemicolon)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (origins : ActiveBinderCaptureOrigins initial wholeSource) :
    ActiveBinderCaptureOrigins result.state wholeSource := by
  obtain ⟨inferred, expressionState, expressionSuccess, resultEq, _⟩ :=
    inferStatementFuel_success_expression_facts statementEq allocationEq
      success
  have recorded := ((origins.allocateStatementId allocationEq).inferExprFuel
    expressionSuccess).recordNode (.statement {
      id, span := statement.span,
      type := if trailingSemicolon then .unit else inferred.type,
      form := .expression inferred.id trailingSemicolon
    })
  simpa only [resultEq] using recorded

/-- A value assignment preserves the lexical stack through its exact place
and right-hand-side traversal. -/
theorem inferStatementFuel_assignValue_captureOrigins
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {targetExpression value : Syntax.Expr}
    {operator : Syntax.Located Syntax.ValueAssignOp}
    {expectedReturn : Ty} {initial allocated : State}
    {id : StatementId} {result : Detail.StatementResult}
    {wholeSource : TypedSource}
    (statementEq : statement.value =
      .assignValue targetExpression operator value)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (origins : ActiveBinderCaptureOrigins initial wholeSource) :
    ActiveBinderCaptureOrigins result.state wholeSource := by
  obtain ⟨assignment, inferred, assignmentState, assignmentSuccess,
      resultEq, _⟩ :=
    inferStatementFuel_success_assignValue_facts statementEq allocationEq
      success
  have recorded :=
    ((origins.allocateStatementId allocationEq).inferAssignedValueFuel
      assignmentSuccess).recordNode (.statement {
        id, span := statement.span, type := .unit,
        form := .assignValue assignment operator.value inferred.id
      })
  simpa only [resultEq] using recorded

/-- Bit-not assignment preserves the lexical stack through its exact place
traversal and subsequent `Word` unification. -/
theorem inferStatementFuel_assignBitNot_captureOrigins
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {targetExpression : Syntax.Expr}
    {operatorSpan : Syntax.SourceSpan} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult} {wholeSource : TypedSource}
    (statementEq : statement.value =
      .assignBitNot targetExpression operatorSpan)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (origins : ActiveBinderCaptureOrigins initial wholeSource) :
    ActiveBinderCaptureOrigins result.state wholeSource := by
  obtain ⟨place, placeState, unified, placeSuccess, unifySuccess, _,
      resultEq, _⟩ :=
    inferStatementFuel_success_assignBitNot_facts statementEq allocationEq
      success
  have recorded :=
    (((origins.allocateStatementId allocationEq).inferPlaceFuel
      placeSuccess).unify unifySuccess).recordNode (.statement {
        id, span := statement.span, type := .unit,
        form := .assignBitNot {
          target := { place with type := unified.resolve place.type }
        }
      })
  simpa only [resultEq] using recorded

/-- A bare return unifies its type and records a node without changing the
lexical binder stack. -/
theorem inferStatementFuel_returnUnit_captureOrigins
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult} {wholeSource : TypedSource}
    (statementEq : statement.value = .returnStmt none)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (origins : ActiveBinderCaptureOrigins initial wholeSource) :
    ActiveBinderCaptureOrigins result.state wholeSource := by
  obtain ⟨unified, unifySuccess, _, resultEq, _⟩ :=
    inferStatementFuel_success_returnUnit_facts statementEq allocationEq
      success
  have recorded :=
    ((origins.allocateStatementId allocationEq).unify
      unifySuccess).recordNode (.statement {
        id, span := statement.span,
        type := unified.resolve expectedReturn,
        form := .returnStmt none
      })
  simpa only [resultEq] using recorded

/-- A value return preserves capture origins across its actual expression
traversal. -/
theorem inferStatementFuel_returnValue_captureOrigins
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {value : Syntax.Expr}
    {expectedReturn : Ty} {initial allocated : State}
    {id : StatementId} {result : Detail.StatementResult}
    {wholeSource : TypedSource}
    (statementEq : statement.value = .returnStmt (some value))
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (origins : ActiveBinderCaptureOrigins initial wholeSource) :
    ActiveBinderCaptureOrigins result.state wholeSource := by
  obtain ⟨inferred, valueState, valueSuccess, resultEq, _⟩ :=
    inferStatementFuel_success_returnValue_facts statementEq allocationEq
      success
  have recorded :=
    ((origins.allocateStatementId allocationEq).inferExprFuel
      valueSuccess).recordNode (.statement {
        id, span := statement.span,
        type := valueState.resolve expectedReturn,
        form := .returnStmt (some inferred.id)
      })
  simpa only [resultEq] using recorded

/-- Loop-control statements allocate only their own occurrence. -/
theorem inferStatementFuel_break_captureOrigins
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult} {wholeSource : TypedSource}
    (statementEq : statement.value = .breakStmt)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (origins : ActiveBinderCaptureOrigins initial wholeSource) :
    ActiveBinderCaptureOrigins result.state wholeSource := by
  obtain ⟨_, resultEq, _⟩ :=
    inferStatementFuel_success_break_facts statementEq allocationEq success
  have recorded := (origins.allocateStatementId allocationEq).recordNode
    (.statement {
      id, span := statement.span, type := .unit,
      form := .breakStmt
    })
  simpa only [resultEq] using recorded

/-- `continue` has the same capture-origin behavior as `break`. -/
theorem inferStatementFuel_continue_captureOrigins
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult} {wholeSource : TypedSource}
    (statementEq : statement.value = .continueStmt)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (origins : ActiveBinderCaptureOrigins initial wholeSource) :
    ActiveBinderCaptureOrigins result.state wholeSource := by
  obtain ⟨_, resultEq, _⟩ :=
    inferStatementFuel_success_continue_facts statementEq allocationEq success
  have recorded := (origins.allocateStatementId allocationEq).recordNode
    (.statement {
      id, span := statement.span, type := .unit,
      form := .continueStmt
    })
  simpa only [resultEq] using recorded

/-- A block restores the lexical scope with which it entered its statement
sequence, so bindings declared inside the block cannot escape. -/
theorem inferStatementFuel_block_captureOrigins
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {body : List Syntax.Statement}
    {expectedReturn : Ty} {initial allocated : State}
    {id : StatementId} {result : Detail.StatementResult}
    {wholeSource : TypedSource}
    (statementEq : statement.value = .block body)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (origins : ActiveBinderCaptureOrigins initial wholeSource) :
    ActiveBinderCaptureOrigins result.state wholeSource := by
  obtain ⟨bodyResult, _, resultEq, _⟩ :=
    inferStatementFuel_success_block_facts statementEq allocationEq success
  have recorded : ActiveBinderCaptureOrigins
      ((bodyResult.state.restoreLexicalScope allocated.lexicalScope).recordNode
        (.statement {
          id, span := statement.span, type := bodyResult.type,
          form := .block bodyResult.statements
        })) wholeSource :=
    (origins.allocateStatementId allocationEq).restoreLexicalScope_recordNode
      _
  simpa only [resultEq] using recorded

/-- The no-else branch restores the condition state's binder stack. -/
theorem inferStatementFuel_ifWithoutElse_captureOrigins
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {condition : Syntax.Expr}
    {thenBody : Syntax.Block} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult} {wholeSource : TypedSource}
    (statementEq : statement.value = .ifThen condition thenBody none)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (origins : ActiveBinderCaptureOrigins initial wholeSource) :
    ActiveBinderCaptureOrigins result.state wholeSource := by
  obtain ⟨inferredCondition, conditionState, thenResult,
      conditionSuccess, _, resultEq, _⟩ :=
    inferStatementFuel_success_ifWithoutElse_facts statementEq allocationEq
      success
  have conditionOrigins : ActiveBinderCaptureOrigins conditionState
      wholeSource :=
    (origins.allocateStatementId allocationEq).inferExprFuel conditionSuccess
  have recorded : ActiveBinderCaptureOrigins
      ((thenResult.state.restoreLexicalScope conditionState.lexicalScope
        ).recordNode (.statement {
          id, span := statement.span, type := .unit,
          form := .ifThen inferredCondition.id thenResult.statements none
        })) wholeSource :=
    conditionOrigins.restoreLexicalScope_recordNode _
  simpa only [resultEq] using recorded

/-- Both arms of an `if` are lexically scoped; after the else arm, the
condition state's original binder stack is restored. -/
theorem inferStatementFuel_ifWithElse_captureOrigins
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {condition : Syntax.Expr}
    {thenBody elseBody : Syntax.Block} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult} {wholeSource : TypedSource}
    (statementEq : statement.value =
      .ifThen condition thenBody (some elseBody))
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (origins : ActiveBinderCaptureOrigins initial wholeSource) :
    ActiveBinderCaptureOrigins result.state wholeSource := by
  obtain ⟨inferredCondition, conditionState, thenResult, elseResult,
      conditionSuccess, _, _, resultEq, _⟩ :=
    inferStatementFuel_success_ifWithElse_facts statementEq allocationEq
      success
  have conditionOrigins : ActiveBinderCaptureOrigins conditionState
      wholeSource :=
    (origins.allocateStatementId allocationEq).inferExprFuel conditionSuccess
  have recorded : ActiveBinderCaptureOrigins
      ((elseResult.state.restoreLexicalScope conditionState.lexicalScope
        ).recordNode (.statement {
          id, span := statement.span,
          type := if thenResult.sawReturn && elseResult.sawReturn then
            elseResult.state.resolve expectedReturn else .unit,
          form := .ifThen inferredCondition.id thenResult.statements
            (some elseResult.statements)
        })) wholeSource :=
    conditionOrigins.restoreLexicalScope_recordNode _
  simpa only [resultEq] using recorded

/-- A `while` body cannot leak binders beyond its enclosing condition. -/
theorem inferStatementFuel_whileLoop_captureOrigins
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {condition : Syntax.Expr}
    {body : Syntax.Block} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult} {wholeSource : TypedSource}
    (statementEq : statement.value = .whileLoop condition body)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (origins : ActiveBinderCaptureOrigins initial wholeSource) :
    ActiveBinderCaptureOrigins result.state wholeSource := by
  obtain ⟨inferredCondition, conditionState, bodyResult,
      conditionSuccess, _, resultEq, _⟩ :=
    inferStatementFuel_success_whileLoop_facts statementEq allocationEq
      success
  have conditionOrigins : ActiveBinderCaptureOrigins conditionState
      wholeSource :=
    (origins.allocateStatementId allocationEq).inferExprFuel conditionSuccess
  have recorded : ActiveBinderCaptureOrigins
      ((bodyResult.state.restoreLexicalScope conditionState.lexicalScope
        ).recordNode (.statement {
          id, span := statement.span, type := .unit,
          form := .whileLoop inferredCondition.id bodyResult.statements
        })) wholeSource :=
    conditionOrigins.restoreLexicalScope_recordNode _
  simpa only [resultEq] using recorded

/-- `for`-header and body locals are discarded at the loop boundary.  Their
internal use still needs the item-level origin lemmas, but the outward state
recovers precisely the original allocated statement scope. -/
theorem inferStatementFuel_forLoop_captureOrigins
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {headerSpan : Syntax.SourceSpan}
    {initializer post : List Syntax.ForItem} {condition : Syntax.Expr}
    {body : Syntax.Block} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult} {wholeSource : TypedSource}
    (statementEq : statement.value =
      .forLoop headerSpan initializer condition post body)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (origins : ActiveBinderCaptureOrigins initial wholeSource) :
    ActiveBinderCaptureOrigins result.state wholeSource := by
  obtain ⟨initializerResult, inferredCondition, conditionState, bodyResult,
      postResult, _, _, _, _, resultEq, _⟩ :=
    inferStatementFuel_success_forLoop_facts statementEq allocationEq success
  have recorded : ActiveBinderCaptureOrigins
      ((postResult.state.restoreLexicalScope allocated.lexicalScope
        ).recordNode (.statement {
          id, span := statement.span, type := .unit,
          form := .forLoop initializerResult.items inferredCondition.id
            postResult.items bodyResult.statements
        })) wholeSource :=
    (origins.allocateStatementId allocationEq).restoreLexicalScope_recordNode
      _
  simpa only [resultEq] using recorded

/-- Match scrutinees preserve the active binder stack, whether inferred as a
single expression or packaged into the synthetic tuple occurrence. -/
theorem ActiveBinderCaptureOrigins.inferMatchScrutineesFuel
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {span : Syntax.SourceSpan} {sources : List Syntax.Expr}
    {state final : State} {inferred : InferredExpression}
    {wholeSource : TypedSource}
    (origins : ActiveBinderCaptureOrigins state wholeSource)
    (success : SourceInferenceSoundness.inferMatchScrutineesFuel fuel
      inferenceContext span sources state = .ok (inferred, final)) :
    ActiveBinderCaptureOrigins final wholeSource := by
  cases sources with
  | nil =>
      unfold SourceInferenceSoundness.inferMatchScrutineesFuel at success
      cases elementsSuccess : Detail.inferExprsFuel fuel inferenceContext []
          state with
      | error error => simp [elementsSuccess, bind, Except.bind] at success
      | ok elementsPair =>
          rcases elementsPair with ⟨elements, elementsState⟩
          simp only [elementsSuccess, bind, Except.bind, pure, Pure.pure,
            Except.pure] at success
          injection success with resultEq
          cases resultEq
          exact (origins.inferExprsFuel elementsSuccess).congr_localBinders rfl
  | cons first rest =>
      cases rest with
      | nil =>
          apply origins.inferExprFuel
          simpa [SourceInferenceSoundness.inferMatchScrutineesFuel] using
            success
      | cons second tail =>
          unfold SourceInferenceSoundness.inferMatchScrutineesFuel at success
          cases elementsSuccess : Detail.inferExprsFuel fuel inferenceContext
              (first :: second :: tail) state with
          | error error => simp [elementsSuccess, bind, Except.bind] at success
          | ok elementsPair =>
              rcases elementsPair with ⟨elements, elementsState⟩
              simp only [elementsSuccess, bind, Except.bind, pure, Pure.pure,
                Except.pure] at success
              injection success with resultEq
              cases resultEq
              exact (origins.inferExprsFuel elementsSuccess).congr_localBinders
                rfl

/-- Explicit match arms restore the outer lexical scope, so their pattern
binders do not escape when there is no default arm. -/
theorem inferStatementFuel_matchWithoutDefault_captureOrigins
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
    {arms : Syntax.MatchArms} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult} {wholeSource : TypedSource}
    (statementEq : statement.value = .matchWith scrutinees arms)
    (defaultEq : arms.value.defaultBody = none)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (origins : ActiveBinderCaptureOrigins initial wholeSource) :
    ActiveBinderCaptureOrigins result.state wholeSource := by
  obtain ⟨scrutinee, scrutineeState, hiddenScrutinee, hiddenState, checked,
      scrutineeSuccess, hiddenAllocation, casesSuccess, _, resultEq, _⟩ :=
    inferStatementFuel_success_matchWithoutDefault_facts statementEq
      defaultEq allocationEq success
  have hiddenOrigins : ActiveBinderCaptureOrigins hiddenState wholeSource :=
    ((origins.allocateStatementId allocationEq).inferMatchScrutineesFuel
      scrutineeSuccess).allocateHiddenLocal hiddenAllocation
  have scopeEq : checked.state.lexicalScope = hiddenState.lexicalScope :=
    Detail.inferMatchCasesFuel_success_lexicalScope_eq rfl casesSuccess
  have checkedOrigins : ActiveBinderCaptureOrigins checked.state wholeSource :=
    hiddenOrigins.congr_localBinders (by
      simpa only [State.lexicalScope] using
        congrArg LexicalScope.binders scopeEq)
  have recorded := checkedOrigins.recordNode (.statement {
    id, span := statement.span,
    type := if checked.allReturn then checked.state.resolve expectedReturn
      else .unit,
    form := .matchWith {
      scrutinee := scrutinee.id
      hiddenScrutinee
      cases := checked.cases
      defaultBody := none
      requirements := checked.cases.flatMap fun arm =>
        arm.pattern.requirements
    }
  })
  simpa only [resultEq] using recorded

/-- A default arm is followed by an explicit lexical restoration; the
outward active binders are exactly those before case traversal. -/
theorem inferStatementFuel_matchWithDefault_captureOrigins
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
    {arms : Syntax.MatchArms} {defaultBody : Syntax.Block}
    {expectedReturn : Ty} {initial allocated : State}
    {id : StatementId} {result : Detail.StatementResult}
    {wholeSource : TypedSource}
    (statementEq : statement.value = .matchWith scrutinees arms)
    (defaultEq : arms.value.defaultBody = some defaultBody)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (origins : ActiveBinderCaptureOrigins initial wholeSource) :
    ActiveBinderCaptureOrigins result.state wholeSource := by
  obtain ⟨scrutinee, scrutineeState, hiddenScrutinee, hiddenState, checked,
      defaultResult, scrutineeSuccess, hiddenAllocation, _, _, _, resultEq,
      _⟩ :=
    inferStatementFuel_success_matchWithDefault_facts statementEq defaultEq
      allocationEq success
  have hiddenOrigins : ActiveBinderCaptureOrigins hiddenState wholeSource :=
    ((origins.allocateStatementId allocationEq).inferMatchScrutineesFuel
      scrutineeSuccess).allocateHiddenLocal hiddenAllocation
  have recorded : ActiveBinderCaptureOrigins
      ((defaultResult.state.restoreLexicalScope hiddenState.lexicalScope
        ).recordNode (.statement {
          id, span := statement.span,
          type := if checked.allReturn && defaultResult.sawReturn then
            (defaultResult.state.restoreLexicalScope
              hiddenState.lexicalScope).resolve expectedReturn else .unit,
          form := .matchWith {
            scrutinee := scrutinee.id
            hiddenScrutinee
            cases := checked.cases
            defaultBody := some defaultResult.statements
            requirements := checked.cases.flatMap fun arm =>
              arm.pattern.requirements
          }
        })) wholeSource :=
    hiddenOrigins.restoreLexicalScope_recordNode _
  simpa only [resultEq] using recorded

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceCaptureOriginDispatcher
/-!
Complete one-statement preservation of raw initialized-binder capture origins.
Unlike semantic typing, this invariant follows from the actual executable
statement result alone: initialized lets record their binder, ordinary
statements preserve the lexical stack, and scoped constructs restore it.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem

/-- Every successful source statement preserves capture provenance relative
to the one raw source which will be passed to finalization. -/
theorem inferStatementFuel_captureOrigins
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expectedReturn : Ty}
    {initial evidenceState : State} {result : Detail.StatementResult}
    {roots : List NodeId}
    (success : Detail.inferStatementFuel fuel inferenceContext statement
      expectedReturn initial = .ok result)
    (origins : ActiveBinderCaptureOrigins initial
      (evidenceState.toTypedSource roots))
    (resultToEvidence : TypingSourceExtends
      (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots)) :
    ActiveBinderCaptureOrigins result.state
      (evidenceState.toTypedSource roots) := by
  cases fuel with
  | zero => simp [Detail.inferStatementFuel] at success
  | succ fuel =>
      cases allocationEq : initial.allocateStatementId with
      | mk id allocated =>
          cases statementEq : statement.value with
          | letDecl name sourceType initializer =>
              cases sourceType with
              | none =>
                  cases initializer with
                  | none =>
                      simp [Detail.inferStatementFuel, allocationEq,
                        statementEq] at success
                      change (Except.error (.missingInitializer name.value) :
                        Except Frontend.SourceInference.Error
                          Detail.StatementResult) = .ok result at success
                      cases success
                  | some initializer =>
                      exact inferStatementFuel_letUnannotatedInitialized_captureOrigins
                        statementEq allocationEq success origins
                        resultToEvidence
              | some sourceType =>
                  cases initializer with
                  | none =>
                      exact inferStatementFuel_letAnnotatedUninitialized_captureOrigins
                        statementEq allocationEq success origins
                  | some initializer =>
                      exact inferStatementFuel_letAnnotatedInitialized_captureOrigins
                        statementEq allocationEq success origins
                        resultToEvidence
          | returnStmt value =>
              cases value with
              | none =>
                  exact inferStatementFuel_returnUnit_captureOrigins
                    statementEq allocationEq success origins
              | some value =>
                  exact inferStatementFuel_returnValue_captureOrigins
                    statementEq allocationEq success origins
          | expression expression trailingSemicolon =>
              exact inferStatementFuel_expression_captureOrigins
                statementEq allocationEq success origins
          | assignValue target operator value =>
              exact inferStatementFuel_assignValue_captureOrigins
                statementEq allocationEq success origins
          | assignBitNot target operatorSpan =>
              exact inferStatementFuel_assignBitNot_captureOrigins
                statementEq allocationEq success origins
          | matchWith scrutinees arms =>
              cases defaultEq : arms.value.defaultBody with
              | none =>
                  exact inferStatementFuel_matchWithoutDefault_captureOrigins
                    statementEq defaultEq allocationEq success origins
              | some defaultBody =>
                  exact inferStatementFuel_matchWithDefault_captureOrigins
                    statementEq defaultEq allocationEq success origins
          | forLoop headerSpan initializer condition post body =>
              exact inferStatementFuel_forLoop_captureOrigins statementEq
                allocationEq success origins
          | whileLoop condition body =>
              exact inferStatementFuel_whileLoop_captureOrigins statementEq
                allocationEq success origins
          | ifThen condition thenBody elseBody =>
              cases elseBody with
              | none =>
                  exact inferStatementFuel_ifWithoutElse_captureOrigins
                    statementEq allocationEq success origins
              | some elseBody =>
                  exact inferStatementFuel_ifWithElse_captureOrigins
                    statementEq allocationEq success origins
          | block body =>
              exact inferStatementFuel_block_captureOrigins statementEq
                allocationEq success origins
          | assembly body =>
              simp [Detail.inferStatementFuel, statementEq]
                at success
          | breakStmt =>
              exact inferStatementFuel_break_captureOrigins statementEq
                allocationEq success origins
          | continueStmt =>
              exact inferStatementFuel_continue_captureOrigins statementEq
                allocationEq success origins
          | error =>
              simp [Detail.inferStatementFuel, statementEq]
                at success

/-- The one-statement theorem composes over the executable statement-list
traversal.  Each prefix result is retained in the final raw evidence source,
so an initialized binder remains certified at every later lookup. -/
theorem inferStatementsFuel_captureOrigins
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statements : List Syntax.Statement} {expectedReturn : Ty}
    {initial evidenceState : State} {result : Detail.BlockResult}
    {roots : List NodeId}
    (success : Detail.inferStatementsFuel fuel inferenceContext statements
      expectedReturn initial = .ok result)
    (below : initial.NodesBelowNextOccurrence)
    (origins : ActiveBinderCaptureOrigins initial
      (evidenceState.toTypedSource roots))
    (resultToEvidence : TypingSourceExtends
      (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots)) :
    ActiveBinderCaptureOrigins result.state
      (evidenceState.toTypedSource roots) := by
  induction fuel generalizing statements initial result with
  | zero => simp [Detail.inferStatementsFuel] at success
  | succ fuel induction =>
      cases statements with
      | nil =>
          simp [Detail.inferStatementsFuel] at success
          subst result
          exact origins
      | cons statement rest =>
          cases rest with
          | nil =>
              obtain ⟨head, headSuccess, resultEq⟩ :=
                inferStatementsFuel_success_singleton_facts success
              have headToEvidence : TypingSourceExtends
                  (head.state.toTypedSource roots)
                  (evidenceState.toTypedSource roots) := by
                simpa only [resultEq] using resultToEvidence
              have headOrigins := inferStatementFuel_captureOrigins
                headSuccess origins headToEvidence
              simpa only [resultEq] using headOrigins
          | cons next tail =>
              obtain ⟨head, restResult, headSuccess, tailSuccess,
                  resultEq⟩ :=
                inferStatementsFuel_success_cons_facts success
              have headBelow : head.state.NodesBelowNextOccurrence :=
                (Detail.inferStatementFuel_occurrenceBoundExtends
                  headSuccess).nodesBelowNextOccurrence below
              have tailToEvidence : TypingSourceExtends
                  (restResult.state.toTypedSource roots)
                  (evidenceState.toTypedSource roots) := by
                simpa only [resultEq] using resultToEvidence
              have headToEvidence : TypingSourceExtends
                  (head.state.toTypedSource roots)
                  (evidenceState.toTypedSource roots) :=
                (inferStatementsFuel_success_typingSourceExtends tailSuccess
                  headBelow roots).trans tailToEvidence
              have headOrigins := inferStatementFuel_captureOrigins
                headSuccess origins headToEvidence
              have restOrigins := induction tailSuccess headBelow headOrigins
                tailToEvidence
              simpa only [resultEq] using restOrigins

end Solcore.SourceSemantics.SourceInferenceSoundness
end
