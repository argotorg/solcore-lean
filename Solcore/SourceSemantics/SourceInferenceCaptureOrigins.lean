import Solcore.SourceSemantics.SourceInferenceSoundness

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

end Solcore.SourceSemantics.SourceInferenceSoundness
