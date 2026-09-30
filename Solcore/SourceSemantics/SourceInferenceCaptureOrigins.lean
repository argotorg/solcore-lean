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

end Solcore.SourceSemantics.SourceInferenceSoundness
