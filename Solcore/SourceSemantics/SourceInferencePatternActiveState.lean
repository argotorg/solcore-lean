import Solcore.SourceSemantics.SourceInferencePatternActiveOrigins
import Solcore.SourceSemantics.SourceInferenceLiveTemplateBacking

/-! The actual pattern scope and inference progress preserve active template
provenance and privacy, including when the incoming scope is generalized. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

theorem PatternScope.captureOrigins {before after : State} {whole : TypedSource}
    (scope : PatternScope before after)
    (origins : ActiveBinderCaptureOrigins before whole) :
    ActiveBinderCaptureOrigins after whole := by
  constructor
  intro binder member
  rcases scope.origin binder member with old | mono
  · exact origins.origin binder old
  · exact .inl mono.1

theorem PatternScope.templates {before after : State}
    (scope : PatternScope before after) (backed : LiveTemplatesBacked before)
    (rows : before.requirements ⊆ after.requirements)
    (extension : after.inference.substitution.SemanticallyExtends before.inference.substitution) :
    LiveTemplatesBacked after := by
  intro binder member requirement present
  rcases scope.origin binder member with old | mono
  · obtain ⟨raw, retained, same⟩ := backed binder old requirement present
    refine ⟨raw, rows retained, ?_⟩
    have transported := congrArg (Detail.applyPredicate after) same
    have normalized (predicate : ProgramPredicate) :
        Detail.applyPredicate after (Detail.applyPredicate before predicate) =
          Detail.applyPredicate after predicate :=
      TypedTraitResolution.applySubstitution_semanticallyExtends extension predicate
    simpa only [normalized] using transported
  · simp only [mono.2, List.not_mem_nil] at present

/-- Every active scheme after an accepted pattern call is either an old
scheme or a newly allocated monomorphic binder. Privacy is transported by
the actual pattern computation, not by a final-state assumption. -/
theorem inferMatchPatternFuel_active_state
    {fuel : Nat} {context : SourceInference.Context} {pattern : Syntax.Pattern}
    {expected : Ty} {state : State} {result : TypedMatchPattern × State}
    {whole : TypedSource}
    (ready : state.InferenceReady) (expectedBelow : expected.VariablesBelow state.inference.next)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (bound : ActiveQuantifiersBelowNext state)
    (privateVars : ActiveQuantifiersPrivate state)
    (backed : LiveTemplatesBacked state)
    (origins : ActiveBinderCaptureOrigins state whole)
    (expectedSafe : Safe (activeSchemeQuantifiers state) state expected)
    (accepted : Detail.inferMatchPatternFuel fuel context pattern expected state = .ok result) :
    ActiveQuantifiersPrivate result.2 ∧ ActiveQuantifiersBelowNext result.2 ∧
      LiveTemplatesBacked result.2 ∧ ActiveBinderCaptureOrigins result.2 whole := by
  have scope := inferMatchPatternFuel_scope accepted
  have progress := Detail.inferMatchPatternFuel_inferenceProperties ready expectedBelow formation accepted
  have protectedBound := activeSchemeQuantifiers_below_next bound
  have privacy := inferMatchPatternFuel_private ready expectedBelow formation
    protectedBound expectedSafe privateVars.all_live accepted
  refine ⟨?_, ?_, scope.templates backed
    (Detail.inferMatchPatternFuel_requirements_subset accepted) progress.1.substitution_extends,
    scope.captureOrigins origins⟩
  · intro owner ownerMember binder member
    constructor
    · intro v occurs q image quantified
      have active : q ∈ activeSchemeQuantifiers state :=
        scope.quantified ▸ List.mem_flatMap.mpr ⟨owner, ownerMember, quantified⟩
      exact (privacy.2.1 binder member).body v occurs q image active
    · intro requirement present type typeMember v occurs outside q image quantified
      have active : q ∈ activeSchemeQuantifiers state :=
        scope.quantified ▸ List.mem_flatMap.mpr ⟨owner, ownerMember, quantified⟩
      exact (privacy.2.1 binder member).requirements
        requirement present type typeMember v occurs outside q image active
  · intro binder member q quantified
    have active : q ∈ activeSchemeQuantifiers state :=
      scope.quantified ▸ List.mem_flatMap.mpr ⟨binder, member, quantified⟩
    exact Nat.lt_of_lt_of_le (protectedBound q active) progress.1.next_le

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
