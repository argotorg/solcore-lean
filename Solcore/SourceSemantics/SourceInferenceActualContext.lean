import Solcore.SourceSemantics.SourceInferenceRecursiveSoundness

/-! Recursive checking uses the actual stack of enclosing generalized
initializers. Its flexible variables and added predicates come only from
retained binders whose initializer subtrees contain the current occurrence. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

namespace ActualContext

def variables (frames : List InitializedLetBinding) : List TypeVarId :=
  frames.flatMap fun frame => frame.binder.scheme.quantified

def predicates (frames : List InitializedLetBinding) : List ProgramPredicate :=
  frames.flatMap fun frame => frame.binder.schemeRequirements.map fun requirement => requirement.predicate

def Covers (finalized : Frontend.SourceInference.Result)
    (frames : List InitializedLetBinding) (occurrence : NodeId) : Prop :=
  ∀ frame ∈ frames, InReflexiveSubtree finalized.typedSource frame.initializer occurrence

end ActualContext

/-- The additional context provenance needed by exact local generalization.
Lexical-table alignment and formation remain in the existing recursive
invariants. Every frame is a literal finalized source binder. -/
structure ActualContext (wholeContext : Frontend.SourceInference.Context)
    (finalized : Frontend.SourceInference.Result)
    (frames : List InitializedLetBinding) (context : SourceSemantics.Context) : Prop where
  retained : ∀ frame ∈ frames, frame ∈ initializedLetBindings finalized.typedSource
  nested : frames.Pairwise (fun outer inner => Descends finalized.typedSource outer.initializer inner.initializer)
  variables_eq : context.typeVariables = ActualContext.variables frames
  assumptions_eq : context.assumptions =
    (finalizedRequirementContext wholeContext finalized).assumptions ++ ActualContext.predicates frames

  sourceOwner : finalized.typedSource.owner = wholeContext.scope.genericOwner

namespace ActualContext
variable {wholeContext : Frontend.SourceInference.Context}
  {finalized : Frontend.SourceInference.Result}
  {frames : List InitializedLetBinding} {context final : SourceSemantics.Context}

/-- The canonical checked body starts outside every generalized initializer. -/
theorem empty (variables : context.typeVariables = [])
    (assumptions : context.assumptions = (finalizedRequirementContext wholeContext finalized).assumptions)
    (sourceOwner : finalized.typedSource.owner = wholeContext.scope.genericOwner) :
    ActualContext wholeContext finalized [] context := by
  exact ⟨by simp, by simp, variables, by simpa [predicates] using assumptions, sourceOwner⟩

theorem covers_empty (occurrence : NodeId) : Covers finalized [] occurrence := by
  intro frame member
  cases member

/-- Local scope changes do not introduce flexible type-variable scopes. -/
theorem congr (actual : ActualContext wholeContext finalized frames context)
    (variables : final.typeVariables = context.typeVariables)
    (assumptions : final.assumptions = context.assumptions) :
    ActualContext wholeContext finalized frames final :=
  ⟨actual.retained, actual.nested, variables.trans actual.variables_eq,
    assumptions.trans actual.assumptions_eq, actual.sourceOwner⟩

theorem withLocal (actual : ActualContext wholeContext finalized frames context)
    (id : Resolved.LocalId) (scheme : Scheme) (requirements : List LocalSchemeRequirement := []) :
    ActualContext wholeContext finalized frames (context.withLocal id scheme requirements) :=
  actual.congr rfl rfl

theorem binder {owner : Resolved.DeclarationId} {binding : TypedBinder}
    (actual : ActualContext wholeContext finalized frames context)
    (extension : BinderExtends owner context binding final) :
    ActualContext wholeContext finalized frames final :=
  actual.congr extension.typeVariables_eq extension.context_fields.2.2.2.1

theorem binders {owner : Resolved.DeclarationId} {bindings : List TypedBinder}
    (actual : ActualContext wholeContext finalized frames context)
    (extension : BindersExtend owner context bindings final) :
    ActualContext wholeContext finalized frames final := by
  induction extension with
  | nil => exact actual
  | cons head tail induction => exact induction (actual.binder head)

theorem monoBinders {owner : Resolved.DeclarationId} {bindings : List TypedBinder} {types : List Ty}
    (actual : ActualContext wholeContext finalized frames context)
    (extension : MonoBindersExtend owner context bindings types final) :
    ActualContext wholeContext finalized frames final := by
  induction extension with
  | nil => exact actual
  | cons _ head _ induction => exact induction (actual.binder head)

/-- Statement typing changes only the actual lexical bindings. -/
theorem of_statement {source : TypedSource} {control : ControlContext}
    {id : StatementId} {facts : StatementFacts}
    (actual : ActualContext wholeContext finalized frames context)
    (typed : StatementHasType source control context id final facts) :
    ActualContext wholeContext finalized frames final := by
  cases typed <;> first | exact actual | exact actual.binder (by assumption)

/-- The same lexical fact holds for each actual for-header item. -/
theorem of_forItem {source : TypedSource} {control : ControlContext}
    {item : ForItemForm}
    (actual : ActualContext wholeContext finalized frames context)
    (typed : ForItemHasType source control context item final) :
    ActualContext wholeContext finalized frames final := by
  cases typed <;> first | exact actual | exact actual.binder (by assumption)

/-- A genuine nested initializer extends the stack by its retained binder. -/
theorem initializer (actual : ActualContext wholeContext finalized frames context)
    (binding : InitializedLetBinding)
    (retained : binding ∈ initializedLetBindings finalized.typedSource)
    (nested : ∀ outer ∈ frames, Descends finalized.typedSource outer.initializer binding.initializer) :
    ActualContext wholeContext finalized (frames ++ [binding])
      (localSchemeInitializerContext context binding.binder) := by
  refine ⟨?_, ?_, ?_, ?_, actual.sourceOwner⟩
  · intro frame member
    rcases List.mem_append.mp member with member | member
    · exact actual.retained frame member
    · exact (List.mem_singleton.mp member) ▸ retained
  · exact List.pairwise_append.mpr ⟨actual.nested, by simp, by simpa using nested⟩
  · simp only [localSchemeInitializerContext, Context.withAssumptions,
      Context.withTypeVariables, actual.variables_eq, variables, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil]
  · simp only [localSchemeInitializerContext, Context.withAssumptions,
      Context.withTypeVariables, actual.assumptions_eq, predicates, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

theorem Covers.descends {parent child : NodeId}
    (covered : Covers finalized frames parent)
    (path : Descends finalized.typedSource parent child) : Covers finalized frames child := by
  intro frame member
  rcases covered frame member with same | below
  · exact .inr (same ▸ path)
  · exact .inr (below.trans path)

theorem Covers.directChild {parent child : NodeId}
    (covered : Covers finalized frames parent)
    (edge : DirectChild finalized.typedSource parent child) : Covers finalized frames child :=
  covered.descends (.direct edge)

theorem Covers.push {binding : InitializedLetBinding} {occurrence : NodeId}
    (covered : Covers finalized frames occurrence)
    (inside : InReflexiveSubtree finalized.typedSource binding.initializer occurrence) :
    Covers finalized (frames ++ [binding]) occurrence := by
  intro frame member
  rcases List.mem_append.mp member with member | member
  · exact covered frame member
  · exact (List.mem_singleton.mp member) ▸ inside

/-- At an actual initializer child, all older active scopes strictly contain
its root; the new binder then covers that same root reflexively. -/
theorem enter {parent : NodeId}
    (actual : ActualContext wholeContext finalized frames context)
    (covered : Covers finalized frames parent) (binding : InitializedLetBinding)
    (retained : binding ∈ initializedLetBindings finalized.typedSource)
    (edge : DirectChild finalized.typedSource parent binding.initializer) :
    ActualContext wholeContext finalized (frames ++ [binding])
      (localSchemeInitializerContext context binding.binder) ∧
      Covers finalized (frames ++ [binding]) binding.initializer := by
  constructor
  · apply actual.initializer binding retained
    intro outer member
    rcases covered outer member with same | below
    · exact same ▸ Descends.direct edge
    · exact below.trans (.direct edge)
  · exact (covered.directChild edge).push (.inl rfl)

end ActualContext
end Solcore.SourceSemantics.SourceInferenceSoundness
