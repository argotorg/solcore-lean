import Solcore.SourceSemantics.Requirements

/-!
Declarative validity of retained source coercion paths.

Every edge is justified by the resolved `Coerce<From, To>` trait predicate and
the selected `coerce` method's instantiated where predicates.  The path
relation composes edge endpoints structurally and never invokes coercion
search.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics

open Frontend
open Frontend.SourceInference

/-- A cataloged `Coerce` method profile instantiated at one source/target
pair. -/
inductive CoercionProfileInstantiates
    (context : Context) (source target : TypeSystem.Ty) :
    ProgramPredicate → List ProgramPredicate → Prop where
  | intro
      {signature : ProgramTraitSignature}
      {method : ProgramTraitMethodSignature}
      {fromParameter toParameter : TypeSystem.TypeParameterId}
      (signature_mem : signature ∈ context.signatures.traits)
      (name_eq : signature.name = "Coerce")
      (parameters_eq : signature.parameters = [fromParameter, toParameter])
      (method_unique :
        signature.methods.filter (fun candidate => candidate.name == "coerce") =
          [method])
      (parameter_types_eq :
        method.parameterTypes.map
          (TypeSystem.ParameterSubstitution.apply
            [(fromParameter, source), (toParameter, target)]) = [source])
      (return_types_eq :
        method.returnTypes.map
          (TypeSystem.ParameterSubstitution.apply
            [(fromParameter, source), (toParameter, target)]) = [target]) :
      CoercionProfileInstantiates context source target {
        trait := .declaration signature.id
        subject := source
        arguments := [target]
      } (method.wherePredicates.map
        (ProgramPredicate.applyParameters
          [(fromParameter, source), (toParameter, target)]))

/-- One retained coercion edge has exactly the primary `Coerce` evidence and
the selected method's source-ordered local evidence. -/
inductive CoercionStepValid (context : Context) : CoercionStep → Prop where
  | intro
      {step : CoercionStep}
      {primary : ProgramPredicate}
      {methodPredicates : List ProgramPredicate}
      (profile : CoercionProfileInstantiates context step.source step.target
        primary methodPredicates)
      (requirements : RequirementSequenceProves context
        (step.requirement :: step.methodRequirements)
        (primary :: methodPredicates)) :
      CoercionStepValid context step

/-- A coercion path starts at the first edge's source, composes every adjacent
endpoint, and ends at the requested target. -/
inductive CoercionPathValid (context : Context) :
    TypeSystem.Ty → TypeSystem.Ty → List CoercionStep → Prop where
  | nil (type : TypeSystem.Ty) : CoercionPathValid context type type []
  | cons {step : CoercionStep} {target : TypeSystem.Ty}
      {rest : List CoercionStep}
      (head : CoercionStepValid context step)
      (tail : CoercionPathValid context step.target target rest) :
      CoercionPathValid context step.source target (step :: rest)

/-- Requirement identities owned by a path in edge and method-source order. -/
def coercionRequirementIds (steps : List CoercionStep) : List RequirementId :=
  steps.flatMap CoercionStep.requirements

namespace CoercionPathValid

private theorem step_requirements_valid
    {context : Context}
    {step : CoercionStep}
    (valid : CoercionStepValid context step) :
    RequirementIdsValid context step.requirements := by
  cases valid with
  | intro _ requirements => exact requirements.ids_valid

theorem requirements_valid
    {context : Context}
    {source target : TypeSystem.Ty}
    {steps : List CoercionStep}
    (valid : CoercionPathValid context source target steps) :
    RequirementIdsValid context (coercionRequirementIds steps) := by
  intro id member
  induction valid with
  | nil => simp [coercionRequirementIds] at member
  | @cons step target rest head tail induction =>
      change id ∈ step.requirements ++ coercionRequirementIds rest at member
      rcases List.mem_append.mp member with headMember | tailMember
      · exact step_requirements_valid head id headMember
      · exact induction tailMember

private theorem endpoints_of_nil
    {context : Context}
    {source target : TypeSystem.Ty}
    (valid : CoercionPathValid context source target []) :
    source = target := by
  cases valid
  rfl

theorem endpoints_of_singleton
    {context : Context}
    {source target : TypeSystem.Ty}
    {step : CoercionStep}
    (valid : CoercionPathValid context source target [step]) :
    step.source = source ∧ step.target = target := by
  cases valid with
  | cons _ tail => exact ⟨rfl, endpoints_of_nil tail⟩

/-- Structural endpoint checking plus semantic validity of every retained
edge is sufficient to construct the declarative path judgment.  This is the
small bridge used by executable coercion producers: path search and commit
establish adjacency, while the solved requirement ledger justifies each
individual edge. -/
theorem of_isValid
    {context : Context} {source target : TypeSystem.Ty}
    {steps : List CoercionStep}
    (structural : CoercionPath.isValid source target steps = true)
    (stepsValid : ∀ step, step ∈ steps → CoercionStepValid context step) :
    CoercionPathValid context source target steps := by
  induction steps generalizing source with
  | nil =>
      simp only [CoercionPath.isValid, beq_iff_eq] at structural
      subst target
      exact .nil source
  | cons step rest induction =>
      have structural_eq :
          CoercionPath.isValid source target (step :: rest) =
            ((step.source == source) &&
              CoercionPath.isValid step.target target rest) := by
        cases rest <;> rfl
      rw [structural_eq, Bool.and_eq_true] at structural
      have source_eq : step.source = source :=
        beq_iff_eq.mp structural.1
      subst source
      exact .cons (stepsValid step (by simp))
        (induction structural.2 fun candidate member =>
          stepsValid candidate (by simp [member]))

end CoercionPathValid

end Solcore.SourceSemantics
