import Solcore.SourceSemantics.Internal.Inference.Soundness
import Solcore.SourceSemantics.Internal.Formation.CoercionTargets

/-!
# Formation of requirements

Obligations formed from their signature and operand producers, along the real coercion search, with
their residual transport.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceRequirementFormation
/-! Formation of obligations from their actual signature and operand producers. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceRequirementFormation

open Frontend SourceInference TypeSystem
open SourceInferenceSoundness

/-- A closed signature predicate remains meaningful when its rigid parameters
are replaced by admissible occurrence types, including residual variables. -/
theorem predicate_applyParameters_admissible
    {source target : SourceSemantics.Context} {predicate : ProgramPredicate}
    (substitution : TypeSystem.ParameterSubstitution)
    (exact : SourceSemantics.ParameterSubstitution.Exact substitution
      source.typeParameters)
    (range : SourceSemantics.ParameterSubstitution.RangeAdmissible target substitution)
    (signatures : target.signatures = source.signatures)
    (binders : TypeParameterBindersWellFormed target)
    (formed : PredicateWellFormed source predicate) :
    PredicateAdmissible target (predicate.applyParameters substitution) := by
  constructor
  · exact StructuralSubstitution.TypeWellScoped.applyParametersAdmissibleTo
      substitution exact range signatures binders formed.subject.typeWellScoped
  · intro argument member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    exact StructuralSubstitution.TypeWellScoped.applyParametersAdmissibleTo
      substitution exact range signatures binders
      (formed.arguments original originalMember).typeWellScoped
  · cases traitEq : predicate.trait with
    | builtin builtin =>
        cases builtin
        have valid := formed.trait
        rw [traitEq] at valid
        simpa [ProgramPredicate.applyParameters, traitEq] using valid
    | declaration id =>
        have valid := formed.trait
        rw [traitEq] at valid
        obtain ⟨signature, member, idEq, arity⟩ := valid
        simp only [ProgramPredicate.applyParameters, traitEq]
        exact ⟨signature, by simpa [signatures] using member, idEq,
          by simpa [ProgramPredicate.applyParameters, traitEq] using arity⟩

/-- The catalog and exact fresh instantiation establish every declaration
predicate before its requirement identities are allocated. -/
theorem instantiated_function_predicates
    {context : SourceSemantics.Context}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (binders : TypeParameterBindersWellFormed context)
    (residual : context.residualTypeVariables = true)
    {signature : ProgramFunctionSignature}
    (member : signature ∈ context.signatures.functions) (next : Nat) :
    ∀ predicate ∈ (signature.scheme.instantiate next).predicates,
      PredicateAdmissible context predicate := by
  rw [ConstrainedDeclarationScheme.instantiate_predicates]
  intro predicate predicateMember
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp predicateMember
  exact predicate_applyParameters_admissible
    (source := signatureContext context.signatures signature.id
      signature.scheme.parameters signature.scheme.predicates)
    (signature.scheme.instantiate next).parameterSubstitution
    (DeclarationInstantiation.instantiate_parameterSubstitution_exact
      signature.scheme next (catalog.function_parameters signature member).1)
    (DeclarationInstantiation.instantiate_parameterSubstitution_rangeAdmissible
      binders residual signature.scheme next) rfl binders
    ((catalog.functions_semantic signature member).predicates original originalMember)

/-- Recover the exact declaration predicate batch and its ledger allocation
from the accepted candidate, with formation for every predicate in that batch. -/
theorem candidate_signature_issuance
    {inferenceContext : Frontend.SourceInference.Context}
    {arguments : List InferredExpression}
    {integerOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {signature : ProgramFunctionSignature} {result : Detail.CandidateAttemptResult}
    {context : SourceSemantics.Context}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (binders : TypeParameterBindersWellFormed context)
    (residual : context.residualTypeVariables = true)
    (member : signature ∈ context.signatures.functions)
    (success : Detail.tryFunctionCandidate inferenceContext arguments integerOrigins
      call expected state signature = .ok (some result)) :
    RequirementPredicatesCorrespond result.state.requirements
      (signature.scheme.instantiate state.inference.next).predicates
      result.signatureRequirements ∧
    (∀ predicate ∈ (signature.scheme.instantiate state.inference.next).predicates,
      PredicateAdmissible context predicate) := by
  obtain ⟨fittedArguments, fittedResult, _, _, _, _, _, _, idsEq, stateEq⟩ :=
    Detail.tryFunctionCandidate_some_resultFitAllocationWitness
      (catalog.functions_semantic signature member).scheme_body success
  constructor
  · rw [idsEq, stateEq]
    exact State.addRequirementsWithIds_correspond fittedResult.state _
  · exact instantiated_function_predicates catalog binders residual member _

/-- The builtin integer obligation is formed by the type of its operand. -/
theorem builtin_integer_predicate {context : SourceSemantics.Context} {type : Ty}
    (formed : TypeAdmissible context type) :
    PredicateAdmissible context (ProgramSignatures.builtinIntPredicate type) := by
  exact ⟨formed, by simp [ProgramSignatures.builtinIntPredicate], rfl⟩

/-- An operator profile supplies the real trait member, exact singleton rigid
substitution, and cataloged method predicates. Its operand supplies the range. -/
theorem operator_profile_predicates
    {context : SourceSemantics.Context} {traitName methodName : String}
    {operand : Ty} {parameters returns : List Ty} {predicates : List ProgramPredicate}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (binders : TypeParameterBindersWellFormed context)
    (operandFormed : TypeAdmissible context operand)
    (profile : OperatorProfileInstantiates context traitName methodName operand
      parameters returns predicates) :
    ∀ predicate ∈ predicates, PredicateAdmissible context predicate := by
  cases profile with
  | @intro signature method parameter signatureMember _ parametersEq methodUnique _ _ =>
      have signatureFormed := catalog.traits_semantic signature signatureMember
      have methodMember : method ∈ signature.methods := by
        have filtered : method ∈ signature.methods.filter
            (fun candidate => candidate.name == methodName) := by
          rw [methodUnique]
          simp
        exact (List.mem_filter.mp filtered).1
      have exactSubstitution : SourceSemantics.ParameterSubstitution.Exact
          [(parameter, operand)] signature.parameters := by
        rw [parametersEq]
        exact SourceSemantics.ParameterSubstitution.exact_singleton _ _
      have range : SourceSemantics.ParameterSubstitution.RangeAdmissible context
          [(parameter, operand)] := by
        intro candidate replacement member
        simp only [List.mem_singleton] at member
        cases member
        exact operandFormed
      intro predicate member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨operandFormed, by simp,
          signature, signatureMember, rfl, by simp [parametersEq]⟩
      · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
        exact predicate_applyParameters_admissible
          (source := signatureContext context.signatures signature.id signature.parameters
            (signature.wherePredicates ++ method.wherePredicates))
          [(parameter, operand)] exactSubstitution range rfl binders
          ((signatureFormed.methods method methodMember).predicates original originalMember)

/-- Successful operator-profile construction therefore issues formed
predicates. No evidence-entailment premise is used to establish formation. -/
theorem operator_issuance
    {inferenceContext : Frontend.SourceInference.Context}
    {context : SourceSemantics.Context} {trait : Resolved.DeclarationId}
    {traitName methodName : String} {operand : Ty}
    {parameters returns : List Ty} {predicates : List ProgramPredicate}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (binders : TypeParameterBindersWellFormed context)
    (signatures : context.signatures = inferenceContext.signatures)
    (traitNameEq : (inferenceContext.signatures.trait? trait).map (·.name) = some traitName)
    (operandFormed : TypeAdmissible context operand)
    (success : Detail.operatorTraitPredicates inferenceContext trait methodName operand
      parameters returns = .ok predicates) :
    ∀ predicate ∈ predicates, PredicateAdmissible context predicate :=
  operator_profile_predicates catalog binders operandFormed
    (operatorTraitPredicates_instantiates signatures traitNameEq success)

/-- Every issued identity selects one of the producer's exact predicates.
Ledger extension preserves this statement without assuming arbitrary row formation. -/
theorem issued_identity_formed
    {context : SourceSemantics.Context} {requirements : List Requirement}
    {predicates : List ProgramPredicate} {ids : List RequirementId}
    (correspondence : RequirementPredicatesCorrespond requirements predicates ids)
    (formed : ∀ predicate ∈ predicates, PredicateAdmissible context predicate)
    {id : RequirementId} (member : id ∈ ids) :
    ∃ predicate, ({ id, predicate } : Requirement) ∈ requirements ∧
      PredicateAdmissible context predicate := by
  induction correspondence with
  | nil => simp at member
  | @cons predicate head predicates ids headMember _ induction =>
      rcases List.mem_cons.mp member with rfl | tailMember
      · exact ⟨predicate, headMember, formed predicate (by simp)⟩
      · exact induction (fun predicate member => formed predicate (by simp [member])) tailMember

end Solcore.SourceSemantics.SourceInferenceRequirementFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceCoercionRequirementFormation
/-! Catalog and operand origins of actual coercion requirements. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceRequirementFormation

open Frontend SourceInference TypeSystem

/-- The executable profile lookup retains a real trait signature and, when
present, one of its methods. Empty legacy marker traits keep the same origin. -/
def CoercionProfileOrigin (context : Frontend.SourceInference.Context)
    (trait : Resolved.DeclarationId) (profile : Option Detail.CoercionMethodProfile) : Prop :=
  ∃ signature ∈ context.signatures.traits,
    signature.id = trait ∧ signature.parameters.length = 2 ∧
      ∀ selected ∈ profile, selected.trait = trait ∧
        selected.parameters = signature.parameters ∧ selected.method ∈ signature.methods

theorem coercion_profile_origin
    {context : Frontend.SourceInference.Context} {trait : Resolved.DeclarationId}
    {profile : Option Detail.CoercionMethodProfile}
    (accepted : Detail.coercionMethodProfile? context trait = .ok profile) :
    CoercionProfileOrigin context trait profile := by
  unfold Detail.coercionMethodProfile? at accepted
  cases found : context.signatures.trait? trait with
  | none => simp [found, bind, Except.bind] at accepted
  | some signature =>
      have member : signature ∈ context.signatures.traits := List.mem_of_find?_eq_some found
      have idEq : signature.id = trait := of_decide_eq_true
        (List.find?_some (p := fun candidate : ProgramTraitSignature => decide (candidate.id = trait)) found)
      simp only [found, pure, Pure.pure, Except.pure, bind, Except.bind] at accepted
      split at accepted
      · rename_i arity
        cases methods : signature.methods.filter (fun method => method.name == "coerce") with
        | nil =>
            simp only [methods, Except.ok.injEq] at accepted
            cases accepted
            exact ⟨signature, member, idEq, arity, by simp⟩
        | cons method rest =>
            cases rest with
            | cons second rest => simp [methods] at accepted
            | nil =>
                simp only [methods, Except.ok.injEq] at accepted
                cases accepted
                refine ⟨signature, member, idEq, arity, ?_⟩
                intro selected selectedMember
                simp only [Option.mem_def, Option.some.injEq] at selectedMember
                cases selectedMember
                refine ⟨rfl, rfl, ?_⟩
                exact (List.mem_filter.mp (show method ∈ signature.methods.filter
                  (fun method => method.name == "coerce") by rw [methods]; simp)).1
      · simp_all

/-- Actual profile and method-predicate computation produce a formed primary
trait predicate and formed companion predicates from the two endpoint types.
The optional absent method is accepted exactly as by the inference runtime. -/
theorem coercion_issuance
    {inferenceContext : Frontend.SourceInference.Context}
    {context : SourceSemantics.Context} {trait : Resolved.DeclarationId}
    {profile : Option Detail.CoercionMethodProfile}
    {source target : Ty} {predicates : List ProgramPredicate}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (binders : TypeParameterBindersWellFormed context)
    (signatures : context.signatures = inferenceContext.signatures)
    (sourceFormed : TypeAdmissible context source)
    (targetFormed : TypeAdmissible context target)
    (profileAccepted : Detail.coercionMethodProfile? inferenceContext trait = .ok profile)
    (predicatesAccepted : Detail.coercionMethodPredicates profile source target = .ok predicates) :
    PredicateAdmissible context { trait := .declaration trait, subject := source, arguments := [target] } ∧
      (∀ predicate ∈ predicates, PredicateAdmissible context predicate) := by
  obtain ⟨signature, signatureMember, idEq, arity, selectedOrigin⟩ :=
    coercion_profile_origin profileAccepted
  have semanticMember : signature ∈ context.signatures.traits := signatures.symm ▸ signatureMember
  have signatureFormed := catalog.traits_semantic signature semanticMember
  constructor
  · exact ⟨sourceFormed, by intro argument member; simp only [List.mem_singleton] at member; subst argument; exact targetFormed,
      signature, semanticMember, idEq, arity.symm⟩
  · cases profile with
    | none =>
        simp [Detail.coercionMethodPredicates] at predicatesAccepted
        subst predicates
        simp
    | some profile =>
        have origin := selectedOrigin profile (by simp)
        have exactSubstitution : SourceSemantics.ParameterSubstitution.Exact
            (profile.parameters.zip [source, target]) signature.parameters := by
          rw [origin.2.1]
          exact SourceSemantics.ParameterSubstitution.exact_zip
            signatureFormed.parameters_nodup (by simpa using arity.symm)
        have range : SourceSemantics.ParameterSubstitution.RangeAdmissible context
            (profile.parameters.zip [source, target]) := by
          intro parameter replacement member
          have choice := (List.of_mem_zip member).2
          simp only [List.mem_cons, List.not_mem_nil, or_false] at choice
          rcases choice with rfl | rfl
          · exact sourceFormed
          · exact targetFormed
        simp only [Detail.coercionMethodPredicates] at predicatesAccepted
        split at predicatesAccepted
        · simp only [pure, Pure.pure, Except.pure, Except.ok.injEq] at predicatesAccepted
          cases predicatesAccepted
          intro predicate member
          obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
          exact predicate_applyParameters_admissible
            (source := signatureContext context.signatures signature.id signature.parameters
              (signature.wherePredicates ++ profile.method.wherePredicates))
            (profile.parameters.zip [source, target]) exactSubstitution range rfl binders
            ((signatureFormed.methods profile.method origin.2.2).predicates original originalMember)
        · simp [throw, Functor.map, Except.map] at predicatesAccepted

end Solcore.SourceSemantics.SourceInferenceRequirementFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceCoercionGraphFormation
/-! Formation of every requirement produced by the real coercion search. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.SourceInferenceRequirementFormation
open Frontend SourceInference TypeSystem

/-- Declaration facts available at a real inference entry. The current source
and expected types are supplied separately by the expression derivation. -/
structure CoercionFormationContext (semantic : SourceSemantics.Context)
    (context : SourceInference.Context) : Prop where
  signatures : semantic.signatures = context.signatures
  catalog : SignatureCatalogWellFormed semantic.signatures
  residual : semantic.residualTypeVariables = true
  assumptions : ∀ predicate ∈ context.assumptions, PredicateWellFormed semantic predicate

/-- A real function signature forms the inference context's actual declared
assumptions. No whole-body typing certificate is used at this entry. -/
theorem CoercionFormationContext.of_function
    {semantic : SourceSemantics.Context} {context : SourceInference.Context}
    {signature : ProgramFunctionSignature}
    (signatures : semantic.signatures = context.signatures)
    (catalog : SignatureCatalogWellFormed semantic.signatures)
    (member : signature ∈ semantic.signatures.functions)
    (parameters : semantic.typeParameters = signature.scheme.parameters)
    (owner : semantic.currentDeclaration = some signature.id)
    (residual : semantic.residualTypeVariables = true)
    (assumptions : context.assumptions = signature.scheme.predicates) :
    CoercionFormationContext semantic context := by
  refine ⟨signatures, catalog, residual, ?_⟩
  intro predicate predicateMember
  rw [assumptions] at predicateMember
  have formed := (catalog.functions_semantic signature member).predicates predicate predicateMember
  exact ⟨StructuralSubstitution.TypeWellFormed.transportContext
    (source := signatureContext semantic.signatures signature.id signature.scheme.parameters signature.scheme.predicates)
    rfl parameters owner formed.subject,
    fun argument member => StructuralSubstitution.TypeWellFormed.transportContext
    (source := signatureContext semantic.signatures signature.id signature.scheme.parameters signature.scheme.predicates)
    rfl parameters owner
      (formed.arguments argument member), formed.trait⟩

private def EdgeFormed (semantic : SourceSemantics.Context) (edge : Detail.CoercionEdge) : Prop :=
  TypeAdmissible semantic edge.source ∧ TypeAdmissible semantic edge.target ∧
    PredicateAdmissible semantic edge.predicate

private def FullEdgeFormed (semantic : SourceSemantics.Context) (edge : Detail.CoercionEdge) : Prop :=
  EdgeFormed semantic edge ∧ ∀ predicate ∈ edge.methodPredicates, PredicateAdmissible semantic predicate

private theorem primary_formed {semantic : SourceSemantics.Context}
    {context : SourceInference.Context} {trait : Resolved.DeclarationId}
    {profile : Option Detail.CoercionMethodProfile} {source target : Ty}
    (formation : CoercionFormationContext semantic context)
    (profileAccepted : Detail.coercionMethodProfile? context trait = .ok profile)
    (sourceFormed : TypeAdmissible semantic source) (targetFormed : TypeAdmissible semantic target) :
    PredicateAdmissible semantic {trait, subject := source, arguments := [target]} := by
  obtain ⟨signature, member, idEq, arity, _⟩ := coercion_profile_origin profileAccepted
  exact ⟨sourceFormed, by intro argument member; cases List.mem_singleton.mp member; exact targetFormed,
    signature, formation.signatures.symm ▸ member, idEq, arity.symm⟩

private theorem attachMethods_formed {semantic : SourceSemantics.Context} {context : SourceInference.Context}
    {trait : Resolved.DeclarationId} {profile : Option Detail.CoercionMethodProfile}
    (formation : CoercionFormationContext semantic context)
    (profileAccepted : Detail.coercionMethodProfile? context trait = .ok profile)
    (edges : List Detail.CoercionEdge) (rawFormed : ∀ edge ∈ edges, EdgeFormed semantic edge)
    {results : List Detail.CoercionEdge}
    (accepted : edges.mapM (fun edge => do
      let methodPredicates ← Detail.coercionMethodPredicates profile edge.source edge.target
      pure { edge with methodPredicates }) = Except.ok results) :
    ∀ edge ∈ results, FullEdgeFormed semantic edge := by
  induction edges generalizing results with
  | nil => simp at accepted; subst results; simp
  | cons head tail ih =>
    simp only [List.mapM_cons] at accepted
    cases methods : Detail.coercionMethodPredicates profile head.source head.target with
    | error error => simp [methods, bind, Except.bind] at accepted
    | ok predicates =>
      simp only [methods, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
      cases tails : tail.mapM (fun edge => do
          let methodPredicates ← Detail.coercionMethodPredicates profile edge.source edge.target
          pure { edge with methodPredicates }) with
      | error error =>
        dsimp only [bind, Except.bind, pure, Pure.pure, Except.pure] at tails
        simp [tails] at accepted
      | ok rest =>
        dsimp only [bind, Except.bind, pure, Pure.pure, Except.pure] at tails
        simp only [tails, Except.ok.injEq] at accepted
        subst results
        intro edge member
        rcases List.mem_cons.mp member with rfl | member
        · have raw := rawFormed head (by simp)
          exact ⟨raw, (coercion_issuance formation.catalog raw.1.binders formation.signatures
            raw.1 raw.2.1 profileAccepted methods).2⟩
        · exact ih (fun edge member => rawFormed edge (by simp [member])) tails edge member

private theorem coercionEdges_formed {semantic : SourceSemantics.Context} {state : State}
    {context : SourceInference.Context} {profile : Option Detail.CoercionMethodProfile}
    {trait : Resolved.DeclarationId} {source : Ty} {edges : List Detail.CoercionEdge}
    (formation : CoercionFormationContext semantic context)
    (profileAccepted : Detail.coercionMethodProfile? context trait = .ok profile)
    (sourceFormed : TypeAdmissible semantic source)
    (accepted : Detail.coercionEdges context state profile trait source = .ok edges) :
    ∀ edge ∈ edges, FullEdgeFormed semantic edge := by
  apply attachMethods_formed formation profileAccepted _ _ accepted
  intro edge member
  rw [List.mem_eraseDups, List.mem_append] at member
  rcases member with rules | assumptions
  · obtain ⟨rule, ruleMember, produced⟩ := List.mem_filterMap.mp rules
    have result := coercion_rule_edge_target formation.catalog formation.residual
      (formation.signatures.symm ▸ ruleMember) sourceFormed produced
    refine ⟨result.1.symm ▸ sourceFormed, result.2.1, ?_⟩
    rw [result.2.2]
    exact primary_formed formation profileAccepted sourceFormed result.2.1
  · have result := coercion_assumption_edge_target formation.assumptions assumptions
    exact ⟨result.1.symm ▸ sourceFormed, result.2⟩

def PlannedCoercionStepFormed (semantic : SourceSemantics.Context)
    (step : Detail.PlannedCoercionStep) : Prop :=
  TypeAdmissible semantic step.source ∧ TypeAdmissible semantic step.target ∧
    PredicateAdmissible semantic step.predicate ∧
    ∀ predicate ∈ step.methodPredicates, PredicateAdmissible semantic predicate

private def PathFormed (semantic : SourceSemantics.Context)
    (path : Detail.CoercionPath) : Prop :=
  TypeAdmissible semantic path.current ∧ ∀ step ∈ path.steps, PlannedCoercionStepFormed semantic step

private theorem viable_member {context : SourceInference.Context} {state : State}
    (edges : List Detail.CoercionEdge) {edge : Detail.CoercionEdge}
    (member : edge ∈ (Detail.viableCoercionEdges context state edges).viable) : edge ∈ edges := by
  induction edges with
  | nil => cases member
  | cons head tail ih =>
    unfold Detail.viableCoercionEdges at member
    cases viable : Detail.coercionEvidenceViable context state head.predicate head.methodPredicates with
    | error error =>
      simp only [viable] at member
      exact List.mem_cons_of_mem _ (ih member)
    | ok value =>
      cases value with
      | false =>
        simp only [viable] at member
        exact List.mem_cons_of_mem _ (ih member)
      | true =>
        simp only [viable, List.mem_cons] at member
        rcases member with rfl | member
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih member)

private theorem expandPath_formed {semantic : SourceSemantics.Context} {state : State}
    {context : SourceInference.Context} {profile : Option Detail.CoercionMethodProfile}
    {trait : Resolved.DeclarationId} {path : Detail.CoercionPath}
    {result : Detail.CoercionExpansion}
    (formation : CoercionFormationContext semantic context)
    (profileAccepted : Detail.coercionMethodProfile? context trait = .ok profile)
    (pathFormed : PathFormed semantic path)
    (accepted : Detail.expandCoercionPath context state profile trait path = .ok result) :
    ∀ next ∈ result.paths, PathFormed semantic next := by
  unfold Detail.expandCoercionPath at accepted
  cases edges : Detail.coercionEdges context state profile trait path.current with
  | error error => simp [edges, bind, Except.bind] at accepted
  | ok candidates =>
    simp only [edges, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    intro next member
    obtain ⟨edge, edgeMember, rfl⟩ := List.mem_map.mp member
    have safe := coercionEdges_formed formation profileAccepted pathFormed.1 edges edge
      (List.mem_filter.mp (viable_member _ edgeMember)).1
    refine ⟨safe.1.2.1, ?_⟩
    intro step stepMember
    rcases List.mem_append.mp stepMember with old | fresh
    · exact pathFormed.2 step old
    · cases List.mem_singleton.mp fresh
      exact ⟨safe.1.1, safe.1.2.1, safe.1.2.2, safe.2⟩

private theorem expandPaths_formed {semantic : SourceSemantics.Context} {state : State}
    {context : SourceInference.Context} {profile : Option Detail.CoercionMethodProfile}
    {trait : Resolved.DeclarationId} (paths : List Detail.CoercionPath)
    {result : Detail.CoercionExpansion}
    (formation : CoercionFormationContext semantic context)
    (profileAccepted : Detail.coercionMethodProfile? context trait = .ok profile)
    (pathsFormed : ∀ path ∈ paths, PathFormed semantic path)
    (accepted : Detail.expandCoercionPaths context state profile trait paths = .ok result) :
    ∀ next ∈ result.paths, PathFormed semantic next := by
  induction paths generalizing result with
  | nil => simp [Detail.expandCoercionPaths] at accepted; subst result; simp
  | cons head tail ih =>
    simp only [Detail.expandCoercionPaths] at accepted
    cases headResult : Detail.expandCoercionPath context state profile trait head with
    | error error => simp [headResult, bind, Except.bind] at accepted
    | ok first =>
      simp only [headResult, bind, Except.bind] at accepted
      cases tailResult : Detail.expandCoercionPaths context state profile trait tail with
      | error error => simp [tailResult] at accepted
      | ok rest =>
        simp only [tailResult, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
        cases accepted
        intro next member
        rcases List.mem_append.mp member with firstMember | restMember
        · exact expandPath_formed formation profileAccepted (pathsFormed _ (by simp)) headResult _ firstMember
        · exact ih (fun path member => pathsFormed path (by simp [member])) tailResult _ restMember

private theorem selectPath_formed {semantic : SourceSemantics.Context}
    {source target : Ty} {paths : List Detail.CoercionPath}
    {steps : List Detail.PlannedCoercionStep}
    (pathsFormed : ∀ path ∈ paths, PathFormed semantic path)
    (accepted : Detail.selectCoercionPath source target paths = .ok (some steps)) :
    ∀ step ∈ steps, PlannedCoercionStepFormed semantic step := by
  unfold Detail.selectCoercionPath at accepted
  cases found : (paths.filter fun path => path.current == target).eraseDups with
  | nil => simp [found] at accepted
  | cons path rest =>
    cases rest with
    | cons second tail => simp [found] at accepted
    | nil =>
      simp only [found, Except.ok.injEq, Option.some.injEq] at accepted
      subst steps
      have member : path ∈ paths :=
        (List.mem_filter.mp (List.mem_eraseDups.mp
          (show path ∈ (paths.filter fun path => path.current == target).eraseDups by rw [found]; simp))).1
      exact (pathsFormed path member).2

private theorem finish_not_some {blocked : List Error} {steps : List Detail.PlannedCoercionStep}
    (accepted : Detail.finishCoercionSearch blocked = .ok (some steps)) : False := by
  cases blocked <;> simp [Detail.finishCoercionSearch] at accepted

private theorem searchPaths_formed {semantic : SourceSemantics.Context} {state : State}
    {context : SourceInference.Context} {profile : Option Detail.CoercionMethodProfile}
    {trait : Resolved.DeclarationId} {source target : Ty}
    (fuel : Nat) {frontier : List Detail.CoercionPath} {blocked : List Error}
    {steps : List Detail.PlannedCoercionStep}
    (formation : CoercionFormationContext semantic context)
    (profileAccepted : Detail.coercionMethodProfile? context trait = .ok profile)
    (frontierFormed : ∀ path ∈ frontier, PathFormed semantic path)
    (accepted : Detail.searchCoercionPaths context state profile trait source target
      fuel frontier blocked = .ok (some steps)) :
    ∀ step ∈ steps, PlannedCoercionStepFormed semantic step := by
  induction fuel generalizing frontier blocked with
  | zero =>
    simp only [Detail.searchCoercionPaths] at accepted
    cases expanded : Detail.expandCoercionPaths context state profile trait frontier with
    | error error => simp [expanded, bind, Except.bind] at accepted
    | ok beyond =>
      simp only [expanded, bind, Except.bind] at accepted
      split at accepted
      · exact (finish_not_some accepted).elim
      · cases accepted
  | succ fuel ih =>
    simp only [Detail.searchCoercionPaths] at accepted
    cases expanded : Detail.expandCoercionPaths context state profile trait frontier with
    | error error => simp [expanded, bind, Except.bind] at accepted
    | ok next =>
      simp only [expanded, bind, Except.bind] at accepted
      have nextFormed := expandPaths_formed frontier formation profileAccepted frontierFormed expanded
      cases selected : Detail.selectCoercionPath source target next.paths with
      | error error => simp [selected] at accepted
      | ok option =>
        cases option with
        | some chosen =>
          simp only [selected, pure, Pure.pure, Except.pure,
            Except.ok.injEq, Option.some.injEq] at accepted
          subst steps
          exact selectPath_formed nextFormed selected
        | none =>
          simp only [selected] at accepted
          split at accepted
          · exact (finish_not_some accepted).elim
          · exact ih nextFormed accepted


/-- Every actual direct, searched or fallback step has formed endpoint types
and obligations. Intermediate targets come from catalog rules and declared
assumptions; the successful search does not supply its own formation premise. -/
theorem coercion_plan_formation {semantic : SourceSemantics.Context} {state : State}
    {context : SourceInference.Context} {source target : Ty}
    {steps : List Detail.PlannedCoercionStep}
    (formation : CoercionFormationContext semantic context)
    (sourceFormed : TypeAdmissible semantic source)
    (targetFormed : TypeAdmissible semantic target)
    (accepted : Detail.coercionPlan? context state source target = .ok (some steps)) :
    ∀ step ∈ steps, PlannedCoercionStepFormed semantic step := by
  unfold Detail.coercionPlan? at accepted
  cases traitResult : Detail.conventionalTraitWithArity? context "Coerce" 2 with
  | error error => simp [traitResult, bind, Except.bind] at accepted
  | ok option =>
    cases option with
    | none => simp [traitResult, bind, Except.bind] at accepted
    | some trait =>
      simp only [traitResult, bind, Except.bind] at accepted
      cases profileResult : Detail.coercionMethodProfile? context trait with
      | error error => simp [profileResult] at accepted
      | ok profile =>
        simp only [profileResult] at accepted
        cases methodResult : Detail.coercionMethodPredicates profile source target with
        | error error => simp [methodResult] at accepted
        | ok methods =>
          simp only [methodResult] at accepted
          have methodsFormed := coercion_issuance formation.catalog sourceFormed.binders
            formation.signatures sourceFormed targetFormed profileResult methodResult
          let direct : ProgramPredicate := {trait, subject := source, arguments := [target]}
          let directStep : Detail.PlannedCoercionStep := {
            source, target, predicate := direct, methodPredicates := methods
          }
          have directFormed : PlannedCoercionStepFormed semantic directStep :=
            ⟨sourceFormed, targetFormed, methodsFormed.1, methodsFormed.2⟩
          change (match Detail.coercionEvidenceViable context state direct methods with
            | .ok true => Except.ok (some [directStep])
            | .ok false => do
                match ← Detail.searchCoercionPaths context state profile trait source target
                  context.coercionDepth [{current := source, visited := [source], steps := []}] [] with
                | some searched => pure (some searched)
                | none => pure (some [directStep])
            | .error error => Except.error error) = Except.ok (some steps) at accepted
          cases viable : Detail.coercionEvidenceViable context state direct methods with
          | error error => simp [viable] at accepted
          | ok value =>
            cases value with
            | true =>
              simp only [viable, Except.ok.injEq, Option.some.injEq] at accepted
              subst steps
              intro step member
              cases List.mem_singleton.mp member
              exact directFormed
            | false =>
              simp only [viable] at accepted
              cases searched : Detail.searchCoercionPaths context state profile trait source target
                  context.coercionDepth [{current := source, visited := [source], steps := []}] [] with
              | error error => simp [searched, bind, Except.bind] at accepted
              | ok found =>
                cases found with
                | none =>
                  simp only [searched, bind, Except.bind, pure, Pure.pure, Except.pure,
                    Except.ok.injEq, Option.some.injEq] at accepted
                  subst steps
                  intro step member
                  cases List.mem_singleton.mp member
                  exact directFormed
                | some chosen =>
                  simp only [searched, bind, Except.bind, pure, Pure.pure, Except.pure,
                    Except.ok.injEq, Option.some.injEq] at accepted
                  subst steps
                  apply searchPaths_formed _ formation profileResult _ searched
                  intro path member
                  cases List.mem_singleton.mp member
                  exact ⟨sourceFormed, by simp⟩

end Solcore.SourceSemantics.SourceInferenceRequirementFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceCoercionIssuedFormation
/-! The committed rows retain formation from the actual selected coercion plan. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceRequirementFormation
open Frontend SourceInference TypeSystem

private theorem requirementBatch_row_origin (state : State) (predicates : List ProgramPredicate)
    {row : Requirement} (member : row ∈ (state.addRequirementsWithIds predicates).2.requirements) :
    row ∈ state.requirements ∨ row.predicate ∈ predicates := by
  induction predicates generalizing state with
  | nil => exact .inl member
  | cons head tail ih =>
    rcases ih (state.addRequirementWithId head).2 member with old | new
    · rcases List.mem_append.mp old with old | fresh
      · exact .inl old
      · cases List.mem_singleton.mp fresh
        exact .inr List.mem_cons_self
    · exact .inr (List.mem_cons_of_mem _ new)

/-- A newly committed row is the actual primary predicate or one of the
actual method predicates of a selected step. -/
theorem committed_coercion_requirement_origin (state : State)
    (steps : List Detail.PlannedCoercionStep) {row : Requirement}
    (member : row ∈ (Detail.commitCoercionPlan state steps).2.requirements) :
    row ∈ state.requirements ∨ ∃ step ∈ steps,
      row.predicate = step.predicate ∨ row.predicate ∈ step.methodPredicates := by
  induction steps generalizing state with
  | nil => exact .inl member
  | cons step rest ih =>
    rcases ih _ member with old | fresh
    · rcases requirementBatch_row_origin _ _ old with old | method
      · rcases List.mem_append.mp old with old | primary
        · exact .inl old
        · cases List.mem_singleton.mp primary
          exact .inr ⟨step, List.mem_cons_self, .inl rfl⟩
      · exact .inr ⟨step, List.mem_cons_self, .inr method⟩
    · obtain ⟨origin, originMember, occurrence⟩ := fresh
      exact .inr ⟨origin, List.mem_cons_of_mem _ originMember, occurrence⟩

/-- A new ledger row is formed because its exact selected producer is formed. -/
theorem committed_coercion_new_formation {semantic : SourceSemantics.Context} {state : State}
    {steps : List Detail.PlannedCoercionStep}
    (stepsFormed : ∀ step ∈ steps, PlannedCoercionStepFormed semantic step)
    {row : Requirement}
    (member : row ∈ (Detail.commitCoercionPlan state steps).2.requirements)
    (fresh : row ∉ state.requirements) : PredicateAdmissible semantic row.predicate := by
  rcases committed_coercion_requirement_origin state steps member with old | new
  · exact (fresh old).elim
  · obtain ⟨step, stepMember, primary | method⟩ := new
    · exact primary ▸ (stepsFormed step stepMember).2.2.1
    · exact (stepsFormed step stepMember).2.2.2 row.predicate method

/-- Successful expected fitting either preserves the requirement ledger or
commits the actual search result. The normalized operand and expected type
are supplied by the enclosing expression derivation. -/
theorem withExpected_new_requirements_formation
    {semantic : SourceSemantics.Context} {context : SourceInference.Context}
    {state : State} {actual : InferredExpression} {expected : Option Ty}
    {result : Detail.ExpectationResult}
    (formation : CoercionFormationContext semantic context)
    (actualFormed : TypeAdmissible semantic (state.resolve actual.type))
    (expectedFormed : ∀ type ∈ expected, TypeAdmissible semantic (state.resolve type))
    (accepted : Detail.withExpected context state actual expected = .ok result) :
    ∀ row ∈ result.state.requirements, row ∉ state.requirements →
      PredicateAdmissible semantic row.predicate := by
  cases expected with
  | none =>
    simp only [Detail.withExpected, Except.ok.injEq] at accepted
    cases accepted
    exact fun row member fresh => (fresh member).elim
  | some expected =>
    have expectedFormed := expectedFormed expected (by simp)
    cases unified : state.inference.unify actual.type expected with
    | ok inference =>
      simp only [Detail.withExpected, unified, Except.ok.injEq] at accepted
      cases accepted
      exact fun row member fresh => (fresh member).elim
    | error error =>
      cases error with
      | occursCheck _ _ => simp [Detail.withExpected, unified] at accepted
      | exhausted => simp [Detail.withExpected, unified] at accepted
      | mismatch left right =>
        simp only [Detail.withExpected, unified] at accepted
        cases planned : Detail.coercionPlan? context state
            (state.resolve actual.type) (state.resolve expected) with
        | error error => simp [planned, bind, Except.bind] at accepted
        | ok option =>
          cases option with
          | none => simp [planned, bind, Except.bind] at accepted
          | some plan =>
            simp only [planned, bind, Except.bind] at accepted
            change Except.ok _ = Except.ok result at accepted
            cases Except.ok.inj accepted
            exact fun _ member fresh => committed_coercion_new_formation
              (coercion_plan_formation formation actualFormed expectedFormed planned) member fresh

end Solcore.SourceSemantics.SourceInferenceRequirementFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceRequirementSubstitution
/-! Residual-aware formation transport for requirements and finalizer ranges. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceRequirementFormation

open Frontend SourceInference TypeSystem
open SourceInferenceSoundness

private theorem mem_freeVariables_foldl_application_iff
    (metavariable : TypeVarId) (head : Ty) (arguments : List Ty) :
    metavariable ∈ (arguments.foldl Ty.application head).freeVariables ↔
      metavariable ∈ head.freeVariables ∨
        ∃ argument, argument ∈ arguments ∧
          metavariable ∈ argument.freeVariables := by
  induction arguments generalizing head with
  | nil => simp
  | cons argument arguments induction =>
      rw [List.foldl_cons, induction,
        SourceSemantics.mem_freeVariables_application_iff]
      simp only [List.mem_cons]
      constructor
      · rintro ((headMember | argumentMember) | tailMember)
        · exact Or.inl headMember
        · exact Or.inr ⟨argument, Or.inl rfl, argumentMember⟩
        · rcases tailMember with ⟨candidate, candidateMember, occurs⟩
          exact Or.inr ⟨candidate, Or.inr candidateMember, occurs⟩
      · rintro (headMember | ⟨candidate, candidateMember, occurs⟩)
        · exact Or.inl (Or.inl headMember)
        · rcases candidateMember with rfl | candidateMember
          · exact Or.inl (Or.inr occurs)
          · exact Or.inr ⟨candidate, candidateMember, occurs⟩

private theorem mem_freeVariables_nominal_iff
    {metavariable : TypeVarId} {declaration : Resolved.DeclarationId}
    {arguments : List Ty} :
    metavariable ∈ (Ty.nominal declaration arguments).freeVariables ↔
      ∃ argument, argument ∈ arguments ∧
        metavariable ∈ argument.freeVariables := by
  rw [Ty.nominal, Ty.applyMany,
    mem_freeVariables_foldl_application_iff]
  simp [Ty.freeVariables]

private theorem TypesWellScoped.ofEachAdmissibleWithin
    {context : Context} {types : List Ty} {outer : Ty}
    (admissible : ∀ type, type ∈ types → TypeAdmissible context type)
    (included : ∀ type, type ∈ types →
      ∀ metavariable, metavariable ∈ type.freeVariables →
        metavariable ∈ outer.freeVariables) :
    TypesWellScoped context (admissibleTypeVariables context outer) types := by
  induction types with
  | nil => exact .nil
  | cons head tail induction =>
      exact .cons
        (TypeAdmissible.typeWellScopedWithin
          (included head (by simp)) (admissible head (by simp)))
        (induction
          (fun type member => admissible type (by simp [member]))
          (fun type member => included type (by simp [member])))

/-- An admissible flexible range preserves type formation in a context that
admits residual variables. No groundness or substitution-domain coverage is needed. -/
theorem type_applySubstitution_residual
    {context : SourceSemantics.Context} {type : Ty}
    {substitution : Substitution}
    (residual : context.residualTypeVariables = true)
    (range : SubstitutionRangeAdmissible context substitution)
    (formed : TypeAdmissible context type) :
    TypeAdmissible context (substitution.apply type) := by
  have binders := formed.binders
  refine TypeWellScoped.rec
    (motive_1 := fun current _ => TypeAdmissible context (substitution.apply current))
    (motive_2 := fun types _ => ∀ current ∈ types,
      TypeAdmissible context (substitution.apply current))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ formed.typeWellScoped
  · intro metavariable _
    cases found : substitution.lookup? metavariable with
    | none =>
        simpa [Substitution.apply, found] using
          TypeAdmissible.variableOfResidual binders residual metavariable
    | some replacement =>
        simpa [Substitution.apply, found] using
          range metavariable replacement (Substitution.lookup?_eq_some_mem found)
  · intro parameter bound owned
    exact ⟨binders, .parameter bound owned⟩
  · intro builtin
    exact TypeAdmissible.builtin binders builtin
  · intro dataType arguments cataloged arity _ argumentInduction
    rw [StructuralSubstitution.applyFlexible_nominal]
    refine ⟨binders, .nominal dataType (arguments.map substitution.apply)
      cataloged (by simpa using arity) ?_⟩
    apply TypesWellScoped.ofEachAdmissibleWithin
    · intro argument member
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
      exact argumentInduction original originalMember
    · intro argument member metavariable occurs
      exact mem_freeVariables_nominal_iff.mpr
        ⟨argument, member, occurs⟩
  · intro contract arguments cataloged arity _ argumentInduction
    rw [StructuralSubstitution.applyFlexible_nominal]
    refine ⟨binders, .contractNominal contract (arguments.map substitution.apply)
      cataloged (by simpa using arity) ?_⟩
    apply TypesWellScoped.ofEachAdmissibleWithin
    · intro argument member
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
      exact argumentInduction original originalMember
    · intro argument member metavariable occurs
      exact mem_freeVariables_nominal_iff.mpr
        ⟨argument, member, occurs⟩
  · intro parameter result _ _ parameterInduction resultInduction
    exact TypeAdmissible.function parameterInduction resultInduction
  · intro left right _ _ leftInduction rightInduction
    exact TypeAdmissible.product leftInduction rightInduction
  · intro key value _ _ keyInduction valueInduction
    exact TypeAdmissible.mapping keyInduction valueInduction
  · intro inner _ innerInduction
    exact TypeAdmissible.proxy innerInduction
  · intro inner _ innerInduction
    exact TypeAdmissible.comptime innerInduction
  · intro current member
    simp at member
  · intro head tail _ _ headInduction tailInduction current member
    rcases List.mem_cons.mp member with rfl | member
    · exact headInduction
    · exact tailInduction current member

/-- Predicate component formation survives an admissible flexible
substitution in the residual context used for generalized initializers. -/
theorem predicate_applySubstitution_residual
    {context : SourceSemantics.Context} {predicate : ProgramPredicate}
    {substitution : Substitution}
    (residual : context.residualTypeVariables = true)
    (range : SubstitutionRangeAdmissible context substitution)
    (formed : PredicateAdmissible context predicate) :
    PredicateAdmissible context
      (TypedTraitResolution.applySubstitution substitution predicate) := by
  constructor
  · exact type_applySubstitution_residual residual range formed.subject
  · intro argument member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    exact type_applySubstitution_residual residual range
      (formed.arguments original originalMember)
  · cases traitEq : predicate.trait with
    | builtin builtin =>
        cases builtin
        have valid := formed.trait
        rw [traitEq] at valid
        simpa [TypedTraitResolution.applySubstitution, traitEq] using valid
    | declaration id =>
        have valid := formed.trait
        rw [traitEq] at valid
        obtain ⟨signature, member, idEq, arity⟩ := valid
        simp only [TypedTraitResolution.applySubstitution, traitEq]
        exact ⟨signature, member, idEq, by simpa using arity⟩

/-- A residual target can change lexical flexible scope while retaining the
same rigid declaration binders and signature catalog. -/
theorem predicate_transport_residual
    {source target : SourceSemantics.Context} {predicate : ProgramPredicate}
    (binders : TypeParameterBindersWellFormed target)
    (signatures : target.signatures = source.signatures)
    (parameters : target.typeParameters = source.typeParameters)
    (owner : target.currentDeclaration = source.currentDeclaration)
    (residual : target.residualTypeVariables = true)
    (formed : PredicateAdmissible source predicate) :
    PredicateAdmissible target predicate := by
  constructor
  · exact StructuralSubstitution.TypeWellScoped.toAdmissibleOfResidual binders residual
      (StructuralSubstitution.TypeWellScoped.transportContext signatures parameters owner
        formed.subject.typeWellScoped)
  · intro argument member
    exact StructuralSubstitution.TypeWellScoped.toAdmissibleOfResidual binders residual
      (StructuralSubstitution.TypeWellScoped.transportContext signatures parameters owner
        (formed.arguments argument member).typeWellScoped)
  · cases traitEq : predicate.trait with
    | builtin builtin =>
        cases builtin
        simpa only [traitEq] using formed.trait
    | declaration id =>
        have valid := formed.trait
        rw [traitEq] at valid
        obtain ⟨signature, member, idEq, arity⟩ := valid
        simpa only [traitEq] using
          (show ∃ signature ∈ target.signatures.traits,
            signature.id = id ∧ predicate.arguments.length + 1 = signature.parameters.length from
            ⟨signature, signatures.symm ▸ member, idEq, arity⟩)

/-- Removing quantified quantifiers from an admissible substitution does not
introduce new replacements. -/
theorem range_without {context : SourceSemantics.Context}
    {substitution : Substitution}
    (range : SubstitutionRangeAdmissible context substitution)
    (quantified : List TypeVarId) :
    SubstitutionRangeAdmissible context (substitution.without quantified) :=
  fun metavariable replacement member =>
    range metavariable replacement (Substitution.mem_of_mem_without member)

/-- Actual finalization provides the replacement formation needed to normalize
an issued predicate. This uses its range validator without assuming ground types. -/
theorem finalizer_predicate_formation
    {inferenceContext : Frontend.SourceInference.Context}
    {type : Ty} {state : State} {roots : List NodeId}
    {result : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources inferenceContext type state roots result)
    {context : SourceSemantics.Context} {predicate : ProgramPredicate}
    (binders : TypeParameterBindersWellFormed context)
    (signatures : context.signatures = inferenceContext.signatures)
    (parameters : context.typeParameters = inferenceContext.typeParameters)
    (owner : context.currentDeclaration = some inferenceContext.scope.genericOwner)
    (residual : context.residualTypeVariables = true)
    (formed : PredicateAdmissible context predicate)
    (quantified : List TypeVarId) :
    PredicateAdmissible context (TypedTraitResolution.applySubstitution
      (result.substitution.without quantified) predicate) :=
  predicate_applySubstitution_residual residual
    (range_without (InferenceSubstitutionRangeFormationValidated.rangeAdmissible
      resources.range_formation binders signatures parameters owner residual) quantified)
    formed

end Solcore.SourceSemantics.SourceInferenceRequirementFormation
end
