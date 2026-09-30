import Solcore.SourceSemantics.SourceInferenceSoundness

/-!
The executable `generalizeValue` result is connected to the semantic
certificate for an unannotated initialized `let`.  Initializer typing is kept
as an explicit premise; qualified-template evidence, the exact generalization
barrier, and freshness of previously retained scheme binders are stated at
the points where they enter the proof.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend SourceInference TypeSystem

/-- A retained statement may own an initialized binder directly or through
one of its `for`-header items.  Every corresponding qualified row remains an
exact template site after append-only raw source growth. -/
theorem containsLocalSchemeTemplate_of_retainedStatementBinding
    {before after : TypedSource} {id : StatementId}
    {node : StatementNode}
    (recorded : ContainsStatement before id node)
    (extension : TypingSourceExtends before after)
    {binding : InitializedLetBinding}
    (bindingMember : binding ∈ statementInitializedLetBindings node.form)
    {requirement : LocalSchemeRequirement}
    (member : requirement ∈ binding.binder.schemeRequirements) :
    ContainsLocalSchemeTemplate after {
      binder := binding.binder
      initializer := binding.initializer
      requirement
    } := by
  have retained := extension.containsStatement recorded
  unfold ContainsLocalSchemeTemplate localSchemeTemplateOwners
  apply List.mem_flatMap.mpr
  refine ⟨binding, ?_, ?_⟩
  · unfold initializedLetBindings
    exact List.mem_flatMap.mpr ⟨.statement node, retained.1,
      bindingMember⟩
  · simp [InitializedLetBinding.templateOwners, member]

/-- A recorded initialized `let` owns each of its qualified template rows in
every append-only raw source containing that statement.  This is the exact
source occurrence recovered by the one-step branch inversion. -/
theorem containsLocalSchemeTemplate_of_retainedLet
    {before after : TypedSource} {id : StatementId}
    {span : Syntax.SourceSpan} {type : Ty}
    {binder : TypedBinder} {initializer : ExpressionId}
    (recorded : ContainsStatement before id {
      id, span, type, form := .letDecl binder (some initializer) })
    (extension : TypingSourceExtends before after)
    {requirement : LocalSchemeRequirement}
    (member : requirement ∈ binder.schemeRequirements) :
    ContainsLocalSchemeTemplate after {
      binder, initializer := .expression initializer, requirement } := by
  exact containsLocalSchemeTemplate_of_retainedStatementBinding
    (binding := { binder, initializer := .expression initializer }) recorded
    extension (by simp [statementInitializedLetBindings]) member

/-- Scoped requirement evidence is monotone in the available assumptions.
The exact solved rows, signature catalog, and source-owned template sites stay
fixed; only ordinary retained evidence needs assumption weakening. -/
theorem scopedRequirementLedgerWellFormed_weakenAssumptions
    {source target : SourceSemantics.Context} {typedSource : TypedSource}
    (signaturesEq : target.signatures = source.signatures)
    (assumptionsMono : source.assumptions ⊆ target.assumptions)
    (solvedEq : target.solvedRequirements = source.solvedRequirements)
    (wellFormed : ScopedRequirementLedgerWellFormed source typedSource) :
    ScopedRequirementLedgerWellFormed target typedSource := by
  refine {
    idsUnique := ?_
    templateOwnership := wellFormed.templateOwnership
    entriesValid := ?_
    templatesComplete := ?_
  }
  · simpa [RequirementIdsUnique, solvedEq] using wellFormed.idsUnique
  · intro row member
    have sourceMember : row ∈ source.solvedRequirements := by
      simpa [solvedEq] using member
    cases wellFormed.entriesValid row sourceMember with
    | ordinary notTemplate valid =>
        cases valid with
        | intro evidenceValid =>
            exact .ordinary notTemplate (.intro (by
              simpa [signaturesEq] using
                evidenceValid.weakenAssumptions assumptionsMono))
    | template scopeProof => exact .template scopeProof
  · intro owner contains
    obtain ⟨row, member, idEq⟩ :=
      wellFormed.templatesComplete owner contains
    exact ⟨row, by simpa [solvedEq] using member, idEq⟩

/-- The exact non-escape condition needed at one executable generalization:
if a variable from an older local scheme reaches the new inferred value,
the executable barrier must already classify it as blocked.  This is weaker
than requiring old scheme variables never to reach the value at all. -/
def PriorQuantifiersBlockedAt
    (state : Frontend.SourceInference.State)
    (locals : Environment) (requirementStart : Nat) (valueType : Ty)
    (target : SourceSemantics.Context) : Prop :=
  ∀ metavariable, metavariable ∈ valueType.freeVariables →
    ∀ entry, entry ∈ target.locals →
      metavariable ∈ entry.2.quantified →
        metavariable ∈ Detail.generalizeValueBlockedVariables state locals
          requirementStart

/-- A declaration's initial monomorphic input context satisfies the
non-escape condition without inspecting an initializer. -/
theorem priorQuantifiersBlockedAt_of_monomorphicLocals
    (state : Frontend.SourceInference.State)
    (locals : Environment) (requirementStart : Nat) (valueType : Ty)
    (target : SourceSemantics.Context)
    (monomorphic : ∀ entry, entry ∈ target.locals →
      entry.2.quantified = []) :
    PriorQuantifiersBlockedAt state locals requirementStart valueType target := by
  intro metavariable _ entry member quantified
  rw [monomorphic entry member] at quantified
  simp at quantified

/-- Exact executable generalization excludes an old quantified variable
whenever that variable is blocked at the actual inferred value.  The final
flexible substitution leaves the new scheme's quantifier list unchanged. -/
theorem generalizeValue_quantified_fresh_prior_of_blocked
    {state : Frontend.SourceInference.State}
    {locals : Environment} {requirementStart : Nat} {valueType : Ty}
    {target : SourceSemantics.Context} {outer : Substitution}
    {binder : TypedBinder}
    (schemeEq : binder.scheme =
      (Detail.generalizeValue state locals requirementStart valueType).scheme)
    (priorBlocked : PriorQuantifiersBlockedAt state locals requirementStart
      valueType target) :
    ∀ metavariable,
      metavariable ∈ (binder.applySubstitution outer).scheme.quantified →
        ∀ entry, entry ∈ target.locals →
          metavariable ∉ entry.2.quantified := by
  intro metavariable quantified entry entryMember priorQuantified
  have rawQuantified : metavariable ∈ binder.scheme.quantified := by
    simpa [TypedBinder.applySubstitution, Scheme.apply] using quantified
  rw [schemeEq, Detail.generalizeValue_scheme_quantified] at rawQuantified
  obtain ⟨valueMember, selected⟩ := List.mem_filter.mp rawQuantified
  have blocked := priorBlocked metavariable valueMember entry entryMember
    priorQuantified
  have notBlocked :
      metavariable ∉ Detail.generalizeValueBlockedVariables state locals
        requirementStart := by
    simpa using selected
  exact notBlocked blocked

/-- The three non-expression fields of an initialized-let certificate follow
from exact executable generalization, the closing context, final scoped
requirement evidence, and freshness against older retained scheme binders. -/
theorem unannotatedInitializedLetCertificate_of_generalizeValue
    {inferenceContext : Frontend.SourceInference.Context}
    {finalType : Ty}
    {evidenceState : Frontend.SourceInference.State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources inferenceContext finalType
      evidenceState roots finalized)
    {source : TypedSource}
    {sourceContext target : SourceSemantics.Context}
    {outer : Substitution} {closedVariables : List TypeVarId}
    {state final : Frontend.SourceInference.State}
    {locals : Environment} {requirementStart : Nat} {valueType : Ty}
    {generalized : Detail.GeneralizedValue}
    {name : Syntax.Identifier} {binder : TypedBinder}
    {initializer : ExpressionId}
    (outerEq : outer = finalized.substitution)
    (generalizedEq : generalized = Detail.generalizeValue state locals
      requirementStart valueType)
    (allocated : (state.withLocals locals).allocateBinder name.value
      generalized.scheme (some name.span) false generalized.requirements =
        (binder, final))
    (closes : FlexibleSubstitution.ContextCloses outer closedVariables
      sourceContext target)
    (barrier : ∀ metavariable,
      metavariable ∈ valueType.freeVariables →
        (metavariable ∈ Detail.generalizeValueBlockedVariables state locals
          requirementStart ↔
          metavariable ∈ GeneralizationBlockedVariablesExcept sourceContext
            ((Detail.generalizeValue state locals requirementStart valueType
              ).requirements.map fun requirement =>
                requirement.templateRequirement)))
    (signaturesEq : target.signatures =
      (finalizedRequirementContext inferenceContext finalized).signatures)
    (assumptionsMono :
      (finalizedRequirementContext inferenceContext finalized).assumptions ⊆
        target.assumptions)
    (solvedEq : target.solvedRequirements =
      (finalizedRequirementContext inferenceContext finalized
        ).solvedRequirements)
    {statementId : StatementId} {span : Syntax.SourceSpan}
    {statementType : Ty}
    (recorded : ContainsStatement source statementId {
      id := statementId
      span
      type := statementType
      form := .letDecl binder (some initializer)
    })
    (rawExtension : TypingSourceExtends source
      (evidenceState.toTypedSource roots))
    (predicates : ∀ requirement,
      requirement ∈ binder.schemeRequirements →
        PredicateAdmissible
          (localSchemeInitializerContext sourceContext binder)
          requirement.predicate)
    (priorBlocked : PriorQuantifiersBlockedAt state locals requirementStart
      valueType target)
    (initializerType : ExpressionHasType (source.applySubstitution outer)
      (localSchemeInitializerContext target
        (binder.applySubstitution outer)) initializer
      (binder.applySubstitution outer).scheme.body) :
    UnannotatedInitializedLetCertificate source target outer binder
      initializer := by
  have binderEq :
      ((state.withLocals locals).allocateBinder name.value
        generalized.scheme (some name.span) false
        generalized.requirements).1 = binder :=
    congrArg Prod.fst allocated
  have rawSchemeEq0 : binder.scheme = generalized.scheme := by
    rw [← binderEq]
    rfl
  have rawRequirementsEq0 : binder.schemeRequirements =
      generalized.requirements := by
    rw [← binderEq]
    rfl
  have rawSchemeEq : binder.scheme =
      (Detail.generalizeValue state locals requirementStart
        valueType).scheme := by
    rw [rawSchemeEq0, generalizedEq]
  have rawRequirementsEq : binder.schemeRequirements =
      (Detail.generalizeValue state locals requirementStart
        valueType).requirements := by
    rw [rawRequirementsEq0, generalizedEq]
  have freshPrior := generalizeValue_quantified_fresh_prior_of_blocked
    (outer := outer) rawSchemeEq priorBlocked
  have canonicalGeneralizes :=
    generalizeValue_schemeGeneralizesExcept_of_barrier state locals
      requirementStart valueType sourceContext barrier
  have rawGeneralizes : SchemeGeneralizesExcept sourceContext
      (localSchemeTemplateIds binder) binder.scheme := by
    simpa [localSchemeTemplateIds, rawSchemeEq, rawRequirementsEq] using
      canonicalGeneralizes
  have freshDomain : ∀ metavariable,
      metavariable ∈ binder.scheme.quantified →
        metavariable ∉ outer.domain := by
    intro metavariable quantified domainMember
    have notAmbient := FlexibleSubstitution.SchemeGeneralizesExcept.quantified_fresh
      rawGeneralizes metavariable quantified
    apply notAmbient
    rw [closes.variables_eq]
    exact List.mem_append.mpr (Or.inl
      ((closes.exact.mem_domain_iff metavariable).mp domainMember))
  have closedGeneralizes : SchemeGeneralizesExcept target
      (localSchemeTemplateIds (binder.applySubstitution outer))
      (binder.applySubstitution outer).scheme := by
    have transported := FlexibleSubstitution.SchemeGeneralizesExcept.applySubstitution closes
      rawGeneralizes
    have restrictedEq : outer.without binder.scheme.quantified = outer :=
      FlexibleSubstitution.Substitution.without_eq_self_of_disjoint_domain outer
        binder.scheme.quantified freshDomain
    rw [FlexibleSubstitution.localSchemeTemplateIds_applySubstitution]
    simpa [TypedBinder.applySubstitution, restrictedEq] using transported
  have ledgerFinal : ScopedRequirementLedgerWellFormed target
      finalized.typedSource :=
    scopedRequirementLedgerWellFormed_weakenAssumptions signaturesEq
      assumptionsMono solvedEq resources.ledger
  have ledgerRaw : ScopedRequirementLedgerWellFormed target
      ((evidenceState.toTypedSource roots).applySubstitution outer) := by
    rw [outerEq, ← resources.source_eq]
    exact ledgerFinal
  have contains : ∀ requirement,
      requirement ∈ binder.schemeRequirements →
        ContainsLocalSchemeTemplate (evidenceState.toTypedSource roots) {
          binder
          initializer := .expression initializer
          requirement
        } := by
    intro requirement member
    exact containsLocalSchemeTemplate_of_retainedLet recorded rawExtension
      member
  have formation := generalizeValue_binderFormation_afterSubstitution
    state locals requirementStart valueType rawSchemeEq rawRequirementsEq
    closes freshDomain ledgerRaw contains predicates
    initializerType.type_admissible
  refine {
    initializer_type := initializerType
    requirements_well_formed := formation.2
    generalizes := closedGeneralizes
    quantified_fresh := ?_
  }
  intro metavariable quantified
  exact ⟨FlexibleSubstitution.SchemeGeneralizesExcept.quantified_fresh closedGeneralizes
    metavariable quantified, freshPrior metavariable quantified⟩

/-- A genuinely closed inferred value is the fully discharged monomorphic
case: executable generalization cannot retain a qualified template row or
introduce a quantified variable.  No context-closure, barrier, or template
ownership premise is needed for this branch. -/
theorem unannotatedInitializedLetCertificate_of_closedValue
    {source : TypedSource} {target : SourceSemantics.Context}
    {outer : Substitution}
    {state final : Frontend.SourceInference.State}
    {locals : Environment} {requirementStart : Nat} {valueType : Ty}
    {generalized : Detail.GeneralizedValue}
    {name : Syntax.Identifier} {binder : TypedBinder}
    {initializer : ExpressionId}
    (generalizedEq : generalized = Detail.generalizeValue state locals
      requirementStart valueType)
    (allocated : (state.withLocals locals).allocateBinder name.value
      generalized.scheme (some name.span) false generalized.requirements =
        (binder, final))
    (closed : valueType.freeVariables = [])
    (initializerType : ExpressionHasType (source.applySubstitution outer)
      (localSchemeInitializerContext target
        (binder.applySubstitution outer)) initializer
      (binder.applySubstitution outer).scheme.body) :
    UnannotatedInitializedLetCertificate source target outer binder
      initializer := by
  have binderEq :
      ((state.withLocals locals).allocateBinder name.value
        generalized.scheme (some name.span) false
        generalized.requirements).1 = binder :=
    congrArg Prod.fst allocated
  have rawSchemeEq : binder.scheme = .mono valueType := by
    rw [← binderEq]
    exact (generalizedEq ▸
      (generalizeValue_closed_facts state locals requirementStart valueType
        target closed).1)
  have rawRequirementsEq : binder.schemeRequirements = [] := by
    rw [← binderEq]
    exact (generalizedEq ▸
      (generalizeValue_closed_facts state locals requirementStart valueType
        target closed).2.1)
  have finalSchemeEq : (binder.applySubstitution outer).scheme =
      .mono valueType := by
    simp only [TypedBinder.applySubstitution, rawSchemeEq]
    apply FlexibleSubstitution.Scheme.apply_eq_self_of_domain_disjoint_freeVariables
    intro metavariable _ occurs
    simp [Scheme.freeVariables, Scheme.mono, closed] at occurs
  have finalRequirementsEq :
      (binder.applySubstitution outer).schemeRequirements = [] := by
    simp [TypedBinder.applySubstitution, rawRequirementsEq]
  refine {
    initializer_type := initializerType
    requirements_well_formed :=
      LocalSchemeRequirementsWellFormed.empty target
        (binder.applySubstitution outer) finalRequirementsEq
    generalizes := ?_
    quantified_fresh := ?_
  }
  · change SchemeGeneralizesExcept target
        (localSchemeTemplateIds (binder.applySubstitution outer))
        (binder.applySubstitution outer).scheme
    rw [finalSchemeEq]
    have idsEmpty :
        localSchemeTemplateIds (binder.applySubstitution outer) = [] := by
      simp [localSchemeTemplateIds, rawRequirementsEq]
    rw [idsEmpty]
    simp [SchemeGeneralizesExcept, Scheme.mono, closed]
  · change SchemeQuantifiersFresh target
        (binder.applySubstitution outer).scheme
    rw [finalSchemeEq]
    simp [SchemeQuantifiersFresh, Scheme.mono]

end Solcore.SourceSemantics.SourceInferenceSoundness
