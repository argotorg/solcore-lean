import Solcore.SourceSemantics.SourceInferenceRecursiveSoundness
import Solcore.SourceSemantics.SourceInferenceUnannotatedLetCertificate

/-!
An actual-success, two-source contract for restricted `for` headers.  The
single-item theorem is the remaining syntax-directed obligation; the list
theorem below threads its semantic context, finalization evidence, and raw
source provenance through the actual source-ordered traversal.  No callback
asserts typing for an arbitrary expression unrelated to an inferred item.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem
open SourceInferenceStatementsSoundness

/-- A generalized header-let initializer is checked under its own
qualified assumptions.  Other header references use the ordinary ambient
context.  In particular, requiring the generalized initializer to be covered
under the ambient context would be false. -/
def forItemCoverageContext (outer : Substitution)
    (context : SourceSemantics.Context) (item : ForItemForm) :
    SourceSemantics.Context :=
  match item with
  | .letDecl binder (some _) =>
      localSchemeInitializerContext context (binder.applySubstitution outer)
  | _ => context

/-- Coverage for each actual expression occurrence referenced by one
inferred `for` item, using the initializer's qualified context when needed. -/
def ForItemReferencesCovered (source : TypedSource) (outer : Substitution)
    (context : SourceSemantics.Context) (item : ForItemForm) : Prop :=
  ∀ reference, reference ∈ item.references →
    TemplateScopeCovered source
      (forItemCoverageContext outer context item) reference

/-- Coverage for source-ordered items; each initialized let has its own
qualified initializer context. -/
def ForItemsReferencesCovered (source : TypedSource) (outer : Substitution)
    (context : SourceSemantics.Context) (items : List ForItemForm) : Prop :=
  ∀ item, item ∈ items → ForItemReferencesCovered source outer context item

/-- Lexical binder extension leaves the assumptions relevant to coverage
unchanged, including after entering a qualified initializer context. -/
theorem forItemCoverageContext_assumptions_eq
    (outer : Substitution) (item : ForItemForm)
    {before after : SourceSemantics.Context}
    (assumptionsEq : after.assumptions = before.assumptions) :
    (forItemCoverageContext outer after item).assumptions =
      (forItemCoverageContext outer before item).assumptions := by
  cases item with
  | letDecl binder initializer =>
      cases initializer <;>
        simp [forItemCoverageContext, localSchemeInitializerContext,
          SourceSemantics.Context.withTypeVariables,
          SourceSemantics.Context.withAssumptions, assumptionsEq]
  | expression expression => simp [forItemCoverageContext, assumptionsEq]
  | assignValue assignment operator value =>
      simp [forItemCoverageContext, assumptionsEq]
  | assignBitNot assignment =>
      simp [forItemCoverageContext, assumptionsEq]

theorem ForItemReferencesCovered.transportAssumptions
    {source : TypedSource} {outer : Substitution}
    {before after : SourceSemantics.Context} {item : ForItemForm}
    (covered : ForItemReferencesCovered source outer before item)
    (assumptionsEq : after.assumptions = before.assumptions) :
    ForItemReferencesCovered source outer after item := by
  intro reference member owner scopes
  rw [forItemCoverageContext_assumptions_eq outer item assumptionsEq]
  exact covered reference member owner scopes

/-- Raw ownership required by finalization for an initialized `for`-header
let.  The enclosing loop node, not the header item itself, must supply this
fact; it is independent of expression-reference coverage. -/
def ForItemBindingRetained (source : TypedSource)
    (item : ForItemForm) : Prop :=
  ∀ binding, binding ∈ forItemInitializedLetBindings item →
    binding.binder ∈ source.initializedLetBinders ∧
      ∀ requirement, requirement ∈ binding.binder.schemeRequirements →
        ContainsLocalSchemeTemplate source {
          binder := binding.binder,
          initializer := binding.initializer,
          requirement }

/-- Ownership for every initialized header binder in traversal order. -/
def ForItemsBindingsRetained (source : TypedSource)
    (items : List ForItemForm) : Prop :=
  ∀ binding, binding ∈ items.flatMap forItemInitializedLetBindings →
    binding.binder ∈ source.initializedLetBinders ∧
      ∀ requirement, requirement ∈ binding.binder.schemeRequirements →
        ContainsLocalSchemeTemplate source {
          binder := binding.binder,
          initializer := binding.initializer,
          requirement }

/-- Every initialized binding enumerated for an individual header item is
also included in the finalizer's binder inventory for that item. -/
theorem forItemInitializedLetBindings_binder_mem
    {item : ForItemForm} {binding : InitializedLetBinding}
    (member : binding ∈ forItemInitializedLetBindings item) :
    binding.binder ∈ item.initializedLetBinders := by
  cases item with
  | letDecl binder initializer =>
      cases initializer with
      | none => simp [forItemInitializedLetBindings] at member
      | some initializer =>
          simp [forItemInitializedLetBindings] at member
          subst binding
          simp [ForItemForm.initializedLetBinders]
  | expression expression => simp [forItemInitializedLetBindings] at member
  | assignValue assignment operator value =>
      simp [forItemInitializedLetBindings] at member
  | assignBitNot assignment =>
      simp [forItemInitializedLetBindings] at member

/-- The actual enclosing `for` occurrence supplies finalizer ownership for
both source-ordered header lists.  This is the discharge of the ownership
premise in `InferForItemsFuelScopedSoundness`; it cannot be obtained from a
header item's expression references alone. -/
theorem forItemsBindingsRetained_of_containedForLoop
    {before after : TypedSource} {id : StatementId}
    {span : Syntax.SourceSpan} {type : Ty}
    {initializer post : List ForItemForm}
    {condition : ExpressionId} {body : List StatementId}
    (recorded : ContainsStatement before id {
      id, span, type, form := .forLoop initializer condition post body })
    (extension : TypingSourceExtends before after) :
    ForItemsBindingsRetained after initializer ∧
      ForItemsBindingsRetained after post := by
  have retained := extension.containsStatement recorded
  constructor
  · intro binding member
    have formMember : binding ∈ statementInitializedLetBindings
        (.forLoop initializer condition post body) := by
      simp only [statementInitializedLetBindings, List.mem_append]
      exact Or.inl member
    have binderMember : binding.binder ∈
        (StatementForm.forLoop initializer condition post body
          ).initializedLetBinders := by
      rcases List.mem_flatMap.mp member with
        ⟨item, itemMember, bindingMember⟩
      simp only [StatementForm.initializedLetBinders, List.mem_append]
      exact Or.inl (List.mem_flatMap.mpr
        ⟨item, itemMember,
          forItemInitializedLetBindings_binder_mem bindingMember⟩)
    constructor
    · exact retained.initializedLetBinder_mem binderMember
    · intro requirement requirementMember
      exact containsLocalSchemeTemplate_of_retainedStatementBinding
        recorded extension formMember requirementMember
  · intro binding member
    have formMember : binding ∈ statementInitializedLetBindings
        (.forLoop initializer condition post body) := by
      simp only [statementInitializedLetBindings, List.mem_append]
      exact Or.inr member
    have binderMember : binding.binder ∈
        (StatementForm.forLoop initializer condition post body
          ).initializedLetBinders := by
      rcases List.mem_flatMap.mp member with
        ⟨item, itemMember, bindingMember⟩
      simp only [StatementForm.initializedLetBinders, List.mem_append]
      exact Or.inr (List.mem_flatMap.mpr
        ⟨item, itemMember,
          forItemInitializedLetBindings_binder_mem bindingMember⟩)
    constructor
    · exact retained.initializedLetBinder_mem binderMember
    · intro requirement requirementMember
      exact containsLocalSchemeTemplate_of_retainedStatementBinding
        recorded extension formMember requirementMember

/-- The only expression child of an expression header item is the one
actually traversed by its successful parent computation. -/
theorem inferForItemFuel_success_expression_facts
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {item : Syntax.ForItem} {expression : Syntax.Expr}
    {initial : State} {result : ForItemForm × State}
    (itemEq : item.value = .expression expression)
    (success : Detail.inferForItemFuel (fuel + 1) inferenceContext item
      initial = .ok result) :
    ∃ inferred resultState,
      Detail.inferExprFuel fuel inferenceContext expression none initial =
        .ok (inferred, resultState) ∧
      result = (.expression inferred.id, resultState) := by
  unfold Detail.inferForItemFuel at success
  simp only [itemEq, bind, Except.bind] at success
  cases childSuccess : Detail.inferExprFuel fuel inferenceContext expression
      none initial with
  | error error => simp [childSuccess] at success
  | ok child =>
      rcases child with ⟨inferred, resultState⟩
      simp only [childSuccess, pure, Pure.pure, Except.pure] at success
      injection success with resultEq
      rw [← resultEq]
      exact ⟨inferred, resultState, rfl, rfl⟩

/-- A value-assignment header item has exactly one assigned-value child
traversal.  The returned value occurrence is the one selected by that
traversal, rather than an arbitrary successful expression. -/
theorem inferForItemFuel_success_assignValue_facts
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {item : Syntax.ForItem} {target value : Syntax.Expr}
    {operator : Syntax.Located Syntax.ValueAssignOp}
    {initial : State} {result : ForItemForm × State}
    (itemEq : item.value = .assignValue target operator value)
    (success : Detail.inferForItemFuel (fuel + 1) inferenceContext item
      initial = .ok result) :
    ∃ assignment inferredValue resultState,
      Detail.inferAssignedValueFuel fuel inferenceContext target
        operator.value value initial =
          .ok (assignment, inferredValue, resultState) ∧
      result = (.assignValue assignment operator.value inferredValue.id,
        resultState) := by
  unfold Detail.inferForItemFuel at success
  simp only [itemEq, bind, Except.bind] at success
  cases childSuccess : Detail.inferAssignedValueFuel fuel inferenceContext
      target operator.value value initial with
  | error error => simp [childSuccess] at success
  | ok child =>
      rcases child with ⟨assignment, inferredValue, resultState⟩
      simp only [childSuccess, pure, Pure.pure, Except.pure] at success
      injection success with resultEq
      rw [← resultEq]
      exact ⟨assignment, inferredValue, resultState, rfl, rfl⟩

/-- A bit-not assignment first infers its actual place and then performs
the word-type unification.  Keeping both equalities is essential: the final
state may be later than the place state even though no expression id changes. -/
theorem inferForItemFuel_success_assignBitNot_facts
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {item : Syntax.ForItem} {target : Syntax.Expr}
    {operatorSpan : Syntax.SourceSpan}
    {initial : State} {result : ForItemForm × State}
    (itemEq : item.value = .assignBitNot target operatorSpan)
    (success : Detail.inferForItemFuel (fuel + 1) inferenceContext item
      initial = .ok result) :
    ∃ place placeState unifiedState,
      Detail.inferPlaceFuel fuel inferenceContext target initial =
        .ok (place, placeState) ∧
      Detail.unify placeState place.type .word = .ok unifiedState ∧
      result = (.assignBitNot {
        target := { place with type := unifiedState.resolve place.type }
      }, unifiedState) := by
  unfold Detail.inferForItemFuel at success
  simp only [itemEq, bind, Except.bind] at success
  cases placeSuccess : Detail.inferPlaceFuel fuel inferenceContext target
      initial with
  | error error => simp [placeSuccess] at success
  | ok child =>
      rcases child with ⟨place, placeState⟩
      simp only [placeSuccess] at success
      cases unifySuccess : Detail.unify placeState place.type .word with
      | error error => simp [unifySuccess] at success
      | ok unifiedState =>
          simp only [unifySuccess, pure, Pure.pure, Except.pure] at success
          injection success with resultEq
          rw [← resultEq]
          exact ⟨place, placeState, unifiedState, rfl, unifySuccess, rfl⟩

/-- An annotated declaration without an initializer resolves its source
type, then allocates the resulting (necessarily monomorphic) binder. -/
theorem inferForItemFuel_success_letAnnotatedUninitialized_facts
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {item : Syntax.ForItem} {name : Syntax.Identifier}
    {sourceType : Syntax.TypeExpr}
    {initial : State} {result : ForItemForm × State}
    (itemEq : item.value = .letDecl name (some sourceType) none)
    (success : Detail.inferForItemFuel (fuel + 1) inferenceContext item
      initial = .ok result) :
    ∃ resolvedType locals valueType generalized binding,
      Detail.resolveSourceType inferenceContext sourceType =
        .ok resolvedType ∧
      locals = initial.binderEnvironment.apply initial.inference.substitution ∧
      valueType = initial.resolve resolvedType ∧
      generalized = Detail.generalizeValue initial locals
        initial.nextRequirement valueType ∧
      (initial.withLocals locals).allocateBinder name.value
        generalized.scheme (some name.span) false generalized.requirements =
          binding ∧
      result = (.letDecl binding.1 none, binding.2) := by
  unfold Detail.inferForItemFuel at success
  simp only [itemEq, bind, Except.bind] at success
  cases resolution : Detail.resolveSourceType inferenceContext sourceType with
  | error error => simp [resolution] at success
  | ok resolvedType =>
      simp only [resolution, pure, Pure.pure, Except.pure] at success
      let locals := initial.binderEnvironment.apply
        initial.inference.substitution
      let valueType := initial.resolve resolvedType
      let generalized := Detail.generalizeValue initial locals
        initial.nextRequirement valueType
      let binding := (initial.withLocals locals).allocateBinder name.value
        generalized.scheme (some name.span) false generalized.requirements
      injection success with resultEq
      rw [← resultEq]
      exact ⟨resolvedType, locals, valueType, generalized, binding,
        rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- An annotated initialized header let infers only its selected
initializer under the resolved annotation before binder allocation. -/
theorem inferForItemFuel_success_letAnnotatedInitialized_facts
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {item : Syntax.ForItem} {name : Syntax.Identifier}
    {sourceType : Syntax.TypeExpr} {initializer : Syntax.Expr}
    {initial : State} {result : ForItemForm × State}
    (itemEq : item.value = .letDecl name (some sourceType)
      (some initializer))
    (success : Detail.inferForItemFuel (fuel + 1) inferenceContext item
      initial = .ok result) :
    ∃ resolvedType inferred initializerState locals valueType generalized
      binding,
      Detail.resolveSourceType inferenceContext sourceType =
        .ok resolvedType ∧
      Detail.inferExprFuel fuel inferenceContext initializer
        (some resolvedType) initial = .ok (inferred, initializerState) ∧
      locals = initializerState.binderEnvironment.apply
        initializerState.inference.substitution ∧
      valueType = initializerState.resolve inferred.type ∧
      generalized = Detail.generalizeValue initializerState locals
        initial.nextRequirement valueType ∧
      (initializerState.withLocals locals).allocateBinder name.value
        generalized.scheme (some name.span) false
        generalized.requirements = binding ∧
      result = (.letDecl binding.1 (some inferred.id), binding.2) := by
  unfold Detail.inferForItemFuel at success
  simp only [itemEq, bind, Except.bind] at success
  cases resolution : Detail.resolveSourceType inferenceContext sourceType with
  | error error => simp [resolution] at success
  | ok resolvedType =>
      simp only [resolution] at success
      cases childSuccess : Detail.inferExprFuel fuel inferenceContext
          initializer (some resolvedType) initial with
      | error error => simp [childSuccess] at success
      | ok child =>
          rcases child with ⟨inferred, initializerState⟩
          simp only [childSuccess, pure, Pure.pure, Except.pure] at success
          let locals := initializerState.binderEnvironment.apply
            initializerState.inference.substitution
          let valueType := initializerState.resolve inferred.type
          let generalized := Detail.generalizeValue initializerState locals
            initial.nextRequirement valueType
          let binding := (initializerState.withLocals locals).allocateBinder
            name.value generalized.scheme (some name.span) false
            generalized.requirements
          injection success with resultEq
          rw [← resultEq]
          exact ⟨resolvedType, inferred, initializerState, locals,
            valueType, generalized, binding,
            rfl, childSuccess,
            rfl, rfl, rfl, rfl, rfl⟩

/-- A restricted `for` header item changes only the lexical tables.  This
is the context-field transport needed by the recursive item invariant. -/
theorem forItemHasType_nonlocal_fields_eq
    {source : TypedSource} {control : ControlContext}
    {before after : SourceSemantics.Context} {item : ForItemForm}
    (typing : ForItemHasType source control before item after) :
    after.signatures = before.signatures ∧
      after.typeParameters = before.typeParameters ∧
      after.currentDeclaration = before.currentDeclaration ∧
      after.residualTypeVariables = before.residualTypeVariables ∧
      after.solvedRequirements = before.solvedRequirements ∧
      after.assumptions = before.assumptions := by
  cases typing <;> try simp
  all_goals
    have fields := BinderExtends.context_fields
      (by assumption : BinderExtends source.owner before _ after)
    have residual := BinderExtends.residualTypeVariables_eq
      (by assumption : BinderExtends source.owner before _ after)
    exact ⟨fields.1, fields.2.2.1, fields.2.1, residual,
      fields.2.2.2.2, fields.2.2.2.1⟩

/-- Close the recursive state invariant after actual successful single-item
inference.  Declarative typing accounts for the lexical context change;
scheme isolation is a distinct operational obligation, especially for a
generalized header let. -/
theorem RecursiveStatementInvariant.of_forItem_typing
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {expectedReturn : Ty}
    {item : Syntax.ForItem} {initial final : State}
    {inferred : ForItemForm}
    {finalized : Frontend.SourceInference.Result}
    {initialContext finalContext : SourceSemantics.Context}
    {source : TypedSource} {control : ControlContext}
    (initialInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initial initialContext)
    (success : Detail.inferForItemFuel fuel inferenceContext item initial =
      .ok (inferred, final))
    (signatureFormation : ProgramSignatureFormationValidated
      inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈
      inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (resultActive : ActiveLocalContextInvariant final
      finalized.substitution finalContext)
    (resultSchemeIsolation : ActiveSchemeQuantifierIsolation final)
    (resultSubstitutionExtension : finalized.substitution.SemanticallyExtends
      final.inference.substitution)
    (typing : ForItemHasType source control initialContext
      (inferred.applySubstitution finalized.substitution) finalContext) :
    RecursiveStatementInvariant wholeContext expectedReturn finalized final
      finalContext := by
  have properties := Detail.inferForItemFuel_inferenceProperties
    initialInvariant.ready signatureFormation functionsCanonical success
  have fields := forItemHasType_nonlocal_fields_eq typing
  refine {
    active := resultActive
    ready := properties.2
    returnBelow := initialInvariant.returnBelow.weaken
      properties.1.next_le
    bindersBelow := Detail.inferForItemFuel_preserves_localBindersBelowNextLocal
      initialInvariant.bindersBelow success
    nodesBelow := (Detail.inferForItemFuel_occurrenceBoundExtends success
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

/-- An actual unannotated initialized header let preserves capture-origin
provenance.  The required `.inr` origin comes from the enclosing loop's
retained binder inventory, not merely from the child initializer expression. -/
theorem inferForItemFuel_success_letUnannotatedInitialized_captureOrigins
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {item : Syntax.ForItem} {name : Syntax.Identifier}
    {initializer : Syntax.Expr}
    {initial : State} {result : ForItemForm × State}
    {wholeSource : TypedSource}
    (itemEq : item.value = .letDecl name none (some initializer))
    (success : Detail.inferForItemFuel (fuel + 1) inferenceContext item
      initial = .ok result)
    (origins : ActiveBinderCaptureOrigins initial wholeSource)
    (retained : ForItemBindingRetained wholeSource result.1) :
    ActiveBinderCaptureOrigins result.2 wholeSource := by
  obtain ⟨inferred, initializerState, locals, valueType, generalized,
      binding, initializerSuccess, localsEq, valueTypeEq, generalizedEq,
      bindingEq, resultEq⟩ :=
    inferForItemFuel_success_letUnannotatedInitialized_facts itemEq success
  have binderRetained : binding.1 ∈ wholeSource.initializedLetBinders := by
    let selected : InitializedLetBinding :=
      ⟨binding.1, .expression inferred.id⟩
    have selectedMember : selected ∈
        forItemInitializedLetBindings result.1 := by
      rw [resultEq]
      simp [selected, forItemInitializedLetBindings]
    exact (retained selected selectedMember).1
  rw [resultEq]
  exact ((origins.inferExprFuel initializerSuccess).withLocals locals
    ).allocateBinder bindingEq (.inr binderRetained)

/-- The semantic obligations attached to the *actual* initializer returned
by one successful unannotated header let.  The trace fields prevent this
certificate from asserting typing for unrelated expression traversals. -/
def ActualUnannotatedForItemInitializerCertificate
    (fuel : Nat) (inferenceContext : Frontend.SourceInference.Context)
    (name : Syntax.Identifier) (initializer : Syntax.Expr) (initial : State)
    (result : ForItemForm × State) (roots : List NodeId)
    (outer : Substitution) (semanticContext : SourceSemantics.Context) :
    Prop :=
  ∃ inferred : InferredExpression,
    ∃ initializerState : State,
      ∃ locals : Environment,
        ∃ valueType : Ty,
          ∃ generalized : Detail.GeneralizedValue,
            ∃ binding : TypedBinder × State,
              Detail.inferExprFuel fuel inferenceContext initializer none
                initial = .ok (inferred, initializerState) ∧
              locals = initializerState.binderEnvironment.apply
                initializerState.inference.substitution ∧
              valueType = initializerState.resolve inferred.type ∧
              generalized = Detail.generalizeValue initializerState
                locals initial.nextRequirement valueType ∧
              (initializerState.withLocals locals).allocateBinder
                name.value generalized.scheme (some name.span) false
                generalized.requirements = binding ∧
              result = (.letDecl binding.1 (some inferred.id), binding.2) ∧
              UnannotatedInitializedLetCertificate
                (result.2.toTypedSource roots) semanticContext outer binding.1
                inferred.id ∧
              (∀ metavariable,
                metavariable ∈ valueType.freeVariables →
                  metavariable ∉ activeSchemeQuantifiers initial)

/-- Assemble the certificate for the *actual* generalized header let from
finalized resources and its retained enclosing-loop ownership.  Three
genuine recursive obligations remain explicit: ordered barrier transport,
formation of the generated predicate rows, and typing of the selected
initializer in the raw item source.  Finalization alone does not prove these
facts. -/
theorem actualUnannotatedForItemInitializerCertificate_of_finalBarrier
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {item : Syntax.ForItem} {name : Syntax.Identifier}
    {initializer : Syntax.Expr}
    {initial : State} {result : ForItemForm × State}
    {evidenceState : State} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticContext : SourceSemantics.Context}
    (itemEq : item.value = .letDecl name none (some initializer))
    (success : Detail.inferForItemFuel (fuel + 1) inferenceContext item
      initial = .ok result)
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    (initialInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initial semanticContext)
    (retained : ForItemBindingRetained
      (evidenceState.toTypedSource roots) result.1)
    (barrier : ∀ {inferred : InferredExpression}
      {initializerState : State} {locals : Environment}
      {valueType : Ty} {generalized : Detail.GeneralizedValue}
      {binding : TypedBinder × State},
      Detail.inferExprFuel fuel inferenceContext initializer none initial =
        .ok (inferred, initializerState) →
      locals = initializerState.binderEnvironment.apply
        initializerState.inference.substitution →
      valueType = initializerState.resolve inferred.type →
      generalized = Detail.generalizeValue initializerState locals
        initial.nextRequirement valueType →
      (initializerState.withLocals locals).allocateBinder name.value
        generalized.scheme (some name.span) false
        generalized.requirements = binding →
      GeneralizationBarrierTransport initializerState locals
        initial.nextRequirement valueType finalized.substitution
        semanticContext
        (localSchemeTemplateIds
          (binding.1.applySubstitution finalized.substitution)))
    (generated : ∀ {inferred : InferredExpression}
      {initializerState : State} {locals : Environment}
      {valueType : Ty} {generalized : Detail.GeneralizedValue}
      {binding : TypedBinder × State},
      Detail.inferExprFuel fuel inferenceContext initializer none initial =
        .ok (inferred, initializerState) →
      locals = initializerState.binderEnvironment.apply
        initializerState.inference.substitution →
      valueType = initializerState.resolve inferred.type →
      generalized = Detail.generalizeValue initializerState locals
        initial.nextRequirement valueType →
      (initializerState.withLocals locals).allocateBinder name.value
        generalized.scheme (some name.span) false
        generalized.requirements = binding →
      RetainedRequirementPredicateFormationAt initializerState binding.1
        finalized.substitution semanticContext)
    (initializerTyping : ∀ {inferred : InferredExpression}
      {initializerState : State} {locals : Environment}
      {valueType : Ty} {generalized : Detail.GeneralizedValue}
      {binding : TypedBinder × State},
      Detail.inferExprFuel fuel inferenceContext initializer none initial =
        .ok (inferred, initializerState) →
      locals = initializerState.binderEnvironment.apply
        initializerState.inference.substitution →
      valueType = initializerState.resolve inferred.type →
      generalized = Detail.generalizeValue initializerState locals
        initial.nextRequirement valueType →
      (initializerState.withLocals locals).allocateBinder name.value
        generalized.scheme (some name.span) false
        generalized.requirements = binding →
      ExpressionHasType
        ((result.2.toTypedSource roots).applySubstitution
          finalized.substitution)
        (localSchemeInitializerContext semanticContext
          (binding.1.applySubstitution finalized.substitution)) inferred.id
        (binding.1.applySubstitution finalized.substitution).scheme.body)
    (avoidsOld : ∀ {inferred : InferredExpression}
      {initializerState : State},
      Detail.inferExprFuel fuel inferenceContext initializer none initial =
        .ok (inferred, initializerState) →
      ∀ metavariable,
        metavariable ∈
          (initializerState.resolve inferred.type).freeVariables →
          metavariable ∉ activeSchemeQuantifiers initial) :
    ActualUnannotatedForItemInitializerCertificate fuel inferenceContext
      name initializer initial result roots finalized.substitution
      semanticContext := by
  obtain ⟨inferred, initializerState, locals, valueType, generalized,
      binding, childSuccess, localsEq, valueTypeEq, generalizedEq,
      bindingEq, resultEq⟩ :=
    inferForItemFuel_success_letUnannotatedInitialized_facts itemEq success
  have rawRequirementsEq : binding.1.schemeRequirements =
      (Detail.generalizeValue initializerState locals
        initial.nextRequirement valueType).requirements := by
    have binderEq := congrArg Prod.fst bindingEq
    rw [← binderEq, generalizedEq]
    rfl
  have selectedMember :
      (⟨binding.1, .expression inferred.id⟩ : InitializedLetBinding) ∈
        forItemInitializedLetBindings result.1 := by
    rw [resultEq]
    simp [forItemInitializedLetBindings]
  have binderRetained : binding.1 ∈
      (evidenceState.toTypedSource roots).initializedLetBinders :=
    (retained _ selectedMember).1
  have templatesRetained : ∀ requirement,
      requirement ∈ binding.1.schemeRequirements →
        ContainsLocalSchemeTemplate (evidenceState.toTypedSource roots) {
          binder := binding.1,
          initializer := .expression inferred.id,
          requirement } := by
    intro requirement member
    exact (retained _ selectedMember).2 requirement member
  have finalPredicates :=
    generalizeValue_finalPredicates_of_requirementGeneration
      rawRequirementsEq
      (generated childSuccess localsEq valueTypeEq generalizedEq bindingEq)
  have priorBlocked : PriorQuantifiersBlockedAt initializerState locals
      initial.nextRequirement valueType semanticContext :=
    priorQuantifiersBlockedAt_of_activeQuantifiersAvoided
      initialInvariant.active.aligned (by
        intro metavariable member
        exact avoidsOld childSuccess metavariable (by
          simpa [valueTypeEq] using member))
  have certificate :=
    unannotatedInitializedLetCertificate_of_finalBarrier_retained
      resources (source := result.2.toTypedSource roots)
      (state := initializerState) (final := binding.2)
      (locals := locals) (requirementStart := initial.nextRequirement)
      (valueType := valueType) (generalized := generalized)
      (name := name) (binder := binding.1)
      (initializer := inferred.id) rfl generalizedEq bindingEq
      initialInvariant.signaturesEq initialInvariant.assumptionsMono
      initialInvariant.solvedRequirementsEq binderRetained
      templatesRetained
      (barrier childSuccess localsEq valueTypeEq generalizedEq bindingEq)
      finalPredicates priorBlocked
      (initializerTyping childSuccess localsEq valueTypeEq generalizedEq
        bindingEq)
  exact ⟨inferred, initializerState, locals, valueType, generalized,
    binding, childSuccess, localsEq, valueTypeEq, generalizedEq, bindingEq,
    resultEq, certificate, by
      intro metavariable member
      exact avoidsOld childSuccess metavariable (by
        simpa [valueTypeEq] using member)⟩

/-- Close the actual unannotated header-let branch from its selected
initializer certificate.  The certificate itself is obtained from the
retained-binder finalization theorem once the mutual expression, barrier,
and predicate-formation inductions supply their respective fields. -/
theorem inferForItemFuel_success_letUnannotatedInitialized_of_certificate
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {expectedReturn : Ty}
    {item : Syntax.ForItem} {name : Syntax.Identifier}
    {initializer : Syntax.Expr}
    {initial : State} {result : ForItemForm × State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {semanticContext : SourceSemantics.Context}
    {control : ControlContext}
    (itemEq : item.value = .letDecl name none (some initializer))
    (success : Detail.inferForItemFuel (fuel + 1) inferenceContext item
      initial = .ok result)
    (signatureFormation : ProgramSignatureFormationValidated
      inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈
      inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (initialInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initial semanticContext)
    (substitutionExtension : finalized.substitution.SemanticallyExtends
      result.2.inference.substitution)
    (resultExtension : TypingSourceExtends
      ((result.2.toTypedSource roots).applySubstitution
        finalized.substitution) semanticSource)
    (actual : ActualUnannotatedForItemInitializerCertificate fuel
      inferenceContext name initializer initial result roots
      finalized.substitution semanticContext) :
    ∃ finalContext,
      RecursiveStatementInvariant wholeContext expectedReturn finalized
        result.2 finalContext ∧
      ForItemHasType semanticSource control semanticContext
        (result.1.applySubstitution finalized.substitution)
        finalContext := by
  rcases actual with ⟨inferred, initializerState, locals, valueType,
    generalized, binding, childSuccess, localsEq, valueTypeEq,
    generalizedEq, bindingEq, resultEq, certificate, avoidsOld⟩
  have initializerInvariant : ActiveLocalContextInvariant initializerState
      finalized.substitution semanticContext :=
    initialInvariant.active.inferExprFuel childSuccess
  have initializerBelow : initializerState.LocalBindersBelowNextLocal :=
    Detail.inferExprFuel_preserves_localBindersBelowNextLocal
      initialInvariant.bindersBelow childSuccess
  have sourceOwner : (result.2.toTypedSource roots).owner =
      initializerState.owner := by
    change result.2.owner = initializerState.owner
    exact (Detail.inferForItemFuel_preserves_owner success).trans
      (Detail.inferExprFuel_preserves_owner childSuccess).symm
  obtain ⟨finalContext, activeFinal, typingRaw⟩ :=
    unannotatedInitializedForItemHasType_afterSubstitution
      (control := control) (name := name)
      (initializer := inferred.id)
      (requirementStart := initial.nextRequirement)
      generalizedEq bindingEq initializerInvariant initializerBelow
      sourceOwner certificate
  have finalActive : ActiveLocalContextInvariant result.2
      finalized.substitution finalContext := by
    simpa [resultEq] using activeFinal
  have isolatedFinal : ActiveSchemeQuantifierIsolation result.2 := by
    apply inferForItemFuel_success_letUnannotatedInitialized_activeSchemeQuantifierIsolation
      itemEq success initialInvariant.schemeIsolation initialInvariant.ready
      signatureFormation functionsCanonical
    intro candidate candidateState candidateSuccess metavariable member
    have pairEq : (candidate, candidateState) =
        (inferred, initializerState) := by
      exact Except.ok.inj (candidateSuccess.symm.trans childSuccess)
    cases pairEq
    exact avoidsOld metavariable (by simpa [valueTypeEq] using member)
  have typing : ForItemHasType semanticSource control semanticContext
      (result.1.applySubstitution finalized.substitution)
      finalContext := by
    have weakened := ForItemHasType.weakenSource resultExtension typingRaw
    simpa [resultEq, ForItemForm.applySubstitution] using weakened
  have finalInvariant := RecursiveStatementInvariant.of_forItem_typing
    initialInvariant success signatureFormation functionsCanonical
    finalActive isolatedFinal substitutionExtension typing
  exact ⟨finalContext, finalInvariant, typing⟩

/-- The typed child for a successful expression header item.  Its trace and
returned item form are fixed by the actual parent inference result. -/
def ActualExpressionForItemCertificate
    (fuel : Nat) (inferenceContext : Frontend.SourceInference.Context)
    (expression : Syntax.Expr) (initial : State)
    (result : ForItemForm × State)
    (semanticSource : TypedSource)
    (semanticContext : SourceSemantics.Context)
    (outer : Substitution) : Prop :=
  ∃ inferred resultState,
    Detail.inferExprFuel fuel inferenceContext expression none initial =
      .ok (inferred, resultState) ∧
    result = (.expression inferred.id, resultState) ∧
    ExpressionHasType semanticSource semanticContext inferred.id
      (outer.apply inferred.type)

/-- The ordinary expression item closes directly under the statement
invariant because expression inference restores the caller's binder stack. -/
theorem expressionForItem_of_actualCertificate
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {expectedReturn : Ty}
    {expression : Syntax.Expr}
    {initial : State} {result : ForItemForm × State}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {semanticContext : SourceSemantics.Context}
    {control : ControlContext}
    (signatureFormation : ProgramSignatureFormationValidated
      inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈
      inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (initialInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initial semanticContext)
    (substitutionExtension : finalized.substitution.SemanticallyExtends
      result.2.inference.substitution)
    (actual : ActualExpressionForItemCertificate fuel inferenceContext
      expression initial result semanticSource semanticContext
      finalized.substitution) :
    ∃ finalContext,
      RecursiveStatementInvariant wholeContext expectedReturn finalized
        result.2 finalContext ∧
      ForItemHasType semanticSource control semanticContext
        (result.1.applySubstitution finalized.substitution)
        finalContext := by
  obtain ⟨inferred, resultState, childSuccess, resultEq, childTyping⟩ :=
    actual
  have resultSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        resultState.inference.substitution := by
    simpa [resultEq] using substitutionExtension
  have finalInvariant := initialInvariant.inferExprFuel childSuccess
    signatureFormation functionsCanonical (by simp)
    resultSubstitutionExtension
  refine ⟨semanticContext, ?_, ?_⟩
  · simpa [resultEq] using finalInvariant
  · simpa [resultEq, ForItemForm.applySubstitution] using
      (ForItemHasType.expression (control := control) childTyping)

/-- The assigned-value child selected by an actual header item, together
with its already-established place/value typing in the local semantic source. -/
def ActualAssignedValueForItemCertificate
    (fuel : Nat) (inferenceContext : Frontend.SourceInference.Context)
    (target value : Syntax.Expr)
    (operator : Syntax.Located Syntax.ValueAssignOp)
    (initial : State) (result : ForItemForm × State)
    (semanticSource : TypedSource)
    (semanticContext : SourceSemantics.Context)
    (outer : Substitution) : Prop :=
  ∃ assignment inferredValue resultState,
    Detail.inferAssignedValueFuel fuel inferenceContext target
      operator.value value initial =
        .ok (assignment, inferredValue, resultState) ∧
    result = (.assignValue assignment operator.value inferredValue.id,
      resultState) ∧
    SourceAssignmentHasType semanticSource semanticContext
      (assignment.applySubstitution outer) operator.value inferredValue.id

/-- The assignment header item closes from its actual assigned-value child.
That traversal preserves the lexical binder stack, so scheme isolation is
transported without a new binder obligation. -/
theorem inferForItemFuel_success_assignValue_of_certificate
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {expectedReturn : Ty}
    {item : Syntax.ForItem} {target value : Syntax.Expr}
    {operator : Syntax.Located Syntax.ValueAssignOp}
    {initial : State} {result : ForItemForm × State}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {semanticContext : SourceSemantics.Context}
    {control : ControlContext}
    (success : Detail.inferForItemFuel (fuel + 1) inferenceContext item
      initial = .ok result)
    (signatureFormation : ProgramSignatureFormationValidated
      inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈
      inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (initialInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initial semanticContext)
    (substitutionExtension : finalized.substitution.SemanticallyExtends
      result.2.inference.substitution)
    (actual : ActualAssignedValueForItemCertificate fuel inferenceContext
      target value operator initial result semanticSource semanticContext
      finalized.substitution) :
    ∃ finalContext,
      RecursiveStatementInvariant wholeContext expectedReturn finalized
        result.2 finalContext ∧
      ForItemHasType semanticSource control semanticContext
        (result.1.applySubstitution finalized.substitution)
        finalContext := by
  obtain ⟨assignment, inferredValue, resultState, childSuccess, resultEq,
    childTyping⟩ := actual
  have childActive : ActiveLocalContextInvariant resultState
      finalized.substitution semanticContext :=
    initialInvariant.active.inferAssignedValueFuel childSuccess
  have resultActive : ActiveLocalContextInvariant result.2
      finalized.substitution semanticContext := by
    simpa [resultEq] using childActive
  have bindersEq : resultState.localBinders = initial.localBinders := by
    simpa [State.lexicalScope] using congrArg LexicalScope.binders
      (Detail.inferAssignedValueFuel_success_lexicalScope_eq childSuccess)
  have childIsolated : ActiveSchemeQuantifierIsolation resultState :=
    activeSchemeQuantifierIsolation_transport initialInvariant.schemeIsolation
      bindersEq
  have resultIsolated : ActiveSchemeQuantifierIsolation result.2 := by
    simpa [resultEq] using childIsolated
  have typing : ForItemHasType semanticSource control semanticContext
      (result.1.applySubstitution finalized.substitution)
      semanticContext := by
    simpa [resultEq, ForItemForm.applySubstitution] using
      (ForItemHasType.assignValue (control := control) childTyping)
  have finalInvariant := RecursiveStatementInvariant.of_forItem_typing
    initialInvariant success signatureFormation functionsCanonical
    resultActive resultIsolated substitutionExtension typing
  exact ⟨semanticContext, finalInvariant, typing⟩

/-- The actual place and word-unification trace of a bit-not assignment,
with declarative typing for precisely that place occurrence. -/
def ActualBitNotForItemCertificate
    (fuel : Nat) (inferenceContext : Frontend.SourceInference.Context)
    (target : Syntax.Expr) (initial : State)
    (result : ForItemForm × State)
    (semanticSource : TypedSource)
    (semanticContext : SourceSemantics.Context)
    (outer : Substitution) : Prop :=
  ∃ place placeState unifiedState,
    Detail.inferPlaceFuel fuel inferenceContext target initial =
      .ok (place, placeState) ∧
    Detail.unify placeState place.type .word = .ok unifiedState ∧
    result = (.assignBitNot {
      target := { place with type := unifiedState.resolve place.type }
    }, unifiedState) ∧
    SourcePlaceHasType semanticSource semanticContext
      (place.applySubstitution outer) (outer.apply place.type)

/-- The actual bit-not header item combines place typing with its recorded
word unification, then closes the recursive state invariant. -/
theorem inferForItemFuel_success_assignBitNot_of_certificate
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {expectedReturn : Ty}
    {item : Syntax.ForItem} {target : Syntax.Expr}
    {initial : State} {result : ForItemForm × State}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {semanticContext : SourceSemantics.Context}
    {control : ControlContext}
    (success : Detail.inferForItemFuel (fuel + 1) inferenceContext item
      initial = .ok result)
    (signatureFormation : ProgramSignatureFormationValidated
      inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈
      inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (initialInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initial semanticContext)
    (substitutionExtension : finalized.substitution.SemanticallyExtends
      result.2.inference.substitution)
    (actual : ActualBitNotForItemCertificate fuel inferenceContext target
      initial result semanticSource semanticContext finalized.substitution) :
    ∃ finalContext,
      RecursiveStatementInvariant wholeContext expectedReturn finalized
        result.2 finalContext ∧
      ForItemHasType semanticSource control semanticContext
        (result.1.applySubstitution finalized.substitution)
        finalContext := by
  obtain ⟨place, placeState, unifiedState, placeSuccess, unifySuccess,
    resultEq, placeTyping⟩ := actual
  have unifiedExtension : finalized.substitution.SemanticallyExtends
      unifiedState.inference.substitution := by
    simpa [resultEq] using substitutionExtension
  have resolvedWord : unifiedState.resolve place.type = .word :=
    (Detail.unify_resolve_eq unifySuccess).trans (by rfl)
  have resolvedFinal : finalized.substitution.apply
      (unifiedState.resolve place.type) =
        finalized.substitution.apply place.type := by
    simpa [State.resolve, InferState.resolve] using
      unifiedExtension place.type
  have placeWord : finalized.substitution.apply place.type = .word := by
    rw [← resolvedFinal, resolvedWord]
    rfl
  have storedPlaceEq :
      ({ place with type := unifiedState.resolve place.type } :
        PlaceResolution).applySubstitution finalized.substitution =
          place.applySubstitution finalized.substitution := by
    cases place
    simp [PlaceResolution.applySubstitution, resolvedFinal]
  have assignmentTyping : SourceBitNotAssignmentValid semanticSource
      semanticContext
      (({ target := { place with
        type := unifiedState.resolve place.type } } :
          AssignmentResolution).applySubstitution
            finalized.substitution) := by
    apply SourceBitNotAssignmentValid.intro
    · change SourcePlaceHasType semanticSource semanticContext
        (({ place with type := unifiedState.resolve place.type } :
          PlaceResolution).applySubstitution finalized.substitution) .word
      rw [storedPlaceEq, ← placeWord]
      exact placeTyping
    · rfl
  have placeActive : ActiveLocalContextInvariant placeState
      finalized.substitution semanticContext :=
    initialInvariant.active.inferPlaceFuel placeSuccess
  have unifiedActive : ActiveLocalContextInvariant unifiedState
      finalized.substitution semanticContext :=
    placeActive.unify unifySuccess
  have resultActive : ActiveLocalContextInvariant result.2
      finalized.substitution semanticContext := by
    simpa [resultEq] using unifiedActive
  have placeBindersEq : placeState.localBinders = initial.localBinders := by
    simpa [State.lexicalScope] using congrArg LexicalScope.binders
      (Detail.inferPlaceFuel_success_lexicalScope_eq placeSuccess)
  have unifiedBindersEq : unifiedState.localBinders =
      placeState.localBinders := by
    simpa [State.lexicalScope] using congrArg LexicalScope.binders
      (Detail.unify_preserves_lexicalScope unifySuccess)
  have unifiedIsolated : ActiveSchemeQuantifierIsolation unifiedState :=
    activeSchemeQuantifierIsolation_transport
      (activeSchemeQuantifierIsolation_transport
        initialInvariant.schemeIsolation placeBindersEq)
      unifiedBindersEq
  have resultIsolated : ActiveSchemeQuantifierIsolation result.2 := by
    simpa [resultEq] using unifiedIsolated
  have typing : ForItemHasType semanticSource control semanticContext
      (result.1.applySubstitution finalized.substitution)
      semanticContext := by
    simpa [resultEq, ForItemForm.applySubstitution] using
      (ForItemHasType.assignBitNot (control := control) assignmentTyping)
  have finalInvariant := RecursiveStatementInvariant.of_forItem_typing
    initialInvariant success signatureFormation functionsCanonical
    resultActive resultIsolated substitutionExtension typing
  exact ⟨semanticContext, finalInvariant, typing⟩

/-- The annotated, uninitialized header let needs no recursive expression
premise: source-type resolution yields a closed monomorphic scheme, so both
scheme isolation and capture origin follow without a generalized template. -/
theorem inferForItemFuel_success_letAnnotatedUninitialized_scoped
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {expectedReturn : Ty}
    {item : Syntax.ForItem} {name : Syntax.Identifier}
    {sourceType : Syntax.TypeExpr}
    {initial : State} {result : ForItemForm × State}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {semanticContext : SourceSemantics.Context}
    {control : ControlContext}
    (itemEq : item.value = .letDecl name (some sourceType) none)
    (success : Detail.inferForItemFuel (fuel + 1) inferenceContext item
      initial = .ok result)
    (signatureFormation : ProgramSignatureFormationValidated
      inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈
      inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (canonical : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (signaturesEq : semanticContext.signatures =
      inferenceContext.signatures)
    (parametersEq : semanticContext.typeParameters =
      inferenceContext.typeParameters)
    (declarationEq : semanticContext.currentDeclaration =
      some inferenceContext.scope.genericOwner)
    (initialInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initial semanticContext)
    (sourceOwner : semanticSource.owner = initial.owner)
    (substitutionExtension : finalized.substitution.SemanticallyExtends
      result.2.inference.substitution) :
    ∃ finalContext,
      RecursiveStatementInvariant wholeContext expectedReturn finalized
        result.2 finalContext ∧
      ForItemHasType semanticSource control semanticContext
        (result.1.applySubstitution finalized.substitution)
        finalContext := by
  obtain ⟨resolvedType, locals, valueType, generalized, binding,
      resolution, localsEq, valueTypeEq, generalizedEq, bindingEq,
      resultEq⟩ :=
    inferForItemFuel_success_letAnnotatedUninitialized_facts itemEq success
  obtain ⟨typeWellFormed, closedSchemeEq, closedRequirementsEq,
      generalizes⟩ :=
    resolvedAnnotationBinderFacts_afterSubstitution
      (target := semanticContext) (outer := finalized.substitution)
      (inferenceContext := inferenceContext)
      (name := name) (sourceType := sourceType)
      (state := initial) (final := binding.2)
      (requirementStart := initial.nextRequirement)
      (resolvedType := resolvedType) (valueType := valueType)
      (locals := locals) (generalized := generalized)
      (binder := binding.1)
      resolution valueTypeEq generalizedEq bindingEq canonical
      signaturesEq parametersEq declarationEq
  let finalContext := semanticContext.withLocal binding.1.id
    (binding.1.applySubstitution finalized.substitution).scheme
    (binding.1.applySubstitution finalized.substitution).schemeRequirements
  have activeFinal : ActiveLocalContextInvariant binding.2
      finalized.substitution finalContext :=
    resolvedAnnotationBinderPreservesActiveLocalContextInvariant_afterSubstitution
      resolution valueTypeEq generalizedEq bindingEq canonical
      signaturesEq parametersEq declarationEq initialInvariant.active
      initialInvariant.bindersBelow
  have rawExtension : BinderExtends
      (initial.withLocals locals).owner semanticContext
      (binding.1.applySubstitution finalized.substitution)
      finalContext := by
    apply (initialInvariant.active.aligned.withLocals locals
      ).monomorphicBinderExtends_of_allocateBinder
        (State.withLocals_preserves_localBindersBelowNextLocal initial
          locals initialInvariant.bindersBelow)
        bindingEq closedSchemeEq closedRequirementsEq typeWellFormed
  have semanticExtension : BinderExtends semanticSource.owner
      semanticContext (binding.1.applySubstitution finalized.substitution)
      finalContext := by
    rw [sourceOwner]
    simpa [State.withLocals] using rawExtension
  have monomorphic :
      (binding.1.applySubstitution finalized.substitution).scheme.quantified =
        [] := by
    rw [closedSchemeEq]
    rfl
  have typingRaw : ForItemHasType semanticSource control semanticContext
      (.letDecl (binding.1.applySubstitution finalized.substitution) none)
      finalContext :=
    .letUninitialized monomorphic generalizes semanticExtension
  have typing : ForItemHasType semanticSource control semanticContext
      (result.1.applySubstitution finalized.substitution)
      finalContext := by
    simpa [resultEq, ForItemForm.applySubstitution] using typingRaw
  have valueClosed : valueType.freeVariables = [] := by
    have resolvedClosed :=
      StructuralSubstitution.TypeWellFormed.freeVariables_eq_nil
        typeWellFormed
    have resolvedByState : initial.resolve resolvedType = resolvedType := by
      simpa [State.resolve, InferState.resolve] using
        (Detail.resolveSourceType_success_apply_eq_self
          initial.inference.substitution resolution)
    rw [valueTypeEq, resolvedByState]
    exact resolvedClosed
  have generalizedSchemeEq : generalized.scheme = .mono valueType := by
    rw [generalizedEq]
    exact (generalizeValue_closed_facts initial locals
      initial.nextRequirement valueType semanticContext valueClosed).1
  have generalizedRequirementsEq : generalized.requirements = [] := by
    rw [generalizedEq]
    exact (generalizeValue_closed_facts initial locals
      initial.nextRequirement valueType semanticContext valueClosed).2.1
  have isolatedWithLocals : ActiveSchemeQuantifierIsolation
      (initial.withLocals locals) :=
    activeSchemeQuantifierIsolation_transport
      initialInvariant.schemeIsolation rfl
  have bindingIsolated : ActiveSchemeQuantifierIsolation binding.2 := by
    rw [← bindingEq, generalizedSchemeEq, generalizedRequirementsEq]
    exact activeSchemeQuantifierIsolation_allocateMonoBinder
      (initial.withLocals locals) name.value valueType (some name.span)
      isolatedWithLocals (by
        intro metavariable member
        simp [valueClosed] at member)
  have resultActive : ActiveLocalContextInvariant result.2
      finalized.substitution finalContext := by
    simpa [resultEq] using activeFinal
  have resultIsolated : ActiveSchemeQuantifierIsolation result.2 := by
    simpa [resultEq] using bindingIsolated
  have finalInvariant := RecursiveStatementInvariant.of_forItem_typing
    initialInvariant success signatureFormation functionsCanonical
    resultActive resultIsolated substitutionExtension typing
  exact ⟨finalContext, finalInvariant, typing⟩

/-- The actual initialized child of an annotated header declaration.  The
trace fixes the resolved annotation, selected initializer, and final binder;
only typing of that selected expression is supplied by the expression
induction. -/
def ActualAnnotatedInitializedForItemCertificate
    (fuel : Nat) (inferenceContext : Frontend.SourceInference.Context)
    (name : Syntax.Identifier) (sourceType : Syntax.TypeExpr)
    (initializer : Syntax.Expr) (initial : State)
    (result : ForItemForm × State) (semanticSource : TypedSource)
    (semanticContext : SourceSemantics.Context) (outer : Substitution) : Prop :=
  ∃ resolvedType inferred initializerState locals valueType generalized
    binding,
    Detail.resolveSourceType inferenceContext sourceType =
      .ok resolvedType ∧
    Detail.inferExprFuel fuel inferenceContext initializer
      (some resolvedType) initial = .ok (inferred, initializerState) ∧
    locals = initializerState.binderEnvironment.apply
      initializerState.inference.substitution ∧
    valueType = initializerState.resolve inferred.type ∧
    generalized = Detail.generalizeValue initializerState locals
      initial.nextRequirement valueType ∧
    (initializerState.withLocals locals).allocateBinder name.value
      generalized.scheme (some name.span) false
      generalized.requirements = binding ∧
    result = (.letDecl binding.1 (some inferred.id), binding.2) ∧
    ExpressionHasType semanticSource semanticContext inferred.id
      (outer.apply inferred.type)

/-- An annotated initialized header let is monomorphic after successful
source-type resolution.  Its actual initializer supplies the sole recursive
typing obligation; the final binder and lexical invariant are reconstructed
from the recorded inference trace. -/
theorem inferForItemFuel_success_letAnnotatedInitialized_of_certificate
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {expectedReturn : Ty}
    {item : Syntax.ForItem} {name : Syntax.Identifier}
    {sourceType : Syntax.TypeExpr} {initializer : Syntax.Expr}
    {initial : State} {result : ForItemForm × State}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {semanticContext : SourceSemantics.Context}
    {control : ControlContext}
    (success : Detail.inferForItemFuel (fuel + 1) inferenceContext item
      initial = .ok result)
    (signatureFormation : ProgramSignatureFormationValidated
      inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈
      inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (canonical : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (signaturesEq : semanticContext.signatures =
      inferenceContext.signatures)
    (parametersEq : semanticContext.typeParameters =
      inferenceContext.typeParameters)
    (declarationEq : semanticContext.currentDeclaration =
      some inferenceContext.scope.genericOwner)
    (initialInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initial semanticContext)
    (sourceOwner : semanticSource.owner = initial.owner)
    (substitutionExtension : finalized.substitution.SemanticallyExtends
      result.2.inference.substitution)
    (actual : ActualAnnotatedInitializedForItemCertificate fuel
      inferenceContext name sourceType initializer initial result
      semanticSource semanticContext finalized.substitution) :
    ∃ finalContext,
      RecursiveStatementInvariant wholeContext expectedReturn finalized
        result.2 finalContext ∧
      ForItemHasType semanticSource control semanticContext
        (result.1.applySubstitution finalized.substitution)
        finalContext := by
  obtain ⟨resolvedType, inferred, initializerState, locals, valueType,
      generalized, binding, resolution, childSuccess, localsEq,
      valueTypeEq, generalizedEq, bindingEq, resultEq, childTyping⟩ :=
    actual
  have resolvedBelow : resolvedType.VariablesBelow
      initial.inference.next :=
    Detail.resolveSourceType_success_variablesBelow resolution _
  have childProperties := Detail.inferExprFuel_inferenceProperties
    initialInvariant.ready signatureFormation functionsCanonical (by
      intro expected member
      simp only [Option.mem_def] at member
      injection member with expectedEq
      subst expected
      exact resolvedBelow) childSuccess
  have rawExpected : initializerState.resolve inferred.type =
      initializerState.resolve resolvedType :=
    inferExprFuel_success_expected_type_afterProgress childSuccess
      (State.InferenceProgress.refl childProperties.2.1.solved)
  have annotationValueEq : valueType =
      initializerState.resolve resolvedType :=
    valueTypeEq.trans rawExpected
  obtain ⟨typeWellFormed, closedSchemeEq, closedRequirementsEq,
      generalizes⟩ :=
    resolvedAnnotationBinderFacts_afterSubstitution
      (target := semanticContext) (outer := finalized.substitution)
      (inferenceContext := inferenceContext)
      (name := name) (sourceType := sourceType)
      (state := initializerState) (final := binding.2)
      (requirementStart := initial.nextRequirement)
      (resolvedType := resolvedType) (valueType := valueType)
      (locals := locals) (generalized := generalized)
      (binder := binding.1)
      resolution annotationValueEq generalizedEq bindingEq canonical
      signaturesEq parametersEq declarationEq
  have initializerExtension : finalized.substitution.SemanticallyExtends
      initializerState.inference.substitution := by
    have bindingInferenceEq : binding.2.inference =
        initializerState.inference := by
      have finalEq := congrArg Prod.snd bindingEq
      rw [← finalEq]
      rfl
    have resultExtension : finalized.substitution.SemanticallyExtends
        binding.2.inference.substitution := by
      simpa [resultEq] using substitutionExtension
    rw [bindingInferenceEq] at resultExtension
    exact resultExtension
  have outerExpected : finalized.substitution.apply inferred.type =
      finalized.substitution.apply resolvedType :=
    Detail.inferExprFuel_expected_type_apply_eq childSuccess
      initializerExtension
  have resolvedByOuter : finalized.substitution.apply resolvedType =
      resolvedType :=
    Detail.resolveSourceType_success_apply_eq_self
      finalized.substitution resolution
  have initializerType : ExpressionHasType semanticSource semanticContext
      inferred.id (binding.1.applySubstitution finalized.substitution
        ).scheme.body := by
    rw [closedSchemeEq]
    change ExpressionHasType semanticSource semanticContext inferred.id
      resolvedType
    rw [← resolvedByOuter, ← outerExpected]
    exact childTyping
  let finalContext := semanticContext.withLocal binding.1.id
    (binding.1.applySubstitution finalized.substitution).scheme
    (binding.1.applySubstitution finalized.substitution).schemeRequirements
  have initializerActive : ActiveLocalContextInvariant initializerState
      finalized.substitution semanticContext :=
    initialInvariant.active.inferExprFuel childSuccess
  have initializerBelow : initializerState.LocalBindersBelowNextLocal :=
    Detail.inferExprFuel_preserves_localBindersBelowNextLocal
      initialInvariant.bindersBelow childSuccess
  have activeFinal : ActiveLocalContextInvariant binding.2
      finalized.substitution finalContext :=
    resolvedAnnotationBinderPreservesActiveLocalContextInvariant_afterSubstitution
      resolution annotationValueEq generalizedEq bindingEq canonical
      signaturesEq parametersEq declarationEq initializerActive
      initializerBelow
  have rawExtension : BinderExtends
      (initializerState.withLocals locals).owner semanticContext
      (binding.1.applySubstitution finalized.substitution)
      finalContext := by
    apply (initializerActive.aligned.withLocals locals
      ).monomorphicBinderExtends_of_allocateBinder
        (State.withLocals_preserves_localBindersBelowNextLocal
          initializerState locals initializerBelow)
        bindingEq closedSchemeEq closedRequirementsEq typeWellFormed
  have semanticExtension : BinderExtends semanticSource.owner
      semanticContext (binding.1.applySubstitution finalized.substitution)
      finalContext := by
    have ownerPreserved : initializerState.owner = initial.owner :=
      Detail.inferExprFuel_preserves_owner childSuccess
    rw [sourceOwner, ← ownerPreserved]
    simpa [State.withLocals] using rawExtension
  have monomorphic :
      (binding.1.applySubstitution finalized.substitution).scheme.quantified =
        [] := by
    rw [closedSchemeEq]
    rfl
  have typingRaw : ForItemHasType semanticSource control semanticContext
      (.letDecl (binding.1.applySubstitution finalized.substitution)
        (some inferred.id)) finalContext :=
    .letInitialized initializerType monomorphic generalizes
      semanticExtension
  have typing : ForItemHasType semanticSource control semanticContext
      (result.1.applySubstitution finalized.substitution) finalContext := by
    simpa [resultEq, ForItemForm.applySubstitution] using typingRaw
  have valueClosed : valueType.freeVariables = [] := by
    have resolvedClosed :=
      StructuralSubstitution.TypeWellFormed.freeVariables_eq_nil
        typeWellFormed
    have resolvedByState : initializerState.resolve resolvedType =
        resolvedType := by
      simpa [State.resolve, InferState.resolve] using
        (Detail.resolveSourceType_success_apply_eq_self
          initializerState.inference.substitution resolution)
    rw [valueTypeEq, rawExpected, resolvedByState]
    exact resolvedClosed
  have generalizedFacts := generalizeValue_closed_facts initializerState
    locals initial.nextRequirement valueType semanticContext valueClosed
  have generalizedSchemeEq : generalized.scheme = .mono valueType := by
    rw [generalizedEq]
    exact generalizedFacts.1
  have generalizedRequirementsEq : generalized.requirements = [] := by
    rw [generalizedEq]
    exact generalizedFacts.2.1
  have childBindersEq : initializerState.localBinders =
      initial.localBinders := by
    simpa [State.lexicalScope] using congrArg LexicalScope.binders
      (Detail.inferExprFuel_success_lexicalScope_eq childSuccess)
  have childIsolated : ActiveSchemeQuantifierIsolation initializerState :=
    activeSchemeQuantifierIsolation_transport
      initialInvariant.schemeIsolation childBindersEq
  have isolatedWithLocals : ActiveSchemeQuantifierIsolation
      (initializerState.withLocals locals) :=
    activeSchemeQuantifierIsolation_transport childIsolated rfl
  have bindingIsolated : ActiveSchemeQuantifierIsolation binding.2 := by
    rw [← bindingEq, generalizedSchemeEq, generalizedRequirementsEq]
    exact activeSchemeQuantifierIsolation_allocateMonoBinder
      (initializerState.withLocals locals) name.value valueType
      (some name.span) isolatedWithLocals (by
        intro metavariable member
        simp [valueClosed] at member)
  have resultActive : ActiveLocalContextInvariant result.2
      finalized.substitution finalContext := by
    simpa [resultEq] using activeFinal
  have resultIsolated : ActiveSchemeQuantifierIsolation result.2 := by
    simpa [resultEq] using bindingIsolated
  have finalInvariant := RecursiveStatementInvariant.of_forItem_typing
    initialInvariant success signatureFormation functionsCanonical
    resultActive resultIsolated substitutionExtension typing
  exact ⟨finalContext, finalInvariant, typing⟩

/-- The one-item recursive goal is tied to an actual successful
`inferForItemFuel` trace and to the same finalized whole-body evidence used by
the enclosing loop.  Its proof must inspect only the child computations
selected by that item, including the concrete generalized-let certificate. -/
def InferForItemFuelScopedSoundness (fuel : Nat) : Prop :=
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {item : Syntax.ForItem} {initial final : State}
    {inferred : ForItemForm} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {semanticContext : SourceSemantics.Context}
    {control : ControlContext},
    Detail.inferForItemFuel fuel inferenceContext item initial =
      .ok (inferred, final) →
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
    finalized.substitution.SemanticallyExtends final.inference.substitution →
    TypingSourceExtends
      ((final.toTypedSource roots).applySubstitution
        finalized.substitution) semanticSource →
    TypingSourceExtends semanticSource finalized.typedSource →
    TypingSourceExtends (final.toTypedSource roots)
      (evidenceState.toTypedSource roots) →
    final.integerPatterns ⊆ evidenceState.integerPatterns →
    final.integerLiterals ⊆ evidenceState.integerLiterals →
    final.requirements ⊆ evidenceState.requirements →
    semanticSource.owner = initial.owner →
    ForItemReferencesCovered finalized.typedSource
      finalized.substitution semanticContext inferred →
    ForItemBindingRetained (evidenceState.toTypedSource roots) inferred →
    ∃ finalContext,
      RecursiveStatementInvariant wholeContext expectedReturn finalized
        final finalContext ∧
      ForItemHasType semanticSource control semanticContext
        (inferred.applySubstitution finalized.substitution)
        finalContext

/-- The corresponding whole-header goal.  Coverage follows exactly the
references stored in the returned item forms, so a later binder never has to
be guessed from syntax before the inference trace is known. -/
def InferForItemsFuelScopedSoundness (fuel : Nat) : Prop :=
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {items : List Syntax.ForItem} {initial : State}
    {result : Detail.InferredForItems} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {semanticContext : SourceSemantics.Context}
    {control : ControlContext},
    Detail.inferForItemsFuel fuel inferenceContext items initial = .ok result →
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
    semanticSource.owner = initial.owner →
    ForItemsReferencesCovered finalized.typedSource finalized.substitution
      semanticContext result.items →
    ForItemsBindingsRetained (evidenceState.toTypedSource roots)
      result.items →
    ∃ finalContext,
      RecursiveStatementInvariant wholeContext expectedReturn finalized
        result.state finalContext ∧
      ForItemsHaveType semanticSource control semanticContext
        (result.items.map (ForItemForm.applySubstitution
          finalized.substitution)) finalContext

/-- One-step actual-success soundness composes across the source-ordered
header.  Each head receives provenance from its *actual* inferred suffix,
while the same final substitution, evidence ledgers, and semantic source are
retained for all items. -/
theorem inferForItemsFuelScopedSoundness_of_itemSoundness
    {fuel : Nat}
    (itemSound : InferForItemFuelScopedSoundness fuel) :
    InferForItemsFuelScopedSoundness fuel := by
  intro wholeContext inferenceContext wholeReturn expectedReturn items
    initial result evidenceState roots finalized semanticSource
    semanticContext control success resources signaturesEq ownerEq
    parametersEq assumptionsEq signatureFormation functionsCanonical
    catalog signatureParameters initialInvariant substitutionExtension
    resultExtension semanticSourceExtension rawResultExtension
    integerPatternsSubset integerLiteralsSubset requirementsSubset
    sourceOwner covered bindingsRetained
  induction items generalizing initial result semanticContext with
  | nil =>
      simp only [Detail.inferForItemsFuel, pure, Pure.pure, Except.pure]
        at success
      injection success with resultEq
      subst result
      exact ⟨semanticContext, initialInvariant,
        ForItemsHaveType.nil control semanticContext⟩
  | cons item rest induction =>
      unfold Detail.inferForItemsFuel at success
      cases itemSuccess : Detail.inferForItemFuel fuel inferenceContext item
          initial with
      | error error =>
          simp [itemSuccess, bind, Except.bind] at success
      | ok itemPair =>
          rcases itemPair with ⟨inferredItem, itemState⟩
          simp only [itemSuccess, bind, Except.bind] at success
          cases tailSuccess : Detail.inferForItemsFuel fuel inferenceContext
              rest itemState with
          | error error =>
              simp [tailSuccess] at success
          | ok tail =>
              simp only [tailSuccess, pure, Pure.pure, Except.pure] at success
              injection success with resultEq
              subst result
              have itemProperties := Detail.inferForItemFuel_inferenceProperties
                initialInvariant.ready signatureFormation functionsCanonical
                itemSuccess
              have tailProperties := Detail.inferForItemsFuel_inferenceProperties
                itemProperties.2 signatureFormation functionsCanonical
                tailSuccess
              have itemSubstitutionExtension :
                  finalized.substitution.SemanticallyExtends
                    itemState.inference.substitution :=
                substitutionExtension.trans
                  tailProperties.1.substitution_extends
              have itemBelow : itemState.NodesBelowNextOccurrence :=
                (Detail.inferForItemFuel_occurrenceBoundExtends itemSuccess
                  ).nodesBelowNextOccurrence initialInvariant.nodesBelow
              have itemToResult : TypingSourceExtends
                  (itemState.toTypedSource roots)
                  (tail.state.toTypedSource roots) :=
                inferForItemsFuel_success_typingSourceExtends tailSuccess
                  itemBelow roots
              have itemExtension : TypingSourceExtends
                  ((itemState.toTypedSource roots).applySubstitution
                    finalized.substitution) semanticSource :=
                (TypingSourceExtends.applySubstitution
                  finalized.substitution itemToResult).trans resultExtension
              have itemRawExtension : TypingSourceExtends
                  (itemState.toTypedSource roots)
                  (evidenceState.toTypedSource roots) :=
                itemToResult.trans rawResultExtension
              have itemPatternsSubset : itemState.integerPatterns ⊆
                  evidenceState.integerPatterns := by
                intro origin member
                exact integerPatternsSubset
                  ((Detail.inferForItemsFuel_integerPatterns_subset
                    tailSuccess) member)
              have itemLiteralsSubset : itemState.integerLiterals ⊆
                  evidenceState.integerLiterals := by
                intro origin member
                exact integerLiteralsSubset
                  ((Detail.inferForItemsFuel_integerLiterals_subset
                    tailSuccess) member)
              have itemRequirementsSubset : itemState.requirements ⊆
                  evidenceState.requirements := by
                intro requirement member
                exact requirementsSubset
                  ((Detail.inferForItemsFuel_requirements_subset
                    tailSuccess) member)
              have itemCovered : ForItemReferencesCovered
                  finalized.typedSource finalized.substitution
                  semanticContext inferredItem := by
                apply covered
                simp
              have itemBindingsRetained : ForItemBindingRetained
                  (evidenceState.toTypedSource roots) inferredItem := by
                intro binding member
                apply bindingsRetained
                simp only [List.flatMap_cons, List.mem_append]
                exact Or.inl member
              obtain ⟨middleContext, middleInvariant, itemTyping⟩ :=
                itemSound itemSuccess resources signaturesEq ownerEq
                  parametersEq assumptionsEq signatureFormation
                  functionsCanonical catalog signatureParameters
                  initialInvariant itemSubstitutionExtension itemExtension
                  semanticSourceExtension itemRawExtension itemPatternsSubset
                  itemLiteralsSubset itemRequirementsSubset sourceOwner
                  itemCovered itemBindingsRetained
              have tailOwner : semanticSource.owner = itemState.owner :=
                sourceOwner.trans
                  (Detail.inferForItemFuel_preserves_owner itemSuccess).symm
              have tailCovered : ForItemsReferencesCovered
                  finalized.typedSource finalized.substitution middleContext
                  tail.items := by
                intro nextItem member
                have original : ForItemReferencesCovered
                    finalized.typedSource finalized.substitution
                    semanticContext nextItem := by
                  apply covered
                  simp [member]
                exact original.transportAssumptions
                  (forItemHasType_assumptions_eq itemTyping)
              have tailBindingsRetained : ForItemsBindingsRetained
                  (evidenceState.toTypedSource roots) tail.items := by
                intro binding member
                apply bindingsRetained
                simp only [List.flatMap_cons, List.mem_append]
                exact Or.inr member
              obtain ⟨finalContext, finalInvariant, tailTyping⟩ :=
                induction (initial := itemState) (result := tail)
                  (semanticContext := middleContext) tailSuccess
                  middleInvariant substitutionExtension
                  resultExtension rawResultExtension
                  integerPatternsSubset integerLiteralsSubset
                  requirementsSubset tailOwner tailCovered
                  tailBindingsRetained
              refine ⟨finalContext, finalInvariant, ?_⟩
              exact ForItemsHaveType.cons itemTyping tailTyping

end Solcore.SourceSemantics.SourceInferenceSoundness
