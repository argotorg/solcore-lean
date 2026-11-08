import Solcore.SourceSemantics.Internal.Inference.StatementResources
import Solcore.SourceSemantics.Internal.Inference.LetCertificates
import Solcore.SourceSemantics.Internal.Inference.ExpressionCalls

/-!
# Conditions, loops and matches

Actual-success resources for statement conditions, expression children, restricted `for` headers and
`match` statements.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceForItemsScopedSoundness
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
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceForItemsCoverage
/-!
Coverage of the actual references in a recorded `for` header.  Unlike an
ordinary statement child, a generalized header initializer introduces local
scheme assumptions.  Unique child slots identify the exact header item whose
binder owns those assumptions.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem

private theorem eq_of_common_mem_of_flatMap_nodup
    {α β : Type} (f : α → List β)
    {values : List α} {left right : α} {value : β}
    (unique : (values.flatMap f).Nodup)
    (leftMem : left ∈ values) (rightMem : right ∈ values)
    (leftValue : value ∈ f left) (rightValue : value ∈ f right) :
    left = right := by
  induction values generalizing left right with
  | nil => simp at leftMem
  | cons head tail ih =>
      simp only [List.flatMap_cons, List.nodup_append] at unique
      rcases unique with ⟨_, tailUnique, separated⟩
      simp only [List.mem_cons] at leftMem rightMem
      rcases leftMem with rfl | leftMem
      · rcases rightMem with rfl | rightMem
        · rfl
        · exfalso
          exact separated value leftValue value
            (List.mem_flatMap.mpr ⟨right, rightMem, rightValue⟩) rfl
      · rcases rightMem with rfl | rightMem
        · exfalso
          exact separated value rightValue value
            (List.mem_flatMap.mpr ⟨left, leftMem, leftValue⟩) rfl
        · exact ih tailUnique leftMem rightMem leftValue rightValue

/-- Forgetting the condition and body slots of a closed `for` node still
leaves a globally unique source-ordered header reference inventory. -/
private theorem forLoop_header_references_nodup
    {source : TypedSource} {id : StatementId} {node : StatementNode}
    {initializer post : List ForItemForm} {condition : ExpressionId}
    {body : List StatementId}
    (closed : OccurrenceGraphClosed source)
    (contains : ContainsStatement source id node)
    (formEq : node.form = .forLoop initializer condition post body) :
    ((initializer ++ post).flatMap ForItemForm.references).Nodup := by
  have slots := closed.childSlotsUnique (.statement node) contains.1
  simp only [nodeChildIds, Node.references, formEq,
    StatementForm.references] at slots
  simp only [List.append_assoc] at slots
  have initUnique : (initializer.flatMap ForItemForm.references).Nodup :=
    (List.nodup_append.mp slots).1
  have restUnique := (List.nodup_append.mp slots).2.1
  have postUnique : (post.flatMap ForItemForm.references).Nodup :=
    (List.nodup_append.mp (List.nodup_append.mp restUnique).2.1).1
  have separated := (List.nodup_append.mp slots).2.2
  have combined :
      (initializer.flatMap ForItemForm.references ++
        post.flatMap ForItemForm.references).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨initUnique, postUnique, ?_⟩
    intro value initMember value' postMember eq
    apply separated value initMember value'
    · exact List.mem_append_right _
        (List.mem_append_left _ postMember)
    · exact eq
  simpa [List.flatMap_append] using combined

private theorem forItem_binding_initializer_mem_references
    {item : ForItemForm} {binding : InitializedLetBinding}
    (member : binding ∈ forItemInitializedLetBindings item) :
    binding.initializer ∈ item.references := by
  cases item with
  | letDecl binder initializer =>
      cases initializer with
      | none => simp [forItemInitializedLetBindings] at member
      | some initializer =>
          have bindingEq : binding = {
              binder := binder, initializer := .expression initializer } := by
            simpa [forItemInitializedLetBindings] using member
          subst binding
          simp [ForItemForm.references]
  | expression _ => simp [forItemInitializedLetBindings] at member
  | assignValue _ _ _ => simp [forItemInitializedLetBindings] at member
  | assignBitNot _ => simp [forItemInitializedLetBindings] at member

/-- Any qualified template whose root is a reference of one selected header
item must be owned by a binding of that very item.  The graph's unique parent
identifies the enclosing statement; unique child slots identify the item. -/
private theorem forLoop_template_binding_of_item_reference
    {source : TypedSource} {id : StatementId} {node : StatementNode}
    {initializer post : List ForItemForm} {condition : ExpressionId}
    {body : List StatementId} {item : ForItemForm} {reference : NodeId}
    {owner : LocalSchemeTemplateOwner}
    (closed : OccurrenceGraphClosed source)
    (contains : ContainsStatement source id node)
    (formEq : node.form = .forLoop initializer condition post body)
    (itemMem : item ∈ initializer ++ post)
    (referenceMem : reference ∈ item.references)
    (ownerContains : ContainsLocalSchemeTemplate source owner)
    (initializerEq : owner.initializer = reference) :
    ({ binder := owner.binder, initializer := owner.initializer } :
      InitializedLetBinding) ∈ forItemInitializedLetBindings item := by
  have bindingMem := owner.binding_mem ownerContains
  obtain ⟨ownerNode, ownerNodeContains, ownerBindingMem, ownerEdge⟩ :=
    InitializedLetBinding.owningStatement bindingMem
  have selectedEdge : DirectChild source (.statement id) reference := by
    refine ⟨.statement node, ?_, ?_⟩
    · exact ⟨contains.1, congrArg NodeId.statement contains.2⟩
    · have headerMem : reference ∈
          (initializer ++ post).flatMap ForItemForm.references :=
        List.mem_flatMap.mpr ⟨item, itemMem, referenceMem⟩
      have either : reference ∈ initializer.flatMap ForItemForm.references ∨
          reference ∈ post.flatMap ForItemForm.references := by
        simpa [List.flatMap_append] using headerMem
      have full : reference ∈
          (StatementForm.forLoop initializer condition post body).references := by
        simp only [StatementForm.references, List.mem_append]
        rcases either with initialRef | postRef
        · exact Or.inl (Or.inl (Or.inl initialRef))
        · exact Or.inl (Or.inr postRef)
      simpa [nodeChildIds, Node.references, formEq] using full
  have parentEq : ownerNode.id = id := by
    have parentsEq := closed.childHasUniqueParent
      (by simpa [initializerEq] using ownerEdge) selectedEdge
    cases parentsEq
    rfl
  have nodeEq : ownerNode = node := by
    have ownerLookup := lookupStatement?_complete
      closed.wellFormed.nodeOccurrencesUnique ownerNodeContains
    have selectedLookup := lookupStatement?_complete
      closed.wellFormed.nodeOccurrencesUnique contains
    rw [parentEq, selectedLookup] at ownerLookup
    exact Option.some.inj ownerLookup.symm
  subst ownerNode
  have bindingInHeaders :
      ({ binder := owner.binder, initializer := owner.initializer } :
        InitializedLetBinding) ∈
        (initializer ++ post).flatMap forItemInitializedLetBindings := by
    simpa [formEq, statementInitializedLetBindings,
      List.flatMap_append] using ownerBindingMem
  rcases List.mem_flatMap.mp bindingInHeaders with
    ⟨ownerItem, ownerItemMem, ownerItemBindingMem⟩
  have ownerReference : reference ∈ ownerItem.references := by
    simpa [initializerEq] using
      forItem_binding_initializer_mem_references ownerItemBindingMem
  have itemEq : item = ownerItem :=
    eq_of_common_mem_of_flatMap_nodup ForItemForm.references
      (forLoop_header_references_nodup closed contains formEq)
      itemMem ownerItemMem referenceMem ownerReference
  simpa [itemEq] using ownerItemBindingMem

private theorem forLoop_header_directChild
    {source : TypedSource} {id : StatementId} {node : StatementNode}
    {initializer post : List ForItemForm} {condition : ExpressionId}
    {body : List StatementId} {item : ForItemForm} {reference : NodeId}
    (contains : ContainsStatement source id node)
    (formEq : node.form = .forLoop initializer condition post body)
    (itemMem : item ∈ initializer ++ post)
    (referenceMem : reference ∈ item.references) :
    DirectChild source (.statement id) reference := by
  refine ⟨.statement node, ?_, ?_⟩
  · exact ⟨contains.1, congrArg NodeId.statement contains.2⟩
  · have headerMem : reference ∈
        (initializer ++ post).flatMap ForItemForm.references :=
      List.mem_flatMap.mpr ⟨item, itemMem, referenceMem⟩
    have either : reference ∈ initializer.flatMap ForItemForm.references ∨
        reference ∈ post.flatMap ForItemForm.references := by
      simpa [List.flatMap_append] using headerMem
    have full : reference ∈
        (StatementForm.forLoop initializer condition post body).references := by
      simp only [StatementForm.references, List.mem_append]
      rcases either with initialRef | postRef
      · exact Or.inl (Or.inl (Or.inl initialRef))
      · exact Or.inl (Or.inr postRef)
    simpa [nodeChildIds, Node.references, formEq] using full

/-- Every reference in the recorded final `for` header is covered.  The
context of a generalized let initializer carries precisely its own qualified
scheme predicates; all other references inherit the loop context. -/
theorem forLoop_finalHeaderReferencesCovered
    {source : TypedSource} {id : StatementId} {node : StatementNode}
    {initializer post : List ForItemForm} {condition : ExpressionId}
    {body : List StatementId} {context : SourceSemantics.Context}
    (closed : OccurrenceGraphClosed source)
    (contains : ContainsStatement source id node)
    (formEq : node.form = .forLoop initializer condition post body)
    (parentCovered : TemplateScopeCovered source context (.statement id)) :
    ∀ item, item ∈ initializer ++ post → ∀ reference,
      reference ∈ item.references →
      TemplateScopeCovered source
        (match item with
         | .letDecl binder (some _) =>
             localSchemeInitializerContext context binder
         | _ => context)
        reference := by
  intro item itemMem reference referenceMem
  have edge : DirectChild source (.statement id) reference :=
    forLoop_header_directChild contains formEq itemMem referenceMem
  cases item with
  | letDecl binder initializerId =>
      cases initializerId with
      | none => simp [ForItemForm.references] at referenceMem
      | some initializerId =>
          have referenceEq : reference = .expression initializerId := by
            simpa [ForItemForm.references] using referenceMem
          subst reference
          apply TemplateScopeCovered.localSchemeInitializer_of_newRoots
            parentCovered closed.childHasUniqueParent edge
          intro owner ownerContains ownerInitializerEq
          have bindingMem := forLoop_template_binding_of_item_reference
            closed contains formEq itemMem
            (by simp [ForItemForm.references]) ownerContains
            ownerInitializerEq
          have binderEq : owner.binder = binder := by
            have bindingEq :
                ({ binder := owner.binder, initializer := owner.initializer } :
                  InitializedLetBinding) = {
                    binder := binder, initializer := .expression initializerId
                  } := by
              simpa [forItemInitializedLetBindings] using bindingMem
            exact congrArg InitializedLetBinding.binder bindingEq
          simpa [binderEq] using owner.requirement_mem ownerContains
  | expression expression =>
      apply TemplateScopeCovered.child parentCovered
        closed.childHasUniqueParent edge (fun _ member => member)
      intro owner ownerContains ownerInitializerEq
      have bindingMem := forLoop_template_binding_of_item_reference
        closed contains formEq itemMem referenceMem ownerContains
        ownerInitializerEq
      simp [forItemInitializedLetBindings] at bindingMem
  | assignValue assignment operator value =>
      apply TemplateScopeCovered.child parentCovered
        closed.childHasUniqueParent edge (fun _ member => member)
      intro owner ownerContains ownerInitializerEq
      have bindingMem := forLoop_template_binding_of_item_reference
        closed contains formEq itemMem referenceMem ownerContains
        ownerInitializerEq
      simp [forItemInitializedLetBindings] at bindingMem
  | assignBitNot assignment =>
      apply TemplateScopeCovered.child parentCovered
        closed.childHasUniqueParent edge (fun _ member => member)
      intro owner ownerContains ownerInitializerEq
      have bindingMem := forLoop_template_binding_of_item_reference
        closed contains formEq itemMem referenceMem ownerContains
        ownerInitializerEq
      simp [forItemInitializedLetBindings] at bindingMem

/-- The actual recorded raw loop, together with final substitution and
append-only source growth, discharges both coverage premises passed to the
initializer and post-item recursive traversals.  This theorem does not assume
that unrelated arbitrary children are covered. -/
theorem forItemsReferencesCovered_of_recordedForLoop
    {rawSource finalSource : TypedSource} {outer : Substitution}
    {id : StatementId} {node : StatementNode}
    {initializer post : List ForItemForm} {condition : ExpressionId}
    {body : List StatementId} {context : SourceSemantics.Context}
    (containsRaw : ContainsStatement rawSource id node)
    (formEq : node.form = .forLoop initializer condition post body)
    (extension : TypingSourceExtends
      (rawSource.applySubstitution outer) finalSource)
    (closed : OccurrenceGraphClosed finalSource)
    (parentCovered : TemplateScopeCovered finalSource context
      (.statement id)) :
    ForItemsReferencesCovered finalSource outer context initializer ∧
      ForItemsReferencesCovered finalSource outer context post := by
  have containsFinal : ContainsStatement finalSource id
      (node.applySubstitution outer) :=
    extension.containsStatement
      (FlexibleSubstitution.ContainsStatement.applySubstitution outer
        containsRaw)
  have finalForm : (node.applySubstitution outer).form =
      .forLoop (initializer.map (ForItemForm.applySubstitution outer))
        condition (post.map (ForItemForm.applySubstitution outer)) body := by
    simp [StatementNode.applySubstitution, formEq,
      StatementForm.applySubstitution]
  have covered := forLoop_finalHeaderReferencesCovered closed
    containsFinal finalForm parentCovered
  constructor
  · intro item itemMem reference referenceMem
    have finalItemMem : item.applySubstitution outer ∈
        (initializer.map (ForItemForm.applySubstitution outer)) ++
          (post.map (ForItemForm.applySubstitution outer)) := by
      exact List.mem_append_left _
        (List.mem_map.mpr ⟨item, itemMem, rfl⟩)
    have finalRefMem : reference ∈
        (item.applySubstitution outer).references := by
      simpa using referenceMem
    have finalCovered := covered (item.applySubstitution outer)
      finalItemMem reference finalRefMem
    cases item with
    | letDecl binder initializerId =>
        cases initializerId <;>
          simpa [forItemCoverageContext, ForItemForm.applySubstitution]
            using finalCovered
    | expression expression =>
        simpa [forItemCoverageContext, ForItemForm.applySubstitution]
          using finalCovered
    | assignValue assignment operator value =>
        simpa [forItemCoverageContext, ForItemForm.applySubstitution]
          using finalCovered
    | assignBitNot assignment =>
        simpa [forItemCoverageContext, ForItemForm.applySubstitution]
          using finalCovered
  · intro item itemMem reference referenceMem
    have finalItemMem : item.applySubstitution outer ∈
        (initializer.map (ForItemForm.applySubstitution outer)) ++
          (post.map (ForItemForm.applySubstitution outer)) := by
      exact List.mem_append_right _
        (List.mem_map.mpr ⟨item, itemMem, rfl⟩)
    have finalRefMem : reference ∈
        (item.applySubstitution outer).references := by
      simpa using referenceMem
    have finalCovered := covered (item.applySubstitution outer)
      finalItemMem reference finalRefMem
    cases item with
    | letDecl binder initializerId =>
        cases initializerId <;>
          simpa [forItemCoverageContext, ForItemForm.applySubstitution]
            using finalCovered
    | expression expression =>
        simpa [forItemCoverageContext, ForItemForm.applySubstitution]
          using finalCovered
    | assignValue assignment operator value =>
        simpa [forItemCoverageContext, ForItemForm.applySubstitution]
          using finalCovered
    | assignBitNot assignment =>
        simpa [forItemCoverageContext, ForItemForm.applySubstitution]
          using finalCovered
end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceStatementConditionSoundness
/-!
Actual-success condition-expression typing for statement branches.  The
condition is checked in the completed parent statement source; the proof
tracks its precise inference state through the body and the final record.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem
open SourceInferenceStatementsSoundness

/-- The condition of a successful `while` statement is typed by the actual
expression-inference call, with all evidence and template coverage inherited
from its enclosing completed statement. -/
theorem inferStatementFuel_success_whileLoop_condition_scoped
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {condition : Syntax.Expr}
    {body : Syntax.Block}
    {initial allocated evidenceState : State}
    {id : StatementId} {result : Detail.StatementResult}
    {roots : List NodeId} {finalized : Frontend.SourceInference.Result}
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
    (assumptionsEq : inferenceContext.assumptions = wholeContext.assumptions)
    (signatureFormation : ProgramSignatureFormationValidated
      inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈ inferenceContext.signatures.functions,
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
    (expressionSound : InferExprFuelScopedSoundness fuel) :
    ∀ {inferredCondition : InferredExpression} {conditionState : State},
      Detail.inferExprFuel fuel inferenceContext condition (some .bool)
        allocated = .ok (inferredCondition, conditionState) →
      ExpressionHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        semanticContext inferredCondition.id
        (finalized.substitution.apply inferredCondition.type) := by
  intro inferredCondition conditionState conditionSuccess
  obtain ⟨actualCondition, actualConditionState, bodyResult,
      actualConditionSuccess, bodySuccess, resultEq, containsRaw⟩ :=
    inferStatementFuel_success_whileLoop_facts statementEq allocationEq
      success roots
  rw [conditionSuccess] at actualConditionSuccess
  obtain ⟨rfl, rfl⟩ := (Except.ok.inj actualConditionSuccess).symm
  obtain ⟨actualConditionState, actualBodyResult,
      ⟨actualCondition', actualConditionSuccess'⟩, actualBodySuccess',
      conditionBelow, bodySourceExtension,
      bodyPatternsSubset, bodyRequirementsSubset⟩ :=
    inferStatementFuel_success_whileLoop_child_provenance statementEq
      allocationEq success initialInvariant.nodesBelow roots
  have conditionStateEq : actualConditionState = conditionState := by
    rw [conditionSuccess] at actualConditionSuccess'
    exact (congrArg Prod.snd
      (Except.ok.inj actualConditionSuccess')).symm
  subst actualConditionState
  have bodyResultEq : actualBodyResult = bodyResult := by
    rw [bodySuccess] at actualBodySuccess'
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
    (context := { inferenceContext with
      loopDepth := inferenceContext.loopDepth + 1 })
    conditionProperties.2.1 signatureFormation functionsCanonical
    conditionReturnBelow bodySuccess
  have bodySubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        bodyResult.state.inference.substitution := by
    simpa [resultEq, State.restoreLexicalScope, State.recordNode] using
      resultSubstitutionExtension
  have conditionSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        conditionState.inference.substitution :=
    Substitution.SemanticallyExtends.trans bodySubstitutionExtension
      bodyProperties.1.substitution_extends
  have conditionToBody : TypingSourceExtends
      (conditionState.toTypedSource roots)
      (bodyResult.state.toTypedSource roots) :=
    inferStatementsFuel_success_typingSourceExtends bodySuccess
      conditionBelow roots
  have conditionToParent : TypingSourceExtends
      (conditionState.toTypedSource roots)
      (result.state.toTypedSource roots) :=
    conditionToBody.trans bodySourceExtension
  have bodyLiteralsSubset : bodyResult.state.integerLiterals ⊆
      result.state.integerLiterals := by
    rw [resultEq]
    intro literal member
    simpa [State.restoreLexicalScope, State.recordNode] using member
  have containsFinal : ContainsStatement finalized.typedSource result.id
      (({
        id := result.id
        span := statement.span
        type := result.type
        form := .whileLoop inferredCondition.id bodyResult.statements
      } : StatementNode).applySubstitution finalized.substitution) :=
    resultExtension.containsStatement
      (FlexibleSubstitution.ContainsStatement.applySubstitution
        finalized.substitution containsRaw)
  have conditionCovered : TemplateScopeCovered finalized.typedSource
      semanticContext (.expression inferredCondition.id) := by
    apply TemplateScopeCovered.statementExpressionChild_of_noBindings_and_reference
      parentCovered resources.graph_closed containsFinal
    · simp [StatementNode.applySubstitution, StatementForm.applySubstitution,
        statementInitializedLetBindings]
    · simp [StatementNode.applySubstitution, StatementForm.applySubstitution,
        StatementForm.references]
  exact expressionSound conditionSuccess resources
    conditionSubstitutionExtension signaturesEq ownerEq parametersEq
    assumptionsEq signatureFormation functionsCanonical catalog
    signatureParameters (RecursiveExpressionInvariant.ofStatement
      allocatedInvariant) (by
        intro expected member
        simp only [Option.mem_def] at member
        injection member with expectedEq
        subst expected
        simp [Ty.bool])
    (conditionToParent.applySubstitution finalized.substitution)
    resultExtension
    (conditionToParent.trans rawResultExtension)
    (List.Subset.trans
      (List.Subset.trans
        (Detail.inferStatementsFuel_integerPatterns_subset bodySuccess)
        bodyPatternsSubset) integerPatternsSubset)
    (List.Subset.trans
      (List.Subset.trans
        (Detail.inferStatementsFuel_integerLiterals_subset bodySuccess)
        bodyLiteralsSubset) integerLiteralsSubset)
    (List.Subset.trans
      (List.Subset.trans
        (Detail.inferStatementsFuel_requirements_subset bodySuccess)
        bodyRequirementsSubset) requirementsSubset)
    conditionCovered

/-- The with-else `if` condition remains typed after both branch traversals.
The else branch starts from the restored condition scope, but the occurrence
and requirement ledgers continue to extend the original condition state. -/
theorem inferStatementFuel_success_ifWithElse_condition_scoped
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {condition : Syntax.Expr}
    {thenBody elseBody : Syntax.Block}
    {initial allocated evidenceState : State}
    {id : StatementId} {result : Detail.StatementResult}
    {roots : List NodeId} {finalized : Frontend.SourceInference.Result}
    {semanticContext : SourceSemantics.Context}
    (statementEq : statement.value =
      .ifThen condition thenBody (some elseBody))
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
    (assumptionsEq : inferenceContext.assumptions = wholeContext.assumptions)
    (signatureFormation : ProgramSignatureFormationValidated
      inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈ inferenceContext.signatures.functions,
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
    (expressionSound : InferExprFuelScopedSoundness fuel) :
    ∀ {inferredCondition : InferredExpression} {conditionState : State},
      Detail.inferExprFuel fuel inferenceContext condition (some .bool)
        allocated = .ok (inferredCondition, conditionState) →
      ExpressionHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        semanticContext inferredCondition.id
        (finalized.substitution.apply inferredCondition.type) := by
  intro inferredCondition conditionState conditionSuccess
  obtain ⟨actualCondition, actualConditionState, thenResult, elseResult,
      actualConditionSuccess, thenSuccess, elseSuccess, resultEq,
      containsRaw⟩ :=
    inferStatementFuel_success_ifWithElse_facts statementEq allocationEq
      success roots
  rw [conditionSuccess] at actualConditionSuccess
  obtain ⟨rfl, rfl⟩ := (Except.ok.inj actualConditionSuccess).symm
  obtain ⟨provenanceConditionState, provenanceThenResult,
      provenanceElseResult, ⟨_, provenanceConditionSuccess⟩,
      provenanceThenSuccess, provenanceElseSuccess, conditionBelow,
      _elseInputBelow, thenSourceExtension, _elseSourceExtension,
      thenPatternsSubset, _elsePatternsSubset,
      thenRequirementsSubset, _elseRequirementsSubset⟩ :=
    inferStatementFuel_success_ifWithElse_child_provenance statementEq
      allocationEq success initialInvariant.nodesBelow roots
  have conditionStateEq : provenanceConditionState = conditionState := by
    rw [conditionSuccess] at provenanceConditionSuccess
    exact (congrArg Prod.snd
      (Except.ok.inj provenanceConditionSuccess)).symm
  subst provenanceConditionState
  have thenResultEq : provenanceThenResult = thenResult := by
    rw [thenSuccess] at provenanceThenSuccess
    exact (Except.ok.inj provenanceThenSuccess).symm
  subst provenanceThenResult
  have elseResultEq : provenanceElseResult = elseResult := by
    rw [elseSuccess] at provenanceElseSuccess
    exact (Except.ok.inj provenanceElseSuccess).symm
  subst provenanceElseResult
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
    Substitution.SemanticallyExtends.trans elseSubstitutionExtension
      elseProperties.1.substitution_extends
  have conditionSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        conditionState.inference.substitution :=
    Substitution.SemanticallyExtends.trans elseInputSubstitutionExtension
      restoredProperties.1.substitution_extends
  have conditionToThen : TypingSourceExtends
      (conditionState.toTypedSource roots)
      (thenResult.state.toTypedSource roots) :=
    inferStatementsFuel_success_typingSourceExtends thenSuccess
      conditionBelow roots
  have conditionToParent : TypingSourceExtends
      (conditionState.toTypedSource roots)
      (result.state.toTypedSource roots) :=
    conditionToThen.trans thenSourceExtension
  have thenLiteralsSubset : thenResult.state.integerLiterals ⊆
      result.state.integerLiterals := by
    rw [resultEq]
    intro literal member
    have inElseInput : literal ∈
        (thenResult.state.restoreLexicalScope
          conditionState.lexicalScope).integerLiterals := by
      simpa [State.restoreLexicalScope] using member
    have inElse := Detail.inferStatementsFuel_integerLiterals_subset
      elseSuccess inElseInput
    simpa [State.restoreLexicalScope, State.recordNode] using inElse
  have containsFinal : ContainsStatement finalized.typedSource result.id
      (({
        id := result.id
        span := statement.span
        type := result.type
        form := .ifThen inferredCondition.id thenResult.statements
          (some elseResult.statements)
      } : StatementNode).applySubstitution finalized.substitution) :=
    resultExtension.containsStatement
      (FlexibleSubstitution.ContainsStatement.applySubstitution
        finalized.substitution containsRaw)
  have conditionCovered : TemplateScopeCovered finalized.typedSource
      semanticContext (.expression inferredCondition.id) := by
    apply TemplateScopeCovered.statementExpressionChild_of_noBindings_and_reference
      parentCovered resources.graph_closed containsFinal
    · simp [StatementNode.applySubstitution, StatementForm.applySubstitution,
        statementInitializedLetBindings]
    · simp [StatementNode.applySubstitution, StatementForm.applySubstitution,
        StatementForm.references]
  exact expressionSound conditionSuccess resources
    conditionSubstitutionExtension signaturesEq ownerEq parametersEq
    assumptionsEq signatureFormation functionsCanonical catalog
    signatureParameters (RecursiveExpressionInvariant.ofStatement
      allocatedInvariant) (by
        intro expected member
        simp only [Option.mem_def] at member
        injection member with expectedEq
        subst expected
        simp [Ty.bool])
    (conditionToParent.applySubstitution finalized.substitution)
    resultExtension
    (conditionToParent.trans rawResultExtension)
    (List.Subset.trans
      (List.Subset.trans
        (Detail.inferStatementsFuel_integerPatterns_subset thenSuccess)
        thenPatternsSubset) integerPatternsSubset)
    (List.Subset.trans
      (List.Subset.trans
        (Detail.inferStatementsFuel_integerLiterals_subset thenSuccess)
        thenLiteralsSubset) integerLiteralsSubset)
    (List.Subset.trans
      (List.Subset.trans
        (Detail.inferStatementsFuel_requirements_subset thenSuccess)
        thenRequirementsSubset) requirementsSubset)
    conditionCovered

/-- The no-else `if` condition is typed in its enclosing statement source,
using the precise condition-to-then-to-parent execution trace. -/
theorem inferStatementFuel_success_ifWithoutElse_condition_scoped
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {condition : Syntax.Expr}
    {thenBody : Syntax.Block}
    {initial allocated evidenceState : State}
    {id : StatementId} {result : Detail.StatementResult}
    {roots : List NodeId} {finalized : Frontend.SourceInference.Result}
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
    (assumptionsEq : inferenceContext.assumptions = wholeContext.assumptions)
    (signatureFormation : ProgramSignatureFormationValidated
      inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈ inferenceContext.signatures.functions,
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
    (expressionSound : InferExprFuelScopedSoundness fuel) :
    ∀ {inferredCondition : InferredExpression} {conditionState : State},
      Detail.inferExprFuel fuel inferenceContext condition (some .bool)
        allocated = .ok (inferredCondition, conditionState) →
      ExpressionHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        semanticContext inferredCondition.id
        (finalized.substitution.apply inferredCondition.type) := by
  intro inferredCondition conditionState conditionSuccess
  obtain ⟨actualCondition, actualConditionState, thenResult,
      actualConditionSuccess, thenSuccess, resultEq, containsRaw⟩ :=
    inferStatementFuel_success_ifWithoutElse_facts statementEq allocationEq
      success roots
  rw [conditionSuccess] at actualConditionSuccess
  obtain ⟨rfl, rfl⟩ := (Except.ok.inj actualConditionSuccess).symm
  obtain ⟨provenanceConditionState, provenanceThenResult,
      ⟨_, provenanceConditionSuccess⟩, provenanceThenSuccess,
      conditionBelow, thenSourceExtension, thenPatternsSubset,
      thenRequirementsSubset⟩ :=
    inferStatementFuel_success_ifWithoutElse_child_provenance statementEq
      allocationEq success initialInvariant.nodesBelow roots
  have conditionStateEq : provenanceConditionState = conditionState := by
    rw [conditionSuccess] at provenanceConditionSuccess
    exact (congrArg Prod.snd
      (Except.ok.inj provenanceConditionSuccess)).symm
  subst provenanceConditionState
  have thenResultEq : provenanceThenResult = thenResult := by
    rw [thenSuccess] at provenanceThenSuccess
    exact (Except.ok.inj provenanceThenSuccess).symm
  subst provenanceThenResult
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
    Substitution.SemanticallyExtends.trans thenSubstitutionExtension
      thenProperties.1.substitution_extends
  have conditionToThen : TypingSourceExtends
      (conditionState.toTypedSource roots)
      (thenResult.state.toTypedSource roots) :=
    inferStatementsFuel_success_typingSourceExtends thenSuccess
      conditionBelow roots
  have conditionToParent : TypingSourceExtends
      (conditionState.toTypedSource roots)
      (result.state.toTypedSource roots) :=
    conditionToThen.trans thenSourceExtension
  have thenLiteralsSubset : thenResult.state.integerLiterals ⊆
      result.state.integerLiterals := by
    rw [resultEq]
    intro literal member
    simpa [State.restoreLexicalScope, State.recordNode] using member
  have containsFinal : ContainsStatement finalized.typedSource result.id
      (({
        id := result.id
        span := statement.span
        type := result.type
        form := .ifThen inferredCondition.id thenResult.statements none
      } : StatementNode).applySubstitution finalized.substitution) :=
    resultExtension.containsStatement
      (FlexibleSubstitution.ContainsStatement.applySubstitution
        finalized.substitution containsRaw)
  have conditionCovered : TemplateScopeCovered finalized.typedSource
      semanticContext (.expression inferredCondition.id) := by
    apply TemplateScopeCovered.statementExpressionChild_of_noBindings_and_reference
      parentCovered resources.graph_closed containsFinal
    · simp [StatementNode.applySubstitution, StatementForm.applySubstitution,
        statementInitializedLetBindings]
    · simp [StatementNode.applySubstitution, StatementForm.applySubstitution,
        StatementForm.references]
  exact expressionSound conditionSuccess resources
    conditionSubstitutionExtension signaturesEq ownerEq parametersEq
    assumptionsEq signatureFormation functionsCanonical catalog
    signatureParameters (RecursiveExpressionInvariant.ofStatement
      allocatedInvariant) (by
        intro expected member
        simp only [Option.mem_def] at member
        injection member with expectedEq
        subst expected
        simp [Ty.bool])
    (conditionToParent.applySubstitution finalized.substitution)
    resultExtension
    (conditionToParent.trans rawResultExtension)
    (List.Subset.trans
      (List.Subset.trans
        (Detail.inferStatementsFuel_integerPatterns_subset thenSuccess)
        thenPatternsSubset) integerPatternsSubset)
    (List.Subset.trans
      (List.Subset.trans
        (Detail.inferStatementsFuel_integerLiterals_subset thenSuccess)
        thenLiteralsSubset) integerLiteralsSubset)
    (List.Subset.trans
      (List.Subset.trans
        (Detail.inferStatementsFuel_requirements_subset thenSuccess)
        thenRequirementsSubset) requirementsSubset)
    conditionCovered

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceStatementExpressionSoundness
/-!
Actual-child resources for expression statements and value returns.  The
statement dispatcher can feed these facts to a recursive expression theorem
without assuming soundness of an unrelated expression computation.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem
open SourceInferenceStatementsSoundness

/-- The expression child's actual inference trace is retained under both the
parent's semantic source and the whole finalization evidence source. -/
theorem inferStatementFuel_expression_child_resources
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expression : Syntax.Expr}
    {trailingSemicolon : Bool} {expectedReturn : Ty}
    {initial allocated evidenceState : State} {id : StatementId}
    {result : Detail.StatementResult}
    {outer : Substitution} {roots : List NodeId}
    {semanticSource coverageSource : TypedSource}
    {target : SourceSemantics.Context}
    (statementEq : statement.value =
      .expression expression trailingSemicolon)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (resultSemanticExtension : TypingSourceExtends
      ((result.state.toTypedSource roots).applySubstitution outer)
      semanticSource)
    (semanticCoverageExtension : TypingSourceExtends semanticSource
      coverageSource)
    (rawEvidenceExtension : TypingSourceExtends
      (result.state.toTypedSource roots) (evidenceState.toTypedSource roots))
    (resultPatternsSubset : result.state.integerPatterns ⊆
      evidenceState.integerPatterns)
    (resultLiteralsSubset : result.state.integerLiterals ⊆
      evidenceState.integerLiterals)
    (resultRequirementsSubset : result.state.requirements ⊆
      evidenceState.requirements)
    (parentCovered : TemplateScopeCovered coverageSource target
      (.statement result.id))
    (closed : OccurrenceGraphClosed coverageSource) :
    ∃ inferred childState,
      Detail.inferExprFuel fuel inferenceContext expression none allocated =
        .ok (inferred, childState) ∧
      childState.inference.substitution =
        result.state.inference.substitution ∧
      allocated.NodesBelowNextOccurrence ∧
      TypingSourceExtends
        ((childState.toTypedSource roots).applySubstitution outer)
        semanticSource ∧
      TypingSourceExtends (childState.toTypedSource roots)
        (evidenceState.toTypedSource roots) ∧
      childState.integerPatterns ⊆ evidenceState.integerPatterns ∧
      childState.integerLiterals ⊆ evidenceState.integerLiterals ∧
      childState.requirements ⊆ evidenceState.requirements ∧
      TemplateScopeCovered coverageSource target
        (.expression inferred.id) := by
  obtain ⟨inferred, childState, childSuccess, provenance⟩ :=
    inferStatementFuel_success_expression_child_provenance statementEq
      allocationEq success initialBelow roots
  obtain ⟨inferred', childState', childSuccess', resultEq, containsRaw⟩ :=
    inferStatementFuel_success_expression_facts statementEq allocationEq
      success roots
  rw [childSuccess] at childSuccess'
  obtain ⟨rfl, rfl⟩ := (Except.ok.inj childSuccess').symm
  have resultCoverageExtension : TypingSourceExtends
      ((result.state.toTypedSource roots).applySubstitution outer)
      coverageSource :=
    resultSemanticExtension.trans semanticCoverageExtension
  have containsFinal : ContainsStatement coverageSource result.id
      (({
        id := result.id
        span := statement.span
        type := result.type
        form := .expression inferred.id trailingSemicolon
      } : StatementNode).applySubstitution outer) :=
    resultCoverageExtension.containsStatement
      (FlexibleSubstitution.ContainsStatement.applySubstitution outer
        containsRaw)
  have childCovered : TemplateScopeCovered coverageSource target
      (.expression inferred.id) := by
    apply TemplateScopeCovered.statementExpressionChild_of_noBindings_and_reference
      parentCovered closed containsFinal
    · simp [StatementNode.applySubstitution, StatementForm.applySubstitution,
        statementInitializedLetBindings]
    · simp [StatementNode.applySubstitution, StatementForm.applySubstitution,
        StatementForm.references]
  refine ⟨inferred, childState, childSuccess, ?_, provenance.initialBelow,
    provenance.sourceExtension.applySubstitution outer |>.trans
      resultSemanticExtension,
    provenance.sourceExtension.trans rawEvidenceExtension,
    List.Subset.trans provenance.integerPatternsSubset resultPatternsSubset,
    ?_,
    List.Subset.trans provenance.requirementsSubset resultRequirementsSubset,
    childCovered⟩
  · simp [resultEq, State.recordNode]
  simpa [resultEq, State.recordNode] using resultLiteralsSubset

/-- The value-return child's actual inference trace supplies the same
semantic/evidence transport and its direct-child coverage. -/
theorem inferStatementFuel_returnValue_child_resources
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {value : Syntax.Expr}
    {expectedReturn : Ty}
    {initial allocated evidenceState : State} {id : StatementId}
    {result : Detail.StatementResult}
    {outer : Substitution} {roots : List NodeId}
    {semanticSource coverageSource : TypedSource}
    {target : SourceSemantics.Context}
    (statementEq : statement.value = .returnStmt (some value))
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (resultSemanticExtension : TypingSourceExtends
      ((result.state.toTypedSource roots).applySubstitution outer)
      semanticSource)
    (semanticCoverageExtension : TypingSourceExtends semanticSource
      coverageSource)
    (rawEvidenceExtension : TypingSourceExtends
      (result.state.toTypedSource roots) (evidenceState.toTypedSource roots))
    (resultPatternsSubset : result.state.integerPatterns ⊆
      evidenceState.integerPatterns)
    (resultLiteralsSubset : result.state.integerLiterals ⊆
      evidenceState.integerLiterals)
    (resultRequirementsSubset : result.state.requirements ⊆
      evidenceState.requirements)
    (parentCovered : TemplateScopeCovered coverageSource target
      (.statement result.id))
    (closed : OccurrenceGraphClosed coverageSource) :
    ∃ inferred childState,
      Detail.inferExprFuel fuel inferenceContext value (some expectedReturn)
        allocated = .ok (inferred, childState) ∧
      childState.inference.substitution =
        result.state.inference.substitution ∧
      allocated.NodesBelowNextOccurrence ∧
      TypingSourceExtends
        ((childState.toTypedSource roots).applySubstitution outer)
        semanticSource ∧
      TypingSourceExtends (childState.toTypedSource roots)
        (evidenceState.toTypedSource roots) ∧
      childState.integerPatterns ⊆ evidenceState.integerPatterns ∧
      childState.integerLiterals ⊆ evidenceState.integerLiterals ∧
      childState.requirements ⊆ evidenceState.requirements ∧
      TemplateScopeCovered coverageSource target
        (.expression inferred.id) := by
  obtain ⟨inferred, childState, childSuccess, provenance⟩ :=
    inferStatementFuel_success_returnValue_child_provenance statementEq
      allocationEq success initialBelow roots
  obtain ⟨inferred', childState', childSuccess', resultEq, containsRaw⟩ :=
    inferStatementFuel_success_returnValue_facts statementEq allocationEq
      success roots
  rw [childSuccess] at childSuccess'
  obtain ⟨rfl, rfl⟩ := (Except.ok.inj childSuccess').symm
  have resultCoverageExtension : TypingSourceExtends
      ((result.state.toTypedSource roots).applySubstitution outer)
      coverageSource :=
    resultSemanticExtension.trans semanticCoverageExtension
  have containsFinal : ContainsStatement coverageSource result.id
      (({
        id := result.id
        span := statement.span
        type := result.type
        form := .returnStmt (some inferred.id)
      } : StatementNode).applySubstitution outer) :=
    resultCoverageExtension.containsStatement
      (FlexibleSubstitution.ContainsStatement.applySubstitution outer
        containsRaw)
  have childCovered : TemplateScopeCovered coverageSource target
      (.expression inferred.id) := by
    apply TemplateScopeCovered.statementExpressionChild_of_noBindings_and_reference
      parentCovered closed containsFinal
    · simp [StatementNode.applySubstitution, StatementForm.applySubstitution,
        statementInitializedLetBindings]
    · simp [StatementNode.applySubstitution, StatementForm.applySubstitution,
        StatementForm.references]
  refine ⟨inferred, childState, childSuccess, ?_, provenance.initialBelow,
    provenance.sourceExtension.applySubstitution outer |>.trans
      resultSemanticExtension,
    provenance.sourceExtension.trans rawEvidenceExtension,
    List.Subset.trans provenance.integerPatternsSubset resultPatternsSubset,
    ?_,
    List.Subset.trans provenance.requirementsSubset resultRequirementsSubset,
    childCovered⟩
  · simp [resultEq, State.recordNode]
  simpa [resultEq, State.recordNode] using resultLiteralsSubset

/-- The actual expression child is typed by the scoped expression theorem in
the enclosing statement's local source, then the existing statement
constructor discharges the parent typing. -/
theorem inferStatementFuel_expression_scopedBranch
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {expression : Syntax.Expr}
    {trailingSemicolon : Bool}
    {initial allocated evidenceState : State} {id : StatementId}
    {result : Detail.StatementResult} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {semanticContext : SourceSemantics.Context}
    (statementEq : statement.value =
      .expression expression trailingSemicolon)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState
      roots finalized)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (ownerEq : inferenceContext.scope.genericOwner =
      wholeContext.scope.genericOwner)
    (parametersEq : inferenceContext.typeParameters =
      wholeContext.typeParameters)
    (assumptionsEq : inferenceContext.assumptions = wholeContext.assumptions)
    (signatureFormation : ProgramSignatureFormationValidated
      inferenceContext.signatures)
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
    (resultSemanticExtension : TypingSourceExtends
      ((result.state.toTypedSource roots).applySubstitution
        finalized.substitution) semanticSource)
    (semanticCoverageExtension : TypingSourceExtends semanticSource
      finalized.typedSource)
    (rawEvidenceExtension : TypingSourceExtends
      (result.state.toTypedSource roots) (evidenceState.toTypedSource roots))
    (resultPatternsSubset : result.state.integerPatterns ⊆
      evidenceState.integerPatterns)
    (resultLiteralsSubset : result.state.integerLiterals ⊆
      evidenceState.integerLiterals)
    (resultRequirementsSubset : result.state.requirements ⊆
      evidenceState.requirements)
    (parentCovered : TemplateScopeCovered finalized.typedSource
      semanticContext (.statement result.id))
    (expressionSound : InferExprFuelScopedSoundness fuel) :
    ∃ finalContext facts,
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
  let parentSource :=
    (result.state.toTypedSource roots).applySubstitution
      finalized.substitution
  obtain ⟨inferred, childState, childSuccess, childSubstitutionEq,
      _allocatedBelow,
      childParentExtension, rawChildEvidenceExtension,
      childPatternsSubset, childLiteralsSubset, childRequirementsSubset,
      childCovered⟩ :=
    inferStatementFuel_expression_child_resources statementEq allocationEq
      success initialInvariant.nodesBelow (TypingSourceExtends.refl
        parentSource) (resultSemanticExtension.trans
        semanticCoverageExtension) rawEvidenceExtension resultPatternsSubset
      resultLiteralsSubset resultRequirementsSubset parentCovered
      resources.graph_closed
  have allocatedInvariant : RecursiveExpressionInvariant wholeContext finalized
      allocated semanticContext :=
    RecursiveExpressionInvariant.ofStatement
      (initialInvariant.allocateStatementId allocationEq)
  have childSubstitutionExtension : finalized.substitution.SemanticallyExtends
      childState.inference.substitution := by
    rw [childSubstitutionEq]
    exact resultSubstitutionExtension
  have typed : ExpressionHasType parentSource semanticContext inferred.id
      (finalized.substitution.apply inferred.type) :=
    expressionSound childSuccess resources childSubstitutionExtension
      signaturesEq ownerEq parametersEq
      assumptionsEq signatureFormation functionsCanonical catalog
      signatureParameters allocatedInvariant (by simp) childParentExtension
      (resultSemanticExtension.trans semanticCoverageExtension)
      rawChildEvidenceExtension childPatternsSubset childLiteralsSubset
      childRequirementsSubset childCovered
  obtain ⟨facts, active, statementType, agreement⟩ :=
    inferStatementFuel_success_expression_sound statementEq allocationEq
      success initialInvariant.active roots (by
        intro actualInferred actualState actualSuccess
        have pairEq : (actualInferred, actualState) =
            (inferred, childState) := by
          rw [childSuccess] at actualSuccess
          exact (Except.ok.inj actualSuccess).symm
        cases pairEq
        exact typed)
  exact ⟨semanticContext, facts, active, statementType, agreement⟩

/-- The value-return branch sends its actual child to the scoped expression
theorem with the function return type as expected type. -/
theorem inferStatementFuel_returnValue_scopedBranch
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {value : Syntax.Expr}
    {initial allocated evidenceState : State} {id : StatementId}
    {result : Detail.StatementResult} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {semanticContext : SourceSemantics.Context}
    (statementEq : statement.value = .returnStmt (some value))
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState
      roots finalized)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (ownerEq : inferenceContext.scope.genericOwner =
      wholeContext.scope.genericOwner)
    (parametersEq : inferenceContext.typeParameters =
      wholeContext.typeParameters)
    (assumptionsEq : inferenceContext.assumptions = wholeContext.assumptions)
    (signatureFormation : ProgramSignatureFormationValidated
      inferenceContext.signatures)
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
    (resultSemanticExtension : TypingSourceExtends
      ((result.state.toTypedSource roots).applySubstitution
        finalized.substitution) semanticSource)
    (semanticCoverageExtension : TypingSourceExtends semanticSource
      finalized.typedSource)
    (rawEvidenceExtension : TypingSourceExtends
      (result.state.toTypedSource roots) (evidenceState.toTypedSource roots))
    (resultPatternsSubset : result.state.integerPatterns ⊆
      evidenceState.integerPatterns)
    (resultLiteralsSubset : result.state.integerLiterals ⊆
      evidenceState.integerLiterals)
    (resultRequirementsSubset : result.state.requirements ⊆
      evidenceState.requirements)
    (parentCovered : TemplateScopeCovered finalized.typedSource
      semanticContext (.statement result.id))
    (expressionSound : InferExprFuelScopedSoundness fuel) :
    ∃ finalContext facts,
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
  let parentSource :=
    (result.state.toTypedSource roots).applySubstitution
      finalized.substitution
  obtain ⟨inferred, childState, childSuccess, childSubstitutionEq,
      _allocatedBelow,
      childParentExtension, rawChildEvidenceExtension,
      childPatternsSubset, childLiteralsSubset, childRequirementsSubset,
      childCovered⟩ :=
    inferStatementFuel_returnValue_child_resources statementEq allocationEq
      success initialInvariant.nodesBelow (TypingSourceExtends.refl
        parentSource) (resultSemanticExtension.trans
        semanticCoverageExtension) rawEvidenceExtension resultPatternsSubset
      resultLiteralsSubset resultRequirementsSubset parentCovered
      resources.graph_closed
  have allocatedInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized allocated semanticContext :=
    initialInvariant.allocateStatementId allocationEq
  have childExpectedBelow : ∀ expectedType ∈ (some expectedReturn : Option Ty),
      expectedType.VariablesBelow allocated.inference.next := by
    intro expectedType member
    simp only [Option.mem_def] at member
    cases member
    exact allocatedInvariant.returnBelow
  have childSubstitutionExtension : finalized.substitution.SemanticallyExtends
      childState.inference.substitution := by
    rw [childSubstitutionEq]
    exact resultSubstitutionExtension
  have typed : ExpressionHasType parentSource semanticContext inferred.id
      (finalized.substitution.apply inferred.type) :=
    expressionSound childSuccess resources childSubstitutionExtension
      signaturesEq ownerEq parametersEq
      assumptionsEq signatureFormation functionsCanonical catalog
      signatureParameters
      (RecursiveExpressionInvariant.ofStatement allocatedInvariant)
      childExpectedBelow childParentExtension
      (resultSemanticExtension.trans semanticCoverageExtension)
      rawChildEvidenceExtension childPatternsSubset childLiteralsSubset
      childRequirementsSubset childCovered
  have branch := inferStatementFuel_success_returnValue_sound statementEq
    allocationEq success initialInvariant.active resultSubstitutionExtension
    roots (by
      intro actualInferred actualState actualSuccess
      have pairEq : (actualInferred, actualState) =
          (inferred, childState) := by
        rw [childSuccess] at actualSuccess
        exact (Except.ok.inj actualSuccess).symm
      cases pairEq
      exact typed)
  exact ⟨semanticContext, _, branch⟩

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceStatementForLoopChildProgress
/-!
The four successful traversals of a `for` statement are source ordered.  This
module exposes their intermediate substitution and literal-ledger resources
without requiring a semantic proof for any of the children.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem

/-- Finalization extends the substitutions at every actual `for` child
boundary.  Every child's integer-literal ledger is also retained in the
completed statement, including the post-header traversal that runs after
restoring the initializer's lexical scope. -/
theorem inferStatementFuel_success_forLoop_child_progress
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {headerSpan : Syntax.SourceSpan}
    {initializer post : List Syntax.ForItem} {condition : Syntax.Expr}
    {body : Syntax.Block} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult}
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
      result.state.inference.substitution) :
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
      finalized.substitution.SemanticallyExtends
        initializerResult.state.inference.substitution ∧
      finalized.substitution.SemanticallyExtends
        conditionState.inference.substitution ∧
      finalized.substitution.SemanticallyExtends
        bodyResult.state.inference.substitution ∧
      finalized.substitution.SemanticallyExtends
        postResult.state.inference.substitution ∧
      initializerResult.state.integerLiterals ⊆
        result.state.integerLiterals ∧
      conditionState.integerLiterals ⊆ result.state.integerLiterals ∧
      bodyResult.state.integerLiterals ⊆ result.state.integerLiterals ∧
      postResult.state.integerLiterals ⊆ result.state.integerLiterals := by
  obtain ⟨initializerResult, inferredCondition, conditionState, bodyResult,
    postResult, initializerSuccess, conditionSuccess, bodySuccess,
    postSuccess, resultEq, _⟩ :=
    inferStatementFuel_success_forLoop_facts statementEq allocationEq
      success []
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
  have initializerSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        initializerResult.state.inference.substitution :=
    Substitution.SemanticallyExtends.trans conditionSubstitutionExtension
      conditionProperties.1.substitution_extends
  have postLiteralsSubset : postResult.state.integerLiterals ⊆
      result.state.integerLiterals := by
    rw [resultEq]
    intro literal member
    simpa [State.restoreLexicalScope, State.recordNode] using member
  have bodyLiteralsSubset : bodyResult.state.integerLiterals ⊆
      result.state.integerLiterals := by
    apply List.Subset.trans ?_ postLiteralsSubset
    intro literal member
    exact Detail.inferForItemsFuel_integerLiterals_subset postSuccess
      (by simpa [State.restoreLexicalScope] using member)
  have conditionLiteralsSubset : conditionState.integerLiterals ⊆
      result.state.integerLiterals :=
    List.Subset.trans
      (Detail.inferStatementsFuel_integerLiterals_subset bodySuccess)
      bodyLiteralsSubset
  have initializerLiteralsSubset : initializerResult.state.integerLiterals ⊆
      result.state.integerLiterals :=
    List.Subset.trans
      (Detail.inferExprFuel_integerLiterals_subset conditionSuccess)
      conditionLiteralsSubset
  exact ⟨initializerResult, inferredCondition, conditionState, bodyResult,
    postResult, initializerSuccess, conditionSuccess, bodySuccess,
    postSuccess, initializerSubstitutionExtension,
    conditionSubstitutionExtension, bodySubstitutionExtension,
    postSubstitutionExtension, initializerLiteralsSubset,
    conditionLiteralsSubset, bodyLiteralsSubset, postLiteralsSubset⟩

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceStatementForLoopConditionSoundness
/-!
The actual `for` condition is inferred after the initializer header has
established its loop-local lexical context.  This bridge uses the completed
parent's provenance and the unique condition slot to type that expression
without attributing header-let template scopes to it.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem

/-- A successful `for` condition is typed under the initializer-produced
context in the completed parent statement source. -/
theorem inferStatementFuel_success_forLoop_condition_scoped
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {headerSpan : Syntax.SourceSpan}
    {initializer post : List Syntax.ForItem} {condition : Syntax.Expr}
    {body : Syntax.Block}
    {initial allocated evidenceState : State}
    {id : StatementId} {result : Detail.StatementResult}
    {initializerResult : Detail.InferredForItems}
    {inferredCondition : InferredExpression} {conditionState : State}
    {roots : List NodeId} {finalized : Frontend.SourceInference.Result}
    {semanticContext loopContext : SourceSemantics.Context}
    (statementEq : statement.value =
      .forLoop headerSpan initializer condition post body)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (initializerSuccess : Detail.inferForItemsFuel fuel inferenceContext
      initializer allocated = .ok initializerResult)
    (conditionSuccess : Detail.inferExprFuel fuel inferenceContext condition
      (some .bool) initializerResult.state =
        .ok (inferredCondition, conditionState))
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (ownerEq : inferenceContext.scope.genericOwner =
      wholeContext.scope.genericOwner)
    (parametersEq : inferenceContext.typeParameters =
      wholeContext.typeParameters)
    (assumptionsEq : inferenceContext.assumptions = wholeContext.assumptions)
    (signatureFormation : ProgramSignatureFormationValidated
      inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈ inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signatureParameters : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (initialInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initial semanticContext)
    (initializerInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initializerResult.state loopContext)
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
    (loopAssumptionsEq : loopContext.assumptions =
      semanticContext.assumptions)
    (expressionSound : InferExprFuelScopedSoundness fuel) :
    ExpressionHasType
      ((result.state.toTypedSource roots).applySubstitution
        finalized.substitution)
      loopContext inferredCondition.id .bool := by
  obtain ⟨actualInitializer, actualCondition, actualConditionState,
      bodyResult, postResult, actualInitializerSuccess,
      actualConditionSuccess, bodySuccess, postSuccess, initializerBelow,
      conditionSubstitutionExtension, conditionToParent,
      conditionPatternsSubset, conditionLiteralsSubset,
      conditionRequirementsSubset⟩ :=
    inferStatementFuel_success_forLoop_condition_resources statementEq
      allocationEq success signatureFormation functionsCanonical
      initialInvariant resultSubstitutionExtension integerPatternsSubset
      integerLiteralsSubset requirementsSubset
  rw [initializerSuccess] at actualInitializerSuccess
  have initializerEq := (Except.ok.inj actualInitializerSuccess).symm
  subst actualInitializer
  rw [conditionSuccess] at actualConditionSuccess
  obtain ⟨rfl, rfl⟩ := (Except.ok.inj actualConditionSuccess).symm
  obtain ⟨factInitializer, factCondition, factConditionState,
      factBody, factPost, factInitializerSuccess, factConditionSuccess,
      factBodySuccess, factPostSuccess, resultEq, containsRaw⟩ :=
    inferStatementFuel_success_forLoop_facts statementEq allocationEq
      success roots
  rw [initializerSuccess] at factInitializerSuccess
  have factInitializerEq := (Except.ok.inj factInitializerSuccess).symm
  subst factInitializer
  rw [conditionSuccess] at factConditionSuccess
  obtain ⟨rfl, rfl⟩ := (Except.ok.inj factConditionSuccess).symm
  have containsFinal : ContainsStatement finalized.typedSource result.id
      (({
        id := result.id
        span := statement.span
        type := result.type
        form := .forLoop initializerResult.items inferredCondition.id
          factPost.items factBody.statements
      } : StatementNode).applySubstitution finalized.substitution) :=
    resultExtension.containsStatement
      (FlexibleSubstitution.ContainsStatement.applySubstitution
        finalized.substitution containsRaw)
  have conditionCovered : TemplateScopeCovered finalized.typedSource
      loopContext (.expression inferredCondition.id) := by
    apply TemplateScopeCovered.forLoopCondition parentCovered
      resources.graph_closed
    · simpa [StatementNode.applySubstitution,
        StatementForm.applySubstitution] using containsFinal
    · exact loopAssumptionsEq
  have conditionTyped : ExpressionHasType
      ((result.state.toTypedSource roots).applySubstitution
        finalized.substitution)
      loopContext inferredCondition.id
      (finalized.substitution.apply inferredCondition.type) :=
    expressionSound conditionSuccess resources
      conditionSubstitutionExtension signaturesEq ownerEq parametersEq
      assumptionsEq signatureFormation functionsCanonical catalog
      signatureParameters (RecursiveExpressionInvariant.ofStatement
        initializerInvariant) (by
          intro expected member
          simp only [Option.mem_def] at member
          injection member with expectedEq
          subst expected
          simp [Ty.bool])
      (conditionToParent.applySubstitution finalized.substitution)
      resultExtension (conditionToParent.trans rawResultExtension)
      conditionPatternsSubset conditionLiteralsSubset
      conditionRequirementsSubset conditionCovered
  have conditionTypeEq :
      finalized.substitution.apply inferredCondition.type = .bool := by
    simpa using Detail.inferExprFuel_expected_type_apply_eq
      conditionSuccess conditionSubstitutionExtension
  simpa [conditionTypeEq] using conditionTyped

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceStatementForLoopScopedSoundness
/-!
The recursive `for` statement step.  Each induction hypothesis is invoked
only on the actual initializer, condition, body, or post-header trace exposed
by the successful parent computation.  The completed local statement source
is separate from the whole-body finalization and coverage evidence.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem
open SourceInferenceStatementsSoundness

/-- Scoped soundness of one successful `for` statement, conditional only on
the four smaller-fuel recursive soundness propositions. -/
theorem inferStatementFuel_success_forLoop_scoped
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {headerSpan : Syntax.SourceSpan}
    {initializer post : List Syntax.ForItem} {condition : Syntax.Expr}
    {body : Syntax.Block}
    {initial allocated evidenceState : State} {id : StatementId}
    {result : Detail.StatementResult} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticContext : SourceSemantics.Context}
    (statementEq : statement.value =
      .forLoop headerSpan initializer condition post body)
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
    (initializerSound : InferForItemsFuelScopedSoundness fuel)
    (expressionSound : InferExprFuelScopedSoundness fuel)
    (bodySound : InferStatementsFuelScopedSoundness fuel)
    (postSound : InferForItemsFuelScopedSoundness fuel) :
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
    postSuccess, resultEq, containsRaw⟩ :=
    inferStatementFuel_success_forLoop_facts statementEq allocationEq success
      roots
  obtain ⟨progressInitializer, progressCondition, progressConditionState,
    progressBody, progressPost, progressInitializerSuccess,
    progressConditionSuccess, progressBodySuccess, progressPostSuccess,
    initializerSubstitutionExtension, conditionSubstitutionExtension,
    bodySubstitutionExtension, postSubstitutionExtension,
    initializerLiteralsParent, conditionLiteralsParent,
    bodyLiteralsParent, postLiteralsParent⟩ :=
    inferStatementFuel_success_forLoop_child_progress statementEq
      allocationEq success signatureFormation functionsCanonical
      initialInvariant resultSubstitutionExtension
  rw [initializerSuccess] at progressInitializerSuccess
  have progressInitializerEq :=
    (Except.ok.inj progressInitializerSuccess).symm
  subst progressInitializer
  rw [conditionSuccess] at progressConditionSuccess
  obtain ⟨rfl, rfl⟩ :=
    (Except.ok.inj progressConditionSuccess).symm
  rw [bodySuccess] at progressBodySuccess
  have progressBodyEq := (Except.ok.inj progressBodySuccess).symm
  subst progressBody
  rw [postSuccess] at progressPostSuccess
  have progressPostEq := (Except.ok.inj progressPostSuccess).symm
  subst progressPost
  obtain ⟨provenanceInitializer, provenanceCondition,
    provenanceConditionState, provenanceBody, provenancePost,
    provenanceInitializerSuccess, provenanceConditionSuccess,
    provenanceBodySuccess, provenancePostSuccess,
    initializerProvenance, bodyProvenance, postProvenance⟩ :=
    inferStatementFuel_success_forLoop_child_provenance statementEq
      allocationEq success initialInvariant.nodesBelow roots
  rw [initializerSuccess] at provenanceInitializerSuccess
  have provenanceInitializerEq :=
    (Except.ok.inj provenanceInitializerSuccess).symm
  subst provenanceInitializer
  rw [conditionSuccess] at provenanceConditionSuccess
  obtain ⟨rfl, rfl⟩ :=
    (Except.ok.inj provenanceConditionSuccess).symm
  rw [bodySuccess] at provenanceBodySuccess
  have provenanceBodyEq := (Except.ok.inj provenanceBodySuccess).symm
  subst provenanceBody
  rw [postSuccess] at provenancePostSuccess
  have provenancePostEq := (Except.ok.inj provenancePostSuccess).symm
  subst provenancePost
  have allocatedInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized allocated semanticContext :=
    initialInvariant.allocateStatementId allocationEq
  have headerCovered := forItemsReferencesCovered_of_recordedForLoop
    containsRaw rfl resultExtension resources.graph_closed parentCovered
  have headerBindings := forItemsBindingsRetained_of_containedForLoop
    containsRaw rawResultExtension
  have initializerSourceOwner :
      ((result.state.toTypedSource roots).applySubstitution
        finalized.substitution).owner = allocated.owner := by
    have ownerToInitializer := initializerProvenance.sourceExtension.owner_eq
    have initializerOwner :=
      Detail.inferForItemsFuel_preserves_owner initializerSuccess
    simpa [State.toTypedSource] using ownerToInitializer.trans initializerOwner
  obtain ⟨loopContext, initializerInvariant, initializerTyping⟩ :=
    (initializerSound (control := {
        returnType := finalized.substitution.apply expectedReturn
        loopDepth := inferenceContext.loopDepth })
      initializerSuccess resources signaturesEq ownerEq parametersEq
      assumptionsEq signatureFormation functionsCanonical catalog
      signatureParameters allocatedInvariant initializerSubstitutionExtension
      (initializerProvenance.sourceExtension.applySubstitution
        finalized.substitution) resultExtension
      (initializerProvenance.sourceExtension.trans rawResultExtension)
      (List.Subset.trans initializerProvenance.integerPatternsSubset
        integerPatternsSubset)
      (List.Subset.trans initializerLiteralsParent integerLiteralsSubset)
      (List.Subset.trans initializerProvenance.requirementsSubset
        requirementsSubset)
      initializerSourceOwner headerCovered.1 headerBindings.1)
  have loopAssumptionsEq : loopContext.assumptions =
      semanticContext.assumptions :=
    forItemsHaveType_assumptions_eq initializerTyping
  have conditionTyping :=
    inferStatementFuel_success_forLoop_condition_scoped statementEq
      allocationEq success initializerSuccess conditionSuccess resources
      signaturesEq ownerEq parametersEq assumptionsEq signatureFormation
      functionsCanonical catalog signatureParameters initialInvariant
      initializerInvariant resultSubstitutionExtension resultExtension
      rawResultExtension integerPatternsSubset integerLiteralsSubset
      requirementsSubset parentCovered loopAssumptionsEq expressionSound
  have conditionInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized conditionState loopContext :=
    initializerInvariant.inferExprFuel conditionSuccess signatureFormation
      functionsCanonical (by
        intro expected member
        simp only [Option.mem_def] at member
        injection member with expectedEq
        subst expected
        simp [Ty.bool]) conditionSubstitutionExtension
  have bodyCovered : ∀ child, child ∈ bodyResult.statements →
      TemplateScopeCovered finalized.typedSource loopContext
        (.statement child) := by
    intro child member
    have childReference : (.statement child : NodeId) ∈
        (StatementForm.forLoop initializerResult.items inferredCondition.id
          postResult.items bodyResult.statements).references := by
      simp [StatementForm.references, member]
    apply TemplateScopeCovered.statementChild_of_recorded_reference
      containsRaw childReference resultExtension parentCovered
      resources.graph_closed
    intro predicate predicateMember
    simpa [loopAssumptionsEq] using predicateMember
  obtain ⟨bodyFinal, bodyFacts, bodyInvariant, bodyTyping,
    bodyAgreement⟩ :=
    bodySound bodySuccess resources
      (by simpa using signaturesEq)
      (by simpa using ownerEq)
      (by simpa using parametersEq)
      (by simpa using assumptionsEq)
      signatureFormation functionsCanonical catalog signatureParameters
      conditionInvariant bodySubstitutionExtension
      (bodyProvenance.sourceExtension.applySubstitution
        finalized.substitution) resultExtension
      (bodyProvenance.sourceExtension.trans rawResultExtension)
      (List.Subset.trans bodyProvenance.integerPatternsSubset
        integerPatternsSubset)
      (List.Subset.trans bodyLiteralsParent integerLiteralsSubset)
      (List.Subset.trans bodyProvenance.requirementsSubset
        requirementsSubset)
      bodyCovered
  have conditionProperties := Detail.inferExprFuel_inferenceProperties
    initializerInvariant.ready signatureFormation functionsCanonical
    (by
      intro expected member
      simp only [Option.mem_def] at member
      injection member with expectedEq
      subst expected
      simp [Ty.bool]) conditionSuccess
  have conditionReturnBelow : expectedReturn.VariablesBelow
      conditionState.inference.next :=
    initializerInvariant.returnBelow.weaken conditionProperties.1.next_le
  have bodyProperties := Detail.inferStatementsFuel_inferenceProperties
    (context := { inferenceContext with
      loopDepth := inferenceContext.loopDepth + 1 })
    conditionProperties.2.1 signatureFormation functionsCanonical
    conditionReturnBelow bodySuccess
  have bodyBelow : bodyResult.state.NodesBelowNextOccurrence :=
    (Detail.inferStatementsFuel_occurrenceBoundExtends bodySuccess
      ).nodesBelowNextOccurrence bodyProvenance.initialBelow
  have nextLocalLe : initializerResult.state.nextLocal ≤
      bodyResult.state.nextLocal :=
    Nat.le_trans (Detail.inferExprFuel_nextLocal_le conditionSuccess)
      (Detail.inferStatementsFuel_nextLocal_le bodySuccess)
  have postInputInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized
      (bodyResult.state.restoreLexicalScope
        initializerResult.state.lexicalScope) loopContext :=
    initializerInvariant.restoreLexicalScope
      (conditionProperties.1.trans bodyProperties.1) bodyBelow nextLocalLe
      bodySubstitutionExtension
  have postCovered : ForItemsReferencesCovered finalized.typedSource
      finalized.substitution loopContext postResult.items := by
    intro item itemMember
    exact (headerCovered.2 item itemMember).transportAssumptions
      loopAssumptionsEq
  have postSourceOwner :
      ((result.state.toTypedSource roots).applySubstitution
        finalized.substitution).owner =
        (bodyResult.state.restoreLexicalScope
          initializerResult.state.lexicalScope).owner := by
    have ownerToPost := postProvenance.sourceExtension.owner_eq
    have postOwner := Detail.inferForItemsFuel_preserves_owner postSuccess
    simpa [State.toTypedSource] using ownerToPost.trans postOwner
  obtain ⟨postContext, postInvariant, postTyping⟩ :=
    (postSound (control := ({
        returnType := finalized.substitution.apply expectedReturn
        loopDepth := inferenceContext.loopDepth } : ControlContext).enterLoop)
      postSuccess resources
      (by simpa using signaturesEq)
      (by simpa using ownerEq)
      (by simpa using parametersEq)
      (by simpa using assumptionsEq)
      signatureFormation functionsCanonical catalog signatureParameters
      postInputInvariant postSubstitutionExtension
      (postProvenance.sourceExtension.applySubstitution
        finalized.substitution) resultExtension
      (postProvenance.sourceExtension.trans rawResultExtension)
      (List.Subset.trans postProvenance.integerPatternsSubset
        integerPatternsSubset)
      (List.Subset.trans postLiteralsParent integerLiteralsSubset)
      (List.Subset.trans postProvenance.requirementsSubset
        requirementsSubset)
      postSourceOwner postCovered headerBindings.2)
  apply inferStatementFuel_success_forLoop_of_actual_typed_children
    statementEq allocationEq success signatureFormation functionsCanonical
    initialInvariant resultSubstitutionExtension
  intro actualInitializer actualCondition actualConditionState actualBody
    actualPost actualInitializerSuccess actualConditionSuccess
    actualBodySuccess actualPostSuccess
  rw [initializerSuccess] at actualInitializerSuccess
  have actualInitializerEq := (Except.ok.inj actualInitializerSuccess).symm
  subst actualInitializer
  rw [conditionSuccess] at actualConditionSuccess
  obtain ⟨rfl, rfl⟩ := (Except.ok.inj actualConditionSuccess).symm
  rw [bodySuccess] at actualBodySuccess
  have actualBodyEq := (Except.ok.inj actualBodySuccess).symm
  subst actualBody
  rw [postSuccess] at actualPostSuccess
  have actualPostEq := (Except.ok.inj actualPostSuccess).symm
  subst actualPost
  exact ⟨loopContext, bodyFinal, bodyFacts, postContext,
    initializerTyping, conditionTyping, bodyTyping, postTyping⟩

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceStatementMatchAssembly
/-!
Compositional assembly for the two executable `match` statement branches.
The semantic premises are about the exact scrutinee, cases, and optional
default body returned by the successful parent traversal.  No premise claims
soundness for arbitrary independently chosen child computations.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem

/-- Assemble a default-free `match` from its actual typed children.  The
checker guard, rather than a separately postulated exhaustiveness claim,
supplies declarative exhaustiveness. -/
theorem inferStatementFuel_success_matchWithoutDefault_of_actual_typed_children
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
    {arms : Syntax.MatchArms} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult}
    {outer : Substitution} {target : SourceSemantics.Context}
    {scrutinee : InferredExpression} {scrutineeState : State}
    {hiddenScrutinee : Resolved.LocalId} {hiddenState : State}
    {checked : Detail.MatchCasesResult} {caseFacts : List BodyFacts}
    (statementEq : statement.value = .matchWith scrutinees arms)
    (defaultEq : arms.value.defaultBody = none)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (scrutineeSuccess : inferMatchScrutineesFuel fuel inferenceContext
      statement.span scrutinees.elements.toList allocated =
        .ok (scrutinee, scrutineeState))
    (hiddenAllocation : scrutineeState.allocateHiddenLocal =
      (hiddenScrutinee, hiddenState))
    (casesSuccess : Detail.inferMatchCasesFuel fuel inferenceContext
      scrutinee.type expectedReturn hiddenState.lexicalScope
      arms.value.cases hiddenState = .ok checked)
    (catalog : SignatureCatalogWellFormed target.signatures)
    (signaturesEq : target.signatures = inferenceContext.signatures)
    (casesPresent : arms.value.cases ≠ [])
    (invariant : ActiveLocalContextInvariant initial outer target)
    (outerExtension : outer.SemanticallyExtends
      result.state.inference.substitution)
    (roots : List NodeId)
    (scrutineeTyping : ExpressionHasType
      ((result.state.toTypedSource roots).applySubstitution outer)
      target scrutinee.id (outer.apply scrutinee.type))
    (casesTyping : MatchCasesHaveType
      ((result.state.toTypedSource roots).applySubstitution outer) {
        returnType := outer.apply expectedReturn
        loopDepth := inferenceContext.loopDepth
      } target (outer.apply scrutinee.type)
      (checked.cases.map (TypedMatchCase.applySubstitution outer)) caseFacts)
    (allReturnEq : allBodiesSawReturn caseFacts = checked.allReturn) :
    ∃ facts,
      ActiveLocalContextInvariant result.state outer target ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution outer) {
          returnType := outer.apply expectedReturn
          loopDepth := inferenceContext.loopDepth
        } target result.id target facts ∧
      StatementResultMatchesFactsAfterSubstitution outer result facts := by
  obtain ⟨actualScrutinee, actualScrutineeState, actualHidden,
    actualHiddenState, actualChecked, actualScrutineeSuccess,
    actualHiddenAllocation, actualCasesSuccess, guardPassed, resultEq,
    contains⟩ :=
    inferStatementFuel_success_matchWithoutDefault_facts statementEq defaultEq
      allocationEq success roots
  have scrutineePairEq : (actualScrutinee, actualScrutineeState) =
      (scrutinee, scrutineeState) := by
    rw [scrutineeSuccess] at actualScrutineeSuccess
    exact (Except.ok.inj actualScrutineeSuccess).symm
  obtain ⟨rfl, rfl⟩ := scrutineePairEq
  have hiddenPairEq : (actualHidden, actualHiddenState) =
      (hiddenScrutinee, hiddenState) := by
    rw [hiddenAllocation] at actualHiddenAllocation
    exact actualHiddenAllocation.symm
  obtain ⟨rfl, rfl⟩ := hiddenPairEq
  have checkedEq : actualChecked = checked := by
    rw [casesSuccess] at actualCasesSuccess
    exact (Except.ok.inj actualCasesSuccess).symm
  subst actualChecked
  have allocatedInvariant : ActiveLocalContextInvariant allocated outer
      target := invariant.allocateStatementId allocationEq
  have scrutineeInvariant : ActiveLocalContextInvariant scrutineeState outer
      target := allocatedInvariant.inferMatchScrutineesFuel scrutineeSuccess
  have hiddenInvariant : ActiveLocalContextInvariant hiddenState outer target :=
    scrutineeInvariant.allocateHiddenLocal hiddenAllocation
  have checkedInvariant : ActiveLocalContextInvariant checked.state outer
      target := hiddenInvariant.inferMatchCasesFuel casesSuccess
  have checkedExtension : outer.SemanticallyExtends
      checked.state.inference.substitution := by
    simpa [resultEq, State.recordNode] using outerExtension
  have exhaustive : MatchExhaustive target (outer.apply scrutinee.type)
      (checked.cases.map (TypedMatchCase.applySubstitution outer)) none :=
    matchExhaustiveWithoutDefault_of_guard catalog signaturesEq
      casesSuccess casesTyping scrutineeTyping.type_admissible
      checkedExtension guardPassed
  have checkedCasesPresent : checked.cases ≠ [] := by
    intro checkedCasesEq
    have lengthEq := Detail.inferMatchCasesFuel_success_cases_length
      casesSuccess
    rw [checkedCasesEq] at lengthEq
    apply casesPresent
    simpa using lengthEq.symm
  have caseFactsPresent : caseFacts ≠ [] :=
    matchCasesHaveType_facts_ne_nil_of_cases_ne_nil casesTyping (by
      simpa using checkedCasesPresent)
  obtain ⟨summary, merged⟩ :=
    mergeBodyControls_withoutDefault_eq_some_of_ne_nil caseFacts
      caseFactsPresent
  subst result
  refine ⟨{
      type := if allBodiesSawReturn caseFacts then
        outer.apply expectedReturn
      else .unit
      hasValue := allBodiesSawReturn caseFacts
      sawReturn := allBodiesSawReturn caseFacts
      control := summary.eraseValue
    }, checkedInvariant.recordNode _, ?_, ?_⟩
  · exact matchWithoutDefaultStatementHasType_afterSubstitution contains
      scrutineeTyping casesTyping exhaustive allReturnEq merged
      checkedExtension
  · exact StatementResultMatchesFactsAfterSubstitution.matchWithoutDefault
      allReturnEq checkedExtension id _

/-- Assemble a `match` with a default arm from the successful scrutinee,
explicit-case, and default-body traversals.  The default body makes both
exhaustiveness and control merging total. -/
theorem inferStatementFuel_success_matchWithDefault_of_actual_typed_children
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
    {arms : Syntax.MatchArms} {defaultBody : Syntax.Block}
    {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult}
    {outer : Substitution} {target defaultFinal : SourceSemantics.Context}
    {scrutinee : InferredExpression} {scrutineeState : State}
    {hiddenScrutinee : Resolved.LocalId} {hiddenState : State}
    {checked : Detail.MatchCasesResult}
    {defaultResult : Detail.BlockResult}
    {caseFacts : List BodyFacts} {defaultFacts : BodyFacts}
    (statementEq : statement.value = .matchWith scrutinees arms)
    (defaultEq : arms.value.defaultBody = some defaultBody)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (scrutineeSuccess : inferMatchScrutineesFuel fuel inferenceContext
      statement.span scrutinees.elements.toList allocated =
        .ok (scrutinee, scrutineeState))
    (hiddenAllocation : scrutineeState.allocateHiddenLocal =
      (hiddenScrutinee, hiddenState))
    (casesSuccess : Detail.inferMatchCasesFuel fuel inferenceContext
      scrutinee.type expectedReturn hiddenState.lexicalScope
      arms.value.cases hiddenState = .ok checked)
    (defaultSuccess : Detail.inferStatementsFuel fuel inferenceContext
      defaultBody.value expectedReturn checked.state = .ok defaultResult)
    (invariant : ActiveLocalContextInvariant initial outer target)
    (outerExtension : outer.SemanticallyExtends
      result.state.inference.substitution)
    (roots : List NodeId)
    (scrutineeTyping : ExpressionHasType
      ((result.state.toTypedSource roots).applySubstitution outer)
      target scrutinee.id (outer.apply scrutinee.type))
    (casesTyping : MatchCasesHaveType
      ((result.state.toTypedSource roots).applySubstitution outer) {
        returnType := outer.apply expectedReturn
        loopDepth := inferenceContext.loopDepth
      } target (outer.apply scrutinee.type)
      (checked.cases.map (TypedMatchCase.applySubstitution outer)) caseFacts)
    (defaultTyping : StatementsHaveType
      ((result.state.toTypedSource roots).applySubstitution outer) {
        returnType := outer.apply expectedReturn
        loopDepth := inferenceContext.loopDepth
      } target defaultResult.statements defaultFinal defaultFacts)
    (caseReturnEq : allBodiesSawReturn caseFacts = checked.allReturn)
    (defaultAgreement : BlockResultMatchesFactsAfterSubstitution outer
      defaultResult defaultFacts) :
    ∃ facts,
      ActiveLocalContextInvariant result.state outer target ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution outer) {
          returnType := outer.apply expectedReturn
          loopDepth := inferenceContext.loopDepth
        } target result.id target facts ∧
      StatementResultMatchesFactsAfterSubstitution outer result facts := by
  obtain ⟨actualScrutinee, actualScrutineeState, actualHidden,
    actualHiddenState, actualChecked, actualDefault, actualScrutineeSuccess,
    actualHiddenAllocation, actualCasesSuccess, actualDefaultSuccess,
    _guardPassed, resultEq, contains⟩ :=
    inferStatementFuel_success_matchWithDefault_facts statementEq defaultEq
      allocationEq success roots
  have scrutineePairEq : (actualScrutinee, actualScrutineeState) =
      (scrutinee, scrutineeState) := by
    rw [scrutineeSuccess] at actualScrutineeSuccess
    exact (Except.ok.inj actualScrutineeSuccess).symm
  obtain ⟨rfl, rfl⟩ := scrutineePairEq
  have hiddenPairEq : (actualHidden, actualHiddenState) =
      (hiddenScrutinee, hiddenState) := by
    rw [hiddenAllocation] at actualHiddenAllocation
    exact actualHiddenAllocation.symm
  obtain ⟨rfl, rfl⟩ := hiddenPairEq
  have checkedEq : actualChecked = checked := by
    rw [casesSuccess] at actualCasesSuccess
    exact (Except.ok.inj actualCasesSuccess).symm
  subst actualChecked
  have defaultEqResult : actualDefault = defaultResult := by
    rw [defaultSuccess] at actualDefaultSuccess
    exact (Except.ok.inj actualDefaultSuccess).symm
  subst actualDefault
  have allocatedInvariant : ActiveLocalContextInvariant allocated outer
      target := invariant.allocateStatementId allocationEq
  have scrutineeInvariant : ActiveLocalContextInvariant scrutineeState outer
      target := allocatedInvariant.inferMatchScrutineesFuel scrutineeSuccess
  have hiddenInvariant : ActiveLocalContextInvariant hiddenState outer target :=
    scrutineeInvariant.allocateHiddenLocal hiddenAllocation
  have defaultExtension : outer.SemanticallyExtends
      defaultResult.state.inference.substitution := by
    simpa [resultEq, State.restoreLexicalScope, State.recordNode] using
      outerExtension
  obtain ⟨summary, merged⟩ :=
    mergeBodyControls_withDefault_eq_some caseFacts defaultFacts
  subst result
  refine ⟨{
      type := if allBodiesSawReturn caseFacts && defaultFacts.sawReturn then
        outer.apply expectedReturn
      else .unit
      hasValue := allBodiesSawReturn caseFacts && defaultFacts.sawReturn
      sawReturn := allBodiesSawReturn caseFacts && defaultFacts.sawReturn
      control := summary.eraseValue
    }, hiddenInvariant.restoreLexicalScope_recordNode _, ?_, ?_⟩
  · exact matchWithDefaultStatementHasType_afterSubstitution contains
      scrutineeTyping casesTyping defaultTyping caseReturnEq defaultAgreement
      merged defaultExtension
  · exact StatementResultMatchesFactsAfterSubstitution.matchWithDefault
      caseReturnEq defaultAgreement defaultExtension id _

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceStatementMatchChildResources
/-!
Resource transport along the actual source-ordered children of a `match`
statement.  Child typing uses the whole final substitution and evidence
ledgers, so it needs these facts before applying scoped induction hypotheses.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem
open SourceInferenceStatementsSoundness

/-- In a successful default-free match, the scrutinee and explicit cases are
prefixes of the parent result.  Finalization extends their substitutions and
the parent retains their literal and requirement ledgers. -/
theorem inferStatementFuel_success_matchWithoutDefault_child_resources
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
    {arms : Syntax.MatchArms} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult}
    {finalized : Frontend.SourceInference.Result}
    {semanticContext : SourceSemantics.Context}
    (statementEq : statement.value = .matchWith scrutinees arms)
    (defaultEq : arms.value.defaultBody = none)
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
    (roots : List NodeId) :
    ∃ scrutinee scrutineeState hiddenScrutinee hiddenState checked,
      inferMatchScrutineesFuel fuel inferenceContext statement.span
        scrutinees.elements.toList allocated =
          .ok (scrutinee, scrutineeState) ∧
      scrutineeState.allocateHiddenLocal =
        (hiddenScrutinee, hiddenState) ∧
      Detail.inferMatchCasesFuel fuel inferenceContext scrutinee.type
        expectedReturn hiddenState.lexicalScope arms.value.cases
        hiddenState = .ok checked ∧
      finalized.substitution.SemanticallyExtends
        scrutineeState.inference.substitution ∧
      finalized.substitution.SemanticallyExtends
        hiddenState.inference.substitution ∧
      finalized.substitution.SemanticallyExtends
        checked.state.inference.substitution ∧
      TypingSourceExtends (scrutineeState.toTypedSource roots)
        (result.state.toTypedSource roots) ∧
      TypingSourceExtends (hiddenState.toTypedSource roots)
        (result.state.toTypedSource roots) ∧
      TypingSourceExtends (checked.state.toTypedSource roots)
        (result.state.toTypedSource roots) ∧
      scrutineeState.integerPatterns ⊆ result.state.integerPatterns ∧
      scrutineeState.integerLiterals ⊆ result.state.integerLiterals ∧
      scrutineeState.requirements ⊆ result.state.requirements ∧
      checked.state.integerPatterns ⊆ result.state.integerPatterns ∧
      checked.state.integerLiterals ⊆ result.state.integerLiterals ∧
      checked.state.requirements ⊆ result.state.requirements := by
  obtain ⟨scrutinee, scrutineeState, hiddenScrutinee, hiddenState,
    checked, scrutineeSuccess, hiddenAllocation, casesSuccess,
    _guard, resultEq, _contains⟩ :=
    inferStatementFuel_success_matchWithoutDefault_facts statementEq defaultEq
      allocationEq success roots
  have allocatedInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized allocated semanticContext :=
    initialInvariant.allocateStatementId allocationEq
  have scrutineeProperties := inferMatchScrutineesFuel_inferenceProperties
    allocatedInvariant.ready signatureFormation functionsCanonical
    scrutineeSuccess
  have hiddenReady : hiddenState.InferenceReady := by
    have retained := State.InferenceReady.allocateHiddenLocal
      scrutineeProperties.2.1
    have hiddenEq : scrutineeState.allocateHiddenLocal.2 = hiddenState :=
      congrArg Prod.snd hiddenAllocation
    rw [hiddenEq] at retained
    exact retained
  have hiddenScrutineeBelow : scrutinee.type.VariablesBelow
      hiddenState.inference.next := by
    have hiddenEq : scrutineeState.allocateHiddenLocal.2 = hiddenState :=
      congrArg Prod.snd hiddenAllocation
    rw [← hiddenEq]
    exact scrutineeProperties.2.2
  have hiddenReturnBelow : expectedReturn.VariablesBelow
      hiddenState.inference.next := by
    have atScrutinee := allocatedInvariant.returnBelow.weaken
      scrutineeProperties.1.next_le
    have hiddenEq : scrutineeState.allocateHiddenLocal.2 = hiddenState :=
      congrArg Prod.snd hiddenAllocation
    rw [← hiddenEq]
    exact atScrutinee
  have casesProperties := Detail.inferMatchCasesFuel_inferenceProperties
    hiddenReady signatureFormation functionsCanonical
    hiddenScrutineeBelow hiddenReturnBelow rfl casesSuccess
  have checkedExtension : finalized.substitution.SemanticallyExtends
      checked.state.inference.substitution := by
    simpa [resultEq, State.recordNode] using
      resultSubstitutionExtension
  have hiddenExtension : finalized.substitution.SemanticallyExtends
      hiddenState.inference.substitution :=
    Substitution.SemanticallyExtends.trans checkedExtension
      casesProperties.1.substitution_extends
  have hiddenInferenceEq : hiddenState.inference.substitution =
      scrutineeState.inference.substitution := by
    have stateEq := congrArg Prod.snd hiddenAllocation
    simpa [State.allocateHiddenLocal] using
      congrArg (fun state : State => state.inference.substitution)
        stateEq.symm
  have scrutineeExtension : finalized.substitution.SemanticallyExtends
      scrutineeState.inference.substitution := by
    rw [← hiddenInferenceEq]
    exact hiddenExtension
  have allocatedBelow : allocated.NodesBelowNextOccurrence := by
    have retained :=
      State.allocateStatementId_preserves_nodesBelowNextOccurrence initial
        initialInvariant.nodesBelow
    have allocatedEq : initial.allocateStatementId.2 = allocated :=
      congrArg Prod.snd allocationEq
    simpa [allocatedEq] using retained
  have scrutineeBelow : scrutineeState.NodesBelowNextOccurrence :=
    inferMatchScrutineesFuel_success_nodesBelow scrutineeSuccess
      allocatedBelow
  have hiddenBelow : hiddenState.NodesBelowNextOccurrence := by
    have retained := State.allocateHiddenLocal_preserves_nodesBelowNextOccurrence
      scrutineeState scrutineeBelow
    simpa [hiddenAllocation] using retained
  have hiddenToChecked : TypingSourceExtends
      (hiddenState.toTypedSource roots)
      (checked.state.toTypedSource roots) :=
    inferMatchCasesFuel_success_typingSourceExtends casesSuccess
      hiddenBelow roots
  have checkedToResult : TypingSourceExtends
      (checked.state.toTypedSource roots)
      (result.state.toTypedSource roots) := by
    rw [resultEq]
    refine ⟨rfl, ?_⟩
    simp only [State.toTypedSource, State.recordNode]
    exact List.prefix_append _ _
  have scrutineeToHidden : TypingSourceExtends
      (scrutineeState.toTypedSource roots)
      (hiddenState.toTypedSource roots) := by
    have stateEq : scrutineeState.allocateHiddenLocal.2 = hiddenState :=
      congrArg Prod.snd hiddenAllocation
    rw [← stateEq]
    exact ⟨rfl, by simp [State.allocateHiddenLocal, State.toTypedSource]⟩
  have checkedPatterns : checked.state.integerPatterns ⊆
      result.state.integerPatterns := by
    rw [resultEq]
    intro origin member
    exact member
  have checkedLiterals : checked.state.integerLiterals ⊆
      result.state.integerLiterals := by
    rw [resultEq]
    intro origin member
    simpa [State.recordNode] using member
  have checkedRequirements : checked.state.requirements ⊆
      result.state.requirements := by
    rw [resultEq]
    exact State.recordNode_requirements_subset checked.state _
  have hiddenPatternsEq : hiddenState.integerPatterns =
      scrutineeState.integerPatterns := by
    have stateEq := congrArg Prod.snd hiddenAllocation
    simpa [State.allocateHiddenLocal] using
      congrArg State.integerPatterns stateEq.symm
  have hiddenLiteralsEq : hiddenState.integerLiterals =
      scrutineeState.integerLiterals := by
    have stateEq := congrArg Prod.snd hiddenAllocation
    simpa [State.allocateHiddenLocal] using
      congrArg State.integerLiterals stateEq.symm
  have hiddenRequirementsEq : hiddenState.requirements =
      scrutineeState.requirements := by
    have stateEq := congrArg Prod.snd hiddenAllocation
    simpa [State.allocateHiddenLocal] using
      congrArg State.requirements stateEq.symm
  have scrutineePatterns : scrutineeState.integerPatterns ⊆
      result.state.integerPatterns := by
    have initialToChecked : scrutineeState.integerPatterns ⊆
        checked.state.integerPatterns := by
      have viaCases := Detail.inferMatchCasesFuel_integerPatterns_subset
        casesSuccess
      rw [hiddenPatternsEq] at viaCases
      exact viaCases
    exact List.Subset.trans initialToChecked checkedPatterns
  have scrutineeLiterals : scrutineeState.integerLiterals ⊆
      result.state.integerLiterals := by
    have initialToChecked : scrutineeState.integerLiterals ⊆
        checked.state.integerLiterals := by
      have viaCases := Detail.inferMatchCasesFuel_integerLiterals_subset
        casesSuccess
      rw [hiddenLiteralsEq] at viaCases
      exact viaCases
    exact List.Subset.trans initialToChecked checkedLiterals
  have scrutineeRequirements : scrutineeState.requirements ⊆
      result.state.requirements := by
    have initialToChecked : scrutineeState.requirements ⊆
        checked.state.requirements := by
      have viaCases := Detail.inferMatchCasesFuel_requirements_subset
        casesSuccess
      rw [hiddenRequirementsEq] at viaCases
      exact viaCases
    exact List.Subset.trans initialToChecked checkedRequirements
  exact ⟨scrutinee, scrutineeState, hiddenScrutinee, hiddenState, checked,
    scrutineeSuccess, hiddenAllocation, casesSuccess, scrutineeExtension,
    hiddenExtension, checkedExtension,
    scrutineeToHidden.trans (hiddenToChecked.trans checkedToResult),
    hiddenToChecked.trans checkedToResult, checkedToResult,
    scrutineePatterns, scrutineeLiterals, scrutineeRequirements,
    checkedPatterns, checkedLiterals, checkedRequirements⟩

end Solcore.SourceSemantics.SourceInferenceSoundness
end
