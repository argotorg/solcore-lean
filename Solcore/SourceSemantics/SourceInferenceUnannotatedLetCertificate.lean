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

/-- A retained initialized `let` is one of the binders inspected by the
finalizer's capture-avoidance validation.  This uses the actual statement
occurrence and append-only raw-source extension, not an arbitrary binder. -/
theorem localBinderInstantiationNoCapture_of_retainedLet
    {inferenceContext : Frontend.SourceInference.Context}
    {finalType : Ty}
    {evidenceState : Frontend.SourceInference.State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources inferenceContext finalType
      evidenceState roots finalized)
    {source : TypedSource} {id : StatementId}
    {span : Syntax.SourceSpan} {type : Ty}
    {binder : TypedBinder} {initializer : ExpressionId}
    (recorded : ContainsStatement source id {
      id, span, type, form := .letDecl binder (some initializer) })
    (extension : TypingSourceExtends source
      (evidenceState.toTypedSource roots)) :
    Detail.LocalBinderInstantiationNoCapture finalized.substitution binder := by
  have retained := extension.containsStatement recorded
  apply resources.local_no_capture
  unfold TypedSource.initializedLetBinders
  apply List.mem_flatMap.mpr
  refine ⟨.statement {
    id := id, span := span, type := type,
    form := .letDecl binder (some initializer) }, retained.1, ?_⟩
  simp [Node.initializedLetBinders, StatementForm.initializedLetBinders]

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

/-- Every quantified variable already installed in the active binder stack
was allocated before the current inference cutoff.  This is the small
state-only half of the freshness invariant; it does not claim that future
expressions cannot leak such a variable into a new value type. -/
def ActiveQuantifiersBelowNext
    (state : Frontend.SourceInference.State) : Prop :=
  ∀ binder, binder ∈ state.localBinders →
    ∀ metavariable, metavariable ∈ binder.scheme.quantified →
      metavariable.index < state.inference.next

theorem activeQuantifiersBelowNext_transport
    {before after : Frontend.SourceInference.State}
    (bound : ActiveQuantifiersBelowNext before)
    (bindersEq : after.localBinders = before.localBinders)
    (nextLe : before.inference.next ≤ after.inference.next) :
    ActiveQuantifiersBelowNext after := by
  intro binder member metavariable quantified
  rw [bindersEq] at member
  exact Nat.lt_of_lt_of_le (bound binder member metavariable quantified)
    nextLe

/-- Initial monomorphic parameter binders have no quantified variables. -/
theorem activeQuantifiersBelowNext_initial_mono
    (owner : Resolved.DeclarationId) (locals : Environment)
    (inputComptime : List Bool)
    (monomorphic : ∀ entry, entry ∈ locals → entry.2.quantified = []) :
    ActiveQuantifiersBelowNext
      (Frontend.SourceInference.State.initial owner locals inputComptime) := by
  intro binder member metavariable quantified
  rw [← Frontend.SourceInference.State.initial_inputs_eq_localBinders,
    Frontend.SourceInference.State.initial_inputs_definition] at member
  obtain ⟨index, indexLt, binderEq⟩ := List.exists_of_mem_mapIdx member
  subst binder
  have entryMember : locals[index].2.quantified = [] :=
    monomorphic locals[index] (List.getElem_mem indexLt)
  simp [entryMember] at quantified

/-- Expression inference restores the caller's binder stack and advances the
type allocator, so it preserves the state-only quantifier bound. -/
theorem activeQuantifiersBelowNext_inferExprFuel
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {expression : Syntax.Expr} {expected : Option Ty}
    {initial : Frontend.SourceInference.State}
    {result : InferredExpression × Frontend.SourceInference.State}
    (bound : ActiveQuantifiersBelowNext initial)
    (ready : initial.InferenceReady)
    (validated : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function
        (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow initial.inference.next)
    (success : Detail.inferExprFuel fuel context expression expected initial =
      .ok result) :
    ActiveQuantifiersBelowNext result.2 := by
  have progress := Detail.inferExprFuel_inferenceProperties ready validated
    canonical expectedBelow success
  have bindersEq : result.2.localBinders = initial.localBinders :=
    congrArg Frontend.SourceInference.LexicalScope.binders
      (Detail.inferExprFuel_success_lexicalScope_eq success)
  exact activeQuantifiersBelowNext_transport bound bindersEq
    progress.1.next_le

/-- Exact generalization never quantifies beyond the allocator bound of its
inferred value type. -/
theorem activeQuantifiersBelowNext_generalizeValue
    (state : Frontend.SourceInference.State) (locals : Environment)
    (requirementStart : Nat) (valueType : Ty)
    (valueBelow : valueType.VariablesBelow state.inference.next) :
    ∀ metavariable,
      metavariable ∈
        (Detail.generalizeValue state locals requirementStart valueType
          ).scheme.quantified →
        metavariable.index < state.inference.next := by
  intro metavariable quantified
  rw [Detail.generalizeValue_scheme_quantified] at quantified
  exact valueBelow metavariable (List.mem_filter.mp quantified).1

/-- Installing a generalized binder preserves the active quantifier bound
when the new scheme's quantified variables are bounded by the input state. -/
theorem activeQuantifiersBelowNext_allocateBinder
    (state : Frontend.SourceInference.State)
    (name : String) (scheme : Scheme)
    (span : Option Syntax.SourceSpan) (comptime : Bool)
    (requirements : List LocalSchemeRequirement)
    (bound : ActiveQuantifiersBelowNext state)
    (schemeBelow : ∀ metavariable,
      metavariable ∈ scheme.quantified →
        metavariable.index < state.inference.next) :
    ActiveQuantifiersBelowNext
      (state.allocateBinder name scheme span comptime requirements).2 := by
  intro binder member metavariable quantified
  simp only [Frontend.SourceInference.State.allocateBinder] at member ⊢
  rcases List.mem_cons.mp member with newBinder | oldBinder
  · subst binder
    exact schemeBelow metavariable quantified
  · exact bound binder oldBinder metavariable quantified

/-- A source occurrence allocation changes neither the active binders nor
the type-variable allocator. -/
theorem activeQuantifiersBelowNext_allocateStatementId
    (state : Frontend.SourceInference.State)
    (bound : ActiveQuantifiersBelowNext state) :
    ActiveQuantifiersBelowNext state.allocateStatementId.2 := by
  apply activeQuantifiersBelowNext_transport bound
  · rfl
  · exact Nat.le_refl _

/-- Recording a completed statement changes only the occurrence table. -/
theorem activeQuantifiersBelowNext_recordNode
    (state : Frontend.SourceInference.State) (node : Node)
    (bound : ActiveQuantifiersBelowNext state) :
    ActiveQuantifiersBelowNext (state.recordNode node) := by
  apply activeQuantifiersBelowNext_transport bound
  · rfl
  · exact Nat.le_refl _

/-- The actual unannotated initialized-`let` branch preserves the allocator
bound on all active scheme quantifiers.  The new quantified row is a filtered
subset of the resolved initializer type's already-bounded free variables. -/
theorem inferStatementFuel_success_letUnannotatedInitialized_activeQuantifiersBelowNext
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {name : Syntax.Identifier}
    {initializer : Syntax.Expr} {expectedReturn : Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    (statementEq : statement.value =
      .letDecl name none (some initializer))
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) context statement
      expectedReturn initial = .ok result)
    (bound : ActiveQuantifiersBelowNext initial)
    (ready : initial.InferenceReady)
    (validated : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function
        (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes)) :
    ActiveQuantifiersBelowNext result.state := by
  obtain ⟨inferred, initializerState, locals, valueType, generalized,
      binding, initializerSuccess, _, valueTypeEq, generalizedEq, bindingEq,
      resultEq, _⟩ :=
    inferStatementFuel_success_letUnannotatedInitialized_facts statementEq
      allocationEq success []
  have allocatedBound : ActiveQuantifiersBelowNext allocated := by
    have nextBound := activeQuantifiersBelowNext_allocateStatementId initial
      bound
    simpa only [allocationEq] using nextBound
  have allocatedReady : allocated.InferenceReady := by
    have nextReady :=
      Frontend.SourceInference.State.InferenceReady.allocateStatementId ready
    simpa only [allocationEq] using nextReady
  have expressionProperties := Detail.inferExprFuel_inferenceProperties
    allocatedReady validated canonical (by simp) initializerSuccess
  have initializerBound : ActiveQuantifiersBelowNext initializerState :=
    activeQuantifiersBelowNext_inferExprFuel allocatedBound allocatedReady
      validated canonical (by simp) initializerSuccess
  have valueBelow : valueType.VariablesBelow
      initializerState.inference.next := by
    rw [valueTypeEq]
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using
      (expressionProperties.2.1.solved.variablesBelow_apply
        expressionProperties.2.2)
  have withLocalsBound : ActiveQuantifiersBelowNext
      (initializerState.withLocals locals) :=
    activeQuantifiersBelowNext_transport initializerBound rfl
      (Nat.le_refl _)
  have schemeBelow : ∀ metavariable,
      metavariable ∈ generalized.scheme.quantified →
        metavariable.index <
          (initializerState.withLocals locals).inference.next := by
    simpa [generalizedEq, Frontend.SourceInference.State.withLocals] using
      (activeQuantifiersBelowNext_generalizeValue initializerState locals
        allocated.nextRequirement valueType valueBelow)
  have bindingBound : ActiveQuantifiersBelowNext binding.2 := by
    rw [← bindingEq]
    exact activeQuantifiersBelowNext_allocateBinder
      (initializerState.withLocals locals) name.value generalized.scheme
      (some name.span) false generalized.requirements withLocalsBound
      schemeBelow
  rw [resultEq]
  exact activeQuantifiersBelowNext_recordNode binding.2 _ bindingBound

/-- The second, expression-specific half of freshness: every old allocator
variable that survives into this initializer's resolved value is already in
the executable generalization barrier.  A mutual inference proof must provide
this for actual successful initializer traces. -/
def OldVariablesBlockedAt
    (initial state : Frontend.SourceInference.State)
    (locals : Environment) (requirementStart : Nat) (valueType : Ty) : Prop :=
  ∀ metavariable, metavariable ∈ valueType.freeVariables →
    metavariable.index < initial.inference.next →
      metavariable ∈ Detail.generalizeValueBlockedVariables state locals
        requirementStart

/-- The branch-level provenance obligation for an initializer: an old
allocator variable in its resolved value must originate either in the
current lexical environment or in a requirement that executable
generalization does not abstract.  This must be proved by recursive
expression inference; finalization cannot recover the origin of a variable
after the fact. -/
def OldVariableProvenanceAt
    (initial state : Frontend.SourceInference.State)
    (locals : Environment) (requirementStart : Nat) (valueType : Ty) : Prop :=
  ∀ metavariable, metavariable ∈ valueType.freeVariables →
    metavariable.index < initial.inference.next →
      (∃ entry ∈ locals, metavariable ∈ entry.2.freeVariables) ∨
        ∃ requirement ∈
          Detail.generalizeValueBlockingRequirements state requirementStart,
          metavariable ∈ TypedTraitResolution.predicateVariables
            (Detail.applyPredicate state requirement.predicate)

theorem oldVariablesBlockedAt_iff_provenance
    (initial state : Frontend.SourceInference.State)
    (locals : Environment) (requirementStart : Nat) (valueType : Ty) :
    OldVariablesBlockedAt initial state locals requirementStart valueType ↔
      OldVariableProvenanceAt initial state locals requirementStart
        valueType := by
  unfold OldVariablesBlockedAt OldVariableProvenanceAt
  simp only [Detail.mem_generalizeValueBlockedVariables_iff]

/-- Initializers whose resolved type contains only newly allocated variables
discharge old-variable provenance immediately.  Other expression forms need
the lexical/requirement provenance invariant above. -/
theorem oldVariablesBlockedAt_of_freshValue
    {initial state : Frontend.SourceInference.State}
    {locals : Environment} {requirementStart : Nat} {valueType : Ty}
    (fresh : ∀ metavariable, metavariable ∈ valueType.freeVariables →
      initial.inference.next ≤ metavariable.index) :
    OldVariablesBlockedAt initial state locals requirementStart valueType := by
  intro metavariable member old
  exact False.elim ((Nat.not_lt.mpr (fresh metavariable member)) old)

/-- A simultaneous substitution cannot introduce an unprotected old variable
if every replacement range protects old variables and every untouched source
variable is protected.  This is the common resolve/unify preservation step;
`InferenceReady` alone says nothing about this *lower-bound* provenance, so
the range condition must be threaded separately through inference. -/
theorem oldVariablesProtected_applySubstitution
    (substitution : Substitution) (type : Ty)
    (cutoff : Nat) (protectedVars : List TypeVarId)
    (rangeProtected : ∀ {candidate replacement},
      (candidate, replacement) ∈ substitution →
        ∀ metavariable, metavariable ∈ replacement.freeVariables →
          metavariable.index < cutoff → metavariable ∈ protectedVars)
    (sourceProtected : ∀ metavariable,
      metavariable ∈ type.freeVariables →
        metavariable ∉ substitution.domain →
          metavariable.index < cutoff → metavariable ∈ protectedVars) :
    ∀ metavariable,
      metavariable ∈ (substitution.apply type).freeVariables →
        metavariable.index < cutoff → metavariable ∈ protectedVars := by
  induction type with
  | «variable» candidate =>
      cases found : substitution.lookup? candidate with
      | none =>
          intro metavariable member old
          simp only [Substitution.apply, found, Option.getD_none,
            Ty.freeVariables, List.mem_singleton] at member
          subst metavariable
          exact sourceProtected candidate (by simp [Ty.freeVariables])
            ((Substitution.lookup?_eq_none_iff_not_mem_domain
              substitution candidate).mp found) old
      | some replacement =>
          intro metavariable member old
          simp only [Substitution.apply, found, Option.getD_some] at member
          exact rangeProtected
            (Substitution.lookup?_eq_some_mem found) metavariable member old
  | parameter parameter => simp [Substitution.apply, Ty.freeVariables]
  | constructor constructor => simp [Substitution.apply, Ty.freeVariables]
  | application left right leftInduction rightInduction =>
      intro metavariable member old
      simp only [Substitution.apply] at member
      rw [Ty.mem_freeVariables_application_iff] at member
      rcases member with leftMember | rightMember
      · apply leftInduction (fun candidate sourceMember absent lower =>
          sourceProtected candidate
            ((Ty.mem_freeVariables_application_iff candidate left right).mpr
              (Or.inl sourceMember)) absent lower) metavariable leftMember old
      · apply rightInduction (fun candidate sourceMember absent lower =>
          sourceProtected candidate
            ((Ty.mem_freeVariables_application_iff candidate left right).mpr
              (Or.inr sourceMember)) absent lower) metavariable rightMember old
  | function parameter result parameterInduction resultInduction =>
      intro metavariable member old
      simp only [Substitution.apply] at member
      rw [Ty.mem_freeVariables_function_iff] at member
      rcases member with parameterMember | resultMember
      · apply parameterInduction (fun candidate sourceMember absent lower =>
          sourceProtected candidate
            ((Ty.mem_freeVariables_function_iff candidate parameter result).mpr
              (Or.inl sourceMember)) absent lower) metavariable
            parameterMember old
      · apply resultInduction (fun candidate sourceMember absent lower =>
          sourceProtected candidate
            ((Ty.mem_freeVariables_function_iff candidate parameter result).mpr
              (Or.inr sourceMember)) absent lower) metavariable resultMember old
  | product left right leftInduction rightInduction =>
      intro metavariable member old
      simp only [Substitution.apply] at member
      rw [Ty.mem_freeVariables_product_iff] at member
      rcases member with leftMember | rightMember
      · apply leftInduction (fun candidate sourceMember absent lower =>
          sourceProtected candidate
            ((Ty.mem_freeVariables_product_iff candidate left right).mpr
              (Or.inl sourceMember)) absent lower) metavariable leftMember old
      · apply rightInduction (fun candidate sourceMember absent lower =>
          sourceProtected candidate
            ((Ty.mem_freeVariables_product_iff candidate left right).mpr
              (Or.inr sourceMember)) absent lower) metavariable rightMember old
  | mapping key value keyInduction valueInduction =>
      intro metavariable member old
      simp only [Substitution.apply] at member
      rw [Ty.mem_freeVariables_mapping_iff] at member
      rcases member with keyMember | valueMember
      · apply keyInduction (fun candidate sourceMember absent lower =>
          sourceProtected candidate
            ((Ty.mem_freeVariables_mapping_iff candidate key value).mpr
              (Or.inl sourceMember)) absent lower) metavariable keyMember old
      · apply valueInduction (fun candidate sourceMember absent lower =>
          sourceProtected candidate
            ((Ty.mem_freeVariables_mapping_iff candidate key value).mpr
              (Or.inr sourceMember)) absent lower) metavariable valueMember old
  | proxy inner induction =>
      intro metavariable member old
      simp only [Substitution.apply, Ty.freeVariables] at member
      exact induction sourceProtected metavariable member old
  | comptime inner induction =>
      intro metavariable member old
      simp only [Substitution.apply, Ty.freeVariables] at member
      exact induction sourceProtected metavariable member old
  | error => simp [Substitution.apply, Ty.freeVariables]

/-- Relevance-restricted variant: only first-match substitution entries
reachable from free variables of this particular input type need provenance.
Dead entries may contain earlier scheme quantifiers without affecting this
application. -/
theorem oldVariablesProtected_applySubstitution_relevant
    (substitution : Substitution) (type : Ty)
    (cutoff : Nat) (protectedVars : List TypeVarId)
    (rangeProtected : ∀ candidate,
      candidate ∈ type.freeVariables →
        ∀ replacement, substitution.lookup? candidate = some replacement →
          ∀ metavariable, metavariable ∈ replacement.freeVariables →
            metavariable.index < cutoff →
              metavariable ∈ protectedVars)
    (sourceProtected : ∀ metavariable,
      metavariable ∈ type.freeVariables →
        metavariable ∉ substitution.domain →
          metavariable.index < cutoff → metavariable ∈ protectedVars) :
    ∀ metavariable,
      metavariable ∈ (substitution.apply type).freeVariables →
        metavariable.index < cutoff → metavariable ∈ protectedVars := by
  induction type with
  | «variable» candidate =>
      cases found : substitution.lookup? candidate with
      | none =>
          intro metavariable member old
          simp only [Substitution.apply, found, Option.getD_none,
            Ty.freeVariables, List.mem_singleton] at member
          subst metavariable
          exact sourceProtected candidate (by simp [Ty.freeVariables])
            ((Substitution.lookup?_eq_none_iff_not_mem_domain
              substitution candidate).mp found) old
      | some replacement =>
          intro metavariable member old
          simp only [Substitution.apply, found, Option.getD_some] at member
          exact rangeProtected candidate (by simp [Ty.freeVariables])
            replacement found metavariable member old
  | parameter parameter => simp [Substitution.apply, Ty.freeVariables]
  | constructor constructor => simp [Substitution.apply, Ty.freeVariables]
  | application left right leftInduction rightInduction =>
      intro metavariable member old
      simp only [Substitution.apply] at member
      rw [Ty.mem_freeVariables_application_iff] at member
      rcases member with leftMember | rightMember
      · exact leftInduction
          (fun candidate occurs replacement found rangeVariable rangeOccurs
              lower =>
            rangeProtected candidate
              ((Ty.mem_freeVariables_application_iff candidate left right).mpr
                (Or.inl occurs)) replacement found rangeVariable rangeOccurs
              lower)
          (fun candidate occurs absent lower =>
            sourceProtected candidate
              ((Ty.mem_freeVariables_application_iff candidate left right).mpr
                (Or.inl occurs)) absent lower)
          metavariable leftMember old
      · exact rightInduction
          (fun candidate occurs replacement found rangeVariable rangeOccurs
              lower =>
            rangeProtected candidate
              ((Ty.mem_freeVariables_application_iff candidate left right).mpr
                (Or.inr occurs)) replacement found rangeVariable rangeOccurs
              lower)
          (fun candidate occurs absent lower =>
            sourceProtected candidate
              ((Ty.mem_freeVariables_application_iff candidate left right).mpr
                (Or.inr occurs)) absent lower)
          metavariable rightMember old
  | function parameter result parameterInduction resultInduction =>
      intro metavariable member old
      simp only [Substitution.apply] at member
      rw [Ty.mem_freeVariables_function_iff] at member
      rcases member with parameterMember | resultMember
      · exact parameterInduction
          (fun candidate occurs replacement found rangeVariable rangeOccurs
              lower =>
            rangeProtected candidate
              ((Ty.mem_freeVariables_function_iff candidate parameter result).mpr
                (Or.inl occurs)) replacement found rangeVariable rangeOccurs
              lower)
          (fun candidate occurs absent lower =>
            sourceProtected candidate
              ((Ty.mem_freeVariables_function_iff candidate parameter result).mpr
                (Or.inl occurs)) absent lower)
          metavariable parameterMember old
      · exact resultInduction
          (fun candidate occurs replacement found rangeVariable rangeOccurs
              lower =>
            rangeProtected candidate
              ((Ty.mem_freeVariables_function_iff candidate parameter result).mpr
                (Or.inr occurs)) replacement found rangeVariable rangeOccurs
              lower)
          (fun candidate occurs absent lower =>
            sourceProtected candidate
              ((Ty.mem_freeVariables_function_iff candidate parameter result).mpr
                (Or.inr occurs)) absent lower)
          metavariable resultMember old
  | product left right leftInduction rightInduction =>
      intro metavariable member old
      simp only [Substitution.apply] at member
      rw [Ty.mem_freeVariables_product_iff] at member
      rcases member with leftMember | rightMember
      · exact leftInduction
          (fun candidate occurs replacement found rangeVariable rangeOccurs
              lower =>
            rangeProtected candidate
              ((Ty.mem_freeVariables_product_iff candidate left right).mpr
                (Or.inl occurs)) replacement found rangeVariable rangeOccurs
              lower)
          (fun candidate occurs absent lower =>
            sourceProtected candidate
              ((Ty.mem_freeVariables_product_iff candidate left right).mpr
                (Or.inl occurs)) absent lower)
          metavariable leftMember old
      · exact rightInduction
          (fun candidate occurs replacement found rangeVariable rangeOccurs
              lower =>
            rangeProtected candidate
              ((Ty.mem_freeVariables_product_iff candidate left right).mpr
                (Or.inr occurs)) replacement found rangeVariable rangeOccurs
              lower)
          (fun candidate occurs absent lower =>
            sourceProtected candidate
              ((Ty.mem_freeVariables_product_iff candidate left right).mpr
                (Or.inr occurs)) absent lower)
          metavariable rightMember old
  | mapping key value keyInduction valueInduction =>
      intro metavariable member old
      simp only [Substitution.apply] at member
      rw [Ty.mem_freeVariables_mapping_iff] at member
      rcases member with keyMember | valueMember
      · exact keyInduction
          (fun candidate occurs replacement found rangeVariable rangeOccurs
              lower =>
            rangeProtected candidate
              ((Ty.mem_freeVariables_mapping_iff candidate key value).mpr
                (Or.inl occurs)) replacement found rangeVariable rangeOccurs
              lower)
          (fun candidate occurs absent lower =>
            sourceProtected candidate
              ((Ty.mem_freeVariables_mapping_iff candidate key value).mpr
                (Or.inl occurs)) absent lower)
          metavariable keyMember old
      · exact valueInduction
          (fun candidate occurs replacement found rangeVariable rangeOccurs
              lower =>
            rangeProtected candidate
              ((Ty.mem_freeVariables_mapping_iff candidate key value).mpr
                (Or.inr occurs)) replacement found rangeVariable rangeOccurs
              lower)
          (fun candidate occurs absent lower =>
            sourceProtected candidate
              ((Ty.mem_freeVariables_mapping_iff candidate key value).mpr
                (Or.inr occurs)) absent lower)
          metavariable valueMember old
  | proxy inner induction =>
      intro metavariable member old
      simp only [Substitution.apply, Ty.freeVariables] at member
      exact induction rangeProtected sourceProtected metavariable member old
  | comptime inner induction =>
      intro metavariable member old
      simp only [Substitution.apply, Ty.freeVariables] at member
      exact induction rangeProtected sourceProtected metavariable member old
  | error => simp [Substitution.apply, Ty.freeVariables]

/-- A no-capture check restricted to the free variables of the concrete input
is sufficient to keep its resolved output disjoint from protected variables.
No condition is imposed on dead or shadowed substitution entries. -/
theorem rangeAvoidsVariablesOn_apply_variables_outside
    (substitution : Substitution) (protectedVars : List TypeVarId)
    (type : Ty)
    (rangeAvoids : substitution.RangeAvoidsVariablesOn protectedVars type)
    (sourceOutside : ∀ metavariable,
      metavariable ∈ type.freeVariables → metavariable ∉ protectedVars) :
    ∀ metavariable,
      metavariable ∈ (substitution.apply type).freeVariables →
        metavariable ∉ protectedVars := by
  induction type with
  | «variable» candidate =>
      intro metavariable member
      cases found : substitution.lookup? candidate with
      | none =>
          simp only [Substitution.apply, found, Option.getD_none,
            Ty.freeVariables, List.mem_singleton] at member
          subst metavariable
          exact sourceOutside candidate (by simp [Ty.freeVariables])
      | some replacement =>
          simp only [Substitution.apply, found, Option.getD_some] at member
          exact rangeAvoids candidate (by simp [Ty.freeVariables])
            replacement found metavariable member
  | parameter parameter => simp [Substitution.apply, Ty.freeVariables]
  | constructor constructor => simp [Substitution.apply, Ty.freeVariables]
  | application left right leftInduction rightInduction =>
      intro metavariable member
      simp only [Substitution.apply] at member
      rw [Ty.mem_freeVariables_application_iff] at member
      rcases member with leftMember | rightMember
      · apply leftInduction
          (rangeAvoids.mono (fun candidate occurs =>
            (Ty.mem_freeVariables_application_iff candidate left right).mpr
              (Or.inl occurs)))
          (fun candidate occurs => sourceOutside candidate
            ((Ty.mem_freeVariables_application_iff candidate left right).mpr
              (Or.inl occurs))) metavariable leftMember
      · apply rightInduction
          (rangeAvoids.mono (fun candidate occurs =>
            (Ty.mem_freeVariables_application_iff candidate left right).mpr
              (Or.inr occurs)))
          (fun candidate occurs => sourceOutside candidate
            ((Ty.mem_freeVariables_application_iff candidate left right).mpr
              (Or.inr occurs))) metavariable rightMember
  | function parameter result parameterInduction resultInduction =>
      intro metavariable member
      simp only [Substitution.apply] at member
      rw [Ty.mem_freeVariables_function_iff] at member
      rcases member with parameterMember | resultMember
      · apply parameterInduction
          (rangeAvoids.mono (fun candidate occurs =>
            (Ty.mem_freeVariables_function_iff candidate parameter result).mpr
              (Or.inl occurs)))
          (fun candidate occurs => sourceOutside candidate
            ((Ty.mem_freeVariables_function_iff candidate parameter result).mpr
              (Or.inl occurs))) metavariable parameterMember
      · apply resultInduction
          (rangeAvoids.mono (fun candidate occurs =>
            (Ty.mem_freeVariables_function_iff candidate parameter result).mpr
              (Or.inr occurs)))
          (fun candidate occurs => sourceOutside candidate
            ((Ty.mem_freeVariables_function_iff candidate parameter result).mpr
              (Or.inr occurs))) metavariable resultMember
  | product left right leftInduction rightInduction =>
      intro metavariable member
      simp only [Substitution.apply] at member
      rw [Ty.mem_freeVariables_product_iff] at member
      rcases member with leftMember | rightMember
      · apply leftInduction
          (rangeAvoids.mono (fun candidate occurs =>
            (Ty.mem_freeVariables_product_iff candidate left right).mpr
              (Or.inl occurs)))
          (fun candidate occurs => sourceOutside candidate
            ((Ty.mem_freeVariables_product_iff candidate left right).mpr
              (Or.inl occurs))) metavariable leftMember
      · apply rightInduction
          (rangeAvoids.mono (fun candidate occurs =>
            (Ty.mem_freeVariables_product_iff candidate left right).mpr
              (Or.inr occurs)))
          (fun candidate occurs => sourceOutside candidate
            ((Ty.mem_freeVariables_product_iff candidate left right).mpr
              (Or.inr occurs))) metavariable rightMember
  | mapping key value keyInduction valueInduction =>
      intro metavariable member
      simp only [Substitution.apply] at member
      rw [Ty.mem_freeVariables_mapping_iff] at member
      rcases member with keyMember | valueMember
      · apply keyInduction
          (rangeAvoids.mono (fun candidate occurs =>
            (Ty.mem_freeVariables_mapping_iff candidate key value).mpr
              (Or.inl occurs)))
          (fun candidate occurs => sourceOutside candidate
            ((Ty.mem_freeVariables_mapping_iff candidate key value).mpr
              (Or.inl occurs))) metavariable keyMember
      · apply valueInduction
          (rangeAvoids.mono (fun candidate occurs =>
            (Ty.mem_freeVariables_mapping_iff candidate key value).mpr
              (Or.inr occurs)))
          (fun candidate occurs => sourceOutside candidate
            ((Ty.mem_freeVariables_mapping_iff candidate key value).mpr
              (Or.inr occurs))) metavariable valueMember
  | proxy inner induction => exact induction rangeAvoids sourceOutside
  | comptime inner induction => exact induction rangeAvoids sourceOutside
  | error => simp [Substitution.apply, Ty.freeVariables]

/-- A new unifier update can be composed with an older substitution without
requiring the *older* substitution to avoid the protected variables on dead
entries.  Only old entries selected from the concrete source type matter. -/
theorem rangeAvoidsVariablesOn_compose_of_newerRangeAvoids
    (newer older guard : Substitution) (type : Ty)
    (newerAvoids : newer.RangeAvoidsDomain guard)
    (olderAvoids : older.RangeAvoidsVariablesOn guard.domain type) :
    (newer.compose older).RangeAvoidsVariablesOn guard.domain type := by
  intro candidate sourceMember replacement found metavariable occurs
  rw [Substitution.lookup?_compose] at found
  cases olderFound : older.lookup? candidate with
  | none =>
      rw [olderFound] at found
      exact newerAvoids (Substitution.lookup?_eq_some_mem found)
        metavariable occurs
  | some olderReplacement =>
      rw [olderFound] at found
      injection found with replacementEq
      subst replacement
      have olderRangeOutside : ∀ sourceVariable,
          sourceVariable ∈ olderReplacement.freeVariables →
            sourceVariable ∉ guard.domain := by
        intro sourceVariable sourceOccurs
        exact olderAvoids candidate sourceMember olderReplacement olderFound
          sourceVariable sourceOccurs
      exact newerAvoids.apply_variables_outside_older_domain
        olderReplacement olderRangeOutside metavariable occurs

/-- The result of resolving a type with a solved substitution never consults
that substitution again.  Thus a second resolve needs no new relevance-range
premise, even if unrelated entries contain protected variables. -/
theorem rangeAvoidsVariablesOn_resolved_of_solved
    {substitution : Substitution} {next : Nat}
    (solved : substitution.SolvedBelow next)
    (guarded : List TypeVarId) (type : Ty) :
    substitution.RangeAvoidsVariablesOn guarded
      (substitution.apply type) := by
  intro candidate member replacement found _ _
  have candidateDomain : candidate ∈ substitution.domain := by
    exact List.mem_map.mpr ⟨(candidate, replacement),
      Substitution.lookup?_eq_some_mem found, rfl⟩
  exact False.elim
    ((solved.apply_variables_outside_domain type candidate member)
      candidateDomain)

/-- Unification cannot reintroduce a protected old quantifier in its range
when both normalized inputs already avoid it.  The checker composes its new
solution with the old one; both parts preserve avoidance by the existing
unifier and substitution-composition theorems.  Recursive expression
soundness must still establish avoidance of each actual unification input. -/
theorem inferState_unify_rangeAvoidsProtected
    {before after : InferState} {left right : Ty}
    (protectedDomain : Substitution)
    (beforeAvoids : before.substitution.RangeAvoidsDomain protectedDomain)
    (leftOutside : ∀ metavariable,
      metavariable ∈ (before.resolve left).freeVariables →
        metavariable ∉ protectedDomain.domain)
    (rightOutside : ∀ metavariable,
      metavariable ∈ (before.resolve right).freeVariables →
        metavariable ∉ protectedDomain.domain)
    (success : before.unify left right = .ok after) :
    after.substitution.RangeAvoidsDomain protectedDomain := by
  unfold InferState.unify at success
  cases unified : Unification.unifyTypes (before.resolve left)
      (before.resolve right) with
  | error error =>
      rw [unified] at success
      change Except.error error = Except.ok after at success
      cases success
  | ok update =>
      rw [unified] at success
      change Except.ok {
        before with substitution := update.compose before.substitution
      } = Except.ok after at success
      injection success with afterEq
      subst after
      exact Substitution.RangeAvoidsDomain.compose
        (Unification.unifyTypes_rangeAvoidsDomain leftOutside rightOutside
          unified) beforeAvoids

/-- Relevant form of `inferState_unify_rangeAvoidsProtected`: the older
substitution needs protection only where `sourceType` can consult it.  The
unifier's *new* entries are still all protected by the actual resolved input
types. -/
theorem inferState_unify_rangeAvoidsProtected_on
    {before after : InferState} {left right sourceType : Ty}
    (protectedDomain : Substitution)
    (beforeAvoids : before.substitution.RangeAvoidsVariablesOn
      protectedDomain.domain sourceType)
    (leftOutside : ∀ metavariable,
      metavariable ∈ (before.resolve left).freeVariables →
        metavariable ∉ protectedDomain.domain)
    (rightOutside : ∀ metavariable,
      metavariable ∈ (before.resolve right).freeVariables →
        metavariable ∉ protectedDomain.domain)
    (success : before.unify left right = .ok after) :
    after.substitution.RangeAvoidsVariablesOn protectedDomain.domain
      sourceType := by
  unfold InferState.unify at success
  cases unified : Unification.unifyTypes (before.resolve left)
      (before.resolve right) with
  | error error =>
      rw [unified] at success
      change Except.error error = Except.ok after at success
      cases success
  | ok update =>
      rw [unified] at success
      change Except.ok {
        before with substitution := update.compose before.substitution
      } = Except.ok after at success
      injection success with afterEq
      subst after
      exact rangeAvoidsVariablesOn_compose_of_newerRangeAvoids update
        before.substitution protectedDomain sourceType
        (Unification.unifyTypes_rangeAvoidsDomain leftOutside rightOutside
          unified) beforeAvoids

/-- The entire active binder stack, including shadowed entries, contributes
protected scheme quantifiers.  A synthetic substitution is used only to put
this list in the domain expected by the generic unifier-avoidance theorem;
its dummy range is never applied. -/
def activeSchemeQuantifiers
    (state : Frontend.SourceInference.State) : List TypeVarId :=
  state.localBinders.flatMap fun binder => binder.scheme.quantified

/-- A prior generalized variable is private to its scheme: no active lexical
binder may expose it among its *unquantified* free variables.  This is the
minimal lexical half of the old-quantifier non-escape invariant used by local
identifier inference.  It is stronger than the allocator bound alone. -/
def ActiveSchemeQuantifierIsolation
    (state : Frontend.SourceInference.State) : Prop :=
  ∀ binder, binder ∈ state.localBinders →
    ∀ metavariable,
      metavariable ∈ activeSchemeQuantifiers state →
        metavariable ∉ binder.scheme.freeVariables

theorem activeSchemeQuantifierIsolation_transport
    {before after : Frontend.SourceInference.State}
    (isolated : ActiveSchemeQuantifierIsolation before)
    (bindersEq : after.localBinders = before.localBinders) :
    ActiveSchemeQuantifierIsolation after := by
  simpa [ActiveSchemeQuantifierIsolation, activeSchemeQuantifiers,
    bindersEq] using isolated

theorem activeSchemeQuantifierIsolation_lookupBinder
    {state : Frontend.SourceInference.State}
    {name : String} {binder : TypedBinder}
    (isolated : ActiveSchemeQuantifierIsolation state)
    (found : state.lookupBinder? name = some binder) :
    ∀ metavariable,
      metavariable ∈ binder.scheme.freeVariables →
        metavariable ∉ activeSchemeQuantifiers state := by
  intro metavariable free quantified
  exact isolated binder
    (Frontend.SourceInference.State.lookupBinder?_eq_some_facts found).1
    metavariable quantified free

theorem activeSchemeQuantifierIsolation_allocateExpressionId
    {initial allocated : Frontend.SourceInference.State}
    {id : ExpressionId}
    (isolated : ActiveSchemeQuantifierIsolation initial)
    (allocationEq : initial.allocateExpressionId = (id, allocated)) :
    ActiveSchemeQuantifierIsolation allocated := by
  apply activeSchemeQuantifierIsolation_transport isolated
  have projection := congrArg
    (fun pair : ExpressionId × Frontend.SourceInference.State =>
      pair.2.localBinders) allocationEq
  change initial.localBinders = allocated.localBinders at projection
  exact projection.symm

theorem allocateExpressionId_inferenceNext_eq
    {initial allocated : Frontend.SourceInference.State}
    {id : ExpressionId}
    (allocationEq : initial.allocateExpressionId = (id, allocated)) :
    allocated.inference.next = initial.inference.next := by
  have projection := congrArg
    (fun pair : ExpressionId × Frontend.SourceInference.State =>
      pair.2.inference.next) allocationEq
  change initial.inference.next = allocated.inference.next at projection
  exact projection.symm

theorem activeSchemeQuantifierIsolation_allocateStatementId
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId}
    (isolated : ActiveSchemeQuantifierIsolation initial)
    (allocationEq : initial.allocateStatementId = (id, allocated)) :
    ActiveSchemeQuantifierIsolation allocated := by
  apply activeSchemeQuantifierIsolation_transport isolated
  have projection := congrArg
    (fun pair : StatementId × Frontend.SourceInference.State =>
      pair.2.localBinders) allocationEq
  change initial.localBinders = allocated.localBinders at projection
  exact projection.symm

/-- Entering a new binder preserves lexical quantifier isolation when its
free variables avoid old quantifiers and its new quantifiers avoid every
older binder's free variables.  The same-binder case is automatic from the
definition of `Scheme.freeVariables`. -/
theorem activeSchemeQuantifierIsolation_allocateBinder
    (state : Frontend.SourceInference.State)
    (name : String) (scheme : Scheme)
    (span : Option Syntax.SourceSpan) (comptime : Bool)
    (requirements : List LocalSchemeRequirement)
    (isolated : ActiveSchemeQuantifierIsolation state)
    (newFreeOutsideOld : ∀ metavariable,
      metavariable ∈ scheme.freeVariables →
        metavariable ∉ activeSchemeQuantifiers state)
    (newQuantifiedOutsideOld : ∀ metavariable,
      metavariable ∈ scheme.quantified →
        ∀ binder, binder ∈ state.localBinders →
          metavariable ∉ binder.scheme.freeVariables) :
    ActiveSchemeQuantifierIsolation
      (state.allocateBinder name scheme span comptime requirements).2 := by
  intro binder binderMember metavariable quantifiedMember
  let freshBinder :=
    (state.allocateBinder name scheme span comptime requirements).1
  have binderCases : binder = freshBinder ∨
      binder ∈ state.localBinders := by
    simpa [freshBinder, Frontend.SourceInference.State.allocateBinder]
      using binderMember
  have quantifiedCases : metavariable ∈ scheme.quantified ∨
      metavariable ∈ activeSchemeQuantifiers state := by
    simpa [activeSchemeQuantifiers,
      Frontend.SourceInference.State.allocateBinder] using quantifiedMember
  rcases binderCases with rfl | oldBinder
  · rcases quantifiedCases with newQuantified | oldQuantified
    · intro free
      have freeScheme : metavariable ∈ scheme.freeVariables := by
        simpa [freshBinder, Frontend.SourceInference.State.allocateBinder]
          using free
      simp [Scheme.freeVariables, newQuantified] at freeScheme
    · intro free
      exact newFreeOutsideOld metavariable (by
        simpa [freshBinder, Frontend.SourceInference.State.allocateBinder]
          using free) oldQuantified
  · rcases quantifiedCases with newQuantified | oldQuantified
    · exact newQuantifiedOutsideOld metavariable newQuantified binder
        oldBinder
    · exact isolated binder oldBinder metavariable oldQuantified

/-- A pattern binder is monomorphic.  Its allocation preserves isolation
exactly when its resolved body avoids the quantifiers already active in the
arm scope.  Monomorphic allocation by itself is not enough: an arbitrary
expected pattern type could mention one of those old quantified variables. -/
theorem activeSchemeQuantifierIsolation_allocateMonoBinder
    (state : Frontend.SourceInference.State)
    (name : String) (type : Ty)
    (span : Option Syntax.SourceSpan)
    (isolated : ActiveSchemeQuantifierIsolation state)
    (typeAvoidsOld : ∀ metavariable,
      metavariable ∈ type.freeVariables →
        metavariable ∉ activeSchemeQuantifiers state) :
    ActiveSchemeQuantifierIsolation
      (state.allocateBinder name (.mono type) span false []).2 := by
  apply activeSchemeQuantifierIsolation_allocateBinder state name (.mono type)
    span false [] isolated
  · simpa [Scheme.freeVariables, Scheme.mono] using typeAvoidsOld
  · intro metavariable quantified
    simp [Scheme.mono] at quantified

/-- The checker starts ordinary body inference with monomorphic parameters,
so the lexical quantifier-isolation invariant is initially vacuous. -/
theorem activeSchemeQuantifierIsolation_initial_mono
    (owner : Resolved.DeclarationId) (locals : Environment)
    (inputComptime : List Bool)
    (monomorphic : ∀ entry, entry ∈ locals → entry.2.quantified = []) :
    ActiveSchemeQuantifierIsolation
      (Frontend.SourceInference.State.initial owner locals inputComptime) := by
  intro _ _ metavariable quantified
  rcases List.mem_flatMap.mp quantified with
    ⟨binder, binderMember, rawQuantified⟩
  rw [← Frontend.SourceInference.State.initial_inputs_eq_localBinders,
    Frontend.SourceInference.State.initial_inputs_definition] at binderMember
  obtain ⟨index, indexLt, binderEq⟩ :=
    List.exists_of_mem_mapIdx binderMember
  subst binder
  have noQuantified : locals[index].2.quantified = [] :=
    monomorphic locals[index] (List.getElem_mem indexLt)
  simp [noQuantified] at rawQuantified

/-- A scheme variable outside the outer substitution's domain remains free
after applying that substitution to the scheme.  Restricting the substitution
at quantified variables cannot remove an originally unquantified variable. -/
theorem schemeFreeVariable_survives_outside_domain
    (substitution : Substitution) (scheme : Scheme)
    {metavariable : TypeVarId}
    (free : metavariable ∈ scheme.freeVariables)
    (absent : metavariable ∉ substitution.domain) :
    metavariable ∈ (scheme.apply substitution).freeVariables := by
  have bodyFree : metavariable ∈ scheme.body.freeVariables :=
    (List.mem_filter.mp free).1
  have notQuantified : metavariable ∉ scheme.quantified := by
    have selected := (List.mem_filter.mp free).2
    intro quantified
    simp [quantified] at selected
  have restrictedAbsent : metavariable ∉
      (substitution.without scheme.quantified).domain := by
    intro restrictedMember
    rcases List.mem_map.mp restrictedMember with
      ⟨entry, entryMember, keyEq⟩
    exact absent (List.mem_map.mpr
      ⟨entry, Substitution.mem_of_mem_without entryMember, keyEq⟩)
  have appliedFree :=
    FlexibleSubstitution.Substitution.mem_freeVariables_apply_of_not_mem_domain
      (substitution.without scheme.quantified) restrictedAbsent bodyFree
  apply List.mem_filter.mpr
  exact ⟨by simpa [Scheme.apply] using appliedFree, by
    simp [notQuantified]⟩

/-- A variable selected for executable generalization cannot have been an
unquantified free variable of any older lexical binder.  The crucial facts
are that `generalizeValue` receives the already-substituted binder
environment, and that the value type was resolved by a solved substitution.
This is the new-quantifier/old-binder half of lexical isolation. -/
theorem generalizeValue_quantified_outside_oldBinderFree
    (state : Frontend.SourceInference.State)
    (locals : Environment) (requirementStart : Nat) (valueType : Ty)
    (localsEq : locals =
      state.binderEnvironment.apply state.inference.substitution)
    (valueOutsideDomain : ∀ metavariable,
      metavariable ∈ valueType.freeVariables →
        metavariable ∉ state.inference.substitution.domain) :
    ∀ metavariable,
      metavariable ∈
        (Detail.generalizeValue state locals requirementStart valueType
          ).scheme.quantified →
        ∀ binder, binder ∈ state.localBinders →
          metavariable ∉ binder.scheme.freeVariables := by
  intro metavariable quantified binder binderMember binderFree
  rw [Detail.generalizeValue_scheme_quantified] at quantified
  obtain ⟨valueFree, selected⟩ := List.mem_filter.mp quantified
  have notBlocked : metavariable ∉
      Detail.generalizeValueBlockedVariables state locals
        requirementStart := by
    intro blocked
    simp [blocked] at selected
  have appliedFree : metavariable ∈
      (binder.scheme.apply state.inference.substitution).freeVariables :=
    schemeFreeVariable_survives_outside_domain
      state.inference.substitution binder.scheme binderFree
      (valueOutsideDomain metavariable valueFree)
  have entryMember : (binder.name,
      binder.scheme.apply state.inference.substitution) ∈ locals := by
    rw [localsEq]
    unfold Environment.apply
    apply List.mem_map.mpr
    refine ⟨(binder.name, binder.scheme), ?_, rfl⟩
    unfold Frontend.SourceInference.State.binderEnvironment
    exact List.mem_map.mpr ⟨binder, binderMember, rfl⟩
  have blocked : metavariable ∈
      Detail.generalizeValueBlockedVariables state locals
        requirementStart := by
    apply List.mem_append.mpr
    apply Or.inl
    exact (TypeSystem.Environment.mem_freeVariables_iff
      metavariable locals).mpr
      ⟨(binder.name,
        binder.scheme.apply state.inference.substitution), entryMember,
        appliedFree⟩
  exact notBlocked blocked

theorem generalizeValue_schemeFree_subset_valueType
    (state : Frontend.SourceInference.State)
    (locals : Environment) (requirementStart : Nat) (valueType : Ty) :
    ∀ metavariable,
      metavariable ∈
        (Detail.generalizeValue state locals requirementStart valueType
          ).scheme.freeVariables →
        metavariable ∈ valueType.freeVariables := by
  intro metavariable member
  have bodyEq := Detail.generalizeValue_scheme_body state locals
    requirementStart valueType
  have bodyMember := (List.mem_filter.mp member).1
  simpa [Scheme.freeVariables, bodyEq] using bodyMember

/-- One actual `generalizeValue` binder installation preserves lexical
quantifier isolation.  The statement/for-item recursion still has to prove
that its inferred initializer value avoids the older active quantifiers;
that is an expression-provenance obligation, not a finalizer consequence. -/
theorem activeSchemeQuantifierIsolation_generalizeValue
    (state : Frontend.SourceInference.State)
    (locals : Environment) (requirementStart : Nat) (valueType : Ty)
    (name : String) (span : Option Syntax.SourceSpan)
    (comptime : Bool) (requirements : List LocalSchemeRequirement)
    (isolated : ActiveSchemeQuantifierIsolation state)
    (localsEq : locals =
      state.binderEnvironment.apply state.inference.substitution)
    (valueOutsideDomain : ∀ metavariable,
      metavariable ∈ valueType.freeVariables →
        metavariable ∉ state.inference.substitution.domain)
    (valueOutsideOld : ∀ metavariable,
      metavariable ∈ valueType.freeVariables →
        metavariable ∉ activeSchemeQuantifiers state) :
    ActiveSchemeQuantifierIsolation
      ((state.withLocals locals).allocateBinder name
        (Detail.generalizeValue state locals requirementStart valueType
          ).scheme span comptime requirements).2 := by
  apply activeSchemeQuantifierIsolation_allocateBinder
  · exact activeSchemeQuantifierIsolation_transport isolated rfl
  · intro metavariable free
    have valueFree := generalizeValue_schemeFree_subset_valueType state locals
      requirementStart valueType metavariable free
    simpa [activeSchemeQuantifiers,
      Frontend.SourceInference.State.withLocals] using
      (valueOutsideOld metavariable valueFree)
  · intro metavariable quantified binder binderMember
    have outside := generalizeValue_quantified_outside_oldBinderFree
      state locals requirementStart valueType localsEq valueOutsideDomain
      metavariable quantified binder
    exact outside (by simpa [Frontend.SourceInference.State.withLocals]
      using binderMember)

/-- The executable initialized-`let` branch retains lexical quantifier
isolation once its actual initializer result is known to avoid the caller's
older quantifiers.  The child premise is tied to the successful recursive
call, not to arbitrary inferred expressions. -/
theorem inferStatementFuel_success_letUnannotatedInitialized_activeSchemeQuantifierIsolation
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {name : Syntax.Identifier}
    {initializer : Syntax.Expr} {expectedReturn : Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    (statementEq : statement.value =
      .letDecl name none (some initializer))
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) context statement
      expectedReturn initial = .ok result)
    (isolated : ActiveSchemeQuantifierIsolation initial)
    (ready : initial.InferenceReady)
    (validated : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function
        (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (initializerIsolation : ∀ inferred initializerState,
      Detail.inferExprFuel fuel context initializer none allocated =
        .ok (inferred, initializerState) →
      ∀ metavariable,
        metavariable ∈
          (initializerState.resolve inferred.type).freeVariables →
            metavariable ∉ activeSchemeQuantifiers initial) :
    ActiveSchemeQuantifierIsolation result.state := by
  obtain ⟨inferred, initializerState, locals, valueType, generalized,
      binding, initializerSuccess, localsEq, valueTypeEq, generalizedEq,
      bindingEq, resultEq, _⟩ :=
    inferStatementFuel_success_letUnannotatedInitialized_facts statementEq
      allocationEq success []
  have allocatedIsolated : ActiveSchemeQuantifierIsolation allocated :=
    activeSchemeQuantifierIsolation_allocateStatementId isolated allocationEq
  have allocatedReady : allocated.InferenceReady := by
    have nextReady :=
      Frontend.SourceInference.State.InferenceReady.allocateStatementId ready
    simpa only [allocationEq] using nextReady
  have initializerProperties := Detail.inferExprFuel_inferenceProperties
    allocatedReady validated canonical (by simp) initializerSuccess
  have initializerIsolated : ActiveSchemeQuantifierIsolation
      initializerState := by
    apply activeSchemeQuantifierIsolation_transport allocatedIsolated
    exact congrArg Frontend.SourceInference.LexicalScope.binders
      (Detail.inferExprFuel_success_lexicalScope_eq initializerSuccess)
  have valueOutsideDomain : ∀ metavariable,
      metavariable ∈ valueType.freeVariables →
        metavariable ∉ initializerState.inference.substitution.domain := by
    intro metavariable member
    rw [valueTypeEq] at member
    exact initializerProperties.2.1.solved.apply_variables_outside_domain
      inferred.type metavariable (by
        simpa [Frontend.SourceInference.State.resolve,
          TypeSystem.InferState.resolve] using member)
  have allocatedBindersEq : allocated.localBinders = initial.localBinders := by
    have projection := congrArg
      (fun pair : StatementId × Frontend.SourceInference.State =>
        pair.2.localBinders) allocationEq
    change initial.localBinders = allocated.localBinders at projection
    exact projection.symm
  have valueOutsideOld : ∀ metavariable,
      metavariable ∈ valueType.freeVariables →
        metavariable ∉ activeSchemeQuantifiers initializerState := by
    intro metavariable member
    have outside := initializerIsolation inferred initializerState
      initializerSuccess metavariable (by simpa [valueTypeEq] using member)
    have expressionBindersEq : initializerState.localBinders =
        allocated.localBinders := congrArg
      Frontend.SourceInference.LexicalScope.binders
        (Detail.inferExprFuel_success_lexicalScope_eq initializerSuccess)
    simpa [activeSchemeQuantifiers, expressionBindersEq,
      allocatedBindersEq] using outside
  have bindingIsolated : ActiveSchemeQuantifierIsolation binding.2 := by
    rw [← bindingEq, generalizedEq]
    exact activeSchemeQuantifierIsolation_generalizeValue
      initializerState locals allocated.nextRequirement valueType name.value
      (some name.span) false
      (Detail.generalizeValue initializerState locals
        allocated.nextRequirement valueType).requirements
      initializerIsolated localsEq valueOutsideDomain valueOutsideOld
  rw [resultEq]
  exact activeSchemeQuantifierIsolation_transport bindingIsolated rfl

/-- Inversion of the actual unannotated initialized declaration in a `for`
header.  The returned state is exactly the state after the new binder is
allocated; no extra source node is recorded by this header item. -/
theorem inferForItemFuel_success_letUnannotatedInitialized_facts
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {item : Syntax.ForItem} {name : Syntax.Identifier}
    {initializer : Syntax.Expr}
    {initial : Frontend.SourceInference.State}
    {result : ForItemForm × Frontend.SourceInference.State}
    (itemEq : item.value = .letDecl name none (some initializer))
    (success : Detail.inferForItemFuel (fuel + 1) context item initial =
      .ok result) :
    ∃ inferred initializerState locals valueType generalized binding,
      Detail.inferExprFuel fuel context initializer none initial =
        .ok (inferred, initializerState) ∧
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
  cases initializerSuccess :
      Detail.inferExprFuel fuel context initializer none initial with
  | error error =>
      simp [initializerSuccess] at success
  | ok initializerPair =>
      rcases initializerPair with ⟨inferred, initializerState⟩
      simp only [initializerSuccess, pure, Pure.pure, Except.pure] at success
      let locals := initializerState.binderEnvironment.apply
        initializerState.inference.substitution
      let valueType := initializerState.resolve inferred.type
      let generalized := Detail.generalizeValue initializerState locals
        initial.nextRequirement valueType
      let binding :=
        (initializerState.withLocals locals).allocateBinder name.value
          generalized.scheme (some name.span) false
          generalized.requirements
      injection success with resultEq
      rw [← resultEq]
      exact ⟨inferred, initializerState, locals, valueType, generalized,
        binding, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The corresponding `for`-header item preserves the same lexical
isolation invariant, with its actual initializer as the only recursive
expression premise. -/
theorem inferForItemFuel_success_letUnannotatedInitialized_activeSchemeQuantifierIsolation
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {item : Syntax.ForItem} {name : Syntax.Identifier}
    {initializer : Syntax.Expr}
    {initial : Frontend.SourceInference.State}
    {result : ForItemForm × Frontend.SourceInference.State}
    (itemEq : item.value = .letDecl name none (some initializer))
    (success : Detail.inferForItemFuel (fuel + 1) context item initial =
      .ok result)
    (isolated : ActiveSchemeQuantifierIsolation initial)
    (ready : initial.InferenceReady)
    (validated : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function
        (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (initializerIsolation : ∀ inferred initializerState,
      Detail.inferExprFuel fuel context initializer none initial =
        .ok (inferred, initializerState) →
      ∀ metavariable,
        metavariable ∈
          (initializerState.resolve inferred.type).freeVariables →
            metavariable ∉ activeSchemeQuantifiers initial) :
    ActiveSchemeQuantifierIsolation result.2 := by
  obtain ⟨inferred, initializerState, locals, valueType, generalized,
      binding, initializerSuccess, localsEq, valueTypeEq, generalizedEq,
      bindingEq, resultEq⟩ :=
    inferForItemFuel_success_letUnannotatedInitialized_facts itemEq success
  have initializerProperties := Detail.inferExprFuel_inferenceProperties
    ready validated canonical (by simp) initializerSuccess
  have bindersEq : initializerState.localBinders = initial.localBinders :=
    congrArg Frontend.SourceInference.LexicalScope.binders
      (Detail.inferExprFuel_success_lexicalScope_eq initializerSuccess)
  have initializerIsolated : ActiveSchemeQuantifierIsolation
      initializerState :=
    activeSchemeQuantifierIsolation_transport isolated bindersEq
  have valueOutsideDomain : ∀ metavariable,
      metavariable ∈ valueType.freeVariables →
        metavariable ∉ initializerState.inference.substitution.domain := by
    intro metavariable member
    rw [valueTypeEq] at member
    exact initializerProperties.2.1.solved.apply_variables_outside_domain
      inferred.type metavariable (by
        simpa [Frontend.SourceInference.State.resolve,
          TypeSystem.InferState.resolve] using member)
  have valueOutsideOld : ∀ metavariable,
      metavariable ∈ valueType.freeVariables →
        metavariable ∉ activeSchemeQuantifiers initializerState := by
    intro metavariable member
    have outside := initializerIsolation inferred initializerState
      initializerSuccess metavariable (by simpa [valueTypeEq] using member)
    simpa [activeSchemeQuantifiers, bindersEq] using outside
  have bindingIsolated : ActiveSchemeQuantifierIsolation binding.2 := by
    rw [← bindingEq, generalizedEq]
    exact activeSchemeQuantifierIsolation_generalizeValue
      initializerState locals initial.nextRequirement valueType name.value
      (some name.span) false
      (Detail.generalizeValue initializerState locals
        initial.nextRequirement valueType).requirements
      initializerIsolated localsEq valueOutsideDomain valueOutsideOld
  rw [resultEq]
  exact bindingIsolated

def activeSchemeQuantifierGuard
    (state : Frontend.SourceInference.State) : Substitution :=
  (activeSchemeQuantifiers state).map fun metavariable =>
    (metavariable, Ty.word)

@[simp] theorem activeSchemeQuantifierGuard_domain
    (state : Frontend.SourceInference.State) :
    (activeSchemeQuantifierGuard state).domain =
      activeSchemeQuantifiers state := by
  simp [activeSchemeQuantifierGuard, Substitution.domain,
    List.map_map, Function.comp_def]

/-- Actual source-inference unification preserves range isolation from every
previously active scheme quantifier, provided both resolved inputs avoid
those quantifiers.  This is the unification step of the non-escape invariant;
expression branches must provide the input-side avoidance. -/
theorem inferState_unify_rangeAvoidsActiveSchemeQuantifiers
    (state : Frontend.SourceInference.State)
    {after : InferState} {left right : Ty}
    (beforeAvoids : state.inference.substitution.RangeAvoidsDomain
      (activeSchemeQuantifierGuard state))
    (leftOutside : ∀ metavariable,
      metavariable ∈ (state.inference.resolve left).freeVariables →
        metavariable ∉ activeSchemeQuantifiers state)
    (rightOutside : ∀ metavariable,
      metavariable ∈ (state.inference.resolve right).freeVariables →
        metavariable ∉ activeSchemeQuantifiers state)
    (success : state.inference.unify left right = .ok after) :
    after.substitution.RangeAvoidsDomain
      (activeSchemeQuantifierGuard state) := by
  apply inferState_unify_rangeAvoidsProtected
    (activeSchemeQuantifierGuard state) beforeAvoids
  · simpa using leftOutside
  · simpa using rightOutside
  · exact success

/-- Reachability-restricted variant for the active scheme quantifiers. -/
theorem inferState_unify_rangeAvoidsActiveSchemeQuantifiers_on
    (state : Frontend.SourceInference.State)
    {after : InferState} {left right sourceType : Ty}
    (beforeAvoids : state.inference.substitution.RangeAvoidsVariablesOn
      (activeSchemeQuantifiers state) sourceType)
    (leftOutside : ∀ metavariable,
      metavariable ∈ (state.inference.resolve left).freeVariables →
        metavariable ∉ activeSchemeQuantifiers state)
    (rightOutside : ∀ metavariable,
      metavariable ∈ (state.inference.resolve right).freeVariables →
        metavariable ∉ activeSchemeQuantifiers state)
    (success : state.inference.unify left right = .ok after) :
    after.substitution.RangeAvoidsVariablesOn
      (activeSchemeQuantifiers state) sourceType := by
  simpa only [activeSchemeQuantifierGuard_domain] using
    (inferState_unify_rangeAvoidsProtected_on
      (activeSchemeQuantifierGuard state)
      (by simpa only [activeSchemeQuantifierGuard_domain] using beforeAvoids)
      (by simpa only [activeSchemeQuantifierGuard_domain] using leftOutside)
      (by simpa only [activeSchemeQuantifierGuard_domain] using rightOutside)
      success)

/-- A local scheme instantiation cannot expose any of its protected
quantified variables as an *old* result variable.  Fresh instantiation ranges
start at `next`; an older survivor must have been unquantified in the source
scheme and therefore appears in the lexical environment's free-variable
collector.  Subsequent inference substitution needs the separate range
provenance invariant of `oldVariablesProtected_applySubstitution`. -/
theorem instantiateWithSubstitution_oldVariables_in_schemeFreeVariables
    (scheme : Scheme) (cutoff next : Nat)
    (cutoffLe : cutoff ≤ next)
    (quantifiedUnique : scheme.quantified.Nodup) :
    ∀ metavariable,
      metavariable ∈
        (scheme.instantiateWithSubstitution next).body.freeVariables →
        metavariable.index < cutoff →
          metavariable ∈ scheme.freeVariables := by
  let instantiated := scheme.instantiateWithSubstitution next
  have domainPerm :=
    Scheme.instantiateWithSubstitution_substitution_domain_permutation scheme
      next quantifiedUnique
  change ∀ metavariable,
    metavariable ∈ (instantiated.substitution.apply scheme.body
      ).freeVariables →
      metavariable.index < cutoff → metavariable ∈ scheme.freeVariables
  apply oldVariablesProtected_applySubstitution
    instantiated.substitution scheme.body cutoff scheme.freeVariables
  · intro candidate replacement member metavariable occurs old
    rcases Scheme.instantiateWithSubstitution_substitution_range_fresh
        scheme next member with ⟨fresh, replacementEq, freshLower, _⟩
    rw [replacementEq] at occurs
    have variableEq : metavariable = fresh := by
      simpa [Ty.freeVariables] using occurs
    subst metavariable
    exact False.elim ((Nat.not_lt.mpr (Nat.le_trans cutoffLe freshLower)) old)
  · intro metavariable occurs absent _
    have notQuantified : metavariable ∉ scheme.quantified := by
      intro quantified
      exact absent (domainPerm.mem_iff.mpr quantified)
    exact List.mem_filter.mpr ⟨occurs, by simp [notQuantified]⟩

/-- Fresh instantiation cannot expose a protected old scheme quantifier if
the source scheme's unquantified free variables already avoid the protected
set.  This isolates the precise lexical invariant needed by the actual local
identifier branch. -/
theorem instantiateWithSubstitution_avoidsOldQuantifiers
    (scheme : Scheme) (cutoff next : Nat) (guarded : List TypeVarId)
    (cutoffLe : cutoff ≤ next)
    (quantifiedUnique : scheme.quantified.Nodup)
    (guardedBelow : ∀ metavariable,
      metavariable ∈ guarded → metavariable.index < cutoff)
    (schemeFreeOutside : ∀ metavariable,
      metavariable ∈ scheme.freeVariables → metavariable ∉ guarded) :
    ∀ metavariable,
      metavariable ∈
        (scheme.instantiateWithSubstitution next).body.freeVariables →
        metavariable ∉ guarded := by
  intro metavariable occurs guardedMember
  have schemeFree :=
    instantiateWithSubstitution_oldVariables_in_schemeFreeVariables
      scheme cutoff next cutoffLe quantifiedUnique metavariable occurs
      (guardedBelow metavariable guardedMember)
  exact schemeFreeOutside metavariable schemeFree guardedMember

theorem activeSchemeQuantifiers_below_next
    {state : Frontend.SourceInference.State}
    (bound : ActiveQuantifiersBelowNext state) :
    ∀ metavariable,
      metavariable ∈ activeSchemeQuantifiers state →
        metavariable.index < state.inference.next := by
  intro metavariable member
  rcases List.mem_flatMap.mp member with
    ⟨binder, binderMember, quantified⟩
  exact bound binder binderMember metavariable quantified

/-- The exact additional state invariant needed to carry old-variable
provenance through `State.resolve`: every substitution replacement that
mentions an old allocator variable must place it in the active executable
generalization barrier.  This is not a consequence of `InferenceReady`, which
only bounds indices above and states solvedness. -/
def InferenceRangeOldVariablesBlockedAt
    (initial state : Frontend.SourceInference.State)
    (locals : Environment) (requirementStart : Nat) : Prop :=
  ∀ {candidate replacement},
    (candidate, replacement) ∈ state.inference.substitution →
      ∀ metavariable, metavariable ∈ replacement.freeVariables →
        metavariable.index < initial.inference.next →
          metavariable ∈ Detail.generalizeValueBlockedVariables state locals
            requirementStart

/-- Only entries reached by the free variables of the concrete input type
can contribute an old variable to its resolved value.  In particular, a
shadowed or otherwise dead substitution entry need not satisfy the let
generalization barrier. -/
def InferenceRangeOldVariablesBlockedOn
    (initial state : Frontend.SourceInference.State)
    (locals : Environment) (requirementStart : Nat) (type : Ty) : Prop :=
  ∀ candidate, candidate ∈ type.freeVariables →
    ∀ replacement, state.inference.substitution.lookup? candidate =
      some replacement →
      ∀ metavariable, metavariable ∈ replacement.freeVariables →
        metavariable.index < initial.inference.next →
          metavariable ∈ Detail.generalizeValueBlockedVariables state locals
            requirementStart

theorem InferenceRangeOldVariablesBlockedAt.on
    {initial state : Frontend.SourceInference.State}
    {locals : Environment} {requirementStart : Nat} {type : Ty}
    (blocked : InferenceRangeOldVariablesBlockedAt initial state locals
      requirementStart) :
    InferenceRangeOldVariablesBlockedOn initial state locals requirementStart
      type := by
  intro candidate _ replacement found metavariable occurs older
  exact blocked (Substitution.lookup?_eq_some_mem found) metavariable
    occurs older

/-- The checker need only preserve range provenance at first-match entries
actually reachable from the type being resolved. -/
theorem oldVariablesBlockedAt_resolve_on
    {initial state : Frontend.SourceInference.State}
    {locals : Environment} {requirementStart : Nat} {type : Ty}
    (rangeBlocked : InferenceRangeOldVariablesBlockedOn initial state locals
      requirementStart type)
    (sourceBlocked : ∀ metavariable,
      metavariable ∈ type.freeVariables →
        metavariable ∉ state.inference.substitution.domain →
          metavariable.index < initial.inference.next →
            metavariable ∈ Detail.generalizeValueBlockedVariables state locals
              requirementStart) :
    OldVariablesBlockedAt initial state locals requirementStart
      (state.resolve type) := by
  change ∀ metavariable,
    metavariable ∈
      (state.inference.substitution.apply type).freeVariables →
      metavariable.index < initial.inference.next →
        metavariable ∈ Detail.generalizeValueBlockedVariables state locals
          requirementStart
  exact oldVariablesProtected_applySubstitution_relevant
    state.inference.substitution type initial.inference.next
    (Detail.generalizeValueBlockedVariables state locals requirementStart)
    rangeBlocked sourceBlocked

/-- Resolve preserves the executable old-variable barrier when its
substitution range satisfies the provenance invariant and untouched source
variables were already blocked. -/
theorem oldVariablesBlockedAt_resolve
    {initial state : Frontend.SourceInference.State}
    {locals : Environment} {requirementStart : Nat} {type : Ty}
    (rangeBlocked : InferenceRangeOldVariablesBlockedAt initial state locals
      requirementStart)
    (sourceBlocked : ∀ metavariable,
      metavariable ∈ type.freeVariables →
        metavariable ∉ state.inference.substitution.domain →
          metavariable.index < initial.inference.next →
            metavariable ∈ Detail.generalizeValueBlockedVariables state locals
              requirementStart) :
    OldVariablesBlockedAt initial state locals requirementStart
      (state.resolve type) := by
  exact oldVariablesBlockedAt_resolve_on rangeBlocked.on sourceBlocked

/-- Local-scheme instantiation needs range provenance only for the fresh
instantiated body that is actually resolved by this branch. -/
theorem oldVariablesBlockedAt_resolvedLocalInstantiation_on
    {initial state : Frontend.SourceInference.State}
    {locals : Environment} {requirementStart : Nat}
    (binder : TypedBinder) (instantiationStart : Nat)
    (startLe : initial.inference.next ≤ instantiationStart)
    (quantifiedUnique : binder.scheme.quantified.Nodup)
    (binderFreeInLocals : binder.scheme.freeVariables ⊆ locals.freeVariables)
    (rangeBlocked : InferenceRangeOldVariablesBlockedOn initial state locals
      requirementStart
      (binder.scheme.instantiateWithSubstitution instantiationStart).body) :
    OldVariablesBlockedAt initial state locals requirementStart
      (state.resolve
        (binder.scheme.instantiateWithSubstitution instantiationStart).body) := by
  apply oldVariablesBlockedAt_resolve_on rangeBlocked
  intro metavariable member _ old
  have schemeFree :=
    instantiateWithSubstitution_oldVariables_in_schemeFreeVariables
      binder.scheme initial.inference.next instantiationStart startLe
      quantifiedUnique metavariable member old
  exact List.mem_append.mpr (Or.inl (binderFreeInLocals schemeFree))

/-- In the local-reference branch, fresh scheme instantiation itself cannot
leak an older quantified binder.  After its explicit `state.resolve`, the only
extra hypothesis is the substitution-range provenance invariant.  The lexical
premise is exactly the binder's free-variable contribution to the current
environment collected by `generalizeValue`. -/
theorem oldVariablesBlockedAt_resolvedLocalInstantiation
    {initial state : Frontend.SourceInference.State}
    {locals : Environment} {requirementStart : Nat}
    (binder : TypedBinder) (instantiationStart : Nat)
    (startLe : initial.inference.next ≤ instantiationStart)
    (quantifiedUnique : binder.scheme.quantified.Nodup)
    (binderFreeInLocals : binder.scheme.freeVariables ⊆ locals.freeVariables)
    (rangeBlocked : InferenceRangeOldVariablesBlockedAt initial state locals
      requirementStart) :
    OldVariablesBlockedAt initial state locals requirementStart
      (state.resolve
        (binder.scheme.instantiateWithSubstitution instantiationStart).body) := by
  exact oldVariablesBlockedAt_resolvedLocalInstantiation_on binder
    instantiationStart startLe quantifiedUnique binderFreeInLocals
    rangeBlocked.on

/-- The concrete local-identifier traversal with no expected type exposes
the resolved instantiated body as its returned type.  Requirement allocation
and expression recording do not alter the inference substitution; the second
resolve performed by `withExpected none` is explicit here so this inversion
does not silently rely on solved-substitution idempotence. -/
theorem inferExprFuel_success_localIdentifier_noExpected_type
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {expression : Syntax.Expr}
    {initial allocated : Frontend.SourceInference.State}
    {id : ExpressionId} {name : Syntax.Identifier}
    {binder : TypedBinder}
    {result : InferredExpression × Frontend.SourceInference.State}
    (expressionEq : expression.value = .identifier name)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (lookupEq : allocated.lookupBinder? name.value = some binder)
    (success : Detail.inferExprFuel (fuel + 1) context expression none
      initial = .ok result) :
    result.1.type =
      (let instantiationStart := allocated.inference.next
       let instantiated :=
         binder.scheme.instantiateWithSubstitution instantiationStart
       let advanced : Frontend.SourceInference.State := {
         allocated with inference := {
           allocated.inference with next := instantiated.next
         }
       }
       result.2.resolve (advanced.resolve instantiated.body)) := by
  have recorded := Detail.inferExprFuel_success_localIdentifier_record
    expressionEq allocationEq lookupEq success
  simp only [Detail.recordExpressionWithExpected, Detail.withExpected,
    bind, Except.bind, Detail.recordExpression] at recorded
  injection recorded with resultEq
  subst result
  rfl

private theorem addRequirementsWithIds_inference
    (state : Frontend.SourceInference.State)
    (predicates : List ProgramPredicate) :
    (state.addRequirementsWithIds predicates).2.inference =
      state.inference := by
  induction predicates generalizing state with
  | nil => rfl
  | cons predicate rest induction =>
      simp only [Frontend.SourceInference.State.addRequirementsWithIds]
      rw [induction]
      rfl

/-- The same actual local-identifier branch leaves its returned state's
inference component equal to the post-instantiation one.  The intervening
requirement allocation and occurrence recording affect separate fields. -/
theorem inferExprFuel_success_localIdentifier_noExpected_inference
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {expression : Syntax.Expr}
    {initial allocated : Frontend.SourceInference.State}
    {id : ExpressionId} {name : Syntax.Identifier}
    {binder : TypedBinder}
    {result : InferredExpression × Frontend.SourceInference.State}
    (expressionEq : expression.value = .identifier name)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (lookupEq : allocated.lookupBinder? name.value = some binder)
    (success : Detail.inferExprFuel (fuel + 1) context expression none
      initial = .ok result) :
    result.2.inference = {
      allocated.inference with next :=
        (binder.scheme.instantiateWithSubstitution
          allocated.inference.next).next
    } := by
  have recorded := Detail.inferExprFuel_success_localIdentifier_record
    expressionEq allocationEq lookupEq success
  simp only [Detail.recordExpressionWithExpected, Detail.withExpected,
    bind, Except.bind, Detail.recordExpression] at recorded
  injection recorded with resultEq
  subst result
  let advanced : Frontend.SourceInference.State := {
    allocated with inference := {
      allocated.inference with next :=
        (binder.scheme.instantiateWithSubstitution
          allocated.inference.next).next
    }
  }
  change (advanced.addRequirementsWithIds
      (binder.schemeRequirements.map fun requirement =>
        Detail.applyPredicate advanced
          (TypedTraitResolution.applySubstitution
            (binder.scheme.instantiateWithSubstitution
              allocated.inference.next).substitution
            requirement.predicate))).2.inference = advanced.inference
  exact addRequirementsWithIds_inference _ _

/-- Actual successful local-reference inference satisfies the exact
old-variable barrier used by the subsequent unannotated `let`, provided the
state's substitution range is isolated from unblocked old variables.  Fresh
scheme instantiation discharges the potentially dangerous quantified case;
the explicit range invariant covers later substitutions and both resolves
performed by this branch. -/
theorem inferExprFuel_success_localIdentifier_noExpected_oldVariablesBlocked_on
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {expression : Syntax.Expr}
    {initial allocated : Frontend.SourceInference.State}
    {id : ExpressionId} {name : Syntax.Identifier}
    {binder : TypedBinder}
    {result : InferredExpression × Frontend.SourceInference.State}
    {locals : Environment} {requirementStart : Nat}
    (expressionEq : expression.value = .identifier name)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (lookupEq : allocated.lookupBinder? name.value = some binder)
    (success : Detail.inferExprFuel (fuel + 1) context expression none
      initial = .ok result)
    (startLe : initial.inference.next ≤ allocated.inference.next)
    (quantifiedUnique : binder.scheme.quantified.Nodup)
    (binderFreeInLocals : binder.scheme.freeVariables ⊆ locals.freeVariables)
    (rangeBlockedFirst : InferenceRangeOldVariablesBlockedOn initial result.2
      locals requirementStart
      (binder.scheme.instantiateWithSubstitution allocated.inference.next).body)
    (rangeBlockedSecond : InferenceRangeOldVariablesBlockedOn initial result.2
      locals requirementStart
      (result.2.resolve
        (binder.scheme.instantiateWithSubstitution allocated.inference.next).body)) :
    OldVariablesBlockedAt initial result.2 locals requirementStart
      result.1.type := by
  let instantiated := binder.scheme.instantiateWithSubstitution
    allocated.inference.next
  let advanced : Frontend.SourceInference.State := {
    allocated with inference := {
      allocated.inference with next := instantiated.next
    }
  }
  have typeEq : result.1.type =
      result.2.resolve (advanced.resolve instantiated.body) := by
    simpa only [instantiated, advanced] using
      (inferExprFuel_success_localIdentifier_noExpected_type expressionEq
        allocationEq lookupEq success)
  have inferenceEq : result.2.inference = advanced.inference := by
    simpa only [instantiated, advanced] using
      (inferExprFuel_success_localIdentifier_noExpected_inference expressionEq
        allocationEq lookupEq success)
  have resolveEq : advanced.resolve instantiated.body =
      result.2.resolve instantiated.body := by
    simp only [Frontend.SourceInference.State.resolve, InferState.resolve]
    rw [inferenceEq]
  rw [resolveEq] at typeEq
  have innerBlocked : OldVariablesBlockedAt initial result.2 locals
      requirementStart (result.2.resolve instantiated.body) :=
    oldVariablesBlockedAt_resolvedLocalInstantiation_on binder
      allocated.inference.next startLe quantifiedUnique binderFreeInLocals
      rangeBlockedFirst
  have outerBlocked : OldVariablesBlockedAt initial result.2 locals
      requirementStart
      (result.2.resolve (result.2.resolve instantiated.body)) :=
    oldVariablesBlockedAt_resolve_on rangeBlockedSecond
      (fun metavariable member _ old => innerBlocked metavariable member old)
  rw [typeEq]
  exact outerBlocked

/-- The actual successful branch has a solved final inference substitution.
Its second resolve is therefore idempotent, leaving only the first concrete
instantiated-body range as a provenance premise. -/
theorem inferExprFuel_success_localIdentifier_noExpected_oldVariablesBlocked_on_solved
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {expression : Syntax.Expr}
    {initial allocated : Frontend.SourceInference.State}
    {id : ExpressionId} {name : Syntax.Identifier}
    {binder : TypedBinder}
    {result : InferredExpression × Frontend.SourceInference.State}
    {locals : Environment} {requirementStart : Nat}
    (expressionEq : expression.value = .identifier name)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (lookupEq : allocated.lookupBinder? name.value = some binder)
    (success : Detail.inferExprFuel (fuel + 1) context expression none
      initial = .ok result)
    (startLe : initial.inference.next ≤ allocated.inference.next)
    (quantifiedUnique : binder.scheme.quantified.Nodup)
    (binderFreeInLocals : binder.scheme.freeVariables ⊆ locals.freeVariables)
    (solved : result.2.inference.Solved)
    (rangeBlocked : InferenceRangeOldVariablesBlockedOn initial result.2
      locals requirementStart
      (binder.scheme.instantiateWithSubstitution
        allocated.inference.next).body) :
    OldVariablesBlockedAt initial result.2 locals requirementStart
      result.1.type := by
  apply inferExprFuel_success_localIdentifier_noExpected_oldVariablesBlocked_on
    expressionEq allocationEq lookupEq success startLe quantifiedUnique
    binderFreeInLocals rangeBlocked
  intro candidate member replacement found _ _ _
  have absent : candidate ∉ result.2.inference.substitution.domain := by
    exact solved.apply_variables_outside_domain
      (binder.scheme.instantiateWithSubstitution
        allocated.inference.next).body candidate (by
          simpa [Frontend.SourceInference.State.resolve,
            TypeSystem.InferState.resolve] using member)
  have present : candidate ∈ result.2.inference.substitution.domain := by
    exact List.mem_map.mpr ⟨(candidate, replacement),
      Substitution.lookup?_eq_some_mem found, rfl⟩
  exact False.elim (absent present)

/-- Compatibility wrapper for a whole-range invariant.  The useful actual
branch contract above needs provenance only for two concrete resolve inputs,
not for all entries of the substitution. -/
theorem inferExprFuel_success_localIdentifier_noExpected_oldVariablesBlocked
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {expression : Syntax.Expr}
    {initial allocated : Frontend.SourceInference.State}
    {id : ExpressionId} {name : Syntax.Identifier}
    {binder : TypedBinder}
    {result : InferredExpression × Frontend.SourceInference.State}
    {locals : Environment} {requirementStart : Nat}
    (expressionEq : expression.value = .identifier name)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (lookupEq : allocated.lookupBinder? name.value = some binder)
    (success : Detail.inferExprFuel (fuel + 1) context expression none
      initial = .ok result)
    (startLe : initial.inference.next ≤ allocated.inference.next)
    (quantifiedUnique : binder.scheme.quantified.Nodup)
    (binderFreeInLocals : binder.scheme.freeVariables ⊆ locals.freeVariables)
    (rangeBlocked : InferenceRangeOldVariablesBlockedAt initial result.2
      locals requirementStart) :
    OldVariablesBlockedAt initial result.2 locals requirementStart
      result.1.type := by
  exact inferExprFuel_success_localIdentifier_noExpected_oldVariablesBlocked_on
    expressionEq allocationEq lookupEq success startLe quantifiedUnique
    binderFreeInLocals rangeBlocked.on rangeBlocked.on

/-- A local identifier does not expose any previously active scheme
quantifier in its returned type.  The lexical part follows from fresh scheme
instantiation; each of this branch's two concrete resolves needs only
first-match, source-reachable range avoidance.  No condition is imposed on
dead substitution entries. -/
theorem inferExprFuel_success_localIdentifier_noExpected_avoidsActiveQuantifiers
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {expression : Syntax.Expr}
    {initial allocated : Frontend.SourceInference.State}
    {id : ExpressionId} {name : Syntax.Identifier}
    {binder : TypedBinder}
    {result : InferredExpression × Frontend.SourceInference.State}
    (expressionEq : expression.value = .identifier name)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (lookupEq : allocated.lookupBinder? name.value = some binder)
    (success : Detail.inferExprFuel (fuel + 1) context expression none
      initial = .ok result)
    (bound : ActiveQuantifiersBelowNext initial)
    (startLe : initial.inference.next ≤ allocated.inference.next)
    (quantifiedUnique : binder.scheme.quantified.Nodup)
    (binderFreeOutside : ∀ metavariable,
      metavariable ∈ binder.scheme.freeVariables →
        metavariable ∉ activeSchemeQuantifiers initial)
    (firstRange : result.2.inference.substitution.RangeAvoidsVariablesOn
      (activeSchemeQuantifiers initial)
      (binder.scheme.instantiateWithSubstitution
        allocated.inference.next).body)
    (secondRange : result.2.inference.substitution.RangeAvoidsVariablesOn
      (activeSchemeQuantifiers initial)
      (result.2.resolve
        (binder.scheme.instantiateWithSubstitution
          allocated.inference.next).body)) :
    ∀ metavariable,
      metavariable ∈ result.1.type.freeVariables →
        metavariable ∉ activeSchemeQuantifiers initial := by
  let instantiated := binder.scheme.instantiateWithSubstitution
    allocated.inference.next
  let advanced : Frontend.SourceInference.State := {
    allocated with inference := {
      allocated.inference with next := instantiated.next
    }
  }
  have typeEq : result.1.type =
      result.2.resolve (advanced.resolve instantiated.body) := by
    simpa only [instantiated, advanced] using
      (inferExprFuel_success_localIdentifier_noExpected_type expressionEq
        allocationEq lookupEq success)
  have inferenceEq : result.2.inference = advanced.inference := by
    simpa only [instantiated, advanced] using
      (inferExprFuel_success_localIdentifier_noExpected_inference expressionEq
        allocationEq lookupEq success)
  have resolveEq : advanced.resolve instantiated.body =
      result.2.resolve instantiated.body := by
    simp only [Frontend.SourceInference.State.resolve, InferState.resolve]
    rw [inferenceEq]
  rw [resolveEq] at typeEq
  have sourceOutside : ∀ metavariable,
      metavariable ∈ instantiated.body.freeVariables →
        metavariable ∉ activeSchemeQuantifiers initial := by
    exact instantiateWithSubstitution_avoidsOldQuantifiers binder.scheme
      initial.inference.next allocated.inference.next
      (activeSchemeQuantifiers initial) startLe quantifiedUnique
      (activeSchemeQuantifiers_below_next bound) binderFreeOutside
  have firstOutside : ∀ metavariable,
      metavariable ∈
        (result.2.resolve instantiated.body).freeVariables →
          metavariable ∉ activeSchemeQuantifiers initial := by
    intro metavariable member
    exact rangeAvoidsVariablesOn_apply_variables_outside
      result.2.inference.substitution
      (activeSchemeQuantifiers initial) instantiated.body firstRange
      sourceOutside metavariable (by
        simpa [Frontend.SourceInference.State.resolve,
          TypeSystem.InferState.resolve] using member)
  have secondOutside : ∀ metavariable,
      metavariable ∈
        (result.2.resolve (result.2.resolve instantiated.body)).freeVariables →
          metavariable ∉ activeSchemeQuantifiers initial := by
    intro metavariable member
    exact rangeAvoidsVariablesOn_apply_variables_outside
      result.2.inference.substitution
      (activeSchemeQuantifiers initial)
      (result.2.resolve instantiated.body) secondRange firstOutside
      metavariable (by
        simpa [Frontend.SourceInference.State.resolve,
          TypeSystem.InferState.resolve] using member)
  rw [typeEq]
  exact secondOutside

/-- Solvedness discharges the local-reference branch's second range check:
the first resolved type cannot consult any substitution entry again. -/
theorem inferExprFuel_success_localIdentifier_noExpected_avoidsActiveQuantifiers_solved
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {expression : Syntax.Expr}
    {initial allocated : Frontend.SourceInference.State}
    {id : ExpressionId} {name : Syntax.Identifier}
    {binder : TypedBinder}
    {result : InferredExpression × Frontend.SourceInference.State}
    (expressionEq : expression.value = .identifier name)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (lookupEq : allocated.lookupBinder? name.value = some binder)
    (success : Detail.inferExprFuel (fuel + 1) context expression none
      initial = .ok result)
    (bound : ActiveQuantifiersBelowNext initial)
    (startLe : initial.inference.next ≤ allocated.inference.next)
    (quantifiedUnique : binder.scheme.quantified.Nodup)
    (binderFreeOutside : ∀ metavariable,
      metavariable ∈ binder.scheme.freeVariables →
        metavariable ∉ activeSchemeQuantifiers initial)
    (solved : result.2.inference.Solved)
    (firstRange : result.2.inference.substitution.RangeAvoidsVariablesOn
      (activeSchemeQuantifiers initial)
      (binder.scheme.instantiateWithSubstitution
        allocated.inference.next).body) :
    ∀ metavariable,
      metavariable ∈ result.1.type.freeVariables →
        metavariable ∉ activeSchemeQuantifiers initial := by
  apply inferExprFuel_success_localIdentifier_noExpected_avoidsActiveQuantifiers
    expressionEq allocationEq lookupEq success bound startLe
    quantifiedUnique binderFreeOutside firstRange
  simpa [Frontend.SourceInference.State.resolve,
    TypeSystem.InferState.resolve] using
    (rangeAvoidsVariablesOn_resolved_of_solved solved
      (activeSchemeQuantifiers initial)
      (binder.scheme.instantiateWithSubstitution
        allocated.inference.next).body)

/-- The lexical-isolation invariant supplies the local-reference scheme
premise directly from the actual guarded lookup; occurrence allocation leaves
both the binder stack and inference allocator unchanged. -/
theorem inferExprFuel_success_localIdentifier_noExpected_avoidsActiveQuantifiers_of_isolation
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {expression : Syntax.Expr}
    {initial allocated : Frontend.SourceInference.State}
    {id : ExpressionId} {name : Syntax.Identifier}
    {binder : TypedBinder}
    {result : InferredExpression × Frontend.SourceInference.State}
    (expressionEq : expression.value = .identifier name)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (lookupEq : allocated.lookupBinder? name.value = some binder)
    (success : Detail.inferExprFuel (fuel + 1) context expression none
      initial = .ok result)
    (bound : ActiveQuantifiersBelowNext initial)
    (isolated : ActiveSchemeQuantifierIsolation initial)
    (quantifiedUnique : binder.scheme.quantified.Nodup)
    (solved : result.2.inference.Solved)
    (firstRange : result.2.inference.substitution.RangeAvoidsVariablesOn
      (activeSchemeQuantifiers initial)
      (binder.scheme.instantiateWithSubstitution
        allocated.inference.next).body) :
    ∀ metavariable,
      metavariable ∈ result.1.type.freeVariables →
        metavariable ∉ activeSchemeQuantifiers initial := by
  have allocatedIsolated : ActiveSchemeQuantifierIsolation allocated :=
    activeSchemeQuantifierIsolation_allocateExpressionId isolated allocationEq
  have bindersEq : allocated.localBinders = initial.localBinders := by
    have projection := congrArg
      (fun pair : ExpressionId × Frontend.SourceInference.State =>
        pair.2.localBinders) allocationEq
    change initial.localBinders = allocated.localBinders at projection
    exact projection.symm
  have binderFreeOutside : ∀ metavariable,
      metavariable ∈ binder.scheme.freeVariables →
        metavariable ∉ activeSchemeQuantifiers initial := by
    intro metavariable free
    have outside := activeSchemeQuantifierIsolation_lookupBinder
      allocatedIsolated lookupEq metavariable free
    simpa [activeSchemeQuantifiers, bindersEq] using outside
  have startLe : initial.inference.next ≤ allocated.inference.next := by
    rw [allocateExpressionId_inferenceNext_eq allocationEq]
    exact Nat.le_refl _
  exact inferExprFuel_success_localIdentifier_noExpected_avoidsActiveQuantifiers_solved
    expressionEq allocationEq lookupEq success bound startLe
    quantifiedUnique binderFreeOutside solved firstRange

/-- The common no-expected recording tail leaves the inference solution
unchanged and resolves the raw result type exactly once.  This is the small
bridge needed to lift old-quantifier isolation through grouping and other
composite expression constructors. -/
theorem recordExpressionWithExpected_none_typeAndInference
    {context : Frontend.SourceInference.Context}
    {expression : Syntax.Expr} {id : ExpressionId} {type : Ty}
    {form : ExpressionForm} {requirements : List RequirementId}
    {state : Frontend.SourceInference.State}
    {localSchemeInstantiationStart : Option Nat}
    {result : InferredExpression × Frontend.SourceInference.State}
    (success : Detail.recordExpressionWithExpected context expression id type
      form requirements none state
      (localSchemeInstantiationStart := localSchemeInstantiationStart) =
        .ok result) :
    result.1.type = state.resolve type ∧
      result.2.inference = state.inference := by
  simp only [Detail.recordExpressionWithExpected, Detail.withExpected,
    bind, Except.bind, Detail.recordExpression] at success
  injection success with resultEq
  subst result
  exact ⟨rfl, rfl⟩

/-- One actual group-expression parent preserves old-quantifier isolation
from its *actual* recursive child.  The callback is required only for the
child returned by the successful group trace; this is not a hypothesis over
arbitrary expressions. -/
theorem inferExprFuel_success_group_noExpected_avoidsActiveQuantifiers
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {expression inner : Syntax.Expr}
    {initial allocated : Frontend.SourceInference.State}
    {id : ExpressionId}
    {result : InferredExpression × Frontend.SourceInference.State}
    (expressionEq : expression.value = .group inner)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (success : Detail.inferExprFuel (fuel + 1) context expression none
      initial = .ok result)
    (childIsolation : ∀ childResult childState,
      Detail.inferExprFuel fuel context inner none allocated =
        .ok (childResult, childState) →
      childState.inference.substitution.RangeAvoidsVariablesOn
        (activeSchemeQuantifiers initial) childResult.type ∧
      (∀ metavariable,
        metavariable ∈ childResult.type.freeVariables →
          metavariable ∉ activeSchemeQuantifiers initial)) :
    ∀ metavariable,
      metavariable ∈ result.1.type.freeVariables →
        metavariable ∉ activeSchemeQuantifiers initial := by
  obtain ⟨innerResult, innerState, innerSuccess, recorded⟩ :=
    Detail.inferExprFuel_success_group_facts expressionEq allocationEq
      success
  obtain ⟨rangeAvoids, innerAvoids⟩ :=
    childIsolation innerResult innerState innerSuccess
  obtain ⟨typeEq, _⟩ :=
    recordExpressionWithExpected_none_typeAndInference recorded
  intro metavariable member
  rw [typeEq] at member
  exact rangeAvoidsVariablesOn_apply_variables_outside
    innerState.inference.substitution
    (activeSchemeQuantifiers initial) innerResult.type rangeAvoids
    innerAvoids metavariable (by
      simpa [Frontend.SourceInference.State.resolve,
        TypeSystem.InferState.resolve] using member)

/-- Product assembly introduces no flexible variable beyond those already
present in one of its source-ordered element types. -/
theorem productMany_avoidsVariables
    (types : List Ty) (guarded : List TypeVarId)
    (eachAvoids : ∀ type ∈ types, ∀ metavariable,
      metavariable ∈ type.freeVariables → metavariable ∉ guarded) :
    ∀ metavariable,
      metavariable ∈ (Ty.productMany types).freeVariables →
        metavariable ∉ guarded := by
  induction types with
  | nil =>
      intro metavariable member
      simp [Ty.productMany, Ty.unit, Ty.freeVariables] at member
  | cons head tail induction =>
      cases tail with
      | nil =>
          simpa [Ty.productMany] using eachAvoids head (by simp)
      | cons next rest =>
          intro metavariable member
          change metavariable ∈
            (Ty.product head (Ty.productMany (next :: rest))).freeVariables at member
          rw [Ty.mem_freeVariables_product_iff] at member
          rcases member with headMember | tailMember
          · exact eachAvoids head (by simp) metavariable headMember
          · exact induction (by
              intro type typeMember metavariable occurs
              exact eachAvoids type (by simp [typeMember]) metavariable
                occurs) metavariable tailMember

/-- Relevance-restricted replacement avoidance composes over the types
actually used to assemble a tuple product. -/
theorem productMany_rangeAvoidsVariablesOn
    (substitution : Substitution) (guarded : List TypeVarId)
    (types : List Ty)
    (eachAvoids : ∀ type ∈ types,
      substitution.RangeAvoidsVariablesOn guarded type) :
    substitution.RangeAvoidsVariablesOn guarded
      (Ty.productMany types) := by
  induction types with
  | nil =>
      intro candidate member
      simp [Ty.productMany, Ty.unit, Ty.freeVariables] at member
  | cons head tail induction =>
      cases tail with
      | nil =>
          simpa [Ty.productMany] using eachAvoids head (by simp)
      | cons next rest =>
          intro candidate member replacement found protectedVariable captured
          change candidate ∈
            (Ty.product head (Ty.productMany (next :: rest))).freeVariables at member
          rw [Ty.mem_freeVariables_product_iff] at member
          rcases member with headMember | tailMember
          · exact eachAvoids head (by simp) candidate headMember
              replacement found protectedVariable captured
          · exact induction (by
              intro type typeMember
              exact eachAvoids type (by simp [typeMember])) candidate
                tailMember replacement found protectedVariable captured

/-- A concrete tuple-expression parent preserves old-quantifier isolation
from the actual source-ordered element traversal.  Its product type is formed
only from inferred element types, then resolved by the same isolated state. -/
theorem inferExprFuel_success_tuple_noExpected_avoidsActiveQuantifiers
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {expression : Syntax.Expr}
    {elements : Syntax.DelimitedList Syntax.Expr}
    {initial allocated : Frontend.SourceInference.State}
    {id : ExpressionId}
    {result : InferredExpression × Frontend.SourceInference.State}
    (expressionEq : expression.value = .tuple elements)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (success : Detail.inferExprFuel (fuel + 1) context expression none
      initial = .ok result)
    (childrenIsolation : ∀ inferredElements elementsState,
      Detail.inferExprsFuel fuel context elements.elements allocated =
        .ok (inferredElements, elementsState) →
      (∀ inferred, inferred ∈ inferredElements →
        elementsState.inference.substitution.RangeAvoidsVariablesOn
          (activeSchemeQuantifiers initial) inferred.type) ∧
      (∀ inferred, inferred ∈ inferredElements →
        ∀ metavariable, metavariable ∈ inferred.type.freeVariables →
          metavariable ∉ activeSchemeQuantifiers initial)) :
    ∀ metavariable,
      metavariable ∈ result.1.type.freeVariables →
        metavariable ∉ activeSchemeQuantifiers initial := by
  obtain ⟨inferredElements, elementsState, elementsSuccess, recorded⟩ :=
    Detail.inferExprFuel_success_tuple_facts expressionEq allocationEq
      success
  obtain ⟨elementsRangeAvoid, elementsAvoid⟩ :=
    childrenIsolation inferredElements elementsState elementsSuccess
  obtain ⟨typeEq, _⟩ :=
    recordExpressionWithExpected_none_typeAndInference recorded
  intro metavariable member
  rw [typeEq] at member
  have productAvoids : ∀ candidate,
      candidate ∈ (Ty.productMany (inferredElements.map (·.type))
        ).freeVariables →
        candidate ∉ activeSchemeQuantifiers initial := by
    apply productMany_avoidsVariables
    intro type typeMember candidate occurs
    rcases List.mem_map.mp typeMember with
      ⟨inferred, inferredMember, rfl⟩
    exact elementsAvoid inferred inferredMember candidate occurs
  have productRangeAvoids :
      elementsState.inference.substitution.RangeAvoidsVariablesOn
        (activeSchemeQuantifiers initial)
        (Ty.productMany (inferredElements.map (·.type))) := by
    apply productMany_rangeAvoidsVariablesOn
    intro type typeMember
    rcases List.mem_map.mp typeMember with
      ⟨inferred, inferredMember, rfl⟩
    exact elementsRangeAvoid inferred inferredMember
  exact rangeAvoidsVariablesOn_apply_variables_outside
    elementsState.inference.substitution
    (activeSchemeQuantifiers initial)
    (Ty.productMany (inferredElements.map (·.type))) productRangeAvoids
    productAvoids metavariable (by
      simpa [Frontend.SourceInference.State.resolve,
        TypeSystem.InferState.resolve] using member)

/-- If the actual initializer value contains no older active scheme
quantifier, freshness against every corresponding semantic lexical binder is
immediate from executable/semantic local alignment. -/
theorem priorQuantifiersBlockedAt_of_activeQuantifiersAvoided
    {initial state : Frontend.SourceInference.State}
    {locals : Environment} {requirementStart : Nat} {valueType : Ty}
    {target : SourceSemantics.Context} {outer : Substitution}
    (aligned : LocalEnvironmentAligned initial outer target)
    (avoids : ∀ metavariable,
      metavariable ∈ valueType.freeVariables →
        metavariable ∉ activeSchemeQuantifiers initial) :
    PriorQuantifiersBlockedAt state locals requirementStart valueType
      target := by
  intro metavariable valueMember entry entryMember priorQuantified
  have rawMember : entry ∈ closedBinderLocals outer initial.localBinders :=
    aligned.locals_perm.mem_iff.mpr entryMember
  rcases List.mem_map.mp rawMember with ⟨binder, binderMember, rfl⟩
  have rawQuantified : metavariable ∈ binder.scheme.quantified := by
    simpa [closedBinderLocals, TypedBinder.applySubstitution,
      Scheme.apply] using priorQuantified
  have activeQuantified : metavariable ∈
      activeSchemeQuantifiers initial :=
    List.mem_flatMap.mpr ⟨binder, binderMember, rawQuantified⟩
  exact False.elim (avoids metavariable valueMember activeQuantified)

/-- An alternative source of the same premise is old-variable provenance:
every old variable in the initializer value is blocked by executable
generalization. -/
theorem priorQuantifiersBlockedAt_of_oldVariablesBlocked
    {initial state : Frontend.SourceInference.State}
    {locals : Environment} {requirementStart : Nat} {valueType : Ty}
    {target : SourceSemantics.Context} {outer : Substitution}
    (aligned : LocalEnvironmentAligned initial outer target)
    (bound : ActiveQuantifiersBelowNext initial)
    (oldBlocked : OldVariablesBlockedAt initial state locals
      requirementStart valueType) :
    PriorQuantifiersBlockedAt state locals requirementStart valueType
      target := by
  intro metavariable valueMember entry entryMember oldQuantified
  have rawMember : entry ∈ closedBinderLocals outer initial.localBinders :=
    aligned.locals_perm.mem_iff.mpr entryMember
  rcases List.mem_map.mp rawMember with ⟨binder, binderMember, rfl⟩
  have rawQuantified : metavariable ∈ binder.scheme.quantified := by
    simpa [closedBinderLocals, TypedBinder.applySubstitution,
      Scheme.apply] using oldQuantified
  exact oldBlocked metavariable valueMember
    (bound binder binderMember metavariable rawQuantified)

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

/-- The exact ordered frontier that must be stable across final substitution
for executable generalization to agree with the final semantic barrier.  It
allows substitutions with residual flexible variables: such variables are
acceptable only when their appearances leave this frontier unchanged.  The
checker finalizer validates formation and capture avoidance, but does not by
itself prove this cross-time barrier equality. -/
def GeneralizationBarrierTransport
    (state : Frontend.SourceInference.State)
    (locals : Environment) (requirementStart : Nat) (valueType : Ty)
    (outer : Substitution) (target : SourceSemantics.Context)
    (exemptRequirements : List RequirementId) : Prop :=
  (outer.apply valueType).freeVariables.filter (fun metavariable =>
      !(GeneralizationBlockedVariablesExcept target exemptRequirements
        ).contains metavariable) =
    valueType.freeVariables.filter (fun metavariable =>
      !(Detail.generalizeValueBlockedVariables state locals
        requirementStart).contains metavariable)

/-- If finalization does not rewrite the initializer value, the exact
transport obligation reduces to agreement of the two barriers on variables
actually occurring in that value.  This is a useful branch-specific case,
not a claim about arbitrary final substitutions. -/
theorem generalizationBarrierTransport_of_typeFixed
    {state : Frontend.SourceInference.State}
    {locals : Environment} {requirementStart : Nat} {valueType : Ty}
    {outer : Substitution} {target : SourceSemantics.Context}
    {exemptRequirements : List RequirementId}
    (typeFixed : outer.apply valueType = valueType)
    (barrierAgreement : ∀ metavariable,
      metavariable ∈ valueType.freeVariables →
        (metavariable ∈
          GeneralizationBlockedVariablesExcept target exemptRequirements ↔
         metavariable ∈
          Detail.generalizeValueBlockedVariables state locals
            requirementStart)) :
    GeneralizationBarrierTransport state locals requirementStart valueType
      outer target exemptRequirements := by
  unfold GeneralizationBarrierTransport
  rw [typeFixed]
  apply List.filter_congr
  intro metavariable member
  by_cases finalBlocked : metavariable ∈
      GeneralizationBlockedVariablesExcept target exemptRequirements
  · have rawBlocked := (barrierAgreement metavariable member).mp finalBlocked
    simp [finalBlocked, rawBlocked]
  · have rawUnblocked : metavariable ∉
        Detail.generalizeValueBlockedVariables state locals
          requirementStart := by
      intro rawBlocked
      exact finalBlocked ((barrierAgreement metavariable member).mpr
        rawBlocked)
    simp [finalBlocked, rawUnblocked]

/-- With finalizer-validated non-capture, residual-aware barrier transport is
exactly the missing condition for the final scheme's declarative
generalization judgment.  Neither direction assumes a ground substitution. -/
theorem generalizeValue_finalGeneralizes_iff_barrierTransport
    {state : Frontend.SourceInference.State}
    {locals : Environment} {requirementStart : Nat} {valueType : Ty}
    {binder : TypedBinder} {outer : Substitution}
    {target : SourceSemantics.Context}
    {exemptRequirements : List RequirementId}
    (schemeEq : binder.scheme =
      (Detail.generalizeValue state locals requirementStart valueType).scheme)
    (noCapture : Detail.LocalBinderInstantiationNoCapture outer binder) :
    SchemeGeneralizesExcept target exemptRequirements
        (binder.applySubstitution outer).scheme ↔
      GeneralizationBarrierTransport state locals requirementStart valueType
        outer target exemptRequirements := by
  have restrictedEq : outer.without binder.scheme.quantified = outer :=
    FlexibleSubstitution.Substitution.without_eq_self_of_disjoint_domain outer
      binder.scheme.quantified noCapture.quantified_fresh
  unfold SchemeGeneralizesExcept GeneralizationBarrierTransport
  simp only [TypedBinder.applySubstitution, Scheme.apply]
  simp only [restrictedEq]
  simp only [schemeEq, Detail.generalizeValue_scheme_quantified,
    Detail.generalizeValue_scheme_body]
  exact eq_comm

/-- The finalizer's actual capture check and scoped ledger establish binder
formation directly in a residual-variable semantic context.  Unlike
`generalizeValue_binderFormation_afterSubstitution`, no total context closure
or pre-finalization predicate formation is needed: only formation of the
retained final predicate is required. -/
theorem generalizeValue_binderFormation_finalAdmissible
    {inferenceContext : Frontend.SourceInference.Context}
    {finalType : Ty}
    {evidenceState : Frontend.SourceInference.State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources inferenceContext finalType
      evidenceState roots finalized)
    {source : TypedSource} {target : SourceSemantics.Context}
    {binder : TypedBinder} {initializer : ExpressionId}
    {statementId : StatementId} {span : Syntax.SourceSpan}
    {statementType : Ty}
    (recorded : ContainsStatement source statementId {
      id := statementId, span := span, type := statementType,
      form := .letDecl binder (some initializer) })
    (rawExtension : TypingSourceExtends source
      (evidenceState.toTypedSource roots))
    (signaturesEq : target.signatures =
      (finalizedRequirementContext inferenceContext finalized).signatures)
    (assumptionsMono :
      (finalizedRequirementContext inferenceContext finalized).assumptions ⊆
        target.assumptions)
    (solvedEq : target.solvedRequirements =
      (finalizedRequirementContext inferenceContext finalized
        ).solvedRequirements)
    {state : Frontend.SourceInference.State}
    {locals : Environment} {requirementStart : Nat} {valueType : Ty}
    (schemeEq : binder.scheme =
      (Detail.generalizeValue state locals requirementStart valueType).scheme)
    (requirementsEq : binder.schemeRequirements =
      (Detail.generalizeValue state locals requirementStart valueType
        ).requirements)
    (predicates : ∀ requirement,
      requirement ∈ (binder.applySubstitution finalized.substitution
        ).schemeRequirements →
        PredicateAdmissible
          (localSchemeInitializerContext target
            (binder.applySubstitution finalized.substitution))
          requirement.predicate)
    (bodyAdmissible : TypeAdmissible
      (localSchemeInitializerContext target
        (binder.applySubstitution finalized.substitution))
      (binder.applySubstitution finalized.substitution).scheme.body) :
    SchemeWellFormed target
        (binder.applySubstitution finalized.substitution).scheme ∧
      LocalSchemeRequirementsWellFormed target
        (binder.applySubstitution finalized.substitution) := by
  have noCapture := localBinderInstantiationNoCapture_of_retainedLet
    resources recorded rawExtension
  have ledgerFinal := scopedRequirementLedgerWellFormed_weakenAssumptions
    signaturesEq assumptionsMono solvedEq resources.ledger
  have ledgerRaw : ScopedRequirementLedgerWellFormed target
      ((evidenceState.toTypedSource roots).applySubstitution
        finalized.substitution) := by
    rw [← resources.source_eq]
    exact ledgerFinal
  have rawQuantifiedNodup : binder.scheme.quantified.Nodup := by
    rw [schemeEq]
    exact Detail.generalizeValue_scheme_quantified_nodup state locals
      requirementStart valueType
  have finalQuantifiedNodup :
      (binder.applySubstitution finalized.substitution).scheme.quantified.Nodup := by
    simpa using rawQuantifiedNodup
  constructor
  · exact StructuralSubstitution.SchemeWellFormed.ofLocalSchemeInitializerAdmissible
      bodyAdmissible finalQuantifiedNodup
  · apply ledgerRaw.localSchemeRequirementsWellFormed
      (initializer := .expression initializer)
    · intro requirement member
      rw [FlexibleSubstitution.applyTypedBinder_schemeRequirements] at member
      rcases List.mem_map.mp member with ⟨original, originalMember, rfl⟩
      exact FlexibleSubstitution.ContainsLocalSchemeTemplate.applySubstitution
        finalized.substitution
        (containsLocalSchemeTemplate_of_retainedLet recorded rawExtension
          originalMember)
    · exact predicates
    · intro requirement member
      rw [FlexibleSubstitution.applyTypedBinder_schemeRequirements] at member
      rcases List.mem_map.mp member with ⟨original, originalMember, rfl⟩
      rw [requirementsEq] at originalMember
      rcases Detail.generalizeValue_requirement_depends_on_quantified state
          locals requirementStart valueType original originalMember with
        ⟨metavariable, quantified, occurs⟩
      refine ⟨metavariable, ?_, ?_⟩
      · simpa [schemeEq] using quantified
      · have restrictedEq : finalized.substitution.without
            binder.scheme.quantified = finalized.substitution :=
          FlexibleSubstitution.Substitution.without_eq_self_of_disjoint_domain
            finalized.substitution binder.scheme.quantified
            noCapture.quantified_fresh
        simpa [LocalSchemeRequirement.applySubstitution, restrictedEq] using
          (FlexibleSubstitution.Substitution.mem_predicateVariables_applySubstitution_of_not_mem_domain
            finalized.substitution
            (noCapture.quantified_fresh metavariable
              (by simpa [schemeEq] using quantified)) occurs)

/-- The formation argument only needs the binder and its qualified template
sites to be present in the finalizer's raw source.  A `for`-header let is
retained by its enclosing loop statement, not by a standalone let statement.
The caller must derive these two exact ownership facts from that parent node;
finalization alone does not invent an owner for an arbitrary binder. -/
theorem generalizeValue_binderFormation_finalAdmissible_of_retained
    {inferenceContext : Frontend.SourceInference.Context}
    {finalType : Ty}
    {evidenceState : Frontend.SourceInference.State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources inferenceContext finalType
      evidenceState roots finalized)
    {target : SourceSemantics.Context}
    {binder : TypedBinder} {initializer : ExpressionId}
    (binderRetained : binder ∈
      (evidenceState.toTypedSource roots).initializedLetBinders)
    (templatesRetained : ∀ requirement,
      requirement ∈ binder.schemeRequirements →
        ContainsLocalSchemeTemplate (evidenceState.toTypedSource roots) {
          binder, initializer := .expression initializer, requirement })
    (signaturesEq : target.signatures =
      (finalizedRequirementContext inferenceContext finalized).signatures)
    (assumptionsMono :
      (finalizedRequirementContext inferenceContext finalized).assumptions ⊆
        target.assumptions)
    (solvedEq : target.solvedRequirements =
      (finalizedRequirementContext inferenceContext finalized
        ).solvedRequirements)
    {state : Frontend.SourceInference.State}
    {locals : Environment} {requirementStart : Nat} {valueType : Ty}
    (schemeEq : binder.scheme =
      (Detail.generalizeValue state locals requirementStart valueType).scheme)
    (requirementsEq : binder.schemeRequirements =
      (Detail.generalizeValue state locals requirementStart valueType
        ).requirements)
    (predicates : ∀ requirement,
      requirement ∈ (binder.applySubstitution finalized.substitution
        ).schemeRequirements →
        PredicateAdmissible
          (localSchemeInitializerContext target
            (binder.applySubstitution finalized.substitution))
          requirement.predicate)
    (bodyAdmissible : TypeAdmissible
      (localSchemeInitializerContext target
        (binder.applySubstitution finalized.substitution))
      (binder.applySubstitution finalized.substitution).scheme.body) :
    SchemeWellFormed target
        (binder.applySubstitution finalized.substitution).scheme ∧
      LocalSchemeRequirementsWellFormed target
        (binder.applySubstitution finalized.substitution) := by
  have noCapture := resources.local_no_capture binder binderRetained
  have ledgerFinal := scopedRequirementLedgerWellFormed_weakenAssumptions
    signaturesEq assumptionsMono solvedEq resources.ledger
  have ledgerRaw : ScopedRequirementLedgerWellFormed target
      ((evidenceState.toTypedSource roots).applySubstitution
        finalized.substitution) := by
    rw [← resources.source_eq]
    exact ledgerFinal
  have rawQuantifiedNodup : binder.scheme.quantified.Nodup := by
    rw [schemeEq]
    exact Detail.generalizeValue_scheme_quantified_nodup state locals
      requirementStart valueType
  have finalQuantifiedNodup :
      (binder.applySubstitution finalized.substitution).scheme.quantified.Nodup := by
    simpa using rawQuantifiedNodup
  constructor
  · exact StructuralSubstitution.SchemeWellFormed.ofLocalSchemeInitializerAdmissible
      bodyAdmissible finalQuantifiedNodup
  · apply ledgerRaw.localSchemeRequirementsWellFormed
      (initializer := .expression initializer)
    · intro requirement member
      rw [FlexibleSubstitution.applyTypedBinder_schemeRequirements] at member
      rcases List.mem_map.mp member with ⟨original, originalMember, rfl⟩
      exact FlexibleSubstitution.ContainsLocalSchemeTemplate.applySubstitution
        finalized.substitution
        (templatesRetained original originalMember)
    · exact predicates
    · intro requirement member
      rw [FlexibleSubstitution.applyTypedBinder_schemeRequirements] at member
      rcases List.mem_map.mp member with ⟨original, originalMember, rfl⟩
      rw [requirementsEq] at originalMember
      rcases Detail.generalizeValue_requirement_depends_on_quantified state
          locals requirementStart valueType original originalMember with
        ⟨metavariable, quantified, occurs⟩
      refine ⟨metavariable, ?_, ?_⟩
      · simpa [schemeEq] using quantified
      · have restrictedEq : finalized.substitution.without
            binder.scheme.quantified = finalized.substitution :=
          FlexibleSubstitution.Substitution.without_eq_self_of_disjoint_domain
            finalized.substitution binder.scheme.quantified
            noCapture.quantified_fresh
        simpa [LocalSchemeRequirement.applySubstitution, restrictedEq] using
          (FlexibleSubstitution.Substitution.mem_predicateVariables_applySubstitution_of_not_mem_domain
            finalized.substitution
            (noCapture.quantified_fresh metavariable
              (by simpa [schemeEq] using quantified)) occurs)

/-- Inductive provenance contract for qualified predicate formation.  It is
indexed by *actual generated ledger rows* selected as templates by this
binder, rather than by arbitrary predicates or by the solver's entailment
evidence.  The recursive requirement-generating branches must establish this
formation at the final initializer context; finalization's template-scope
validator checks identity/ownership but not predicate type formation. -/
def RetainedRequirementPredicateFormationAt
    (state : Frontend.SourceInference.State) (binder : TypedBinder)
    (outer : Substitution) (target : SourceSemantics.Context) : Prop :=
  ∀ rawRequirement, rawRequirement ∈ state.requirements →
    rawRequirement.id ∈ localSchemeTemplateIds binder →
      PredicateAdmissible
        (localSchemeInitializerContext target
          (binder.applySubstitution outer))
        (TypedTraitResolution.applySubstitution
          (outer.without binder.scheme.quantified)
          (Detail.applyPredicate state rawRequirement.predicate))

/-- Exact `generalizeValue` source provenance turns formation of selected
generated rows into formation of every finalized qualified requirement
carried by the binder.  No entailment-to-formation inference is used. -/
theorem generalizeValue_finalPredicates_of_requirementGeneration
    {state : Frontend.SourceInference.State}
    {locals : Environment} {requirementStart : Nat} {valueType : Ty}
    {binder : TypedBinder} {outer : Substitution}
    {target : SourceSemantics.Context}
    (requirementsEq : binder.schemeRequirements =
      (Detail.generalizeValue state locals requirementStart valueType
        ).requirements)
    (generated : RetainedRequirementPredicateFormationAt state binder outer
      target) :
    ∀ requirement,
      requirement ∈ (binder.applySubstitution outer).schemeRequirements →
        PredicateAdmissible
          (localSchemeInitializerContext target
            (binder.applySubstitution outer)) requirement.predicate := by
  intro requirement member
  rw [FlexibleSubstitution.applyTypedBinder_schemeRequirements] at member
  rcases List.mem_map.mp member with ⟨original, originalMember, rfl⟩
  have generalizedMember : original ∈
      (Detail.generalizeValue state locals requirementStart valueType
        ).requirements := by
    simpa [requirementsEq] using originalMember
  obtain ⟨rawRequirement, rawMember, idEq, predicateEq⟩ :=
    Detail.generalizeValue_requirement_source state locals requirementStart
      valueType original generalizedMember
  have selectedId : rawRequirement.id ∈ localSchemeTemplateIds binder := by
    unfold localSchemeTemplateIds
    exact List.mem_map.mpr ⟨original, originalMember, idEq.symm⟩
  simpa [LocalSchemeRequirement.applySubstitution, predicateEq] using
    generated rawRequirement rawMember selectedId

/-- Residual-aware certificate assembly for an actual initialized `let`.
Finalization itself supplies capture avoidance and the scoped ledger.  The two
remaining semantic interfaces are ordered barrier transport and admissibility
of each final qualified predicate.  This avoids assuming a ground
`ContextCloses` relation, which a checker permitting residual flexible
variables need not satisfy. -/
theorem unannotatedInitializedLetCertificate_of_finalBarrier
    {inferenceContext : Frontend.SourceInference.Context}
    {finalType : Ty}
    {evidenceState : Frontend.SourceInference.State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources inferenceContext finalType
      evidenceState roots finalized)
    {source : TypedSource} {target : SourceSemantics.Context}
    {outer : Substitution}
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
      id := statementId, span := span, type := statementType,
      form := .letDecl binder (some initializer) })
    (rawExtension : TypingSourceExtends source
      (evidenceState.toTypedSource roots))
    (barrierTransport : GeneralizationBarrierTransport state locals
      requirementStart valueType outer target
      (localSchemeTemplateIds (binder.applySubstitution outer)))
    (finalPredicates : ∀ requirement,
      requirement ∈ (binder.applySubstitution outer).schemeRequirements →
        PredicateAdmissible
          (localSchemeInitializerContext target
            (binder.applySubstitution outer)) requirement.predicate)
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
  have rawSchemeEq : binder.scheme =
      (Detail.generalizeValue state locals requirementStart
        valueType).scheme := by
    rw [← binderEq, generalizedEq]
    rfl
  have rawRequirementsEq : binder.schemeRequirements =
      (Detail.generalizeValue state locals requirementStart
        valueType).requirements := by
    rw [← binderEq, generalizedEq]
    rfl
  have noCapture := localBinderInstantiationNoCapture_of_retainedLet
    resources recorded rawExtension
  have finalGeneralizes : SchemeGeneralizesExcept target
      (localSchemeTemplateIds (binder.applySubstitution outer))
      (binder.applySubstitution outer).scheme :=
    (generalizeValue_finalGeneralizes_iff_barrierTransport rawSchemeEq
      (outerEq ▸ noCapture)).mpr barrierTransport
  have formation := generalizeValue_binderFormation_finalAdmissible
    resources recorded rawExtension signaturesEq assumptionsMono solvedEq
    rawSchemeEq rawRequirementsEq
    (by simpa [outerEq] using finalPredicates)
    (by simpa [outerEq] using initializerType.type_admissible)
  refine {
    initializer_type := initializerType
    requirements_well_formed := ?_
    generalizes := finalGeneralizes
    quantified_fresh := ?_
  }
  · simpa [outerEq] using formation.2
  · intro metavariable quantified
    exact ⟨FlexibleSubstitution.SchemeGeneralizesExcept.quantified_fresh
        finalGeneralizes metavariable quantified,
      generalizeValue_quantified_fresh_prior_of_blocked
        (outer := outer) rawSchemeEq priorBlocked metavariable quantified⟩

/-- The same residual-aware certificate for a binder retained through an
enclosing node, notably a `for`-header item.  Exact raw ownership is an
explicit premise: the finalizer checks only binders and templates actually
present in its input source.  The barrier, generated-predicate formation,
and prior-quantifier provenance still require their separate inductive
arguments. -/
theorem unannotatedInitializedLetCertificate_of_finalBarrier_retained
    {inferenceContext : Frontend.SourceInference.Context}
    {finalType : Ty}
    {evidenceState : Frontend.SourceInference.State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources inferenceContext finalType
      evidenceState roots finalized)
    {source : TypedSource} {target : SourceSemantics.Context}
    {outer : Substitution}
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
    (signaturesEq : target.signatures =
      (finalizedRequirementContext inferenceContext finalized).signatures)
    (assumptionsMono :
      (finalizedRequirementContext inferenceContext finalized).assumptions ⊆
        target.assumptions)
    (solvedEq : target.solvedRequirements =
      (finalizedRequirementContext inferenceContext finalized
        ).solvedRequirements)
    (binderRetained : binder ∈
      (evidenceState.toTypedSource roots).initializedLetBinders)
    (templatesRetained : ∀ requirement,
      requirement ∈ binder.schemeRequirements →
        ContainsLocalSchemeTemplate (evidenceState.toTypedSource roots) {
          binder, initializer := .expression initializer, requirement })
    (barrierTransport : GeneralizationBarrierTransport state locals
      requirementStart valueType outer target
      (localSchemeTemplateIds (binder.applySubstitution outer)))
    (finalPredicates : ∀ requirement,
      requirement ∈ (binder.applySubstitution outer).schemeRequirements →
        PredicateAdmissible
          (localSchemeInitializerContext target
            (binder.applySubstitution outer)) requirement.predicate)
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
  have rawSchemeEq : binder.scheme =
      (Detail.generalizeValue state locals requirementStart
        valueType).scheme := by
    rw [← binderEq, generalizedEq]
    rfl
  have rawRequirementsEq : binder.schemeRequirements =
      (Detail.generalizeValue state locals requirementStart
        valueType).requirements := by
    rw [← binderEq, generalizedEq]
    rfl
  have noCapture := resources.local_no_capture binder binderRetained
  have finalGeneralizes : SchemeGeneralizesExcept target
      (localSchemeTemplateIds (binder.applySubstitution outer))
      (binder.applySubstitution outer).scheme :=
    (generalizeValue_finalGeneralizes_iff_barrierTransport rawSchemeEq
      (outerEq ▸ noCapture)).mpr barrierTransport
  have formation := generalizeValue_binderFormation_finalAdmissible_of_retained
    resources binderRetained templatesRetained signaturesEq assumptionsMono
    solvedEq rawSchemeEq rawRequirementsEq
    (by simpa [outerEq] using finalPredicates)
    (by simpa [outerEq] using initializerType.type_admissible)
  refine {
    initializer_type := initializerType
    requirements_well_formed := ?_
    generalizes := finalGeneralizes
    quantified_fresh := ?_
  }
  · simpa [outerEq] using formation.2
  · intro metavariable quantified
    exact ⟨FlexibleSubstitution.SchemeGeneralizesExcept.quantified_fresh
        finalGeneralizes metavariable quantified,
      generalizeValue_quantified_fresh_prior_of_blocked
        (outer := outer) rawSchemeEq priorBlocked metavariable quantified⟩

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
