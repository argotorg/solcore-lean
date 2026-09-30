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

/-- The entire active binder stack, including shadowed entries, contributes
protected scheme quantifiers.  A synthetic substitution is used only to put
this list in the domain expected by the generic unifier-avoidance theorem;
its dummy range is never applied. -/
def activeSchemeQuantifiers
    (state : Frontend.SourceInference.State) : List TypeVarId :=
  state.localBinders.flatMap fun binder => binder.scheme.quantified

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
  change ∀ metavariable,
    metavariable ∈
      (state.inference.substitution.apply type).freeVariables →
      metavariable.index < initial.inference.next →
        metavariable ∈ Detail.generalizeValueBlockedVariables state locals
          requirementStart
  exact oldVariablesProtected_applySubstitution
    state.inference.substitution type initial.inference.next
    (Detail.generalizeValueBlockedVariables state locals requirementStart)
    rangeBlocked sourceBlocked

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
  apply oldVariablesBlockedAt_resolve rangeBlocked
  intro metavariable member _ old
  have schemeFree :=
    instantiateWithSubstitution_oldVariables_in_schemeFreeVariables
      binder.scheme initial.inference.next instantiationStart startLe
      quantifiedUnique metavariable member old
  exact List.mem_append.mpr (Or.inl (binderFreeInLocals schemeFree))

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
    oldVariablesBlockedAt_resolvedLocalInstantiation binder
      allocated.inference.next startLe quantifiedUnique binderFreeInLocals
      rangeBlocked
  have outerBlocked : OldVariablesBlockedAt initial result.2 locals
      requirementStart
      (result.2.resolve (result.2.resolve instantiated.body)) :=
    oldVariablesBlockedAt_resolve rangeBlocked
      (fun metavariable member _ old => innerBlocked metavariable member old)
  rw [typeEq]
  exact outerBlocked

/-- The state bound, executable/semantic local alignment, and the actual
initializer's old-variable barrier imply precisely the prior-quantifier
condition consumed by `generalizeValue`. -/
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
