import Solcore.Frontend.SourceInference.LocalReadOriginsInference

/-! Local-read requirements must reach the actual initializer return state
before they can constrain its enclosing generalization. These receipts expose
that exact executable boundary; no final-ledger fact is moved backwards. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.LocalLetRequirementTiming
open TypeSystem Detail

/-- The source compiler's literal result after the initializer has returned. -/
def finish (statement : Syntax.Statement) (name : Syntax.Identifier)
    (initial : State) (value : InferredExpression) (ready : State) : StatementResult :=
  let locals := ready.binderEnvironment.apply ready.inference.substitution
  let generalized := generalizeValue ready locals initial.nextRequirement (ready.resolve value.type)
  let binding := (ready.withLocals locals).allocateBinder name.value generalized.scheme
    (some name.span) false generalized.requirements
  { id := initial.allocateStatementId.1
    type := .unit
    hasValue := false
    sawReturn := false
    state := binding.2.recordNode (.statement {
      id := initial.allocateStatementId.1
      span := statement.span
      type := .unit
      form := .letDecl binding.1 (some value.id) }) }

/-- The initializer's expected type is taken from the actual optional source
annotation resolution. -/
inductive Annotation (context : Context) : Option Syntax.TypeExpr → Option Ty → Prop where
  | none : Annotation context none none
  | some {syntaxType : Syntax.TypeExpr} {type : Ty}
      (accepted : resolveSourceType context syntaxType = .ok type) :
      Annotation context (some syntaxType) (some type)

/-- Actual initialized-let execution retains its initializer inference and
its exact pre-generalization state. -/
structure Receipt (fuel : Nat) (context : Context) (statement : Syntax.Statement)
    (initial : State) (result : StatementResult) where
  name : Syntax.Identifier
  initializer : Syntax.Expr
  annotation : Option Syntax.TypeExpr
  expected : Option Ty
  annotationAccepted : Annotation context annotation expected
  form : statement.value = .letDecl name annotation (some initializer)
  value : InferredExpression
  ready : State
  child : inferExprFuel fuel context initializer expected initial.allocateStatementId.2 = .ok (value, ready)
  completed : result = finish statement name initial value ready

/-- Inversion is restricted to the real unannotated initialized branch. -/
theorem of_accepted {fuel : Nat} {context : Context} {statement : Syntax.Statement}
    {name : Syntax.Identifier} {initializer : Syntax.Expr} {expected : Ty}
    {initial : State} {result : StatementResult}
    (form : statement.value = .letDecl name none (some initializer))
    (accepted : inferStatementFuel (fuel + 1) context statement expected initial = .ok result) :
    Nonempty (Receipt fuel context statement initial result) := by
  unfold inferStatementFuel at accepted
  simp only [form, bind, Except.bind] at accepted
  cases child : inferExprFuel fuel context initializer none initial.allocateStatementId.2 with
  | error error => simp [child] at accepted
  | ok pair =>
      rcases pair with ⟨value, ready⟩
      simp only [child, pure, Pure.pure, Except.pure] at accepted
      refine ⟨⟨name, initializer, none, none, .none, form, value, ready, child, ?_⟩⟩
      exact (Except.ok.inj accepted).symm

/-- Both optional-annotation branches are inverted from the real statement
computation; no binder shape is used to guess the source annotation. -/
theorem of_initialized_accepted {fuel : Nat} {context : Context} {statement : Syntax.Statement}
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    {expected : Ty} {initial : State} {result : StatementResult}
    (form : statement.value = .letDecl name annotation (some initializer))
    (accepted : inferStatementFuel (fuel + 1) context statement expected initial = .ok result) :
    Nonempty (Receipt fuel context statement initial result) := by
  cases annotation with
  | none => exact of_accepted form accepted
  | some syntaxType =>
      unfold inferStatementFuel at accepted
      simp only [form, bind, Except.bind] at accepted
      cases resolved : resolveSourceType context syntaxType with
      | error error => simp [resolved] at accepted
      | ok type =>
          cases child : inferExprFuel fuel context initializer (some type) initial.allocateStatementId.2 with
          | error error => simp [resolved, child] at accepted
          | ok pair =>
              rcases pair with ⟨value, ready⟩
              simp only [resolved, child, pure, Pure.pure, Except.pure] at accepted
              refine ⟨⟨name, initializer, some syntaxType, some type, .some resolved,
                form, value, ready, child, ?_⟩⟩
              exact (Except.ok.inj accepted).symm

namespace Receipt
variable {fuel : Nat} {context : Context} {statement : Syntax.Statement}
    {initial : State} {result : StatementResult}

def locals (receipt : Receipt fuel context statement initial result) : Environment :=
  receipt.ready.binderEnvironment.apply receipt.ready.inference.substitution

def generalized (receipt : Receipt fuel context statement initial result) : GeneralizedValue :=
  generalizeValue receipt.ready receipt.locals initial.nextRequirement
    (receipt.ready.resolve receipt.value.type)

def binding (receipt : Receipt fuel context statement initial result) : TypedBinder × State :=
  (receipt.ready.withLocals receipt.locals).allocateBinder receipt.name.value receipt.generalized.scheme
    (some receipt.name.span) false receipt.generalized.requirements

/-- The recorded binder is the exact result of this generalization, not a
reconstructed scheme sharing only its final type. -/
theorem recorded (receipt : Receipt fuel context statement initial result) :
    .statement {
      id := initial.allocateStatementId.1
      span := statement.span
      type := .unit
      form := .letDecl receipt.binding.1 (some receipt.value.id) } ∈ result.state.nodes := by
  have nodes := congrArg (fun value : StatementResult => value.state.nodes) receipt.completed
  rw [nodes]
  exact List.mem_append_right _ (List.mem_singleton_self _)

/-- Real origin propagation stops at the initializer's returned state. -/
theorem ready_origins (receipt : Receipt fuel context statement initial result)
    (wellFormed : initial.RequirementsWellFormed)
    (allocated : initial.DirectRequirementsAllocated)
    (origins : LocalReadEvents.Origins initial) : LocalReadEvents.Origins receipt.ready :=
  (LocalReadEvents.inferExprFuel_origins_progress receipt.child).origins wellFormed allocated origins

/-- A local read already recorded during initializer inference contributes
its actual operational batch at the enclosing let's own cutoff. -/
theorem local_operational (receipt : Receipt fuel context statement initial result)
    (wellFormed : initial.RequirementsWellFormed)
    (allocated : initial.DirectRequirementsAllocated)
    (origins : LocalReadEvents.Origins initial)
    {node : ExpressionNode} (member : .expression node ∈ receipt.ready.nodes)
    {name : String} {binder : Resolved.LocalId}
    (form : node.form = .reference name (.local binder)) :
    ∃ lookup : LocalReadEvents.Lookup,
      node.id = lookup.id ∧
      node.form = .reference lookup.name.value (.local lookup.binder.id) ∧
      node.localSchemeInstantiationStart = some lookup.allocated.inference.next ∧
      lookup.batch.1 <+: node.requirements ∧
      RequirementPredicatesCorrespond receipt.ready.requirements lookup.predicates lookup.batch.1 ∧
      (∀ requirement ∈ receipt.ready.requirements, requirement.id ∈ lookup.batch.1 →
        requirement ∈ generalizeValueBlockingRequirements receipt.ready initial.nextRequirement) := by
  obtain ⟨lookup, id, actualForm, start, batchPrefix, predicates, blocked⟩ :=
    LocalReadEvents.Origin.operational
      (receipt.ready_origins wellFormed allocated origins node member name binder form)
  exact ⟨lookup, id, actualForm, start, batchPrefix, predicates,
    fun requirement present issued => blocked requirement present issued initial.nextRequirement⟩

/-- Variables of a genuinely blocking row cannot be quantified by this
particular executable generalization. -/
theorem excludes_blocking_variable (receipt : Receipt fuel context statement initial result)
    {requirement : Requirement}
    (blocked : requirement ∈ generalizeValueBlockingRequirements receipt.ready initial.nextRequirement)
    {metavariable : TypeVarId}
    (present : metavariable ∈ TypedTraitResolution.predicateVariables
      (applyPredicate receipt.ready requirement.predicate)) :
    metavariable ∉ receipt.generalized.scheme.quantified := by
  have blockedVariable : metavariable ∈ generalizeValueBlockedVariables receipt.ready receipt.locals
      initial.nextRequirement :=
    (mem_generalizeValueBlockedVariables_iff _ _ _ _).mpr (.inr ⟨requirement, blocked, present⟩)
  intro quantified
  change metavariable ∈ (generalizeValue receipt.ready receipt.locals initial.nextRequirement
    (receipt.ready.resolve receipt.value.type)).scheme.quantified at quantified
  rw [generalizeValue_scheme_quantified] at quantified
  have excluded := (List.mem_filter.mp quantified).2
  have contained : (generalizeValueBlockedVariables receipt.ready receipt.locals
      initial.nextRequirement).contains metavariable = true := List.contains_iff_mem.mpr blockedVariable
  rw [contained] at excluded
  cases excluded

/-- The same actual lookup both supplies its original predicate batch and
prevents those operational predicate variables from being generalized by the
enclosing let. This conclusion is about the initializer return state. -/
theorem local_generalization (receipt : Receipt fuel context statement initial result)
    (wellFormed : initial.RequirementsWellFormed)
    (allocated : initial.DirectRequirementsAllocated)
    (origins : LocalReadEvents.Origins initial)
    {node : ExpressionNode} (member : .expression node ∈ receipt.ready.nodes)
    {name : String} {binder : Resolved.LocalId}
    (form : node.form = .reference name (.local binder)) :
    ∃ lookup : LocalReadEvents.Lookup,
      node.id = lookup.id ∧
      node.form = .reference lookup.name.value (.local lookup.binder.id) ∧
      node.localSchemeInstantiationStart = some lookup.allocated.inference.next ∧
      lookup.batch.1 <+: node.requirements ∧
      RequirementPredicatesCorrespond receipt.ready.requirements lookup.predicates lookup.batch.1 ∧
      (∀ requirement ∈ receipt.ready.requirements, requirement.id ∈ lookup.batch.1 →
        ∀ metavariable ∈ TypedTraitResolution.predicateVariables (applyPredicate receipt.ready requirement.predicate),
          metavariable ∉ receipt.generalized.scheme.quantified) := by
  obtain ⟨lookup, id, actualForm, start, batchPrefix, predicates, blocked⟩ :=
    receipt.local_operational wellFormed allocated origins member form
  exact ⟨lookup, id, actualForm, start, batchPrefix, predicates,
    fun requirement present issued _ variableMember =>
      receipt.excludes_blocking_variable (blocked requirement present issued) variableMember⟩

/-- Initializer inference restores the exact entering lexical binder stack. -/
theorem ready_binders (receipt : Receipt fuel context statement initial result) :
    receipt.ready.localBinders = initial.localBinders := by
  exact congrArg LexicalScope.binders (inferExprFuel_success_lexicalScope_eq receipt.child)

/-- The only binder added after the initializer returns is this let's real
new binder; nested initializer locals are not installed in its continuation. -/
theorem result_binders (receipt : Receipt fuel context statement initial result) :
    result.state.localBinders = receipt.binding.1 :: initial.localBinders := by
  have binders := congrArg (fun value : StatementResult => value.state.localBinders) receipt.completed
  calc
    result.state.localBinders = receipt.binding.1 :: receipt.ready.localBinders := binders
    _ = receipt.binding.1 :: initial.localBinders := by rw [receipt.ready_binders]

/-- A later lookup immediately after this generalization selects either an
entering binder or this let's fresh binder, with their exact allocator bounds. -/
theorem lookup_after_generalization (receipt : Receipt fuel context statement initial result)
    (below : initial.LocalBindersBelowNextLocal) {name : String} {binder : TypedBinder}
    (found : result.state.lookupBinder? name = some binder) :
    binder.id.binderIndex < initial.nextLocal ∨ binder.id.binderIndex = receipt.ready.nextLocal := by
  have present := (State.lookupBinder?_eq_some_facts found).1
  rw [receipt.result_binders] at present
  rcases List.mem_cons.mp present with current | entering
  · right
    rw [current]
    rfl
  · exact .inl (below binder entering)

/-- A binder created and retired inside the initializer cannot be recovered
by any lookup at the actual enclosing let's continuation. -/
theorem retired_lookup_absent (receipt : Receipt fuel context statement initial result)
    (below : initial.LocalBindersBelowNextLocal) {retired : Resolved.LocalId}
    (created : initial.nextLocal ≤ retired.binderIndex)
    (retiredBeforeReturn : retired.binderIndex < receipt.ready.nextLocal)
    {name : String} {binder : TypedBinder} (same : binder.id = retired) :
    result.state.lookupBinder? name ≠ some binder := by
  intro found
  have bounds := receipt.lookup_after_generalization below found
  rw [same] at bounds
  omega

end Receipt
end Solcore.Frontend.SourceInference.LocalLetRequirementTiming
