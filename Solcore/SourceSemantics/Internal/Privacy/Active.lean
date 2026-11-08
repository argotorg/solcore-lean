import Solcore.Frontend.SourceInference.Internal.LocalGeneralization
import Solcore.SourceSemantics.Internal.Selected.State
import Solcore.SourceSemantics.Internal.Privacy.SelectedInference
import Solcore.Frontend.SourceInference.Internal.Continuations
import Solcore.SourceSemantics.Internal.Inference.CaptureOrigins
import Solcore.SourceSemantics.Internal.Inference.GeneralizationBarriers
import Solcore.SourceSemantics.Internal.Privacy.ProtectedInference
import Solcore.SourceSemantics.Internal.Privacy.SelectedCalls

/-!
# Privacy of active binders

Every active generalized binder stays private through statements, headers, patterns and saved
scopes, with its live template backing.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceLiveTemplateBacking
/-! Active local-scheme predicates retain an actual raw ledger witness.
The invariant follows executable scope preservation and generalization. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

def LiveTemplatesBacked (state : State) : Prop :=
  ∀ binder ∈ state.localBinders, ∀ requirement ∈ binder.schemeRequirements,
    ∃ raw ∈ state.requirements,
      applyPredicate state requirement.predicate = applyPredicate state raw.predicate

private theorem predicate_extends {before after : State}
    (extension : after.inference.substitution.SemanticallyExtends before.inference.substitution)
    (predicate : ProgramPredicate) :
    applyPredicate after (applyPredicate before predicate) = applyPredicate after predicate :=
  TypedTraitResolution.applySubstitution_semanticallyExtends extension predicate

theorem LiveTemplatesBacked.transport {before after : State}
    (backed : LiveTemplatesBacked before)
    (binders : after.localBinders ⊆ before.localBinders)
    (rows : before.requirements ⊆ after.requirements)
    (extension : after.inference.substitution.SemanticallyExtends before.inference.substitution) :
    LiveTemplatesBacked after := by
  intro binder member requirement retained
  obtain ⟨raw, present, same⟩ := backed binder (binders member) requirement retained
  refine ⟨raw, rows present, ?_⟩
  have transported := congrArg (applyPredicate after) same
  simpa only [predicate_extends extension] using transported

theorem LiveTemplatesBacked.congr {before after : State}
    (backed : LiveTemplatesBacked before)
    (binders : after.localBinders = before.localBinders)
    (rows : after.requirements = before.requirements)
    (inference : after.inference.substitution = before.inference.substitution) :
    LiveTemplatesBacked after := by
  intro binder member requirement retained
  obtain ⟨raw, present, same⟩ := backed binder (binders ▸ member) requirement retained
  exact ⟨raw,rows.symm ▸ present,by simpa only [applyPredicate, inference] using same⟩

theorem LiveTemplatesBacked.initial
    (owner : Resolved.DeclarationId) (locals : Environment) (comptime : List Bool) :
    LiveTemplatesBacked (State.initial owner locals comptime) := by
  intro binder member requirement retained
  rw [← State.initial_inputs_eq_localBinders, State.initial_inputs_definition] at member
  obtain ⟨index, below, same⟩ := List.exists_of_mem_mapIdx member
  subst binder
  simp at retained

theorem LiveTemplatesBacked.inferExprFuel
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr} {expected : Option Ty}
    {initial : State} {result : InferredExpression × State}
    (backed : LiveTemplatesBacked initial) (ready : initial.InferenceReady)
    (validated : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (accepted : inferExprFuel fuel context source expected initial = .ok result) :
    LiveTemplatesBacked result.2 := by
  have properties := inferExprFuel_inferenceProperties ready validated canonical expectedBelow accepted
  have same := congrArg LexicalScope.binders (inferExprFuel_success_lexicalScope_eq accepted)
  change result.2.localBinders = initial.localBinders at same
  exact backed.transport (by intro _ member; exact same ▸ member)
    (inferExprFuel_requirements_subset accepted) properties.1.substitution_extends

theorem LiveTemplatesBacked.generalized
    {state : State} (backed : LiveTemplatesBacked state) (solved : state.inference.Solved)
    (locals : Environment) (cutoff : Nat) (type : Ty) (name : String)
    (span : Option Syntax.SourceSpan) (comptime : Bool) :
    let generalized := generalizeValue state locals cutoff type
    LiveTemplatesBacked ((state.withLocals locals).allocateBinder name generalized.scheme span
      comptime generalized.requirements).2 := by
  intro generalized binder member requirement retained
  change binder ∈ ((state.withLocals locals).allocateBinder name generalized.scheme span
    comptime generalized.requirements).1 :: state.localBinders at member
  rcases List.mem_cons.mp member with rfl | old
  · change requirement ∈ generalized.requirements at retained
    obtain ⟨raw, present, _, same⟩ :=
      generalizeValue_requirement_source state locals cutoff type requirement retained
    refine ⟨raw,present,?_⟩
    change applyPredicate state requirement.predicate = applyPredicate state raw.predicate
    rw [same]
    exact predicate_extends solved.apply_idempotent _
  · exact backed binder old requirement retained

theorem LocalLetRequirementTiming.Receipt.templates_ready
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {initial : State} {result : StatementResult}
    (receipt : SourceInference.LocalLetRequirementTiming.Receipt fuel context source initial result)
    (backed : LiveTemplatesBacked initial) (ready : initial.InferenceReady)
    (validated : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes)) :
    LiveTemplatesBacked receipt.ready :=
  (backed.congr (after := initial.allocateStatementId.2) rfl rfl rfl).inferExprFuel ready.allocateStatementId validated canonical
    (receipt.annotationAccepted.variablesBelow _) receipt.child

theorem LocalLetRequirementTiming.Receipt.templates_result
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {initial : State} {result : StatementResult}
    (receipt : SourceInference.LocalLetRequirementTiming.Receipt fuel context source initial result)
    (backed : LiveTemplatesBacked initial) (ready : initial.InferenceReady)
    (validated : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes)) :
    LiveTemplatesBacked result.state := by
  have readyBacked := LocalLetRequirementTiming.Receipt.templates_ready receipt backed ready validated canonical
  have readyProperties := receipt.initializer_inference ready validated canonical
  have allocated := readyBacked.generalized readyProperties.2.1.solved receipt.locals
    initial.nextRequirement (receipt.ready.resolve receipt.value.type) receipt.name.value
    (some receipt.name.span) false
  rw [receipt.completed]
  exact allocated.congr rfl rfl rfl

theorem LocalLetRequirementTiming.Receipt.templates_before
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {initial : State} {result : StatementResult}
    (receipt : SourceInference.LocalLetRequirementTiming.Receipt fuel context source initial result)
    (backed : LiveTemplatesBacked initial) (ready : initial.InferenceReady)
    (wellFormed : initial.RequirementsWellFormed)
    (validated : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes)) :
    ∀ binder ∈ receipt.ready.localBinders, ∀ requirement ∈ binder.schemeRequirements,
      ∃ raw ∈ receipt.ready.requirements.take initial.nextRequirement,
        applyPredicate receipt.ready requirement.predicate = applyPredicate receipt.ready raw.predicate := by
  have properties := receipt.initializer_inference ready validated canonical
  have readyWellFormed := (inferExprFuel_direct_progress receipt.child).wellFormed wellFormed
  have rows : initial.requirements ⊆ receipt.ready.requirements := inferExprFuel_requirements_subset receipt.child
  intro binder member requirement retained
  obtain ⟨raw, present, same⟩ := backed binder (receipt.ready_binders ▸ member) requirement retained
  refine ⟨raw, (State.mem_take_prior_requirements_iff initial receipt.ready wellFormed readyWellFormed
    rows raw).mpr present, ?_⟩
  have transported := congrArg (applyPredicate receipt.ready) same
  simpa only [predicate_extends properties.1.substitution_extends] using transported

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceLiveTemplateStatementBacking
/-! Statement and statement-list inference preserve real predicate backing.
Only the current let adds a binder; scoped children restore the entering stack. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

private theorem unify_binders {before after : State} {left right : Ty}
    (accepted : Detail.unify before left right = .ok after) :
    after.localBinders = before.localBinders := by
  unfold Detail.unify at accepted
  cases inference : liftUnification (before.inference.unify left right) with
  | error error => simp [inference, bind, Except.bind] at accepted
  | ok solved =>
    simp only [inference, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
    cases accepted
    rfl

private theorem scrutinee_binders
    {fuel : Nat} {context : SourceInference.Context} {span : Syntax.SourceSpan}
    {sources : List Syntax.Expr} {initial final : State} {value : InferredExpression}
    (accepted : SourceInferenceSoundness.inferMatchScrutineesFuel fuel context span sources initial =
      .ok (value,final)) : final.localBinders = initial.localBinders := by
  cases sources with
  | nil =>
    unfold SourceInferenceSoundness.inferMatchScrutineesFuel at accepted
    cases child : inferExprsFuel fuel context [] initial with
    | error error => simp [child, bind, Except.bind] at accepted
    | ok pair =>
      rcases pair with ⟨values,state⟩
      simp only [child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
      cases accepted
      exact congrArg LexicalScope.binders (inferExprsFuel_success_lexicalScope_eq child)
  | cons first rest =>
    cases rest with
    | nil =>
      have child : inferExprFuel fuel context first none initial = .ok (value,final) := by
        simpa only [SourceInferenceSoundness.inferMatchScrutineesFuel] using accepted
      exact congrArg LexicalScope.binders (inferExprFuel_success_lexicalScope_eq child)
    | cons second tail =>
      unfold SourceInferenceSoundness.inferMatchScrutineesFuel at accepted
      cases child : inferExprsFuel fuel context (first :: second :: tail) initial with
      | error error => simp [child, bind, Except.bind] at accepted
      | ok pair =>
        rcases pair with ⟨values,state⟩
        simp only [child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
        cases accepted
        exact congrArg LexicalScope.binders (inferExprsFuel_success_lexicalScope_eq child)

private theorem nonlet_binders
    {fuel : Nat} {context : SourceInference.Context} {statement : Syntax.Statement}
    {expectedReturn : Ty} {initial : State} {result : StatementResult}
    (notLet : ∀ name annotation initializer, statement.value ≠ .letDecl name annotation initializer)
    (accepted : inferStatementFuel fuel context statement expectedReturn initial = .ok result) :
    result.state.localBinders = initial.localBinders := by
  cases fuel with
  | zero => simp [Detail.inferStatementFuel] at accepted
  | succ fuel =>
    cases form : statement.value with
    | letDecl name annotation initializer => exact (notLet _ _ _ form).elim
    | expression source trailing =>
      obtain ⟨value, state, child, resultEq, _⟩ :=
        inferStatementFuel_success_expression_facts form rfl accepted
      rw [resultEq]
      exact congrArg LexicalScope.binders (inferExprFuel_success_lexicalScope_eq child)
    | assignValue target operator value =>
      obtain ⟨assignment, inferred, state, child, resultEq, _⟩ :=
        inferStatementFuel_success_assignValue_facts form rfl accepted
      rw [resultEq]
      exact congrArg LexicalScope.binders (inferAssignedValueFuel_success_lexicalScope_eq child)
    | assignBitNot target operator =>
      obtain ⟨place, state, unified, child, unification, _, resultEq, _⟩ :=
        inferStatementFuel_success_assignBitNot_facts form rfl accepted
      rw [resultEq]
      exact (unify_binders unification).trans
        (congrArg LexicalScope.binders (inferPlaceFuel_success_lexicalScope_eq child))
    | returnStmt source =>
      cases source with
      | none =>
        obtain ⟨unified, unification, _, resultEq, _⟩ :=
          inferStatementFuel_success_returnUnit_facts form rfl accepted
        rw [resultEq]
        have h := unify_binders unification
        exact h
      | some source =>
        obtain ⟨value, state, child, resultEq, _⟩ :=
          inferStatementFuel_success_returnValue_facts form rfl accepted
        rw [resultEq]
        exact congrArg LexicalScope.binders (inferExprFuel_success_lexicalScope_eq child)
    | breakStmt =>
      obtain ⟨_, resultEq, _⟩ := inferStatementFuel_success_break_facts form rfl accepted
      rw [resultEq]
      rfl
    | continueStmt =>
      obtain ⟨_, resultEq, _⟩ := inferStatementFuel_success_continue_facts form rfl accepted
      rw [resultEq]
      rfl
    | block body =>
      obtain ⟨block, _, resultEq, _⟩ := inferStatementFuel_success_block_facts form rfl accepted
      rw [resultEq]
      rfl
    | ifThen condition thenBody elseBody =>
      cases elseBody with
      | none =>
        obtain ⟨value, state, thenResult, child, _, resultEq, _⟩ :=
          inferStatementFuel_success_ifWithoutElse_facts form rfl accepted
        rw [resultEq]
        exact congrArg LexicalScope.binders (inferExprFuel_success_lexicalScope_eq child)
      | some elseBody =>
        obtain ⟨value, state, thenResult, elseResult, child, _, _, resultEq, _⟩ :=
          inferStatementFuel_success_ifWithElse_facts form rfl accepted
        rw [resultEq]
        exact congrArg LexicalScope.binders (inferExprFuel_success_lexicalScope_eq child)
    | whileLoop condition body =>
      obtain ⟨value, state, bodyResult, child, _, resultEq, _⟩ :=
        inferStatementFuel_success_whileLoop_facts form rfl accepted
      rw [resultEq]
      exact congrArg LexicalScope.binders (inferExprFuel_success_lexicalScope_eq child)
    | forLoop span initializer condition post body =>
      obtain ⟨initializerResult, value, state, bodyResult, postResult,
          _, _, _, _, resultEq, _⟩ :=
        inferStatementFuel_success_forLoop_facts form rfl accepted
      rw [resultEq]
      rfl
    | matchWith sources arms =>
      cases defaultEq : arms.value.defaultBody with
      | none =>
        obtain ⟨value, state, hidden, hiddenState, checked, child, allocated, checkedRun,
            _, resultEq, _⟩ :=
          inferStatementFuel_success_matchWithoutDefault_facts form defaultEq rfl accepted
        have hiddenEq : hiddenState = state.allocateHiddenLocal.2 := (congrArg Prod.snd allocated).symm
        rw [resultEq]
        have same := congrArg LexicalScope.binders (inferMatchCasesFuel_success_lexicalScope_eq rfl checkedRun)
        change checked.state.localBinders = hiddenState.localBinders at same
        change checked.state.localBinders = initial.localBinders
        rw [same,hiddenEq]
        have h := scrutinee_binders child
        exact h
      | some default =>
        obtain ⟨value, state, hidden, hiddenState, checked, defaultResult, child, allocated,
            _, _, _, resultEq, _⟩ :=
          inferStatementFuel_success_matchWithDefault_facts form defaultEq rfl accepted
        have hiddenEq : hiddenState = state.allocateHiddenLocal.2 := (congrArg Prod.snd allocated).symm
        rw [resultEq]
        change hiddenState.localBinders = initial.localBinders
        rw [hiddenEq]
        have h := scrutinee_binders child
        exact h
    | assembly body => simp [Detail.inferStatementFuel,form] at accepted
    | error => simp [Detail.inferStatementFuel,form] at accepted

theorem LiveTemplatesBacked.inferStatementFuel
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {expectedReturn : Ty} {initial : State} {result : StatementResult}
    (backed : LiveTemplatesBacked initial) (ready : initial.InferenceReady)
    (validated : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (accepted : inferStatementFuel fuel context source expectedReturn initial = .ok result) :
    LiveTemplatesBacked result.state := by
  cases fuel with
  | zero => simp [Detail.inferStatementFuel] at accepted
  | succ fuel =>
    by_cases isLet : ∃ name annotation initializer, source.value = .letDecl name annotation initializer
    · obtain ⟨name,annotation,initializer,form⟩ := isLet
      cases initializer with
      | some initializer =>
        obtain ⟨receipt⟩ := SourceInference.LocalLetRequirementTiming.of_initialized_accepted form accepted
        exact LocalLetRequirementTiming.Receipt.templates_result receipt backed ready validated canonical
      | none =>
        cases annotation with
        | none =>
          simp [Detail.inferStatementFuel,form] at accepted
          change (Except.error (.missingInitializer name.value) : Except SourceInference.Error StatementResult) = .ok result at accepted
          cases accepted
        | some annotation =>
          unfold Detail.inferStatementFuel at accepted
          simp only [form,bind,Except.bind] at accepted
          cases resolved : resolveSourceType context annotation with
          | error error => simp [resolved] at accepted
          | ok type =>
            simp only [resolved,pure,Pure.pure,Except.pure,Except.ok.injEq] at accepted
            subst result
            have allocated : LiveTemplatesBacked initial.allocateStatementId.2 :=
              backed.congr rfl rfl rfl
            exact (allocated.generalized ready.solved _ _ _ _ _ _).congr rfl rfl rfl
    · have same := nonlet_binders (by
        intro name annotation initializer form
        exact isLet ⟨name,annotation,initializer,form⟩) accepted
      have progress := inferStatementFuel_inferenceProperties ready validated canonical returnBelow accepted
      exact backed.transport (by intro _ member; exact same ▸ member)
        (inferStatementFuel_requirements_subset accepted) progress.1.substitution_extends

theorem LiveTemplatesBacked.inferStatementsFuel
    {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.Statement}
    {expectedReturn : Ty} {initial : State} {result : BlockResult}
    (backed : LiveTemplatesBacked initial) (ready : initial.InferenceReady)
    (validated : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (accepted : inferStatementsFuel fuel context sources expectedReturn initial = .ok result) :
    LiveTemplatesBacked result.state := by
  induction fuel generalizing sources initial result with
  | zero => simp [Detail.inferStatementsFuel] at accepted
  | succ fuel ih =>
    cases sources with
    | nil =>
      simp [Detail.inferStatementsFuel] at accepted
      subst result
      exact backed
    | cons head tail =>
      cases tail with
      | nil =>
        obtain ⟨statement, statementRun, resultEq⟩ := inferStatementsFuel_success_singleton_facts accepted
        rw [resultEq]
        exact backed.inferStatementFuel ready validated canonical returnBelow statementRun
      | cons next rest =>
        obtain ⟨statement, tail, statementRun, tailRun, resultEq⟩ :=
          inferStatementsFuel_success_cons_facts accepted
        have properties := inferStatementFuel_inferenceProperties ready validated canonical returnBelow statementRun
        rw [resultEq]
        change LiveTemplatesBacked tail.state
        exact ih (result := tail) (backed.inferStatementFuel ready validated canonical returnBelow statementRun)
          properties.2.1 (returnBelow.weaken properties.1.next_le) tailRun

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActiveQuantifierOrigins
/-! Exact origins and allocation bounds of active scheme quantifiers after actual statement inference. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

/-- Every binder surviving a statement is entering, monomorphic, or this
statement's actual initialized-let allocation. Nested child locals are restored. -/
theorem inferStatementFuel_quantified_origin
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {expectedReturn : Ty} {initial : State} {result : StatementResult}
    (accepted : Detail.inferStatementFuel fuel context source expectedReturn initial = .ok result) :
    ∀ binder ∈ result.state.localBinders,
      binder ∈ initial.localBinders ∨ binder.scheme.quantified = [] ∨
        ∃ childFuel, ∃ receipt : SourceInference.LocalLetRequirementTiming.Receipt childFuel context source initial result,
          binder = receipt.binding.1 := by
  cases fuel with
  | zero => simp [Detail.inferStatementFuel] at accepted
  | succ fuel =>
    by_cases isLet : ∃ name annotation initializer, source.value = .letDecl name annotation initializer
    · obtain ⟨name,annotation,initializer,form⟩ := isLet
      cases initializer with
      | some initializer =>
        obtain ⟨receipt⟩ := SourceInference.LocalLetRequirementTiming.of_initialized_accepted form accepted
        intro binder member
        rw [receipt.result_binders] at member
        rcases List.mem_cons.mp member with current | entering
        · exact .inr (.inr ⟨fuel,receipt,current⟩)
        · exact .inl entering
      | none =>
        cases annotation with
        | none =>
          simp [Detail.inferStatementFuel,form] at accepted
          change (Except.error (.missingInitializer name.value) : Except SourceInference.Error StatementResult) = .ok result at accepted
          cases accepted
        | some annotation =>
          obtain ⟨type, locals, valueType, generalized, ⟨allocated,state⟩, resolved, _, typeEq,
              generalizedEq, allocation, resultEq, _⟩ :=
            inferStatementFuel_success_letAnnotatedUninitialized_facts form rfl accepted
          have closed : type.freeVariables = [] := by
            apply List.eq_nil_iff_forall_not_mem.mpr
            intro q member
            exact (Nat.not_lt_zero _) (resolveSourceType_success_variablesBelow resolved 0 q member)
          have resolveEq : initial.allocateStatementId.2.resolve type = type :=
            resolveSourceType_success_apply_eq_self initial.inference.substitution resolved
          have monomorphic : generalized.scheme.quantified = [] := by
            rw [generalizedEq, generalizeValue_scheme_quantified, typeEq]
            change List.filter _ (initial.allocateStatementId.2.resolve type).freeVariables = []
            rw [resolveEq,closed]
            rfl
          have binders := congrArg (fun p : TypedBinder × State => p.2.localBinders) allocation
          change ((initial.allocateStatementId.2.withLocals locals).allocateBinder name.value
            generalized.scheme (some name.span) false generalized.requirements).1 :: initial.localBinders =
              state.localBinders at binders
          intro binder member
          rw [resultEq] at member
          change binder ∈ state.localBinders at member
          rw [← binders] at member
          rcases List.mem_cons.mp member with current | entering
          · right; left
            rw [current]
            exact monomorphic
          · exact .inl entering
    · have same := nonlet_binders (by
        intro name annotation initializer form
        exact isLet ⟨name,annotation,initializer,form⟩) accepted
      intro binder member
      exact .inl (same ▸ member)

/-- The actual new scheme is bounded by its initializer result; all entering
quantifiers remain below the monotonically advancing inference allocator. -/
theorem activeQuantifiersBelowNext_inferStatementFuel
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {expectedReturn : Ty} {initial : State} {result : StatementResult}
    (bound : ActiveQuantifiersBelowNext initial) (ready : initial.InferenceReady)
    (validated : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (accepted : Detail.inferStatementFuel fuel context source expectedReturn initial = .ok result) :
    ActiveQuantifiersBelowNext result.state := by
  have progress := inferStatementFuel_inferenceProperties ready validated canonical returnBelow accepted
  intro binder member q quantified
  rcases inferStatementFuel_quantified_origin accepted binder member with entering | mono | initialized
  · exact Nat.lt_of_lt_of_le (bound binder entering q quantified) progress.1.next_le
  · simp [mono] at quantified
  · obtain ⟨childFuel,receipt,same⟩ := initialized
    subst binder
    have properties := receipt.initializer_inference ready validated canonical
    have valueBelow := properties.2.1.solved.variablesBelow_apply properties.2.2
    have newBound := activeQuantifiersBelowNext_generalizeValue receipt.ready receipt.locals
      initial.nextRequirement (receipt.ready.resolve receipt.value.type) valueBelow q quantified
    rw [receipt.inference_eq]
    exact newBound

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceStatementPrivacyContinuation
/-! An original statement position supplies its real continuation through the
remaining source statements. Privacy is proved by their actual inference calls. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

structure StatementPrivacyOccurrence (context : SourceInference.Context)
    (source : Syntax.Statement) (expected : Ty) (initial final : State)
    extends StatementInferenceContinuation.Occurrence context source expected initial final where
  resultReady : result.state.InferenceReady
  resultWellFormed : result.state.RequirementsWellFormed
  expectedBelow : expected.VariablesBelow result.state.inference.next
  privacy : ∀ protectedVars : List TypeVarId,
    (∀ v ∈ protectedVars, v.index < result.state.inference.next) →
    LiveBindersSafe protectedVars result.state →
    Safe protectedVars result.state expected →
    SafeTransport protectedVars result.state final ∧
      ∀ row ∈ final.requirements, row ∉ result.state.requirements → PredicateSafe protectedVars final row.predicate

/-- The selected position follows the original list. The continuation is
constructed here from actual later calls, rather than assumed as a trace law. -/
theorem statementPrivacyOccurrence_of_position
    {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.Statement}
    {expected : Ty} {initial : State} {result : BlockResult} {index : Nat} {source : Syntax.Statement}
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (nodesBelow : initial.NodesBelowNextOccurrence)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes))
    (expectedBelow : expected.VariablesBelow initial.inference.next)
    (accepted : inferStatementsFuel fuel context sources expected initial = .ok result)
    (position : sources[index]? = some source) :
    Nonempty (StatementPrivacyOccurrence context source expected initial result.state) := by
  induction fuel generalizing sources initial result index with
  | zero => simp [inferStatementsFuel] at accepted
  | succ fuel ih =>
    cases sources with
    | nil => simp at position
    | cons head rest =>
      cases headRun : inferStatementFuel fuel context head expected initial with
      | error error => simp [inferStatementsFuel,headRun,bind,Except.bind] at accepted
      | ok headResult =>
        have headProgress := inferStatementFuel_inferenceProperties ready formation canonical expectedBelow headRun
        have headWellFormed := (inferStatementFuel_direct_progress headRun).wellFormed wellFormed
        have headBelow := (inferStatementFuel_occurrenceBoundExtends headRun).nodesBelowNextOccurrence nodesBelow
        have afterExpected := expectedBelow.weaken headProgress.1.next_le
        cases rest with
        | nil =>
          have same : result.state = headResult.state := by
            simp only [inferStatementsFuel,headRun,bind,Except.bind,pure,Pure.pure,Except.pure,Except.ok.injEq] at accepted
            exact (congrArg BlockResult.state accepted).symm
          cases index with
          | zero =>
            simp only [List.getElem?_cons_zero,Option.some.injEq] at position
            subst source
            refine ⟨{
              fuel := fuel, entry := initial, result := headResult, accepted := headRun,
              ready := ready, before := .refl ready.solved,
              continuation := same.symm ▸ State.InferenceProgress.refl headProgress.2.1.solved,
              retained := same.symm ▸ List.prefix_refl _,
              resultReady := headProgress.2.1, resultWellFormed := headWellFormed,
              expectedBelow := afterExpected,
              privacy := ?_ }⟩
            intro protectedVars bound live safe
            rw [same]
            exact ⟨.refl _ _,fun row member fresh => False.elim (fresh member)⟩
          | succ index => simp at position
        | cons next remaining =>
          cases tailRun : inferStatementsFuel fuel context (next::remaining) expected headResult.state with
          | error error => simp [inferStatementsFuel,headRun,tailRun,bind,Except.bind] at accepted
          | ok tailResult =>
            have same : result.state = tailResult.state := by
              simp only [inferStatementsFuel,headRun,tailRun,bind,Except.bind,pure,Pure.pure,Except.pure,Except.ok.injEq] at accepted
              exact (congrArg BlockResult.state accepted).symm
            cases index with
            | zero =>
              simp only [List.getElem?_cons_zero,Option.some.injEq] at position
              subst source
              have tailProgress := inferStatementsFuel_inferenceProperties headProgress.2.1 formation canonical afterExpected tailRun
              refine ⟨{
                fuel := fuel, entry := initial, result := headResult, accepted := headRun,
                ready := ready, before := .refl ready.solved,
                continuation := same.symm ▸ tailProgress.1,
                retained := same.symm ▸ inferStatementsFuel_preserves_nodesPrefix tailRun
                  (List.prefix_refl _) headBelow (Nat.le_refl _),
                resultReady := headProgress.2.1, resultWellFormed := headWellFormed,
                expectedBelow := afterExpected,
                privacy := ?_ }⟩
              intro protectedVars bound live safe
              rw [same]
              have actual := inferStatementsFuel_private protectedVars fuel context (next::remaining) expected headResult.state
                headProgress.2.1 headWellFormed bound live catalog formation canonical afterExpected safe tailResult tailRun
              exact ⟨actual.1,actual.2.2.2⟩
            | succ index =>
              have restPosition : (next::remaining)[index]? = some source := position
              obtain ⟨found⟩ := ih headProgress.2.1 headWellFormed headBelow afterExpected tailRun restPosition
              refine ⟨{
                fuel := found.fuel, entry := found.entry, result := found.result, accepted := found.accepted,
                ready := found.ready, before := headProgress.1.trans found.before,
                continuation := same.symm ▸ found.continuation,
                retained := same.symm ▸ found.retained,
                resultReady := found.resultReady, resultWellFormed := found.resultWellFormed,
                expectedBelow := found.expectedBelow,
                privacy := ?_ }⟩
              intro protectedVars bound live safe
              rw [same]
              exact found.privacy protectedVars bound live safe

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceBackedStatementPrivacy
/-! An original statement position supplies its real continuation through the
remaining source statements. Privacy is proved by their actual inference calls. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

structure BackedStatementPrivacyOccurrence (context : SourceInference.Context)
    (source : Syntax.Statement) (expected : Ty) (initial final evidenceState : State) (roots : List NodeId)
    extends StatementPrivacyOccurrence context source expected initial final where
  entryWellFormed : entry.RequirementsWellFormed
  entryTemplates : LiveTemplatesBacked entry
  entryOrigins : ActiveBinderCaptureOrigins entry (evidenceState.toTypedSource roots)

/-- The selected position follows the original list. The continuation is
constructed here from actual later calls, rather than assumed as a trace law. -/
theorem backedStatementPrivacyOccurrence_of_position
    {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.Statement}
    {expected : Ty} {initial evidenceState : State} {roots : List NodeId}
    {result : BlockResult} {index : Nat} {source : Syntax.Statement}
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (nodesBelow : initial.NodesBelowNextOccurrence)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes))
    (expectedBelow : expected.VariablesBelow initial.inference.next)
    (backed : LiveTemplatesBacked initial)
    (origins : ActiveBinderCaptureOrigins initial (evidenceState.toTypedSource roots))
    (retained : TypingSourceExtends (result.state.toTypedSource roots) (evidenceState.toTypedSource roots))
    (accepted : inferStatementsFuel fuel context sources expected initial = .ok result)
    (position : sources[index]? = some source) :
    Nonempty (BackedStatementPrivacyOccurrence context source expected initial result.state evidenceState roots) := by
  induction fuel generalizing sources initial result index with
  | zero => simp [inferStatementsFuel] at accepted
  | succ fuel ih =>
    cases sources with
    | nil => simp at position
    | cons head rest =>
      cases headRun : inferStatementFuel fuel context head expected initial with
      | error error => simp [inferStatementsFuel,headRun,bind,Except.bind] at accepted
      | ok headResult =>
        have headProgress := inferStatementFuel_inferenceProperties ready formation canonical expectedBelow headRun
        have headWellFormed := (inferStatementFuel_direct_progress headRun).wellFormed wellFormed
        have headBelow := (inferStatementFuel_occurrenceBoundExtends headRun).nodesBelowNextOccurrence nodesBelow
        have afterExpected := expectedBelow.weaken headProgress.1.next_le
        cases rest with
        | nil =>
          have same : result.state = headResult.state := by
            simp only [inferStatementsFuel,headRun,bind,Except.bind,pure,Pure.pure,Except.pure,Except.ok.injEq] at accepted
            exact (congrArg BlockResult.state accepted).symm
          cases index with
          | zero =>
            simp only [List.getElem?_cons_zero,Option.some.injEq] at position
            subst source
            refine ⟨{
              fuel := fuel, entry := initial, result := headResult, accepted := headRun,
              ready := ready, before := .refl ready.solved,
              continuation := same.symm ▸ State.InferenceProgress.refl headProgress.2.1.solved,
              retained := same.symm ▸ List.prefix_refl _,
              resultReady := headProgress.2.1, resultWellFormed := headWellFormed,
              expectedBelow := afterExpected,
              entryWellFormed := wellFormed, entryTemplates := backed, entryOrigins := origins,
              privacy := ?_ }⟩
            intro protectedVars bound live safe
            rw [same]
            exact ⟨.refl _ _,fun row member fresh => False.elim (fresh member)⟩
          | succ index => simp at position
        | cons next remaining =>
          cases tailRun : inferStatementsFuel fuel context (next::remaining) expected headResult.state with
          | error error => simp [inferStatementsFuel,headRun,tailRun,bind,Except.bind] at accepted
          | ok tailResult =>
            have same : result.state = tailResult.state := by
              simp only [inferStatementsFuel,headRun,tailRun,bind,Except.bind,pure,Pure.pure,Except.pure,Except.ok.injEq] at accepted
              exact (congrArg BlockResult.state accepted).symm
            cases index with
            | zero =>
              simp only [List.getElem?_cons_zero,Option.some.injEq] at position
              subst source
              have tailProgress := inferStatementsFuel_inferenceProperties headProgress.2.1 formation canonical afterExpected tailRun
              refine ⟨{
                fuel := fuel, entry := initial, result := headResult, accepted := headRun,
                ready := ready, before := .refl ready.solved,
                continuation := same.symm ▸ tailProgress.1,
                retained := same.symm ▸ inferStatementsFuel_preserves_nodesPrefix tailRun
                  (List.prefix_refl _) headBelow (Nat.le_refl _),
                resultReady := headProgress.2.1, resultWellFormed := headWellFormed,
                expectedBelow := afterExpected,
                entryWellFormed := wellFormed, entryTemplates := backed, entryOrigins := origins,
                privacy := ?_ }⟩
              intro protectedVars bound live safe
              rw [same]
              have actual := inferStatementsFuel_private protectedVars fuel context (next::remaining) expected headResult.state
                headProgress.2.1 headWellFormed bound live catalog formation canonical afterExpected safe tailResult tailRun
              exact ⟨actual.1,actual.2.2.2⟩
            | succ index =>
              have restPosition : (next::remaining)[index]? = some source := position
              have headBacked := backed.inferStatementFuel ready formation canonical expectedBelow headRun
              have tailToEvidence : TypingSourceExtends (tailResult.state.toTypedSource roots)
                  (evidenceState.toTypedSource roots) := by
                rwa [same] at retained
              have headToEvidence := (inferStatementsFuel_success_typingSourceExtends tailRun headBelow roots).trans tailToEvidence
              have headOrigins := inferStatementFuel_captureOrigins headRun origins headToEvidence
              obtain ⟨found⟩ := ih headProgress.2.1 headWellFormed headBelow afterExpected
                headBacked headOrigins tailToEvidence tailRun restPosition
              refine ⟨{
                fuel := found.fuel, entry := found.entry, result := found.result, accepted := found.accepted,
                ready := found.ready, before := headProgress.1.trans found.before,
                continuation := same.symm ▸ found.continuation,
                retained := same.symm ▸ found.retained,
                resultReady := found.resultReady, resultWellFormed := found.resultWellFormed,
                expectedBelow := found.expectedBelow,
                entryWellFormed := found.entryWellFormed, entryTemplates := found.entryTemplates,
                entryOrigins := found.entryOrigins,
                privacy := ?_ }⟩
              intro protectedVars bound live safe
              rw [same]
              exact found.privacy protectedVars bound live safe

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActiveQuantifierPrivacy
/-! Each active generalized binder has a privacy invariant for its own variables.
Older binders use actual inference preservation; a new binder uses the real
executable generalizer and finalizer capture checks. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

def ActiveQuantifiersPrivate (state : State) : Prop :=
  ∀ binder ∈ state.localBinders, LiveBindersSafe binder.scheme.quantified state

theorem liveBindersSafe_nil (state : State) : LiveBindersSafe [] state := by
  intro binder member
  constructor
  · intro v occurs q image protectedMember
    exact List.not_mem_nil protectedMember
  · intro requirement present type typeMember v occurs outside q image protectedMember
    exact List.not_mem_nil protectedMember

theorem ActiveQuantifiersPrivate.initial (owner : Resolved.DeclarationId)
    (locals : Environment) (comptime : List Bool)
    (monomorphic : ∀ entry ∈ locals, entry.2.quantified = []) :
    ActiveQuantifiersPrivate (State.initial owner locals comptime) := by
  intro binder member
  rw [← State.initial_inputs_eq_localBinders, State.initial_inputs_definition] at member
  obtain ⟨index, indexLt, binderEq⟩ := List.exists_of_mem_mapIdx member
  subst binder
  have empty := monomorphic locals[index] (List.getElem_mem indexLt)
  change LiveBindersSafe locals[index].2.quantified _
  rw [empty]
  exact liveBindersSafe_nil _

namespace LocalLetRequirementTiming.Receipt

/-- The exact initialized statement supplies the newly generalized binder and
all old-template provenance needed by its actual finalizer capture checks. -/
theorem active_privacy
    {wholeContext : SourceInference.Context} {wholeReturn : Ty}
    {evidenceState : State} {roots : List NodeId} {finalized : SourceInference.Result}
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {initial : State} {result : StatementResult}
    (receipt : SourceInference.LocalLetRequirementTiming.Receipt fuel context source initial result)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes))
    (backed : LiveTemplatesBacked initial)
    (origins : ActiveBinderCaptureOrigins initial (evidenceState.toTypedSource roots))
    (retained : result.state.nodes <+: evidenceState.nodes)
    (extension : finalized.substitution.SemanticallyExtends result.state.inference.substitution) :
    LiveBindersSafe receipt.binding.1.scheme.quantified result.state := by
  have readyOrigins := origins.congr_localBinders receipt.ready_binders
  have templates := templates_before receipt backed ready wellFormed formation canonical
  have readyExtension : finalized.substitution.SemanticallyExtends receipt.ready.inference.substitution := by
    rwa [receipt.inference_eq] at extension
  have retainedBinder : receipt.binding.1 ∈ (evidenceState.toTypedSource roots).initializedLetBinders := by
    unfold TypedSource.initializedLetBinders
    exact List.mem_flatMap.mpr ⟨_,retained.subset receipt.recorded,List.mem_singleton_self _⟩
  have live := allocate_generalized_live_from_finalizer resources initial.nextRequirement
    (receipt.ready.resolve receipt.value.type) receipt.name.value (some receipt.name.span) false
    (readyOrigins.withLocals receipt.locals) readyExtension templates retainedBinder
  have same : result.state.inference = receipt.binding.2.inference :=
    congrArg (fun result : StatementResult => result.state.inference) receipt.completed
  have binders : result.state.localBinders = receipt.binding.2.localBinders :=
    congrArg (fun result : StatementResult => result.state.localBinders) receipt.completed
  intro binder member
  exact (live binder (binders ▸ member)).transport (.of_substitution_eq (congrArg InferState.substitution same))

/-- Inference of this actual initializer avoids every currently active scheme
quantifier when the prefix has established their live privacy. -/
theorem value_avoids_active
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {initial : State} {result : StatementResult}
    (receipt : SourceInference.LocalLetRequirementTiming.Receipt fuel context source initial result)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (bound : ActiveQuantifiersBelowNext initial) (privateVars : ActiveQuantifiersPrivate initial)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes)) :
    Avoids (activeSchemeQuantifiers initial) (receipt.ready.resolve receipt.value.type) := by
  intro q occurs active
  obtain ⟨binder,member,quantified⟩ := List.mem_flatMap.mp active
  have allocatedLive : LiveBindersSafe binder.scheme.quantified initial.allocateStatementId.2 :=
    (privateVars binder member).transport rfl (.of_substitution_eq rfl)
  have expectedSafe : ∀ type ∈ receipt.expected, Safe binder.scheme.quantified initial.allocateStatementId.2 type := by
    intro type present
    exact safe_closed _ _ (receipt.annotationAccepted.variablesBelow 0 type present)
  have actual := inferExprFuel_private binder.scheme.quantified fuel context receipt.initializer receipt.expected
    initial.allocateStatementId.2 ready.allocateStatementId
    wellFormed
    (bound binder member) allocatedLive catalog formation canonical
    (receipt.annotationAccepted.variablesBelow _) expectedSafe _ receipt.child
  exact actual.2.1 q occurs quantified

end LocalLetRequirementTiming.Receipt
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActiveStatementPrivacy
/-! Every active binder's private variables are preserved through real statement
inference. Newly generalized binders obtain privacy from their exact receipt. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

theorem ActiveQuantifiersPrivate.inferStatementFuel
    {wholeContext : SourceInference.Context} {wholeReturn : Ty}
    {evidenceState : State} {roots : List NodeId} {finalized : SourceInference.Result}
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {expected : Ty} {initial : State} {result : StatementResult}
    (privateVars : ActiveQuantifiersPrivate initial)
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (bound : ActiveQuantifiersBelowNext initial)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes))
    (expectedClosed : expected.VariablesBelow 0)
    (backed : LiveTemplatesBacked initial)
    (origins : ActiveBinderCaptureOrigins initial (evidenceState.toTypedSource roots))
    (retained : result.state.nodes <+: evidenceState.nodes)
    (extension : finalized.substitution.SemanticallyExtends result.state.inference.substitution)
    (accepted : inferStatementFuel fuel context source expected initial = .ok result) :
    ActiveQuantifiersPrivate result.state := by
  intro binder member
  rcases inferStatementFuel_quantified_origin accepted binder member with old | empty | created
  · have actual := inferStatementFuel_private binder.scheme.quantified fuel context source expected initial
      ready wellFormed (bound binder old) (privateVars binder old) catalog formation canonical
      (expectedClosed.weaken (Nat.zero_le _)) (safe_closed _ _ expectedClosed) result accepted
    exact actual.2.2.1
  · rw [empty]
    exact liveBindersSafe_nil _
  · obtain ⟨childFuel,receipt,rfl⟩ := created
    exact LocalLetRequirementTiming.Receipt.active_privacy resources receipt ready wellFormed formation
      canonical backed origins retained extension

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActiveStatementPosition
/-! Actual earlier statements establish privacy for every active generalized
binder. The selected initializer receives those invariants from the same prefix. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

structure ActiveStatementPrivacyOccurrence (context : SourceInference.Context)
    (source : Syntax.Statement) (expected : Ty) (initial final evidenceState : State) (roots : List NodeId)
    extends BackedStatementPrivacyOccurrence context source expected initial final evidenceState roots where
  entryPrivate : ActiveQuantifiersPrivate entry
  entryBound : ActiveQuantifiersBelowNext entry

/-- The selected position follows the original list. The continuation is
constructed here from actual later calls, rather than assumed as a trace law. -/
theorem activeStatementPrivacyOccurrence_of_position
    {wholeContext : SourceInference.Context} {wholeReturn : Ty}
    {finalized : SourceInference.Result}
    {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.Statement}
    {expected : Ty} {initial evidenceState : State} {roots : List NodeId}
    {result : BlockResult} {index : Nat} {source : Syntax.Statement}
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (nodesBelow : initial.NodesBelowNextOccurrence)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes))
    (expectedBelow : expected.VariablesBelow initial.inference.next)
    (expectedClosed : expected.VariablesBelow 0)
    (privateVars : ActiveQuantifiersPrivate initial)
    (bound : ActiveQuantifiersBelowNext initial)
    (backed : LiveTemplatesBacked initial)
    (origins : ActiveBinderCaptureOrigins initial (evidenceState.toTypedSource roots))
    (retained : TypingSourceExtends (result.state.toTypedSource roots) (evidenceState.toTypedSource roots))
    (extension : finalized.substitution.SemanticallyExtends result.state.inference.substitution)
    (accepted : inferStatementsFuel fuel context sources expected initial = .ok result)
    (position : sources[index]? = some source) :
    Nonempty (ActiveStatementPrivacyOccurrence context source expected initial result.state evidenceState roots) := by
  induction fuel generalizing sources initial result index with
  | zero => simp [inferStatementsFuel] at accepted
  | succ fuel ih =>
    cases sources with
    | nil => simp at position
    | cons head rest =>
      cases headRun : inferStatementFuel fuel context head expected initial with
      | error error => simp [inferStatementsFuel,headRun,bind,Except.bind] at accepted
      | ok headResult =>
        have headProgress := inferStatementFuel_inferenceProperties ready formation canonical expectedBelow headRun
        have headWellFormed := (inferStatementFuel_direct_progress headRun).wellFormed wellFormed
        have headBelow := (inferStatementFuel_occurrenceBoundExtends headRun).nodesBelowNextOccurrence nodesBelow
        have afterExpected := expectedBelow.weaken headProgress.1.next_le
        cases rest with
        | nil =>
          have same : result.state = headResult.state := by
            simp only [inferStatementsFuel,headRun,bind,Except.bind,pure,Pure.pure,Except.pure,Except.ok.injEq] at accepted
            exact (congrArg BlockResult.state accepted).symm
          cases index with
          | zero =>
            simp only [List.getElem?_cons_zero,Option.some.injEq] at position
            subst source
            refine ⟨{
              fuel := fuel, entry := initial, result := headResult, accepted := headRun,
              ready := ready, before := .refl ready.solved,
              continuation := same.symm ▸ State.InferenceProgress.refl headProgress.2.1.solved,
              retained := same.symm ▸ List.prefix_refl _,
              resultReady := headProgress.2.1, resultWellFormed := headWellFormed,
              expectedBelow := afterExpected,
              entryWellFormed := wellFormed, entryTemplates := backed, entryOrigins := origins,
              entryPrivate := privateVars, entryBound := bound,
              privacy := ?_ }⟩
            intro protectedVars bound live safe
            rw [same]
            exact ⟨.refl _ _,fun row member fresh => False.elim (fresh member)⟩
          | succ index => simp at position
        | cons next remaining =>
          cases tailRun : inferStatementsFuel fuel context (next::remaining) expected headResult.state with
          | error error => simp [inferStatementsFuel,headRun,tailRun,bind,Except.bind] at accepted
          | ok tailResult =>
            have same : result.state = tailResult.state := by
              simp only [inferStatementsFuel,headRun,tailRun,bind,Except.bind,pure,Pure.pure,Except.pure,Except.ok.injEq] at accepted
              exact (congrArg BlockResult.state accepted).symm
            cases index with
            | zero =>
              simp only [List.getElem?_cons_zero,Option.some.injEq] at position
              subst source
              have tailProgress := inferStatementsFuel_inferenceProperties headProgress.2.1 formation canonical afterExpected tailRun
              refine ⟨{
                fuel := fuel, entry := initial, result := headResult, accepted := headRun,
                ready := ready, before := .refl ready.solved,
                continuation := same.symm ▸ tailProgress.1,
                retained := same.symm ▸ inferStatementsFuel_preserves_nodesPrefix tailRun
                  (List.prefix_refl _) headBelow (Nat.le_refl _),
                resultReady := headProgress.2.1, resultWellFormed := headWellFormed,
                expectedBelow := afterExpected,
                entryWellFormed := wellFormed, entryTemplates := backed, entryOrigins := origins,
                entryPrivate := privateVars, entryBound := bound,
                privacy := ?_ }⟩
              intro protectedVars bound live safe
              rw [same]
              have actual := inferStatementsFuel_private protectedVars fuel context (next::remaining) expected headResult.state
                headProgress.2.1 headWellFormed bound live catalog formation canonical afterExpected safe tailResult tailRun
              exact ⟨actual.1,actual.2.2.2⟩
            | succ index =>
              have restPosition : (next::remaining)[index]? = some source := position
              have headBacked := backed.inferStatementFuel ready formation canonical expectedBelow headRun
              have tailToEvidence : TypingSourceExtends (tailResult.state.toTypedSource roots)
                  (evidenceState.toTypedSource roots) := by
                rwa [same] at retained
              have headToEvidence := (inferStatementsFuel_success_typingSourceExtends tailRun headBelow roots).trans tailToEvidence
              have headOrigins := inferStatementFuel_captureOrigins headRun origins headToEvidence
              have tailProgress := inferStatementsFuel_inferenceProperties headProgress.2.1 formation canonical afterExpected tailRun
              have tailExtension : finalized.substitution.SemanticallyExtends tailResult.state.inference.substitution := by
                rwa [same] at extension
              have headExtension := Substitution.SemanticallyExtends.trans tailExtension tailProgress.1.substitution_extends
              have headPrivate := privateVars.inferStatementFuel resources ready wellFormed bound catalog formation canonical
                expectedClosed backed origins headToEvidence.nodes_prefix headExtension headRun
              have headBound := activeQuantifiersBelowNext_inferStatementFuel bound ready formation canonical expectedBelow headRun
              obtain ⟨found⟩ := ih headProgress.2.1 headWellFormed headBelow afterExpected
                headPrivate headBound headBacked headOrigins tailToEvidence tailExtension tailRun restPosition
              refine ⟨{
                fuel := found.fuel, entry := found.entry, result := found.result, accepted := found.accepted,
                ready := found.ready, before := headProgress.1.trans found.before,
                continuation := same.symm ▸ found.continuation,
                retained := same.symm ▸ found.retained,
                resultReady := found.resultReady, resultWellFormed := found.resultWellFormed,
                expectedBelow := found.expectedBelow,
                entryWellFormed := found.entryWellFormed, entryTemplates := found.entryTemplates,
                entryOrigins := found.entryOrigins,
                entryPrivate := found.entryPrivate, entryBound := found.entryBound,
                privacy := ?_ }⟩
              intro protectedVars bound live safe
              rw [same]
              exact found.privacy protectedVars bound live safe

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActiveBlockState
/-! A completed actual statement list carries active scheme privacy and
quantifier bounds into the next restored branch or loop header. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

theorem activeState_inferStatementsFuel
    {wholeContext : SourceInference.Context} {wholeReturn : Ty}
    {evidenceState : State} {roots : List NodeId} {finalized : SourceInference.Result}
    {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.Statement}
    {expected : Ty} {initial : State} {result : BlockResult}
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (nodesBelow : initial.NodesBelowNextOccurrence)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (expectedClosed : expected.VariablesBelow 0)
    (privacy : ActiveQuantifiersPrivate initial)
    (bound : ActiveQuantifiersBelowNext initial)
    (backed : LiveTemplatesBacked initial)
    (origins : ActiveBinderCaptureOrigins initial (evidenceState.toTypedSource roots))
    (retained : TypingSourceExtends
      (result.state.toTypedSource roots) (evidenceState.toTypedSource roots))
    (extension : finalized.substitution.SemanticallyExtends result.state.inference.substitution)
    (accepted : inferStatementsFuel fuel context sources expected initial = .ok result) :
    ActiveQuantifiersPrivate result.state ∧ ActiveQuantifiersBelowNext result.state := by
  induction fuel generalizing sources initial result with
  | zero => simp [inferStatementsFuel] at accepted
  | succ fuel ih =>
    have expectedBelow := expectedClosed.weaken (Nat.zero_le initial.inference.next)
    cases sources with
    | nil =>
      simp [inferStatementsFuel] at accepted
      subst result
      exact ⟨privacy, bound⟩
    | cons head rest =>
      cases rest with
      | nil =>
        obtain ⟨statement, headRun, completed⟩ := inferStatementsFuel_success_singleton_facts accepted
        have same : result.state = statement.state := by
          simpa only using congrArg BlockResult.state completed
        rw [same] at retained extension ⊢
        exact ⟨privacy.inferStatementFuel resources ready wellFormed bound catalog formation canonical
          expectedClosed backed origins retained.nodes_prefix extension headRun,
          activeQuantifiersBelowNext_inferStatementFuel bound ready formation canonical expectedBelow headRun⟩
      | cons next tail =>
        obtain ⟨statement, remaining, headRun, tailRun, completed⟩ := inferStatementsFuel_success_cons_facts accepted
        have same : result.state = remaining.state := by
          simpa only using congrArg BlockResult.state completed
        rw [same] at retained extension ⊢
        have headProperties := inferStatementFuel_inferenceProperties ready formation canonical expectedBelow headRun
        have headWellFormed := (inferStatementFuel_direct_progress headRun).wellFormed wellFormed
        have headBelow := (inferStatementFuel_occurrenceBoundExtends headRun).nodesBelowNextOccurrence nodesBelow
        have tailProperties := inferStatementsFuel_inferenceProperties headProperties.2.1 formation canonical
          (expectedBelow.weaken headProperties.1.next_le) tailRun
        have headRetained :=
          (inferStatementsFuel_success_typingSourceExtends tailRun headBelow roots).trans retained
        have headExtension := Substitution.SemanticallyExtends.trans extension tailProperties.1.substitution_extends
        have headPrivacy := privacy.inferStatementFuel resources ready wellFormed bound catalog formation canonical
          expectedClosed backed origins headRetained.nodes_prefix headExtension headRun
        have headBound := activeQuantifiersBelowNext_inferStatementFuel bound ready formation canonical expectedBelow headRun
        exact ih headProperties.2.1 headWellFormed headBelow headPrivacy headBound
          (backed.inferStatementFuel ready formation canonical expectedBelow headRun)
          (inferStatementFuel_captureOrigins headRun origins headRetained) retained extension tailRun

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceLiveTemplateHeaderBacking
/-! The same raw ledger witnesses survive actual for-header declarations and
their ordered continuation. Header locals are retained until the loop restores
its enclosing lexical scope. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

theorem LocalHeaderRequirementTiming.Receipt.templates_ready
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State}
    (receipt : SourceInference.LocalHeaderRequirementTiming.Receipt fuel context source initial result)
    (backed : LiveTemplatesBacked initial) (ready : initial.InferenceReady)
    (validated : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes)) :
    LiveTemplatesBacked receipt.ready :=
  backed.inferExprFuel ready validated canonical
    (receipt.annotationAccepted.variablesBelow _) receipt.child

theorem LocalHeaderRequirementTiming.Receipt.templates_result
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State}
    (receipt : SourceInference.LocalHeaderRequirementTiming.Receipt fuel context source initial result)
    (backed : LiveTemplatesBacked initial) (ready : initial.InferenceReady)
    (validated : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes)) :
    LiveTemplatesBacked result.2 := by
  have readyBacked := LocalHeaderRequirementTiming.Receipt.templates_ready receipt backed ready validated canonical
  have properties := receipt.initializer_inference ready validated canonical
  rw [receipt.completed]
  exact readyBacked.generalized properties.2.1.solved receipt.locals initial.nextRequirement
    (receipt.ready.resolve receipt.value.type) receipt.name.value (some receipt.name.span) false

theorem LocalHeaderRequirementTiming.Receipt.templates_before
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State}
    (receipt : SourceInference.LocalHeaderRequirementTiming.Receipt fuel context source initial result)
    (backed : LiveTemplatesBacked initial) (ready : initial.InferenceReady)
    (wellFormed : initial.RequirementsWellFormed)
    (validated : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes)) :
    ∀ binder ∈ receipt.ready.localBinders, ∀ requirement ∈ binder.schemeRequirements,
      ∃ raw ∈ receipt.ready.requirements.take initial.nextRequirement,
        applyPredicate receipt.ready requirement.predicate = applyPredicate receipt.ready raw.predicate := by
  have properties := receipt.initializer_inference ready validated canonical
  have readyWellFormed := (inferExprFuel_direct_progress receipt.child).wellFormed wellFormed
  have rows := inferExprFuel_requirements_subset receipt.child
  intro binder member requirement retained
  obtain ⟨raw, present, same⟩ := backed binder (receipt.ready_binders ▸ member) requirement retained
  refine ⟨raw, (State.mem_take_prior_requirements_iff initial receipt.ready wellFormed readyWellFormed
    rows raw).mpr present, ?_⟩
  have transported := congrArg (applyPredicate receipt.ready) same
  simpa only [applyPredicate,TypedTraitResolution.applySubstitution_semanticallyExtends
    properties.1.substitution_extends] using transported

private theorem header_nonlet_binders
    {fuel : Nat} {context : SourceInference.Context} {item : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State}
    (notLet : ∀ name annotation initializer, item.value ≠ .letDecl name annotation initializer)
    (accepted : Detail.inferForItemFuel fuel context item initial = .ok result) :
    result.2.localBinders = initial.localBinders := by
  cases fuel with
  | zero => simp [Detail.inferForItemFuel] at accepted
  | succ fuel =>
    cases form : item.value with
    | letDecl name annotation initializer => exact (notLet _ _ _ form).elim
    | expression source =>
      unfold Detail.inferForItemFuel at accepted
      simp only [form,bind,Except.bind] at accepted
      cases child : Detail.inferExprFuel fuel context source none initial with
      | error error => simp [child] at accepted
      | ok pair =>
        rcases pair with ⟨value,state⟩
        simp only [child,pure,Pure.pure,Except.pure,Except.ok.injEq] at accepted
        subst result
        exact congrArg LexicalScope.binders (inferExprFuel_success_lexicalScope_eq child)
    | assignValue target operator value =>
      unfold Detail.inferForItemFuel at accepted
      simp only [form,bind,Except.bind] at accepted
      cases child : Detail.inferAssignedValueFuel fuel context target operator.value value initial with
      | error error => simp [child] at accepted
      | ok pair =>
        rcases pair with ⟨assignment,value,state⟩
        simp only [child,pure,Pure.pure,Except.pure,Except.ok.injEq] at accepted
        subst result
        exact congrArg LexicalScope.binders (inferAssignedValueFuel_success_lexicalScope_eq child)
    | assignBitNot target operator =>
      unfold Detail.inferForItemFuel at accepted
      simp only [form,bind,Except.bind] at accepted
      cases child : Detail.inferPlaceFuel fuel context target initial with
      | error error => simp [child] at accepted
      | ok pair =>
        rcases pair with ⟨place,state⟩
        simp only [child] at accepted
        cases unified : Detail.unify state place.type .word with
        | error error => simp [unified] at accepted
        | ok final =>
          simp only [unified,pure,Pure.pure,Except.pure,Except.ok.injEq] at accepted
          subst result
          have same : final.localBinders = state.localBinders := by
            unfold Detail.unify at unified
            cases inference : liftUnification (state.inference.unify place.type .word) with
            | error error => simp [inference,bind,Except.bind] at unified
            | ok solved =>
              simp only [inference,bind,Except.bind,pure,Pure.pure,Except.pure] at unified
              cases unified
              rfl
          exact same.trans (congrArg LexicalScope.binders (inferPlaceFuel_success_lexicalScope_eq child))

theorem LiveTemplatesBacked.inferForItemFuel
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State}
    (backed : LiveTemplatesBacked initial) (ready : initial.InferenceReady)
    (validated : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (accepted : Detail.inferForItemFuel fuel context source initial = .ok result) :
    LiveTemplatesBacked result.2 := by
  cases fuel with
  | zero => simp [Detail.inferForItemFuel] at accepted
  | succ fuel =>
    by_cases isLet : ∃ name annotation initializer, source.value = .letDecl name annotation initializer
    · obtain ⟨name,annotation,initializer,form⟩ := isLet
      cases initializer with
      | some initializer =>
        obtain ⟨receipt⟩ := SourceInference.LocalHeaderRequirementTiming.of_initialized_accepted form accepted
        exact LocalHeaderRequirementTiming.Receipt.templates_result receipt backed ready validated canonical
      | none =>
        cases annotation with
        | none =>
          simp [Detail.inferForItemFuel,form] at accepted
          change (Except.error (.missingInitializer name.value) : Except SourceInference.Error
            (ForItemForm × State)) = .ok result at accepted
          cases accepted
        | some annotation =>
          unfold Detail.inferForItemFuel at accepted
          simp only [form,bind,Except.bind] at accepted
          cases resolved : resolveSourceType context annotation with
          | error error => simp [resolved] at accepted
          | ok type =>
            simp only [resolved,pure,Pure.pure,Except.pure,Except.ok.injEq] at accepted
            subst result
            exact backed.generalized ready.solved _ _ _ _ _ _
    · have same := header_nonlet_binders (by
        intro name annotation initializer form
        exact isLet ⟨name,annotation,initializer,form⟩) accepted
      have progress := inferForItemFuel_inferenceProperties ready validated canonical accepted
      exact backed.transport (by intro _ member; exact same ▸ member)
        (inferForItemFuel_requirements_subset accepted) progress.1.substitution_extends

theorem LiveTemplatesBacked.inferForItemsFuel
    {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.ForItem}
    {initial : State} {result : InferredForItems}
    (backed : LiveTemplatesBacked initial) (ready : initial.InferenceReady)
    (validated : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (accepted : Detail.inferForItemsFuel fuel context sources initial = .ok result) :
    LiveTemplatesBacked result.state := by
  induction sources generalizing initial result with
  | nil =>
    simp [Detail.inferForItemsFuel] at accepted
    subst result
    exact backed
  | cons head tail ih =>
    unfold Detail.inferForItemsFuel at accepted
    cases headRun : Detail.inferForItemFuel fuel context head initial with
    | error error => simp [headRun,bind,Except.bind] at accepted
    | ok pair =>
      rcases pair with ⟨item,state⟩
      simp only [headRun,bind,Except.bind] at accepted
      cases tailRun : Detail.inferForItemsFuel fuel context tail state with
      | error error => simp [tailRun] at accepted
      | ok rest =>
        simp only [tailRun,pure,Pure.pure,Except.pure,Except.ok.injEq] at accepted
        subst result
        have properties := inferForItemFuel_inferenceProperties ready validated canonical headRun
        exact ih (result := rest) (backed.inferForItemFuel ready validated canonical headRun)
          properties.2 tailRun

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActiveHeaderPrivacy
/-! Header privacy uses the actual initialized item returned by inference.
The enclosing for node supplies its retained initialized-binder inventory. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

/-- A surviving header binder is entering, monomorphic, or the actual
initialized binder from this accepted header call. -/
theorem inferForItemFuel_quantified_origin
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State}
    (accepted : inferForItemFuel fuel context source initial = .ok result) :
    ∀ binder ∈ result.2.localBinders,
      binder ∈ initial.localBinders ∨ binder.scheme.quantified = [] ∨
        ∃ childFuel, ∃ receipt : SourceInference.LocalHeaderRequirementTiming.Receipt childFuel context source initial result,
          binder = receipt.binding.1 := by
  cases fuel with
  | zero => simp [inferForItemFuel] at accepted
  | succ fuel =>
    by_cases isLet : ∃ name annotation initializer, source.value = .letDecl name annotation initializer
    · obtain ⟨name,annotation,initializer,form⟩ := isLet
      cases initializer with
      | some initializer =>
        obtain ⟨receipt⟩ := SourceInference.LocalHeaderRequirementTiming.of_initialized_accepted form accepted
        intro binder member
        rw [receipt.result_binders] at member
        rcases List.mem_cons.mp member with current | entering
        · exact .inr (.inr ⟨fuel,receipt,current⟩)
        · exact .inl entering
      | none =>
        cases annotation with
        | none =>
          simp [inferForItemFuel,form] at accepted
          change (Except.error (.missingInitializer name.value) : Except SourceInference.Error
            (ForItemForm × State)) = .ok result at accepted
          cases accepted
        | some annotation =>
          unfold inferForItemFuel at accepted
          simp only [form,bind,Except.bind] at accepted
          cases resolved : resolveSourceType context annotation with
          | error error => simp [resolved] at accepted
          | ok type =>
            simp only [resolved,pure,Pure.pure,Except.pure,Except.ok.injEq] at accepted
            subst result
            have closed : type.freeVariables = [] := by
              apply List.eq_nil_iff_forall_not_mem.mpr
              intro q member
              exact (Nat.not_lt_zero _) (resolveSourceType_success_variablesBelow resolved 0 q member)
            have resolveEq : initial.resolve type = type :=
              resolveSourceType_success_apply_eq_self initial.inference.substitution resolved
            intro binder member
            change binder ∈ _ :: initial.localBinders at member
            rcases List.mem_cons.mp member with current | entering
            · right; left
              rw [current]
              change (generalizeValue initial _ initial.nextRequirement (initial.resolve type)).scheme.quantified = []
              rw [generalizeValue_scheme_quantified,resolveEq,closed]
              rfl
            · exact .inl entering
    · have same := header_nonlet_binders (by
        intro name annotation initializer form
        exact isLet ⟨name,annotation,initializer,form⟩) accepted
      intro binder member
      exact .inl (same ▸ member)

/-- Every retained active quantifier is below the actual returned allocator. -/
theorem activeQuantifiersBelowNext_inferForItemFuel
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State}
    (bound : ActiveQuantifiersBelowNext initial) (ready : initial.InferenceReady)
    (validated : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes))
    (accepted : inferForItemFuel fuel context source initial = .ok result) :
    ActiveQuantifiersBelowNext result.2 := by
  have progress := inferForItemFuel_inferenceProperties ready validated canonical accepted
  intro binder member q quantified
  rcases inferForItemFuel_quantified_origin accepted binder member with entering | mono | initialized
  · exact Nat.lt_of_lt_of_le (bound binder entering q quantified) progress.1.next_le
  · simp [mono] at quantified
  · obtain ⟨childFuel,receipt,rfl⟩ := initialized
    have properties := receipt.initializer_inference ready validated canonical
    have valueBelow := properties.2.1.solved.variablesBelow_apply properties.2.2
    have newBound := activeQuantifiersBelowNext_generalizeValue receipt.ready receipt.locals
      initial.nextRequirement (receipt.ready.resolve receipt.value.type) valueBelow q quantified
    rw [receipt.inference_eq]
    exact newBound

namespace LocalHeaderRequirementTiming.Receipt

/-- The recorded enclosing for statement provides this actual header binder's
capture check, while old templates come from the real entering ledger. -/
theorem active_privacy
    {wholeContext : SourceInference.Context} {wholeReturn : Ty}
    {evidenceState : State} {roots : List NodeId} {finalized : SourceInference.Result}
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State}
    (receipt : SourceInference.LocalHeaderRequirementTiming.Receipt fuel context source initial result)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes))
    (backed : LiveTemplatesBacked initial)
    (origins : ActiveBinderCaptureOrigins initial (evidenceState.toTypedSource roots))
    (retained : receipt.binding.1 ∈ (evidenceState.toTypedSource roots).initializedLetBinders)
    (extension : finalized.substitution.SemanticallyExtends result.2.inference.substitution) :
    LiveBindersSafe receipt.binding.1.scheme.quantified result.2 := by
  have readyOrigins := origins.congr_localBinders receipt.ready_binders
  have templates := templates_before receipt backed ready wellFormed formation canonical
  have readyExtension : finalized.substitution.SemanticallyExtends receipt.ready.inference.substitution := by
    rwa [receipt.inference_eq] at extension
  have live := allocate_generalized_live_from_finalizer resources initial.nextRequirement
    (receipt.ready.resolve receipt.value.type) receipt.name.value (some receipt.name.span) false
    (readyOrigins.withLocals receipt.locals) readyExtension templates retained
  have same : result.2.inference = receipt.binding.2.inference :=
    congrArg (fun result : ForItemForm × State => result.2.inference) receipt.completed
  have binders : result.2.localBinders = receipt.binding.2.localBinders :=
    congrArg (fun result : ForItemForm × State => result.2.localBinders) receipt.completed
  intro binder member
  exact (live binder (binders ▸ member)).transport (.of_substitution_eq (congrArg InferState.substitution same))

/-- The actual header initializer avoids every previously active quantifier. -/
theorem value_avoids_active
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State}
    (receipt : SourceInference.LocalHeaderRequirementTiming.Receipt fuel context source initial result)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (bound : ActiveQuantifiersBelowNext initial) (privateVars : ActiveQuantifiersPrivate initial)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes)) :
    Avoids (activeSchemeQuantifiers initial) (receipt.ready.resolve receipt.value.type) := by
  intro q occurs active
  obtain ⟨binder,member,quantified⟩ := List.mem_flatMap.mp active
  have expectedSafe : ∀ type ∈ receipt.expected, Safe binder.scheme.quantified initial type := by
    intro type present
    exact safe_closed _ _ (receipt.annotationAccepted.variablesBelow 0 type present)
  have actual := inferExprFuel_private binder.scheme.quantified fuel context receipt.initializer receipt.expected
    initial ready wellFormed (bound binder member) (privateVars binder member) catalog formation canonical
    (receipt.annotationAccepted.variablesBelow _) expectedSafe _ receipt.child
  exact actual.2.1 q occurs quantified

end LocalHeaderRequirementTiming.Receipt

/-- The actual returned item supplies new-binder origins; incoming binders
retain their existing final-source origin. -/
theorem activeBinderCaptureOrigins_inferForItemFuel
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State} {whole : TypedSource}
    (origins : ActiveBinderCaptureOrigins initial whole)
    (retained : result.1.initializedLetBinders ⊆ whole.initializedLetBinders)
    (accepted : inferForItemFuel fuel context source initial = .ok result) :
    ActiveBinderCaptureOrigins result.2 whole := by
  constructor
  intro binder member
  rcases inferForItemFuel_quantified_origin accepted binder member with old | empty | created
  · exact origins.origin binder old
  · exact .inl empty
  · obtain ⟨childFuel,receipt,rfl⟩ := created
    right
    apply retained
    rw [receipt.recorded]
    exact List.mem_singleton_self _

/-- Old quantifiers follow full inference privacy; the actual new scheme
uses its retained finalizer capture check. -/
theorem ActiveQuantifiersPrivate.inferForItemFuel
    {wholeContext : SourceInference.Context} {wholeReturn : Ty}
    {evidenceState : State} {roots : List NodeId} {finalized : SourceInference.Result}
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State}
    (privateVars : ActiveQuantifiersPrivate initial)
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (bound : ActiveQuantifiersBelowNext initial)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes))
    (backed : LiveTemplatesBacked initial)
    (origins : ActiveBinderCaptureOrigins initial (evidenceState.toTypedSource roots))
    (retained : result.1.initializedLetBinders ⊆ (evidenceState.toTypedSource roots).initializedLetBinders)
    (extension : finalized.substitution.SemanticallyExtends result.2.inference.substitution)
    (accepted : inferForItemFuel fuel context source initial = .ok result) :
    ActiveQuantifiersPrivate result.2 := by
  intro binder member
  rcases inferForItemFuel_quantified_origin accepted binder member with old | empty | created
  · have actual := inferForItemFuel_private binder.scheme.quantified fuel context source initial
      ready wellFormed (bound binder old) (privateVars binder old) catalog formation canonical result accepted
    exact actual.2.1
  · rw [empty]
    exact liveBindersSafe_nil _
  · obtain ⟨childFuel,receipt,rfl⟩ := created
    apply LocalHeaderRequirementTiming.Receipt.active_privacy resources receipt ready wellFormed formation
      canonical backed origins _ extension
    apply retained
    rw [receipt.recorded]
    exact List.mem_singleton_self _

/-- A header item keeps every entering lexical binder. -/
theorem inferForItemFuel_binders_subset
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State}
    (accepted : inferForItemFuel fuel context source initial = .ok result) :
    initial.localBinders ⊆ result.2.localBinders := by
  cases fuel with
  | zero => simp [inferForItemFuel] at accepted
  | succ fuel =>
    by_cases isLet : ∃ name annotation initializer, source.value = .letDecl name annotation initializer
    · obtain ⟨name,annotation,initializer,form⟩ := isLet
      cases initializer with
      | some initializer =>
        obtain ⟨receipt⟩ := SourceInference.LocalHeaderRequirementTiming.of_initialized_accepted form accepted
        rw [receipt.result_binders]
        exact List.subset_cons_self _ _
      | none =>
        cases annotation with
        | none =>
          simp [inferForItemFuel,form] at accepted
          change (Except.error (.missingInitializer name.value) : Except SourceInference.Error
            (ForItemForm × State)) = .ok result at accepted
          cases accepted
        | some annotation =>
          unfold inferForItemFuel at accepted
          simp only [form,bind,Except.bind] at accepted
          cases resolved : resolveSourceType context annotation with
          | error error => simp [resolved] at accepted
          | ok type =>
            simp only [resolved,pure,Pure.pure,Except.pure,Except.ok.injEq] at accepted
            subst result
            exact List.subset_cons_self _ _
    · have same := header_nonlet_binders (by
        intro name annotation initializer form
        exact isLet ⟨name,annotation,initializer,form⟩) accepted
      rw [same]
      exact List.Subset.refl _

/-- The actual ordered header list keeps all entering binders. -/
theorem inferForItemsFuel_binders_subset
    {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.ForItem}
    {initial : State} {result : InferredForItems}
    (accepted : inferForItemsFuel fuel context sources initial = .ok result) :
    initial.localBinders ⊆ result.state.localBinders := by
  induction sources generalizing initial result with
  | nil =>
    simp [inferForItemsFuel] at accepted
    subst result
    exact List.Subset.refl _
  | cons head tail ih =>
    cases headRun : inferForItemFuel fuel context head initial with
    | error error => simp [inferForItemsFuel,headRun,bind,Except.bind] at accepted
    | ok pair =>
      rcases pair with ⟨item,state⟩
      cases tailRun : inferForItemsFuel fuel context tail state with
      | error error => simp [inferForItemsFuel,headRun,tailRun,bind,Except.bind] at accepted
      | ok rest =>
        simp only [inferForItemsFuel,headRun,tailRun,bind,Except.bind,pure,Pure.pure,Except.pure,Except.ok.injEq] at accepted
        subst result
        exact (inferForItemFuel_binders_subset headRun).trans (ih (result := rest) tailRun)

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActiveHeaderSequence
/-! Ordered header inference derives each entering state from its actual prefix
and preserves privacy through the actual remaining header items. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

structure ActiveHeaderState (state : State) (whole : TypedSource) : Prop where
  privateVars : ActiveQuantifiersPrivate state
  bound : ActiveQuantifiersBelowNext state
  backed : LiveTemplatesBacked state
  origins : ActiveBinderCaptureOrigins state whole

theorem ActiveHeaderState.inferForItemsFuel
    {wholeContext : SourceInference.Context} {wholeReturn : Ty}
    {evidenceState : State} {roots : List NodeId} {finalized : SourceInference.Result}
    {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.ForItem}
    {initial : State} {result : InferredForItems}
    (active : ActiveHeaderState initial (evidenceState.toTypedSource roots))
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes))
    (retained : result.items.flatMap ForItemForm.initializedLetBinders ⊆
      (evidenceState.toTypedSource roots).initializedLetBinders)
    (extension : finalized.substitution.SemanticallyExtends result.state.inference.substitution)
    (accepted : Detail.inferForItemsFuel fuel context sources initial = .ok result) :
    ActiveHeaderState result.state (evidenceState.toTypedSource roots) := by
  induction sources generalizing initial result with
  | nil =>
    simp [Detail.inferForItemsFuel] at accepted
    subst result
    exact active
  | cons head tail ih =>
    cases headRun : inferForItemFuel fuel context head initial with
    | error error => simp [Detail.inferForItemsFuel,headRun,bind,Except.bind] at accepted
    | ok pair =>
      rcases pair with ⟨item,state⟩
      cases tailRun : Detail.inferForItemsFuel fuel context tail state with
      | error error => simp [Detail.inferForItemsFuel,headRun,tailRun,bind,Except.bind] at accepted
      | ok rest =>
        simp only [Detail.inferForItemsFuel,headRun,tailRun,bind,Except.bind,pure,Pure.pure,Except.pure,Except.ok.injEq] at accepted
        subst result
        have headProperties := inferForItemFuel_inferenceProperties ready formation canonical headRun
        have tailProperties := inferForItemsFuel_inferenceProperties headProperties.2 formation canonical tailRun
        have headRetained : item.initializedLetBinders ⊆ (evidenceState.toTypedSource roots).initializedLetBinders := by
          intro binder member
          exact retained (List.mem_append_left _ member)
        have tailRetained : rest.items.flatMap ForItemForm.initializedLetBinders ⊆
            (evidenceState.toTypedSource roots).initializedLetBinders := by
          intro binder member
          exact retained (List.mem_append_right _ member)
        have headExtension := Substitution.SemanticallyExtends.trans extension tailProperties.1.substitution_extends
        have headActive : ActiveHeaderState state (evidenceState.toTypedSource roots) := {
          privateVars := active.privateVars.inferForItemFuel resources ready wellFormed active.bound catalog
            formation canonical active.backed active.origins headRetained headExtension headRun
          bound := activeQuantifiersBelowNext_inferForItemFuel active.bound ready formation canonical headRun
          backed := active.backed.inferForItemFuel ready formation canonical headRun
          origins := activeBinderCaptureOrigins_inferForItemFuel active.origins headRetained headRun }
        exact ih (result := rest) headActive headProperties.2
          ((inferForItemFuel_direct_progress headRun).wellFormed wellFormed) tailRetained extension tailRun

structure HeaderPrivacyOccurrence (fuel : Nat) (context : SourceInference.Context)
    (source : Syntax.ForItem) (initial final evidenceState : State) (roots : List NodeId)
    (forms : List ForItemForm)
    extends ForItemInferenceContinuation.Occurrence fuel context source initial final forms where
  entryWellFormed : entry.RequirementsWellFormed
  entryNodesBelow : entry.NodesBelowNextOccurrence
  entryActive : ActiveHeaderState entry (evidenceState.toTypedSource roots)
  resultReady : result.2.InferenceReady
  resultWellFormed : result.2.RequirementsWellFormed
  resultNodesBelow : result.2.NodesBelowNextOccurrence
  retainedNodes : result.2.nodes <+: final.nodes
  privacy : ∀ protectedVars,
    (∀ v ∈ protectedVars, v.index < result.2.inference.next) →
    LiveBindersSafe protectedVars result.2 →
      SafeTransport protectedVars result.2 final ∧ LiveBindersSafe protectedVars final ∧
        ∀ row ∈ final.requirements, row ∉ result.2.requirements → PredicateSafe protectedVars final row.predicate

/-- The same syntactic index selects one actual header call, retaining its
entering active schemes and its real suffix continuation. -/
theorem headerPrivacyOccurrence_of_position
    {wholeContext : SourceInference.Context} {wholeReturn : Ty}
    {evidenceState : State} {roots : List NodeId} {finalized : SourceInference.Result}
    {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.ForItem}
    {initial : State} {result : InferredForItems} {index : Nat} {source : Syntax.ForItem}
    (active : ActiveHeaderState initial (evidenceState.toTypedSource roots))
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (nodesBelow : initial.NodesBelowNextOccurrence)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes))
    (retained : result.items.flatMap ForItemForm.initializedLetBinders ⊆
      (evidenceState.toTypedSource roots).initializedLetBinders)
    (extension : finalized.substitution.SemanticallyExtends result.state.inference.substitution)
    (accepted : Detail.inferForItemsFuel fuel context sources initial = .ok result)
    (position : sources[index]? = some source) :
    Nonempty (HeaderPrivacyOccurrence fuel context source initial result.state evidenceState roots result.items) := by
  induction sources generalizing initial result index with
  | nil => simp at position
  | cons head tail ih =>
    cases headRun : inferForItemFuel fuel context head initial with
    | error error => simp [Detail.inferForItemsFuel,headRun,bind,Except.bind] at accepted
    | ok pair =>
      rcases pair with ⟨item,state⟩
      cases tailRun : Detail.inferForItemsFuel fuel context tail state with
      | error error => simp [Detail.inferForItemsFuel,headRun,tailRun,bind,Except.bind] at accepted
      | ok rest =>
        simp only [Detail.inferForItemsFuel,headRun,tailRun,bind,Except.bind,pure,Pure.pure,Except.pure,Except.ok.injEq] at accepted
        subst result
        have headProperties := inferForItemFuel_inferenceProperties ready formation canonical headRun
        have tailProperties := inferForItemsFuel_inferenceProperties headProperties.2 formation canonical tailRun
        have headWellFormed := (inferForItemFuel_direct_progress headRun).wellFormed wellFormed
        have headNodesBelow := (inferForItemFuel_occurrenceBoundExtends headRun).nodesBelowNextOccurrence nodesBelow
        cases index with
        | zero =>
          simp only [List.getElem?_cons_zero,Option.some.injEq] at position
          subst source
          refine ⟨{
            entry := initial, result := (item,state), accepted := headRun, ready := ready,
            before := .refl ready.solved, continuation := tailProperties.1,
            retained := List.mem_cons_self, entryWellFormed := wellFormed, entryNodesBelow := nodesBelow,
            entryActive := active, resultReady := headProperties.2, resultWellFormed := headWellFormed,
            resultNodesBelow := headNodesBelow,
            retainedNodes := inferForItemsFuel_preserves_nodesPrefix (result := rest) tailRun (List.prefix_refl _) headNodesBelow (Nat.le_refl _),
            privacy := ?_ }⟩
          intro protectedVars bound live
          exact inferForItemsFuel_private protectedVars fuel context tail state headProperties.2 headWellFormed
            bound live catalog formation canonical rest tailRun
        | succ index =>
          have headRetained : item.initializedLetBinders ⊆ (evidenceState.toTypedSource roots).initializedLetBinders := by
            intro binder member
            exact retained (List.mem_append_left _ member)
          have tailRetained : rest.items.flatMap ForItemForm.initializedLetBinders ⊆
              (evidenceState.toTypedSource roots).initializedLetBinders := by
            intro binder member
            exact retained (List.mem_append_right _ member)
          have headExtension := Substitution.SemanticallyExtends.trans extension tailProperties.1.substitution_extends
          have headActive : ActiveHeaderState state (evidenceState.toTypedSource roots) := {
            privateVars := active.privateVars.inferForItemFuel resources ready wellFormed active.bound catalog
              formation canonical active.backed active.origins headRetained headExtension headRun
            bound := activeQuantifiersBelowNext_inferForItemFuel active.bound ready formation canonical headRun
            backed := active.backed.inferForItemFuel ready formation canonical headRun
            origins := activeBinderCaptureOrigins_inferForItemFuel active.origins headRetained headRun }
          obtain ⟨found⟩ := ih headActive headProperties.2 headWellFormed headNodesBelow
            tailRetained extension tailRun position
          exact ⟨{
            entry := found.entry, result := found.result, accepted := found.accepted, ready := found.ready,
            before := headProperties.1.trans found.before, continuation := found.continuation,
            retained := List.mem_cons_of_mem _ found.retained, entryWellFormed := found.entryWellFormed,
            entryNodesBelow := found.entryNodesBelow, entryActive := found.entryActive,
            resultReady := found.resultReady, resultWellFormed := found.resultWellFormed,
            resultNodesBelow := found.resultNodesBelow, retainedNodes := found.retainedNodes,
            privacy := found.privacy }⟩

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferencePrivacyScopeRetention
/-! Actual statement and header calls retain entering binders. This supplies
scope restoration with real membership in the completed child state. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

theorem inferStatementFuel_binders_subset
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {expected : Ty} {initial : State} {result : StatementResult}
    (accepted : inferStatementFuel fuel context source expected initial = .ok result) :
    initial.localBinders ⊆ result.state.localBinders := by
  cases fuel with
  | zero => simp [inferStatementFuel] at accepted
  | succ fuel =>
    by_cases isLet : ∃ name annotation initializer, source.value = .letDecl name annotation initializer
    · obtain ⟨name,annotation,initializer,form⟩ := isLet
      cases initializer with
      | some initializer =>
        obtain ⟨receipt⟩ := SourceInference.LocalLetRequirementTiming.of_initialized_accepted form accepted
        rw [receipt.result_binders]
        exact List.subset_cons_self _ _
      | none =>
        cases annotation with
        | none =>
          simp [inferStatementFuel,form] at accepted
          change (Except.error (.missingInitializer name.value) : Except SourceInference.Error StatementResult) = .ok result at accepted
          cases accepted
        | some annotation =>
          obtain ⟨type,locals,valueType,generalized,binding,_,_,_,_,allocated,completed,_⟩ :=
            inferStatementFuel_success_letAnnotatedUninitialized_facts form rfl accepted
          rw [completed]
          have same := (congrArg (fun pair : TypedBinder × State => pair.2.localBinders) allocated).symm
          change initial.localBinders ⊆ binding.2.localBinders
          rw [same]
          exact List.subset_cons_self _ _
    · rw [nonlet_binders (by intro name annotation initializer form; exact isLet ⟨name,annotation,initializer,form⟩) accepted]
      exact List.Subset.refl _

theorem inferStatementsFuel_binders_subset
    {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.Statement}
    {expected : Ty} {initial : State} {result : BlockResult}
    (accepted : inferStatementsFuel fuel context sources expected initial = .ok result) :
    initial.localBinders ⊆ result.state.localBinders := by
  induction fuel generalizing sources initial result with
  | zero => simp [inferStatementsFuel] at accepted
  | succ fuel ih =>
    cases sources with
    | nil => simp [inferStatementsFuel] at accepted; subst result; exact List.Subset.refl _
    | cons head tail =>
      cases tail with
      | nil =>
        obtain ⟨statement,statementRun,completed⟩ := inferStatementsFuel_success_singleton_facts accepted
        rw [completed]
        exact inferStatementFuel_binders_subset statementRun
      | cons next rest =>
        obtain ⟨statement,tail,statementRun,tailRun,completed⟩ := inferStatementsFuel_success_cons_facts accepted
        rw [completed]
        exact List.Subset.trans (inferStatementFuel_binders_subset statementRun) (ih (result := tail) tailRun)

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActiveScopePrivacy
/-! Scope-preserving inference and actual saved-scope restoration carry the
privacy established for each active generalized binder. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

theorem LiveBindersSafe.restrict {protectedVars : List TypeVarId} {before after : State}
    (live : LiveBindersSafe protectedVars before)
    (subset : after.localBinders ⊆ before.localBinders)
    (same : after.inference.substitution = before.inference.substitution) :
    LiveBindersSafe protectedVars after := by
  intro binder member
  exact (live binder (subset member)).transport (.of_substitution_eq same)

theorem ActiveQuantifiersPrivate.congr {before after : State}
    (privateVars : ActiveQuantifiersPrivate before)
    (binders : after.localBinders = before.localBinders)
    (same : after.inference.substitution = before.inference.substitution) :
    ActiveQuantifiersPrivate after := by
  intro binder member
  exact (privateVars binder (binders ▸ member)).transport binders (.of_substitution_eq same)

theorem ActiveQuantifiersPrivate.restrict {before after : State}
    (privateVars : ActiveQuantifiersPrivate before)
    (subset : after.localBinders ⊆ before.localBinders)
    (same : after.inference.substitution = before.inference.substitution) :
    ActiveQuantifiersPrivate after := by
  intro binder member
  exact (privateVars binder (subset member)).restrict subset same

theorem ActiveQuantifiersPrivate.inferExprFuel
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
    {expected : Option Ty} {initial : State} {result : InferredExpression × State}
    (privateVars : ActiveQuantifiersPrivate initial)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (bound : ActiveQuantifiersBelowNext initial)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes))
    (expectedClosed : ∀ type ∈ expected, type.VariablesBelow 0)
    (accepted : inferExprFuel fuel context source expected initial = .ok result) :
    ActiveQuantifiersPrivate result.2 := by
  have same : result.2.localBinders = initial.localBinders :=
    congrArg LexicalScope.binders (inferExprFuel_success_lexicalScope_eq accepted)
  intro binder member
  have original : binder ∈ initial.localBinders := same ▸ member
  exact (inferExprFuel_private binder.scheme.quantified fuel context source expected initial
    ready wellFormed (bound binder original) (privateVars binder original) catalog formation canonical
    (fun type present => (expectedClosed type present).weaken (Nat.zero_le _))
    (fun type present => safe_closed _ _ (expectedClosed type present)) result accepted).2.2.1

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceForSuffixPrivacy
/-! Both header return points have actual privacy continuations through the
remaining for computation, including its two real saved-scope restorations. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

namespace ForStatementInferenceContinuation.Receipt
variable {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {initializers post : List Syntax.ForItem} {condition : Syntax.Expr}
    {body : Syntax.Located (List Syntax.Statement)} {expected : Ty} {initial : State} {result : StatementResult}

/-- The final scope is a subset of the real post state, and recording the for
node leaves both substitution and requirement ledger unchanged. -/
theorem privacy_after_post
    (receipt : SourceInference.ForStatementInferenceContinuation.Receipt fuel context source initializers condition post body expected initial result)
    {protectedVars : List TypeVarId}
    (live : LiveBindersSafe protectedVars receipt.postResult.state) :
    SafeTransport protectedVars receipt.postResult.state result.state ∧
      LiveBindersSafe protectedVars result.state ∧
      ∀ row ∈ result.state.requirements, row ∉ receipt.postResult.state.requirements →
        PredicateSafe protectedVars result.state row.predicate := by
  have same := congrArg InferState.substitution receipt.inference_eq
  have binders : result.state.localBinders ⊆ receipt.postResult.state.localBinders := by
    rw [congrArg (fun result : StatementResult => result.state.localBinders) receipt.completed]
    exact (inferForItemsFuel_binders_subset receipt.initialization).trans
      (inferForItemsFuel_binders_subset (initial := receipt.bodyResult.state.restoreLexicalScope receipt.initialized.state.lexicalScope) receipt.postAccepted)
  refine ⟨.of_substitution_eq same,live.restrict binders same,?_⟩
  intro row member fresh
  have requirements := congrArg (fun result : StatementResult => result.state.requirements) receipt.completed
  exact False.elim (fresh (requirements ▸ member))

/-- A generalized initializer's returned state reaches the post header and
final saved scope through the actual condition and body calls. -/
theorem privacy_after_initialization
    (receipt : SourceInference.ForStatementInferenceContinuation.Receipt fuel context source initializers condition post body expected initial result)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes))
    (expectedClosed : expected.VariablesBelow 0)
    {protectedVars : List TypeVarId}
    (bound : ∀ v ∈ protectedVars, v.index < receipt.initialized.state.inference.next)
    (live : LiveBindersSafe protectedVars receipt.initialized.state) :
    SafeTransport protectedVars receipt.initialized.state result.state ∧
      LiveBindersSafe protectedVars result.state ∧
      ∀ row ∈ result.state.requirements, row ∉ receipt.initialized.state.requirements →
        PredicateSafe protectedVars result.state row.predicate := by
  have initProperties := inferForItemsFuel_inferenceProperties ready.allocateStatementId formation canonical receipt.initialization
  have initWellFormed := (inferForItemsFuel_direct_progress receipt.initialization).wellFormed wellFormed
  have boolBelow : ∀ type ∈ some Ty.bool, type.VariablesBelow receipt.initialized.state.inference.next := by
    intro type member
    cases Option.mem_def.mp member
    exact Ty.variablesBelow_constructor _ _
  have boolSafe : ∀ type ∈ some Ty.bool, Safe protectedVars receipt.initialized.state type := by
    intro type member
    cases Option.mem_def.mp member
    exact safe_closed _ _ (Ty.variablesBelow_constructor _ _)
  have testProperties := inferExprFuel_inferenceProperties initProperties.2 formation canonical boolBelow receipt.tested
  have testPrivacy := inferExprFuel_private protectedVars fuel context condition (some .bool) receipt.initialized.state
    initProperties.2 initWellFormed bound live catalog formation canonical boolBelow boolSafe _ receipt.tested
  have testWellFormed := (inferExprFuel_direct_progress receipt.tested).wellFormed initWellFormed
  have bodyProperties := inferStatementsFuel_inferenceProperties (context := SourceInference.ForStatementInferenceContinuation.loopContext context)
    testProperties.2.1 formation canonical (expectedClosed.weaken (Nat.zero_le _)) receipt.bodyAccepted
  have bodyPrivacy := inferStatementsFuel_private protectedVars fuel
    (SourceInference.ForStatementInferenceContinuation.loopContext context) body.value expected receipt.testState
    testProperties.2.1 testWellFormed
    (fun v member => Nat.lt_of_lt_of_le (bound v member) testProperties.1.next_le)
    testPrivacy.2.2.1 catalog formation canonical (expectedClosed.weaken (Nat.zero_le _))
    (safe_closed _ _ expectedClosed) _ receipt.bodyAccepted
  let afterBody := receipt.bodyResult.state.restoreLexicalScope receipt.initialized.state.lexicalScope
  have restoredProperties := State.restoreLexicalScope_inferenceProperties initProperties.2
    (testProperties.1.trans bodyProperties.1)
  have restoredPrivacy : SafeTransport protectedVars receipt.bodyResult.state afterBody := .of_substitution_eq rfl
  have afterBodyLive : LiveBindersSafe protectedVars afterBody := live.restore (testPrivacy.1.trans bodyPrivacy.1)
  have afterBodyWellFormed : afterBody.RequirementsWellFormed :=
    State.restoreLexicalScope_preserves_requirementsWellFormed _ _
      ((inferStatementsFuel_direct_progress receipt.bodyAccepted).wellFormed testWellFormed)
  have postPrivacy := inferForItemsFuel_private protectedVars fuel
    (SourceInference.ForStatementInferenceContinuation.loopContext context) post afterBody
    restoredProperties.2 afterBodyWellFormed
    (fun v member => Nat.lt_of_lt_of_le (bound v member) restoredProperties.1.next_le)
    afterBodyLive catalog formation canonical _ receipt.postAccepted
  have finalPrivacy := privacy_after_post receipt postPrivacy.2.1
  refine ⟨testPrivacy.1.trans (bodyPrivacy.1.trans (restoredPrivacy.trans (postPrivacy.1.trans finalPrivacy.1))),
    finalPrivacy.2.1,?_⟩
  have bodyRows := new_requirements_trans testPrivacy.2.2.2 bodyPrivacy.2.2.2 bodyPrivacy.1
  have restoredRows : ∀ row ∈ afterBody.requirements, row ∉ receipt.initialized.state.requirements →
      PredicateSafe protectedVars afterBody row.predicate := by
    intro row member fresh type typeMember
    exact restoredPrivacy _ (bodyRows row member fresh type typeMember)
  have postRows := new_requirements_trans restoredRows postPrivacy.2.2 postPrivacy.1
  exact new_requirements_trans postRows finalPrivacy.2.2 finalPrivacy.1

end ForStatementInferenceContinuation.Receipt
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceForActiveStages
/-! The actual for node retains both header inventories. Its initialized and
restored post states obtain active privacy from the same finalizer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

namespace ForStatementInferenceContinuation.Receipt
variable {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {initializers post : List Syntax.ForItem} {condition : Syntax.Expr}
    {body : Syntax.Located (List Syntax.Statement)} {expected : Ty} {initial : State} {result : StatementResult}

theorem headers_retained
    (receipt : SourceInference.ForStatementInferenceContinuation.Receipt fuel context source initializers condition post body expected initial result)
    {evidenceState : State} {roots : List NodeId}
    (retained : result.state.nodes <+: evidenceState.nodes) :
    (receipt.initialized.items.flatMap ForItemForm.initializedLetBinders ++
      receipt.postResult.items.flatMap ForItemForm.initializedLetBinders) ⊆
        (evidenceState.toTypedSource roots).initializedLetBinders := by
  intro binder member
  unfold TypedSource.initializedLetBinders
  exact List.mem_flatMap.mpr ⟨_,retained.subset receipt.recorded,member⟩

/-- Initializer prefixes and the actual body completion establish every state
condition needed to inspect either header list. -/
theorem active_stages
    (receipt : SourceInference.ForStatementInferenceContinuation.Receipt fuel context source initializers condition post body expected initial result)
    {wholeContext : SourceInference.Context} {wholeReturn : Ty}
    {evidenceState : State} {roots : List NodeId} {finalized : SourceInference.Result}
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (nodesBelow : initial.NodesBelowNextOccurrence)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes))
    (expectedClosed : expected.VariablesBelow 0)
    (active : ActiveHeaderState initial (evidenceState.toTypedSource roots))
    (retained : TypingSourceExtends (result.state.toTypedSource roots) (evidenceState.toTypedSource roots))
    (extension : finalized.substitution.SemanticallyExtends result.state.inference.substitution) :
    ActiveHeaderState receipt.initialized.state (evidenceState.toTypedSource roots) ∧
      ActiveHeaderState (receipt.bodyResult.state.restoreLexicalScope receipt.initialized.state.lexicalScope)
        (evidenceState.toTypedSource roots) := by
  have initProperties := inferForItemsFuel_inferenceProperties ready.allocateStatementId formation canonical receipt.initialization
  have initializedBelow := (inferForItemsFuel_occurrenceBoundExtends receipt.initialization).nodesBelowNextOccurrence
    (State.allocateStatementId_preserves_nodesBelowNextOccurrence initial nodesBelow)
  have initWellFormed := (inferForItemsFuel_direct_progress receipt.initialization).wellFormed wellFormed
  have boolClosed : ∀ type ∈ some Ty.bool, type.VariablesBelow 0 := by
    intro type member
    cases Option.mem_def.mp member
    exact Ty.variablesBelow_constructor _ _
  have testProperties := inferExprFuel_inferenceProperties initProperties.2 formation canonical
    (fun type member => (boolClosed type member).weaken (Nat.zero_le _)) receipt.tested
  have testBelow := (inferExprFuel_occurrenceBoundExtends receipt.tested).nodesBelowNextOccurrence initializedBelow
  have bodyProperties := inferStatementsFuel_inferenceProperties
    (context := SourceInference.ForStatementInferenceContinuation.loopContext context)
    testProperties.2.1 formation canonical (expectedClosed.weaken (Nat.zero_le _)) receipt.bodyAccepted
  have bodyBelow := (inferStatementsFuel_occurrenceBoundExtends receipt.bodyAccepted).nodesBelowNextOccurrence testBelow
  have restored := State.restoreLexicalScope_inferenceProperties initProperties.2 (testProperties.1.trans bodyProperties.1)
  have postProperties := inferForItemsFuel_inferenceProperties
    (context := SourceInference.ForStatementInferenceContinuation.loopContext context)
    restored.2 formation canonical receipt.postAccepted
  have last := State.InferenceProgress.of_inference_eq postProperties.2.solved receipt.inference_eq
  have initExtension := Substitution.SemanticallyExtends.trans extension
    (restored.1.trans (postProperties.1.trans last)).substitution_extends
  have allRetained := headers_retained (roots := roots) receipt retained.nodes_prefix
  have initRetained : receipt.initialized.items.flatMap ForItemForm.initializedLetBinders ⊆
      (evidenceState.toTypedSource roots).initializedLetBinders := by
    intro binder member
    exact allRetained (List.mem_append_left _ member)
  have initializedActive := ActiveHeaderState.inferForItemsFuel
    (initial := initial.allocateStatementId.2) (show ActiveHeaderState initial.allocateStatementId.2
      (evidenceState.toTypedSource roots) from ⟨active.privateVars.congr rfl rfl,active.bound,
      active.backed.congr rfl rfl rfl,active.origins.congr_localBinders rfl⟩)
    resources ready.allocateStatementId wellFormed catalog formation canonical initRetained initExtension receipt.initialization
  have testActive : ActiveHeaderState receipt.testState (evidenceState.toTypedSource roots) := {
    privateVars := initializedActive.privateVars.inferExprFuel initProperties.2 initWellFormed
      initializedActive.bound catalog formation canonical boolClosed receipt.tested
    bound := activeQuantifiersBelowNext_inferExprFuel initializedActive.bound initProperties.2 formation canonical
      (fun type member => (boolClosed type member).weaken (Nat.zero_le _)) receipt.tested
    backed := initializedActive.backed.inferExprFuel initProperties.2 formation canonical
      (fun type member => (boolClosed type member).weaken (Nat.zero_le _)) receipt.tested
    origins := initializedActive.origins.inferExprFuel receipt.tested }
  have testWellFormed := (inferExprFuel_direct_progress receipt.tested).wellFormed initWellFormed
  have bodyNodes : receipt.bodyResult.state.nodes <+: evidenceState.nodes := by
    have beforePost := inferForItemsFuel_preserves_nodesPrefix receipt.postAccepted
      (List.prefix_refl _) bodyBelow (Nat.le_refl _)
    have postNodes : receipt.postResult.state.nodes <+: result.state.nodes := by
      rw [congrArg (fun result : StatementResult => result.state.nodes) receipt.completed]
      exact List.prefix_append _ _
    exact beforePost.trans (postNodes.trans retained.nodes_prefix)
  have bodySource : TypingSourceExtends (receipt.bodyResult.state.toTypedSource roots)
      (evidenceState.toTypedSource roots) := {
    owner_eq := retained.owner_eq.trans ((congrArg (fun result : StatementResult => result.state.owner)
      receipt.completed).trans (inferForItemsFuel_preserves_owner (state := receipt.bodyResult.state.restoreLexicalScope receipt.initialized.state.lexicalScope) receipt.postAccepted))
    nodes_prefix := bodyNodes }
  have bodyExtension := Substitution.SemanticallyExtends.trans extension
    (postProperties.1.trans last).substitution_extends
  have bodyActive := activeState_inferStatementsFuel (context := SourceInference.ForStatementInferenceContinuation.loopContext context) resources testProperties.2.1 testWellFormed testBelow
    catalog formation canonical expectedClosed testActive.privateVars testActive.bound testActive.backed
    testActive.origins bodySource bodyExtension receipt.bodyAccepted
  have savedSubset : receipt.initialized.state.localBinders ⊆ receipt.bodyResult.state.localBinders := by
    have testBinders : receipt.testState.localBinders = receipt.initialized.state.localBinders :=
      congrArg LexicalScope.binders (inferExprFuel_success_lexicalScope_eq receipt.tested)
    rw [← testBinders]
    exact inferStatementsFuel_binders_subset receipt.bodyAccepted
  refine ⟨initializedActive,{
    privateVars := bodyActive.1.restrict savedSubset rfl
    bound := activeQuantifiersBelowNext_transport initializedActive.bound rfl
      (testProperties.1.trans bodyProperties.1).next_le
    backed := initializedActive.backed.transport (List.Subset.refl _)
      ((inferExprFuel_requirements_subset receipt.tested).trans
        (inferStatementsFuel_requirements_subset receipt.bodyAccepted))
      (testProperties.1.trans bodyProperties.1).substitution_extends
    origins := initializedActive.origins.congr_localBinders rfl }⟩

end ForStatementInferenceContinuation.Receipt
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceForBodySuffixPrivacy
/-! Locals created by a loop body may be restored before post inference. The
actual saved initialized scope is retained in that body state. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

namespace ForStatementInferenceContinuation.Receipt
variable {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {initializers post : List Syntax.ForItem} {condition : Syntax.Expr}
    {body : Syntax.Located (List Syntax.Statement)} {expected : Ty} {initial : State} {result : StatementResult}

theorem privacy_after_body
    (receipt : SourceInference.ForStatementInferenceContinuation.Receipt fuel context source initializers condition post body expected initial result)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes))
    (expectedClosed : expected.VariablesBelow 0)
    {protectedVars : List TypeVarId}
    (bound : ∀ v ∈ protectedVars, v.index < receipt.bodyResult.state.inference.next)
    (live : LiveBindersSafe protectedVars receipt.bodyResult.state) :
    SafeTransport protectedVars receipt.bodyResult.state result.state ∧
      LiveBindersSafe protectedVars result.state ∧
      ∀ row ∈ result.state.requirements, row ∉ receipt.bodyResult.state.requirements →
        PredicateSafe protectedVars result.state row.predicate := by
  have initProperties := inferForItemsFuel_inferenceProperties ready.allocateStatementId formation canonical receipt.initialization
  have initWellFormed := (inferForItemsFuel_direct_progress receipt.initialization).wellFormed wellFormed
  have testProperties := inferExprFuel_inferenceProperties initProperties.2 formation canonical
    (by intro type member; cases Option.mem_def.mp member; exact Ty.variablesBelow_constructor _ _) receipt.tested
  have testWellFormed := (inferExprFuel_direct_progress receipt.tested).wellFormed initWellFormed
  have bodyProperties := inferStatementsFuel_inferenceProperties (context := SourceInference.ForStatementInferenceContinuation.loopContext context)
    testProperties.2.1 formation canonical (expectedClosed.weaken (Nat.zero_le _)) receipt.bodyAccepted
  have bodyWellFormed := (inferStatementsFuel_direct_progress receipt.bodyAccepted).wellFormed testWellFormed
  have restoredProperties := State.restoreLexicalScope_inferenceProperties initProperties.2
    (testProperties.1.trans bodyProperties.1)
  have savedSubset : receipt.initialized.state.localBinders ⊆ receipt.bodyResult.state.localBinders := by
    have testBinders : receipt.testState.localBinders = receipt.initialized.state.localBinders :=
      congrArg LexicalScope.binders (inferExprFuel_success_lexicalScope_eq receipt.tested)
    rw [← testBinders]
    exact inferStatementsFuel_binders_subset receipt.bodyAccepted
  have restoredLive : LiveBindersSafe protectedVars
      (receipt.bodyResult.state.restoreLexicalScope receipt.initialized.state.lexicalScope) :=
    live.restrict savedSubset rfl
  have postPrivacy := inferForItemsFuel_private protectedVars fuel
    (SourceInference.ForStatementInferenceContinuation.loopContext context) post
    (receipt.bodyResult.state.restoreLexicalScope receipt.initialized.state.lexicalScope)
    restoredProperties.2 bodyWellFormed bound restoredLive catalog formation canonical _ receipt.postAccepted
  have finalPrivacy := privacy_after_post receipt postPrivacy.2.1
  exact ⟨postPrivacy.1.trans finalPrivacy.1,finalPrivacy.2.1,
    new_requirements_trans postPrivacy.2.2 finalPrivacy.2.2 finalPrivacy.1⟩

end ForStatementInferenceContinuation.Receipt
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceHeaderReturnPrivacy
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

namespace LocalHeaderRequirementTiming.Receipt

variable {wholeContext : SourceInference.Context} {wholeReturn : Ty}
    {evidenceState : State} {roots : List NodeId} {finalized : SourceInference.Result}
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State}

/-- The new header scheme quantifies only variables created by its initializer. -/
theorem quantified_at_or_after_entry
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    (receipt : SourceInference.LocalHeaderRequirementTiming.Receipt fuel context source initial result)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (backed : LiveTemplatesBacked initial)
    (origins : ActiveBinderCaptureOrigins initial (evidenceState.toTypedSource roots))
    (retained : receipt.binding.1 ∈ (evidenceState.toTypedSource roots).initializedLetBinders)
    (extension : finalized.substitution.SemanticallyExtends result.2.inference.substitution) :
    ∀ q ∈ receipt.binding.1.scheme.quantified, initial.inference.next ≤ q.index := by
  have inferred := receipt.initializer_inference ready formation canonical
  have templates := templates_before receipt backed ready wellFormed formation canonical
  have readyExtension : finalized.substitution.SemanticallyExtends receipt.ready.inference.substitution := by
    rwa [receipt.inference_eq] at extension
  have live : LiveBindersSafe receipt.binding.1.scheme.quantified receipt.ready :=
    generalized_live_from_finalizer resources (origins.congr_localBinders receipt.ready_binders)
      readyExtension retained rfl templates
  intro q quantified
  by_cases later : initial.inference.next ≤ q.index
  · exact later
  exfalso
  have earlier : q.index < initial.inference.next := Nat.lt_of_not_ge later
  have occurs : q ∈ (receipt.ready.resolve receipt.value.type).freeVariables :=
    (List.mem_filter.mp quantified).1
  have outside := inferred.2.1.solved.apply_variables_outside_domain receipt.value.type q occurs
  have fixed : receipt.ready.inference.substitution.apply (.variable q) = .variable q := by
    simp only [Substitution.apply,
      (Substitution.lookup?_eq_none_iff_not_mem_domain _ _).mpr outside, Option.getD_none]
  have backwards : ∀ type, Safe receipt.binding.1.scheme.quantified receipt.ready type →
      Safe [q] initial type := by
    intro type privateType v present member
    have same : v = q := List.mem_singleton.mp member
    subst v
    exact privateType q (fixed_variable_occurs_at_final inferred.1.substitution_extends fixed present) quantified
  have entryLive : LiveBindersSafe [q] initial := by
    intro binder member
    have readyMember : binder ∈ receipt.ready.localBinders := by
      rw [receipt.ready_binders]
      exact member
    have prior := live binder readyMember
    constructor
    · intro v free
      exact backwards _ (prior.1 v free)
    · intro requirement present type typeMember v free unbound
      exact backwards _ (prior.2 requirement present type typeMember v free unbound)
  have actual := inferExprFuel_private [q] fuel context receipt.initializer receipt.expected
    initial ready wellFormed
    (by intro v member; obtain rfl := List.mem_singleton.mp member; exact earlier)
    entryLive catalog formation canonical (receipt.annotationAccepted.variablesBelow _)
    (fun type present => safe_closed _ _ (receipt.annotationAccepted.variablesBelow 0 type present))
    _ receipt.child
  exact actual.2.1 q occurs (List.mem_singleton_self _)

/-- A header initializer keeps its new quantifiers out of every entering type. -/
theorem generalized_type_safe
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    (receipt : SourceInference.LocalHeaderRequirementTiming.Receipt fuel context source initial result)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (backed : LiveTemplatesBacked initial)
    (origins : ActiveBinderCaptureOrigins initial (evidenceState.toTypedSource roots))
    (retained : receipt.binding.1 ∈ (evidenceState.toTypedSource roots).initializedLetBinders)
    (extension : finalized.substitution.SemanticallyExtends result.2.inference.substitution)
    {type : Ty} (typeBelow : type.VariablesBelow initial.inference.next) :
    Safe receipt.binding.1.scheme.quantified result.2 type := by
  have templates := templates_before receipt backed ready wellFormed formation canonical
  have readyExtension : finalized.substitution.SemanticallyExtends receipt.ready.inference.substitution := by
    rwa [receipt.inference_eq] at extension
  have live : LiveBindersSafe receipt.binding.1.scheme.quantified receipt.ready :=
    generalized_live_from_finalizer resources (origins.congr_localBinders receipt.ready_binders)
      readyExtension retained rfl templates
  have safe := inferExprFuel_fresh_quantifiers_safe ready wellFormed catalog formation canonical
    (receipt.annotationAccepted.variablesBelow 0) receipt.child
    (quantified_at_or_after_entry resources receipt ready wellFormed catalog formation canonical
      backed origins retained extension) live typeBelow
  simpa only [Safe, State.resolve, InferState.resolve, receipt.inference_eq] using safe

end LocalHeaderRequirementTiming.Receipt

/-- Every binder returned by an accepted header item avoids the entering return type. -/
theorem inferForItemFuel_return_safe
    {wholeContext : SourceInference.Context} {wholeReturn : Ty}
    {evidenceState : State} {roots : List NodeId} {finalized : SourceInference.Result}
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State} {expectedReturn : Ty}
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (bound : ActiveQuantifiersBelowNext initial) (privateVars : ActiveQuantifiersPrivate initial)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (backed : LiveTemplatesBacked initial)
    (origins : ActiveBinderCaptureOrigins initial (evidenceState.toTypedSource roots))
    (retained : result.1.initializedLetBinders ⊆ (evidenceState.toTypedSource roots).initializedLetBinders)
    (extension : finalized.substitution.SemanticallyExtends result.2.inference.substitution)
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (returnSafe : ∀ binder ∈ initial.localBinders, Safe binder.scheme.quantified initial expectedReturn)
    (accepted : inferForItemFuel fuel context source initial = .ok result) :
    ∀ binder ∈ result.2.localBinders, Safe binder.scheme.quantified result.2 expectedReturn := by
  intro binder member
  rcases inferForItemFuel_quantified_origin accepted binder member with old | mono | created
  · exact (inferForItemFuel_private binder.scheme.quantified fuel context source initial ready wellFormed
      (bound binder old) (privateVars binder old) catalog formation canonical result accepted).1 _
      (returnSafe binder old)
  · intro q _ quantified
    simp [mono] at quantified
  · obtain ⟨childFuel, receipt, rfl⟩ := created
    apply LocalHeaderRequirementTiming.Receipt.generalized_type_safe resources receipt ready wellFormed
      catalog formation canonical backed origins _ extension returnBelow
    apply retained
    rw [receipt.recorded]
    exact List.mem_singleton_self _

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceLiveStatementPosition
/-! Actual earlier statements establish privacy for every active generalized
binder. The selected initializer receives those invariants from the same prefix. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

structure LiveStatementPrivacyOccurrence (context : SourceInference.Context)
    (source : Syntax.Statement) (expected : Ty) (initial final evidenceState : State) (roots : List NodeId)
    extends ActiveStatementPrivacyOccurrence context source expected initial final evidenceState roots where
  entryNodesBelow : entry.NodesBelowNextOccurrence
  resultOwner : final.owner = result.state.owner
  liveAfter : ∀ protectedVars,
    (∀ v ∈ protectedVars, v.index < result.state.inference.next) →
    LiveBindersSafe protectedVars result.state → Safe protectedVars result.state expected →
    LiveBindersSafe protectedVars final

/-- The selected position follows the original list. The continuation is
constructed here from actual later calls, rather than assumed as a trace law. -/
theorem liveStatementPrivacyOccurrence_of_position
    {wholeContext : SourceInference.Context} {wholeReturn : Ty}
    {finalized : SourceInference.Result}
    {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.Statement}
    {expected : Ty} {initial evidenceState : State} {roots : List NodeId}
    {result : BlockResult} {index : Nat} {source : Syntax.Statement}
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (nodesBelow : initial.NodesBelowNextOccurrence)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes))
    (expectedBelow : expected.VariablesBelow initial.inference.next)
    (expectedClosed : expected.VariablesBelow 0)
    (privateVars : ActiveQuantifiersPrivate initial)
    (bound : ActiveQuantifiersBelowNext initial)
    (backed : LiveTemplatesBacked initial)
    (origins : ActiveBinderCaptureOrigins initial (evidenceState.toTypedSource roots))
    (retained : TypingSourceExtends (result.state.toTypedSource roots) (evidenceState.toTypedSource roots))
    (extension : finalized.substitution.SemanticallyExtends result.state.inference.substitution)
    (accepted : inferStatementsFuel fuel context sources expected initial = .ok result)
    (position : sources[index]? = some source) :
    Nonempty (LiveStatementPrivacyOccurrence context source expected initial result.state evidenceState roots) := by
  induction fuel generalizing sources initial result index with
  | zero => simp [inferStatementsFuel] at accepted
  | succ fuel ih =>
    cases sources with
    | nil => simp at position
    | cons head rest =>
      cases headRun : inferStatementFuel fuel context head expected initial with
      | error error => simp [inferStatementsFuel,headRun,bind,Except.bind] at accepted
      | ok headResult =>
        have headProgress := inferStatementFuel_inferenceProperties ready formation canonical expectedBelow headRun
        have headWellFormed := (inferStatementFuel_direct_progress headRun).wellFormed wellFormed
        have headBelow := (inferStatementFuel_occurrenceBoundExtends headRun).nodesBelowNextOccurrence nodesBelow
        have afterExpected := expectedBelow.weaken headProgress.1.next_le
        cases rest with
        | nil =>
          have same : result.state = headResult.state := by
            simp only [inferStatementsFuel,headRun,bind,Except.bind,pure,Pure.pure,Except.pure,Except.ok.injEq] at accepted
            exact (congrArg BlockResult.state accepted).symm
          cases index with
          | zero =>
            simp only [List.getElem?_cons_zero,Option.some.injEq] at position
            subst source
            refine ⟨{
              fuel := fuel, entry := initial, result := headResult, accepted := headRun,
              ready := ready, before := .refl ready.solved,
              continuation := same.symm ▸ State.InferenceProgress.refl headProgress.2.1.solved,
              retained := same.symm ▸ List.prefix_refl _,
              resultReady := headProgress.2.1, resultWellFormed := headWellFormed,
              expectedBelow := afterExpected,
              entryWellFormed := wellFormed, entryTemplates := backed, entryOrigins := origins,
              entryPrivate := privateVars, entryBound := bound, entryNodesBelow := nodesBelow,
              resultOwner := congrArg State.owner same,
              liveAfter := ?_, privacy := ?_ }⟩
            · intro protectedVars bound live safe
              rw [same]
              exact ⟨.refl _ _,fun row member fresh => False.elim (fresh member)⟩
            · intro protectedVars bound live safe
              rwa [same]
          | succ index => simp at position
        | cons next remaining =>
          cases tailRun : inferStatementsFuel fuel context (next::remaining) expected headResult.state with
          | error error => simp [inferStatementsFuel,headRun,tailRun,bind,Except.bind] at accepted
          | ok tailResult =>
            have same : result.state = tailResult.state := by
              simp only [inferStatementsFuel,headRun,tailRun,bind,Except.bind,pure,Pure.pure,Except.pure,Except.ok.injEq] at accepted
              exact (congrArg BlockResult.state accepted).symm
            cases index with
            | zero =>
              simp only [List.getElem?_cons_zero,Option.some.injEq] at position
              subst source
              have tailProgress := inferStatementsFuel_inferenceProperties headProgress.2.1 formation canonical afterExpected tailRun
              refine ⟨{
                fuel := fuel, entry := initial, result := headResult, accepted := headRun,
                ready := ready, before := .refl ready.solved,
                continuation := same.symm ▸ tailProgress.1,
                retained := same.symm ▸ inferStatementsFuel_preserves_nodesPrefix tailRun
                  (List.prefix_refl _) headBelow (Nat.le_refl _),
                resultReady := headProgress.2.1, resultWellFormed := headWellFormed,
                expectedBelow := afterExpected,
                entryWellFormed := wellFormed, entryTemplates := backed, entryOrigins := origins,
                entryPrivate := privateVars, entryBound := bound, entryNodesBelow := nodesBelow,
                resultOwner := (congrArg State.owner same).trans (inferStatementsFuel_preserves_owner tailRun),
                liveAfter := ?_, privacy := ?_ }⟩
              · intro protectedVars bound live safe
                rw [same]
                have actual := inferStatementsFuel_private protectedVars fuel context (next::remaining) expected headResult.state
                  headProgress.2.1 headWellFormed bound live catalog formation canonical afterExpected safe tailResult tailRun
                exact ⟨actual.1,actual.2.2.2⟩
              · intro protectedVars bound live safe
                rw [same]
                exact (inferStatementsFuel_private protectedVars fuel context (next::remaining) expected headResult.state
                  headProgress.2.1 headWellFormed bound live catalog formation canonical afterExpected safe tailResult tailRun).2.2.1
            | succ index =>
              have restPosition : (next::remaining)[index]? = some source := position
              have headBacked := backed.inferStatementFuel ready formation canonical expectedBelow headRun
              have tailToEvidence : TypingSourceExtends (tailResult.state.toTypedSource roots)
                  (evidenceState.toTypedSource roots) := by
                rwa [same] at retained
              have headToEvidence := (inferStatementsFuel_success_typingSourceExtends tailRun headBelow roots).trans tailToEvidence
              have headOrigins := inferStatementFuel_captureOrigins headRun origins headToEvidence
              have tailProgress := inferStatementsFuel_inferenceProperties headProgress.2.1 formation canonical afterExpected tailRun
              have tailExtension : finalized.substitution.SemanticallyExtends tailResult.state.inference.substitution := by
                rwa [same] at extension
              have headExtension := Substitution.SemanticallyExtends.trans tailExtension tailProgress.1.substitution_extends
              have headPrivate := privateVars.inferStatementFuel resources ready wellFormed bound catalog formation canonical
                expectedClosed backed origins headToEvidence.nodes_prefix headExtension headRun
              have headBound := activeQuantifiersBelowNext_inferStatementFuel bound ready formation canonical expectedBelow headRun
              obtain ⟨found⟩ := ih headProgress.2.1 headWellFormed headBelow afterExpected
                headPrivate headBound headBacked headOrigins tailToEvidence tailExtension tailRun restPosition
              refine ⟨{
                fuel := found.fuel, entry := found.entry, result := found.result, accepted := found.accepted,
                ready := found.ready, before := headProgress.1.trans found.before,
                continuation := same.symm ▸ found.continuation,
                retained := same.symm ▸ found.retained,
                resultReady := found.resultReady, resultWellFormed := found.resultWellFormed,
                expectedBelow := found.expectedBelow,
                entryWellFormed := found.entryWellFormed, entryTemplates := found.entryTemplates,
                entryOrigins := found.entryOrigins,
                entryPrivate := found.entryPrivate, entryBound := found.entryBound, entryNodesBelow := found.entryNodesBelow,
                resultOwner := (congrArg State.owner same).trans found.resultOwner,
                liveAfter := ?_, privacy := ?_ }⟩
              · intro protectedVars bound live safe
                rw [same]
                exact found.privacy protectedVars bound live safe
              · intro protectedVars bound live safe
                rw [same]
                exact found.liveAfter protectedVars bound live safe

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferencePatternRawIsolation
/-! Raw scheme isolation follows the actual pattern binder allocations. Each
new monomorphic body stores the resolved expected type, whose privacy is known
at that exact allocation; resolved privacy is not identified with raw privacy. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

private theorem unify_requirements {state result : State} {left right : Ty}
    (accepted : Detail.unify state left right = .ok result) : result.requirements = state.requirements := by
  unfold Detail.unify at accepted
  cases unified : state.inference.unify left right with
  | error error => simp [unified, Detail.liftUnification, bind, Except.bind] at accepted
  | ok inference =>
    simp only [unified, Detail.liftUnification, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
    cases accepted
    rfl

private theorem freshTypes_fields (count : Nat) (state : State) :
    (Detail.freshTypes count state).2.localBinders = state.localBinders ∧
      (Detail.freshTypes count state).2.requirements = state.requirements := by
  induction count generalizing state with
  | zero => exact ⟨rfl, rfl⟩
  | succ count ih => exact ih state.fresh.2

private theorem freshConstructor_requirements (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature) (state : State) :
    (Detail.freshDataConstructorInstantiation dataType constructor state).2.requirements = state.requirements := by
  have fold (parameters : List TypeParameterId) (accumulator : List Ty × State) :
      (parameters.foldl (fun result _ =>
        (result.1 ++ [result.2.fresh.1], result.2.fresh.2)) accumulator).2.requirements =
        accumulator.2.requirements := by
    induction parameters generalizing accumulator with
    | nil => rfl
    | cons parameter rest ih => exact ih (accumulator.1 ++ [accumulator.2.fresh.1], accumulator.2.fresh.2)
  exact fold dataType.parameters ([],state)

private def PatternPrivacy (protectedVars : List TypeVarId) (initial final : State) : Prop :=
  SafeTransport protectedVars initial final ∧ LiveBindersSafe protectedVars final ∧
    ∀ row ∈ final.requirements, row ∉ initial.requirements → PredicateSafe protectedVars final row.predicate

private theorem PatternPrivacy.trans {protectedVars : List TypeVarId} {first second third : State}
    (left : PatternPrivacy protectedVars first second) (right : PatternPrivacy protectedVars second third) :
    PatternPrivacy protectedVars first third :=
  ⟨left.1.trans right.1, right.2.1, new_requirements_trans left.2.2 right.2.2 right.1⟩

private theorem PatternPrivacy.of_unchanged {protectedVars : List TypeVarId} {initial final : State}
    (transport : SafeTransport protectedVars initial final) (live : LiveBindersSafe protectedVars final)
    (requirements : final.requirements = initial.requirements) : PatternPrivacy protectedVars initial final := by
  refine ⟨transport, live, ?_⟩
  intro row member fresh
  exact False.elim (fresh (requirements ▸ member))

private theorem integer_prefix_private {protectedVars : List TypeVarId} {state recorded final : State}
    {expected : Ty} {metavariable : TypeVarId} {normalized : Ty} {requirement : RequirementId}
    (ready : state.InferenceReady)
    (bound : ∀ protectedVariable ∈ protectedVars, protectedVariable.index < state.inference.next)
    (expectedSafe : Safe protectedVars state expected) (live : LiveBindersSafe protectedVars state)
    (freshType : state.fresh.1 = .variable metavariable)
    (unified : Detail.unify recorded (.variable metavariable) normalized = .ok final)
    (normalization : recorded.resolve expected = normalized)
    (inference : recorded.inference = state.fresh.2.inference)
    (binders : recorded.localBinders = state.localBinders)
    (requirements : recorded.requirements = state.requirements ++
      [{id := requirement, predicate := ProgramSignatures.builtinIntPredicate (.variable metavariable)}]) :
    PatternPrivacy protectedVars state final := by
  have stage : SafeTransport protectedVars state.fresh.2 recorded :=
    .of_substitution_eq (congrArg InferState.substitution inference)
  have initialStage : SafeTransport protectedVars state recorded := fresh.trans stage
  have targetSafe : Safe protectedVars recorded (.variable metavariable) :=
    freshType ▸ stage _ (fresh_type ready bound)
  have recordedReady : recorded.InferenceReady := by
    apply State.InferenceReady.of_progress_of_binderEnvironment_eq ready.fresh
      (State.InferenceProgress.of_inference_eq ready.fresh.solved inference)
    simp only [State.binderEnvironment, binders]
    rfl
  have normalizedSafe : Safe protectedVars recorded normalized :=
    normalization ▸ safe_resolved recordedReady (initialStage _ expectedSafe)
  have transport := ProtectedVariables.unify targetSafe normalizedSafe unified
  refine ⟨initialStage.trans transport,
    (live.transport binders initialStage).unify targetSafe normalizedSafe unified, ?_⟩
  intro row member fresh
  rw [unify_requirements unified, requirements] at member
  rcases List.mem_append.mp member with old | issued
  · exact False.elim (fresh old)
  · have same := List.mem_singleton.mp issued
    subst row
    intro type member
    have typeEq : type = .variable metavariable := by
      simpa [ProgramSignatures.builtinIntPredicate] using member
    subst type
    exact transport _ targetSafe

private theorem contextual_prefix_private {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {state final : State} {expected : Ty} {name : String}
    {dataType : ProgramDataSignature} {constructor : ProgramDataConstructorSignature} {arguments : List Ty}
    (ready : state.InferenceReady) (expectedBelow : expected.VariablesBelow state.inference.next)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (safe : Safe protectedVars state expected) (live : LiveBindersSafe protectedVars state)
    (selected : Detail.contextualConstructorCandidate context state (some expected) name = .ok (dataType,constructor,arguments))
    (unified : Detail.unify state (Detail.instantiateDataConstructor dataType constructor arguments).resultType expected = .ok final) :
    PatternPrivacy protectedVars state final ∧ state.InferenceProgress final ∧ final.InferenceReady ∧
      (∀ type ∈ (Detail.instantiateDataConstructor dataType constructor arguments).payloadTypes,
        type.VariablesBelow final.inference.next ∧ Safe protectedVars final type) := by
  have privacy := contextual_constructor ready formation safe selected
  obtain ⟨dataMember, constructorMember, actual, expectedEq, nominalEq⟩ :=
    Detail.contextualConstructorCandidate_success_facts selected
  cases Option.some.inj expectedEq
  have resolvedBelow : (state.resolve expected).VariablesBelow state.inference.next :=
    ready.solved.variablesBelow_apply expectedBelow
  rw [nominalEq] at resolvedBelow
  have argumentsBelow := ((Ty.variablesBelow_applyMany_iff state.inference.next
    (.constructor (.declaration dataType.id)) arguments).mp
      (by simpa only [Ty.nominal] using resolvedBelow)).2
  have bounds := Detail.instantiateDataConstructor_types_variablesBelow (dataType := dataType) argumentsBelow
    (formation.data_constructor_payloadTypes_variablesBelow dataMember constructorMember state.inference.next)
  have progress := Detail.unify_inferenceProgress ready.solved bounds.2 expectedBelow unified
  have finalReady := Detail.unify_preserves_inferenceReady ready bounds.2 expectedBelow unified
  have transport := ProtectedVariables.unify privacy.2 safe unified
  exact ⟨PatternPrivacy.of_unchanged transport (live.unify privacy.2 safe unified) (unify_requirements unified),
    progress, finalReady, fun type member => ⟨(bounds.1 type member).weaken progress.next_le, transport _ (privacy.1 type member)⟩⟩

private theorem explicit_prefix_private {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {state allocated final : State} {expected : Ty}
    {qualifiers : List String} {name : String} {dataType : ProgramDataSignature}
    {constructor : ProgramDataConstructorSignature} {instantiation : DataConstructorInstantiation}
    (ready : state.InferenceReady) (expectedBelow : expected.VariablesBelow state.inference.next)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (bound : ∀ protectedVariable ∈ protectedVars, protectedVariable.index < state.inference.next)
    (safe : Safe protectedVars state expected) (live : LiveBindersSafe protectedVars state)
    (selected : Detail.explicitConstructorCandidate context qualifiers name = .ok (dataType,constructor))
    (allocation : Detail.freshDataConstructorInstantiation dataType constructor state = (instantiation,allocated))
    (unified : Detail.unify allocated instantiation.resultType expected = .ok final) :
    PatternPrivacy protectedVars state final ∧ state.InferenceProgress final ∧ final.InferenceReady ∧
      (∀ type ∈ instantiation.payloadTypes, type.VariablesBelow final.inference.next ∧ Safe protectedVars final type) := by
  obtain ⟨dataMember, constructorMember, _⟩ := Detail.explicitConstructorCandidate_success_facts selected
  have payloadClosed := formation.data_constructor_payloadTypes_variablesBelow dataMember constructorMember 0
  have privacy := fresh_constructor (dataType := dataType) ready bound payloadClosed
  have properties := Detail.freshDataConstructorInstantiation_inferenceProperties dataType constructor state ready
    (fun type member => (payloadClosed type member).weaken (Nat.zero_le _))
  have lexical := Detail.freshDataConstructorInstantiation_preserves_lexicalScope dataType constructor state
  have requirements := freshConstructor_requirements dataType constructor state
  rw [allocation] at privacy properties lexical requirements
  have allocatedBinders := congrArg LexicalScope.binders lexical
  have expectedBound := expectedBelow.weaken properties.1.next_le
  have expectedSafe := privacy.1 _ safe
  have transport := ProtectedVariables.unify privacy.2.2 expectedSafe unified
  have progress := Detail.unify_inferenceProgress properties.2.1.solved properties.2.2.2.2 expectedBound unified
  have finalReady := Detail.unify_preserves_inferenceReady properties.2.1 properties.2.2.2.2 expectedBound unified
  have finalLive := (live.transport allocatedBinders privacy.1).unify privacy.2.2 expectedSafe unified
  exact ⟨PatternPrivacy.of_unchanged (privacy.1.trans transport) finalLive ((unify_requirements unified).trans requirements),
    properties.1.trans progress, finalReady, fun type member => ⟨(properties.2.2.2.1 type member).weaken progress.next_le,
      transport _ (privacy.2.1 type member)⟩⟩

private theorem tuple_prefix_private {protectedVars : List TypeVarId} {state allocated final : State}
    {expected : Ty} {types : List Ty} {count : Nat}
    (ready : state.InferenceReady) (expectedBelow : expected.VariablesBelow state.inference.next)
    (bound : ∀ protectedVariable ∈ protectedVars, protectedVariable.index < state.inference.next)
    (safe : Safe protectedVars state expected) (live : LiveBindersSafe protectedVars state)
    (allocation : Detail.freshTypes count state = (types,allocated))
    (unified : Detail.unify allocated expected (Ty.productMany types) = .ok final) :
    PatternPrivacy protectedVars state final ∧ state.InferenceProgress final ∧ final.InferenceReady ∧
      (∀ type ∈ types, type.VariablesBelow final.inference.next ∧ Safe protectedVars final type) := by
  have privacy := freshTypes count ready bound
  have properties := Detail.freshTypes_inferenceProperties count state ready
  have fields := freshTypes_fields count state
  rw [allocation] at privacy properties fields
  have expectedSafe := privacy.1 _ safe
  have argumentsSafe := safe_productMany protectedVars allocated types privacy.2
  have expectedBound := expectedBelow.weaken properties.1.next_le
  have productBound := Ty.variablesBelow_productMany properties.2.2
  have progress := Detail.unify_inferenceProgress properties.2.1.solved expectedBound productBound unified
  have finalReady := Detail.unify_preserves_inferenceReady properties.2.1 expectedBound productBound unified
  have transport := ProtectedVariables.unify expectedSafe argumentsSafe unified
  have finalLive := (live.transport fields.1 privacy.1).unify expectedSafe argumentsSafe unified
  exact ⟨PatternPrivacy.of_unchanged (privacy.1.trans transport) finalLive ((unify_requirements unified).trans fields.2),
    properties.1.trans progress, finalReady, fun type member => ⟨(properties.2.2 type member).weaken progress.next_le, transport _ (privacy.2 type member)⟩⟩



def RawBindersAvoid (protectedVars : List TypeVarId) (state : State) : Prop :=
  ∀ binder ∈ state.localBinders, ∀ q ∈ protectedVars, q ∉ binder.scheme.freeVariables

private def PatternIsolation (protectedVars : List TypeVarId) (initial final : State) : Prop :=
  RawBindersAvoid protectedVars final ∧ activeSchemeQuantifiers final = activeSchemeQuantifiers initial

private theorem PatternIsolation.trans {protectedVars : List TypeVarId} {first second third : State}
    (left : PatternIsolation protectedVars first second) (right : PatternIsolation protectedVars second third) :
    PatternIsolation protectedVars first third := ⟨right.1,right.2.trans left.2⟩

private theorem PatternIsolation.of_binders_eq {protectedVars : List TypeVarId} {initial final : State}
    (raw : RawBindersAvoid protectedVars initial) (same : final.localBinders = initial.localBinders) :
    PatternIsolation protectedVars initial final := by
  constructor
  · intro binder member q protectedMember
    exact raw binder (same ▸ member) q protectedMember
  · simp only [activeSchemeQuantifiers,same]

private theorem unify_raw {protectedVars : List TypeVarId} {state final : State} {left right : Ty}
    (raw : RawBindersAvoid protectedVars state) (unified : Detail.unify state left right = .ok final) :
    PatternIsolation protectedVars state final :=
  .of_binders_eq raw (congrArg LexicalScope.binders (Detail.unify_preserves_lexicalScope unified))

private theorem constructor_prefix_raw {protectedVars : List TypeVarId} {state allocated final : State}
    {dataType : ProgramDataSignature} {constructor : ProgramDataConstructorSignature}
    {instantiation : DataConstructorInstantiation} {expected : Ty}
    (raw : RawBindersAvoid protectedVars state)
    (allocation : Detail.freshDataConstructorInstantiation dataType constructor state = (instantiation,allocated))
    (unified : Detail.unify allocated instantiation.resultType expected = .ok final) :
    PatternIsolation protectedVars state final := by
  have scope := Detail.freshDataConstructorInstantiation_preserves_lexicalScope dataType constructor state
  rw [allocation] at scope
  exact .of_binders_eq raw ((congrArg LexicalScope.binders (Detail.unify_preserves_lexicalScope unified)).trans
    (congrArg LexicalScope.binders scope))

private theorem tuple_prefix_raw {protectedVars : List TypeVarId} {state allocated final : State}
    {count : Nat} {types : List Ty} {expected : Ty}
    (raw : RawBindersAvoid protectedVars state)
    (allocation : Detail.freshTypes count state = (types,allocated))
    (unified : Detail.unify allocated expected (Ty.productMany types) = .ok final) :
    PatternIsolation protectedVars state final := by
  have fields := freshTypes_fields count state
  rw [allocation] at fields
  exact .of_binders_eq raw ((congrArg LexicalScope.binders (Detail.unify_preserves_lexicalScope unified)).trans fields.1)

private theorem allocate_raw {protectedVars : List TypeVarId} {state : State} {type : Ty}
    (name : String) (span : Option Syntax.SourceSpan) (raw : RawBindersAvoid protectedVars state)
    (safe : Safe protectedVars state type) :
    PatternIsolation protectedVars state (state.allocateBinder name (.mono (state.resolve type)) span).2 := by
  constructor
  · intro binder member q protectedMember
    rcases List.mem_cons.mp member with rfl | member
    · intro occurs
      exact safe q (List.mem_filter.mp occurs).1 protectedMember
    · exact raw binder member q protectedMember
  · simp only [activeSchemeQuantifiers,State.allocateBinder,List.flatMap_cons,Scheme.mono,List.nil_append]

private def PatternCallIsolation (protectedVars : List TypeVarId) (fuel : Nat)
    (context : SourceInference.Context) (pattern : Syntax.Pattern) (expected : Ty)
    (seen : List String) (state : State) : Prop :=
  ∀ result, state.InferenceReady → expected.VariablesBelow state.inference.next →
    ProgramSignatureFormationValidated context.signatures →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    Safe protectedVars state expected → LiveBindersSafe protectedVars state → RawBindersAvoid protectedVars state →
    Detail.inferMatchPatternFlatFuel fuel context pattern expected seen state = .ok result →
    PatternIsolation protectedVars state result.state

private def PatternsCallIsolation (protectedVars : List TypeVarId) (fuel : Nat)
    (context : SourceInference.Context) (patterns : List Syntax.Pattern) (expected : List Ty)
    (seen : List String) (state : State) : Prop :=
  ∀ result, state.InferenceReady →
    (∀ type ∈ expected, type.VariablesBelow state.inference.next) →
    ProgramSignatureFormationValidated context.signatures →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    (∀ type ∈ expected, Safe protectedVars state type) → LiveBindersSafe protectedVars state → RawBindersAvoid protectedVars state →
    Detail.inferMatchPatternsFlatFuel fuel context patterns expected seen state = .ok result →
    PatternIsolation protectedVars state result.state

set_option maxHeartbeats 2000000 in
private theorem pattern_call_isolation (protectedVars : List TypeVarId) (fuel : Nat)
    (context : SourceInference.Context) (pattern : Syntax.Pattern) (expected : Ty)
    (seen : List String) (state : State) :
    PatternCallIsolation protectedVars fuel context pattern expected seen state := by
  apply Detail.inferMatchPatternFlatFuel.induct context
    (motive1 := fun fuel pattern expected seen state =>
      PatternCallIsolation protectedVars fuel context pattern expected seen state)
    (motive2 := fun fuel patterns expected seen state =>
      PatternsCallIsolation protectedVars fuel context patterns expected seen state)
  case case3 =>
    intros
    unfold PatternCallIsolation at *
    intro result ready expectedBelow formation bound expectedSafe live raw success
    unfold Detail.inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all [pure, Pure.pure, Except.pure]
    all_goals
      rename_i unified
      exact PatternIsolation.of_binders_eq raw
        (congrArg LexicalScope.binders (Detail.unify_preserves_lexicalScope unified))
  case case5 =>
    intros
    unfold PatternCallIsolation at *
    intro result ready expectedBelow formation bound expectedSafe live raw success
    unfold Detail.inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all [pure, Pure.pure, Except.pure]
    all_goals
      rename_i unified
      exact PatternIsolation.of_binders_eq raw
        (congrArg LexicalScope.binders (Detail.unify_preserves_lexicalScope unified))
  case case10 =>
    intros sourcePattern sourceExpected sourceSeen inputState sourceFuel
      leadingDot qualifiers constructorName sourceArguments patternEq branchEq
      flatArguments contextualBranch childrenIH
    unfold PatternCallIsolation at *
    intro result ready expectedBelow formation bound expectedSafe live raw success
    unfold Detail.inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all [pure, Pure.pure, Except.pure]
    all_goals try subst_vars
    all_goals first
      | have beforeChildren := contextual_prefix_private ready expectedBelow formation expectedSafe live
          (by assumption) (by assumption)
        have prefixRaw := unify_raw raw (by assumption)
        have child := childrenIH _ _ _ beforeChildren.2.2.1
          (fun type member => (beforeChildren.2.2.2 type member).1) formation
          (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) beforeChildren.2.1.next_le)
          (fun type member => (beforeChildren.2.2.2 type member).2) beforeChildren.1.2.1 prefixRaw.1 (by assumption)
        exact prefixRaw.trans child
      | have beforeChildren := explicit_prefix_private ready expectedBelow formation bound expectedSafe live
          (by assumption) rfl (by assumption)
        have prefixRaw := constructor_prefix_raw raw rfl (by assumption)
        have child := childrenIH _ _ _ beforeChildren.2.2.1
          (fun type member => (beforeChildren.2.2.2 type member).1) formation
          (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) beforeChildren.2.1.next_le)
          (fun type member => (beforeChildren.2.2.2 type member).2) beforeChildren.1.2.1 prefixRaw.1 (by assumption)
        exact prefixRaw.trans child
  case case11 =>
    intros sourcePattern sourceExpected sourceSeen inputState sourceFuel
      leadingDot qualifiers constructorName sourceArguments patternEq branchEq
      flatArguments explicitBranch childrenIH
    unfold PatternCallIsolation at *
    intro result ready expectedBelow formation bound expectedSafe live raw success
    unfold Detail.inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all [pure, Pure.pure, Except.pure]
    all_goals try subst_vars
    all_goals first
      | have beforeChildren := contextual_prefix_private ready expectedBelow formation expectedSafe live
          (by assumption) (by assumption)
        have prefixRaw := unify_raw raw (by assumption)
        have child := childrenIH _ _ _ beforeChildren.2.2.1
          (fun type member => (beforeChildren.2.2.2 type member).1) formation
          (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) beforeChildren.2.1.next_le)
          (fun type member => (beforeChildren.2.2.2 type member).2) beforeChildren.1.2.1 prefixRaw.1 (by assumption)
        exact prefixRaw.trans child
      | have beforeChildren := explicit_prefix_private ready expectedBelow formation bound expectedSafe live
          (by assumption) rfl (by assumption)
        have prefixRaw := constructor_prefix_raw raw rfl (by assumption)
        have child := childrenIH _ _ _ beforeChildren.2.2.1
          (fun type member => (beforeChildren.2.2.2 type member).1) formation
          (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) beforeChildren.2.1.next_le)
          (fun type member => (beforeChildren.2.2.2 type member).2) beforeChildren.1.2.1 prefixRaw.1 (by assumption)
        exact prefixRaw.trans child
  case case13 =>
    intros sourcePattern sourceExpected sourceSeen inputState sourceFuel
      elements patternEq sources argumentTypes allocatedState freshEq childrenIH
    unfold PatternCallIsolation at *
    intro result ready expectedBelow formation bound expectedSafe live raw success
    unfold Detail.inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all
    have argumentTypesEq : (Detail.freshTypes sources.length inputState).1 = argumentTypes :=
      congrArg Prod.fst freshEq
    have allocatedStateEq : (Detail.freshTypes sources.length inputState).2 = allocatedState :=
      congrArg Prod.snd freshEq
    have beforeChildren := tuple_prefix_private (count := sources.length) (types := argumentTypes)
      (allocated := allocatedState) ready expectedBelow bound expectedSafe live freshEq (by
        rw [← allocatedStateEq, ← argumentTypesEq]
        simpa only [sources] using (by assumption))
    have prefixRaw := tuple_prefix_raw (count := sources.length) (types := argumentTypes)
      (allocated := allocatedState) raw freshEq (by
        rw [← allocatedStateEq, ← argumentTypesEq]
        simpa only [sources] using (by assumption))
    have child := childrenIH _ _ beforeChildren.2.2.1
      (fun type member => (beforeChildren.2.2.2 type member).1) formation
      (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) beforeChildren.2.1.next_le)
      (fun type member => (beforeChildren.2.2.2 type member).2) beforeChildren.1.2.1 prefixRaw.1 (by
        rw [← argumentTypesEq]
        simpa only [sources] using (by assumption))
    exact prefixRaw.trans child
  case case17 =>
    intros fuel head rest expectedHead expectedTail seen state ihHead ihTail
    unfold PatternsCallIsolation
    unfold PatternCallIsolation at ihHead
    unfold PatternsCallIsolation at ihTail
    intro result ready expectedBelow formation bound expectedSafe live raw success
    simp only [Detail.inferMatchPatternsFlatFuel] at success
    cases headRun : Detail.inferMatchPatternFlatFuel fuel context head expectedHead seen state with
    | error error => simp [headRun, bind, Except.bind] at success
    | ok inferredHead =>
      simp only [headRun, bind, Except.bind] at success
      cases tailRun : Detail.inferMatchPatternsFlatFuel fuel context rest expectedTail inferredHead.names inferredHead.state with
      | error error => simp [tailRun] at success
      | ok inferredTail =>
        simp only [tailRun] at success
        injection success with resultEq
        subst result
        have headIsolation := ihHead inferredHead ready (expectedBelow _ List.mem_cons_self) formation
          bound (expectedSafe _ List.mem_cons_self) live raw headRun
        have headPrivacy := inferMatchPatternFlatFuel_private ready (expectedBelow _ List.mem_cons_self) formation
          bound (expectedSafe _ List.mem_cons_self) live headRun
        have headProperties := Detail.inferMatchPatternFlatFuel_inferenceProperties ready
          (expectedBelow _ List.mem_cons_self) formation headRun
        have tailPrivacy := ihTail inferredHead inferredTail headProperties.2
          (fun type member => (expectedBelow type (List.mem_cons_of_mem _ member)).weaken headProperties.1.next_le)
          formation (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) headProperties.1.next_le)
          (fun type member => headPrivacy.1 _ (expectedSafe type (List.mem_cons_of_mem _ member)))
          headPrivacy.2.1 headIsolation.1 tailRun
        exact headIsolation.trans tailPrivacy
  all_goals
    intros
    first | unfold PatternCallIsolation at * | unfold PatternsCallIsolation at *
    intro result ready expectedBelow formation bound expectedSafe live raw success
    first | unfold Detail.inferMatchPatternFlatFuel at success | unfold Detail.inferMatchPatternsFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals try simp_all
    all_goals try exact PatternIsolation.of_binders_eq raw rfl
    all_goals try exact (by simpa only using ih1 _ ready expectedBelow formation bound expectedSafe live raw (by assumption))
    all_goals
      try
        exact allocate_raw _ _ raw expectedSafe


/-- Actual pattern allocation preserves raw scheme avoidance and does not
introduce a generalized variable into the active quantifier inventory. -/
theorem inferMatchPatternFlatFuel_raw_isolation
    {protectedVars : List TypeVarId} {fuel : Nat} {context : SourceInference.Context}
    {pattern : Syntax.Pattern} {expected : Ty} {seen : List String} {state : State}
    {result : Detail.InferredPattern}
    (ready : state.InferenceReady) (expectedBelow : expected.VariablesBelow state.inference.next)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (expectedSafe : Safe protectedVars state expected) (live : LiveBindersSafe protectedVars state)
    (raw : RawBindersAvoid protectedVars state)
    (accepted : Detail.inferMatchPatternFlatFuel fuel context pattern expected seen state = .ok result) :
    RawBindersAvoid protectedVars result.state ∧
      activeSchemeQuantifiers result.state = activeSchemeQuantifiers state :=
  pattern_call_isolation protectedVars fuel context pattern expected seen state result
    ready expectedBelow formation bound expectedSafe live raw accepted

/-- Public pattern checking exposes the state from its actual flat traversal. -/
theorem inferMatchPatternFuel_raw_isolation
    {protectedVars : List TypeVarId} {fuel : Nat} {context : SourceInference.Context}
    {pattern : Syntax.Pattern} {expected : Ty} {state : State}
    {result : TypedMatchPattern × State}
    (ready : state.InferenceReady) (expectedBelow : expected.VariablesBelow state.inference.next)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (expectedSafe : Safe protectedVars state expected) (live : LiveBindersSafe protectedVars state)
    (raw : RawBindersAvoid protectedVars state)
    (accepted : Detail.inferMatchPatternFuel fuel context pattern expected state = .ok result) :
    RawBindersAvoid protectedVars result.2 ∧
      activeSchemeQuantifiers result.2 = activeSchemeQuantifiers state := by
  unfold Detail.inferMatchPatternFuel at accepted
  cases actual : Detail.inferMatchPatternFlatFuel fuel context pattern expected [] state with
  | error error => simp [actual, bind, Except.bind] at accepted
  | ok inferred =>
    simp only [actual, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    exact inferMatchPatternFlatFuel_raw_isolation ready expectedBelow formation bound expectedSafe live raw actual

/-- Individual live privacy for each active scheme combines into live privacy
for their actual flattened quantifier inventory. -/
theorem ActiveQuantifiersPrivate.all_live {state : State}
    (privateVars : ActiveQuantifiersPrivate state) :
    LiveBindersSafe (activeSchemeQuantifiers state) state := by
  intro binder member
  constructor
  · intro v occurs q image active
    obtain ⟨owner,ownerMember,quantified⟩ := List.mem_flatMap.mp active
    exact (privateVars owner ownerMember binder member).body v occurs q image quantified
  · intro requirement present type typeMember v occurs outside q image active
    obtain ⟨owner,ownerMember,quantified⟩ := List.mem_flatMap.mp active
    exact (privateVars owner ownerMember binder member).requirements
      requirement present type typeMember v occurs outside q image quantified

/-- Pattern recursion retains raw scheme isolation, allocator bounds and the
resolved privacy needed by later children, without requiring monomorphic
incoming binders. -/
theorem inferMatchPatternFuel_active_isolation
    {fuel : Nat} {context : SourceInference.Context}
    {pattern : Syntax.Pattern} {expected : Ty} {state : State}
    {result : TypedMatchPattern × State}
    (ready : state.InferenceReady) (expectedBelow : expected.VariablesBelow state.inference.next)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (bound : ActiveQuantifiersBelowNext state)
    (isolated : ActiveSchemeQuantifierIsolation state)
    (privateVars : ActiveQuantifiersPrivate state)
    (expectedSafe : Safe (activeSchemeQuantifiers state) state expected)
    (accepted : Detail.inferMatchPatternFuel fuel context pattern expected state = .ok result) :
    ActiveSchemeQuantifierIsolation result.2 ∧ ActiveQuantifiersBelowNext result.2 ∧
      ActiveQuantifiersPrivate result.2 := by
  have protectedBound := activeSchemeQuantifiers_below_next bound
  have raw := inferMatchPatternFuel_raw_isolation ready expectedBelow formation
    protectedBound expectedSafe privateVars.all_live isolated accepted
  have privacy := inferMatchPatternFuel_private ready expectedBelow formation
    protectedBound expectedSafe privateVars.all_live accepted
  have progress := Detail.inferMatchPatternFuel_inferenceProperties ready expectedBelow formation accepted
  refine ⟨?_,?_,?_⟩
  · intro binder member q active
    exact raw.1 binder member q (raw.2 ▸ active)
  · intro binder member q quantified
    have active : q ∈ activeSchemeQuantifiers state :=
      raw.2 ▸ List.mem_flatMap.mpr ⟨binder,member,quantified⟩
    exact Nat.lt_of_lt_of_le (protectedBound q active) progress.1.next_le
  · intro owner ownerMember binder member
    constructor
    · intro v occurs q image quantified
      have active : q ∈ activeSchemeQuantifiers state :=
        raw.2 ▸ List.mem_flatMap.mpr ⟨owner,ownerMember,quantified⟩
      exact (privacy.2.1 binder member).body v occurs q image active
    · intro requirement present type typeMember v occurs outside q image quantified
      have active : q ∈ activeSchemeQuantifiers state :=
        raw.2 ▸ List.mem_flatMap.mpr ⟨owner,ownerMember,quantified⟩
      exact (privacy.2.1 binder member).requirements
        requirement present type typeMember v occurs outside q image active

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferencePatternActiveOrigins
/-! Pattern traversal retains old binders and introduces only monomorphic
binders with empty scheme requirements. This is an actual scope fact, without
an incoming monomorphism or raw-isolation assumption. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

structure PatternScope (initial current : State) : Prop where
  quantified : activeSchemeQuantifiers current = activeSchemeQuantifiers initial
  retained : initial.localBinders ⊆ current.localBinders
  origin : ∀ binder ∈ current.localBinders, binder ∈ initial.localBinders ∨
    (binder.scheme.quantified = [] ∧ binder.schemeRequirements = [])

theorem PatternScope.refl (state : State) : PatternScope state state :=
  ⟨rfl,List.Subset.refl _,fun _ member => .inl member⟩

private theorem PatternScope.of_scope {start before after : State}
    (tracked : PatternScope start before) (scope : after.lexicalScope = before.lexicalScope) :
    PatternScope start after := by
  have same : after.localBinders = before.localBinders := congrArg LexicalScope.binders scope
  exact ⟨by simpa [activeSchemeQuantifiers,same] using tracked.quantified,
    same.symm ▸ tracked.retained,fun binder member => tracked.origin binder (same ▸ member)⟩

private theorem PatternScope.fresh {start state : State} (tracked : PatternScope start state) :
    PatternScope start state.fresh.2 := tracked.of_scope rfl

private theorem PatternScope.addRequirementWithId {start state : State}
    (tracked : PatternScope start state) (predicate : ProgramPredicate) :
    PatternScope start (state.addRequirementWithId predicate).2 := tracked.of_scope rfl

private theorem PatternScope.unify {start before after : State} {left right : Ty}
    (tracked : PatternScope start before) (accepted : Detail.unify before left right = .ok after) :
    PatternScope start after := tracked.of_scope (Detail.unify_preserves_lexicalScope accepted)

private theorem PatternScope.freshDataConstructorInstantiation {start state : State}
    (tracked : PatternScope start state) (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature) :
    PatternScope start (Detail.freshDataConstructorInstantiation dataType constructor state).2 :=
  tracked.of_scope (Detail.freshDataConstructorInstantiation_preserves_lexicalScope dataType constructor state)

private theorem PatternScope.allocateMonoBinder {start state : State}
    (tracked : PatternScope start state) (name : String) (type : Ty)
    (span : Option Syntax.SourceSpan) (comptime : Bool) :
    PatternScope start (state.allocateBinder name (.mono type) span comptime []).2 := by
  refine ⟨?_,tracked.retained.trans (List.subset_cons_self _ _),?_⟩
  · simpa only [activeSchemeQuantifiers,State.allocateBinder,List.flatMap_cons,Scheme.mono,List.nil_append]
      using tracked.quantified
  · intro binder member
    simp only [State.allocateBinder,List.mem_cons] at member
    rcases member with rfl | old
    · exact .inr ⟨rfl,rfl⟩
    · exact tracked.origin binder old

private theorem freshTypesTracking {start state : State}
    (tracked : PatternScope start state) (count : Nat) :
    PatternScope start (Detail.freshTypes count state).2 := by
  induction count generalizing state with
  | zero => exact tracked
  | succ count ih => exact ih tracked.fresh

private theorem integerPatternsTracking {start state : State}
    (tracked : PatternScope start state) (patterns : List IntegerPatternOrigin) :
    PatternScope start {state with integerPatterns := patterns} := tracked.of_scope rfl

private def PatternProperty {alpha : Type} (stateOf : alpha → State)
    (start state : State) (computation : Except Error alpha) : Prop :=
  ∀ result, computation = .ok result → PatternScope start state → PatternScope start (stateOf result)

private theorem flatPatternTracking (start : State) (fuel : Nat) (context : Frontend.SourceInference.Context)
    (pattern : Syntax.Pattern) (expected : Ty) (seen : List String) (state : State) :
    PatternProperty Detail.InferredPattern.state start state
      (Detail.inferMatchPatternFlatFuel fuel context pattern expected seen state) := by
  apply Detail.inferMatchPatternFlatFuel.induct context
    (motive1 := fun fuel pattern expected seen state =>
      PatternProperty Detail.InferredPattern.state start state
        (Detail.inferMatchPatternFlatFuel fuel context pattern expected seen state))
    (motive2 := fun fuel patterns expected seen state =>
      PatternProperty Detail.InferredPatterns.state start state
        (Detail.inferMatchPatternsFlatFuel fuel context patterns expected seen state))
  case case3 =>
    intros
    unfold PatternProperty at *
    intro result success tracked
    unfold Detail.inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all [pure, Pure.pure, Except.pure]
    all_goals exact (integerPatternsTracking (tracked.fresh.addRequirementWithId _) _).unify (by assumption)
  case case5 =>
    intros
    unfold PatternProperty at *
    intro result success tracked
    unfold Detail.inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all [pure, Pure.pure, Except.pure]
    all_goals exact (integerPatternsTracking (tracked.fresh.addRequirementWithId _) _).unify (by assumption)
  case case10 =>
    intros sourcePattern sourceExpected sourceSeen inputState sourceFuel leadingDot qualifiers constructorName sourceArguments
      patternEq branchEq flatArguments branch childrenIH
    unfold PatternProperty at *
    intro result success tracked
    unfold Detail.inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all [pure, Pure.pure, Except.pure]
    all_goals try subst_vars
    all_goals first
      | exact childrenIH _ _ _ (by assumption) (tracked.unify (by assumption))
      | exact childrenIH _ _ _ (by assumption)
          ((tracked.freshDataConstructorInstantiation _ _).unify (by assumption))
  case case11 =>
    intros sourcePattern sourceExpected sourceSeen inputState sourceFuel leadingDot qualifiers constructorName sourceArguments
      patternEq branchEq flatArguments branch childrenIH
    unfold PatternProperty at *
    intro result success tracked
    unfold Detail.inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all [pure, Pure.pure, Except.pure]
    all_goals try subst_vars
    all_goals first
      | exact childrenIH _ _ _ (by assumption) (tracked.unify (by assumption))
      | exact childrenIH _ _ _ (by assumption)
          ((tracked.freshDataConstructorInstantiation _ _).unify (by assumption))
  case case13 =>
    intros sourcePattern sourceExpected sourceSeen inputState sourceFuel elements patternEq sources argumentTypes allocatedState freshEq childrenIH
    unfold PatternProperty at *
    intro result success tracked
    unfold Detail.inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all
    rename_i unifyAction next unifyAccepted childAction inferred childAccepted
    simp only [sources] at freshEq
    rw [freshEq] at unifyAccepted childAccepted
    have freshTracked := freshTypesTracking tracked sources.length
    rw [freshEq] at freshTracked
    exact childrenIH _ _ childAccepted (freshTracked.unify unifyAccepted)
  case case17 =>
    intros fuel head rest expectedHead expectedTail seen state headIH tailIH
    unfold PatternProperty at *
    intro result success tracked
    simp only [Detail.inferMatchPatternsFlatFuel] at success
    cases headResult : Detail.inferMatchPatternFlatFuel fuel context head expectedHead seen state with
    | error error => simp [headResult, bind, Except.bind] at success
    | ok inferredHead =>
      simp only [headResult, bind, Except.bind] at success
      cases tailResult : Detail.inferMatchPatternsFlatFuel fuel context rest expectedTail inferredHead.names inferredHead.state with
      | error error => simp [tailResult] at success
      | ok inferredTail =>
        simp only [tailResult, pure, Pure.pure, Except.pure] at success
        cases success
        exact tailIH inferredHead inferredTail tailResult (headIH inferredHead headResult tracked)
  all_goals
    intros
    unfold PatternProperty at *
    intro result success tracked
    first | unfold Detail.inferMatchPatternFlatFuel at success | unfold Detail.inferMatchPatternsFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals try simp_all
    all_goals try exact tracked
    all_goals try exact tracked.allocateMonoBinder _ _ _ _
    all_goals try exact ih1 _ (by assumption) tracked


/-- The exact flat pattern computation retains the actual active scheme list
and identifies every added binder as monomorphic with no template rows. -/
theorem inferMatchPatternFlatFuel_scope
    {fuel : Nat} {context : SourceInference.Context} {pattern : Syntax.Pattern}
    {expected : Ty} {seen : List String} {initial : State} {result : Detail.InferredPattern}
    (accepted : Detail.inferMatchPatternFlatFuel fuel context pattern expected seen initial = .ok result) :
    PatternScope initial result.state :=
  flatPatternTracking initial fuel context pattern expected seen initial result accepted (.refl _)

/-- Public pattern inference returns the scope from the same flat computation. -/
theorem inferMatchPatternFuel_scope
    {fuel : Nat} {context : SourceInference.Context} {pattern : Syntax.Pattern}
    {expected : Ty} {initial : State} {result : TypedMatchPattern × State}
    (accepted : Detail.inferMatchPatternFuel fuel context pattern expected initial = .ok result) :
    PatternScope initial result.2 := by
  unfold Detail.inferMatchPatternFuel at accepted
  cases flatAccepted : Detail.inferMatchPatternFlatFuel fuel context pattern expected [] initial with
  | error error => simp [flatAccepted,bind,Except.bind] at accepted
  | ok inferred =>
    simp only [flatAccepted,bind,Except.bind,pure,Pure.pure,Except.pure,Except.ok.injEq] at accepted
    cases accepted
    exact inferMatchPatternFlatFuel_scope flatAccepted

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferencePatternActiveState
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
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceStatementLifetimePrivacy
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

namespace LocalLetRequirementTiming.Receipt

variable {wholeContext : SourceInference.Context} {wholeReturn : Ty}
    {evidenceState : State} {roots : List NodeId} {finalized : SourceInference.Result}
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {initial : State} {result : StatementResult}

/-- The new statement scheme quantifies only variables created by its initializer. -/
theorem lifetime_quantified_lower_bound
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    (receipt : SourceInference.LocalLetRequirementTiming.Receipt fuel context source initial result)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (backed : LiveTemplatesBacked initial)
    (origins : ActiveBinderCaptureOrigins initial (evidenceState.toTypedSource roots))
    (retained : receipt.binding.1 ∈ (evidenceState.toTypedSource roots).initializedLetBinders)
    (extension : finalized.substitution.SemanticallyExtends result.state.inference.substitution) :
    ∀ q ∈ receipt.binding.1.scheme.quantified, initial.inference.next ≤ q.index := by
  have inferred := receipt.initializer_inference ready formation canonical
  have templates := templates_before receipt backed ready wellFormed formation canonical
  have readyExtension : finalized.substitution.SemanticallyExtends receipt.ready.inference.substitution := by
    rwa [receipt.inference_eq] at extension
  have live : LiveBindersSafe receipt.binding.1.scheme.quantified receipt.ready :=
    generalized_live_from_finalizer resources (origins.congr_localBinders receipt.ready_binders)
      readyExtension retained rfl templates
  intro q quantified
  by_cases later : initial.inference.next ≤ q.index
  · exact later
  exfalso
  have earlier : q.index < initial.inference.next := Nat.lt_of_not_ge later
  have occurs : q ∈ (receipt.ready.resolve receipt.value.type).freeVariables :=
    (List.mem_filter.mp quantified).1
  have outside := inferred.2.1.solved.apply_variables_outside_domain receipt.value.type q occurs
  have fixed : receipt.ready.inference.substitution.apply (.variable q) = .variable q := by
    simp only [Substitution.apply,
      (Substitution.lookup?_eq_none_iff_not_mem_domain _ _).mpr outside, Option.getD_none]
  have backwards : ∀ type, Safe receipt.binding.1.scheme.quantified receipt.ready type →
      Safe [q] initial.allocateStatementId.2 type := by
    intro type privateType v present member
    have same : v = q := List.mem_singleton.mp member
    subst v
    exact privateType q (fixed_variable_occurs_at_final inferred.1.substitution_extends fixed present) quantified
  have entryLive : LiveBindersSafe [q] initial.allocateStatementId.2 := by
    intro binder member
    have readyMember : binder ∈ receipt.ready.localBinders := by
      rw [receipt.ready_binders]
      exact member
    have prior := live binder readyMember
    constructor
    · intro v free
      exact backwards _ (prior.1 v free)
    · intro requirement present type typeMember v free unbound
      exact backwards _ (prior.2 requirement present type typeMember v free unbound)
  have actual := inferExprFuel_private [q] fuel context receipt.initializer receipt.expected
    initial.allocateStatementId.2 ready.allocateStatementId wellFormed
    (by intro v member; obtain rfl := List.mem_singleton.mp member; exact earlier)
    entryLive catalog formation canonical (receipt.annotationAccepted.variablesBelow _)
    (fun type present => safe_closed _ _ (receipt.annotationAccepted.variablesBelow 0 type present))
    _ receipt.child
  exact actual.2.1 q occurs (List.mem_singleton_self _)

/-- A statement initializer keeps its new quantifiers out of every entering type. -/
theorem lifetime_older_type_safe
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    (receipt : SourceInference.LocalLetRequirementTiming.Receipt fuel context source initial result)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (backed : LiveTemplatesBacked initial)
    (origins : ActiveBinderCaptureOrigins initial (evidenceState.toTypedSource roots))
    (retained : receipt.binding.1 ∈ (evidenceState.toTypedSource roots).initializedLetBinders)
    (extension : finalized.substitution.SemanticallyExtends result.state.inference.substitution)
    {type : Ty} (typeBelow : type.VariablesBelow initial.inference.next) :
    Safe receipt.binding.1.scheme.quantified result.state type := by
  have templates := templates_before receipt backed ready wellFormed formation canonical
  have readyExtension : finalized.substitution.SemanticallyExtends receipt.ready.inference.substitution := by
    rwa [receipt.inference_eq] at extension
  have live : LiveBindersSafe receipt.binding.1.scheme.quantified receipt.ready :=
    generalized_live_from_finalizer resources (origins.congr_localBinders receipt.ready_binders)
      readyExtension retained rfl templates
  have safe := inferExprFuel_fresh_quantifiers_safe ready.allocateStatementId wellFormed catalog formation canonical
    (receipt.annotationAccepted.variablesBelow 0) receipt.child
    (lifetime_quantified_lower_bound resources receipt ready wellFormed catalog formation canonical
      backed origins retained extension) live typeBelow
  simpa only [Safe, State.resolve, InferState.resolve, receipt.inference_eq] using safe

end LocalLetRequirementTiming.Receipt

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceStatementPrivacyResume
/-! A real statement position retains the entire suffix, including the block's
result type. Older return expressions may determine that type, so their actual
allocator bounds are retained rather than assuming a closed return type. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

structure StatementPrivacyResume (context : SourceInference.Context)
    (source : Syntax.Statement) (expected : Ty) (initial : State) (final : BlockResult)
    (EntryInvariant : State → Prop := fun _ => True)
    extends StatementInferenceContinuation.Occurrence context source expected initial final.state where
  entryInvariant : EntryInvariant entry
  entryWellFormed : entry.RequirementsWellFormed
  entryNodesBelow : entry.NodesBelowNextOccurrence
  resultReady : result.state.InferenceReady
  resultWellFormed : result.state.RequirementsWellFormed
  expectedBelow : expected.VariablesBelow result.state.inference.next
  resume : ∀ protectedVars : List TypeVarId,
    (∀ v ∈ protectedVars, v.index < result.state.inference.next) →
    LiveBindersSafe protectedVars result.state →
    Safe protectedVars result.state expected →
    Safe protectedVars result.state result.type →
    (∀ type, type.VariablesBelow entry.inference.next →
      Safe protectedVars result.state type) →
    SafeTransport protectedVars result.state final.state ∧
      Safe protectedVars final.state final.type ∧
      LiveBindersSafe protectedVars final.state ∧
      ∀ row ∈ final.state.requirements, row ∉ result.state.requirements →
        PredicateSafe protectedVars final.state row.predicate

theorem statementPrivacyResume_of_position_with_invariant
    {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.Statement}
    {expected : Ty} {initial : State} {result : BlockResult} {index : Nat} {source : Syntax.Statement}
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (nodesBelow : initial.NodesBelowNextOccurrence)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes))
    (expectedBelow : expected.VariablesBelow initial.inference.next)
    (accepted : inferStatementsFuel fuel context sources expected initial = .ok result)
    (position : sources[index]? = some source)
    {EntryInvariant : State → Prop}
    (initialInvariant : EntryInvariant initial)
    (stepInvariant : ∀ {stepFuel : Nat} {statement : Syntax.Statement} {before : State}
        {after : StatementResult},
      before.InferenceReady → before.RequirementsWellFormed →
      expected.VariablesBelow before.inference.next →
      after.state.InferenceProgress result.state → after.state.nodes <+: result.state.nodes →
      inferStatementFuel stepFuel context statement expected before = .ok after →
      EntryInvariant before → EntryInvariant after.state) :
    Nonempty (StatementPrivacyResume context source expected initial result EntryInvariant) := by
  induction fuel generalizing sources initial result index with
  | zero => simp [inferStatementsFuel] at accepted
  | succ fuel ih =>
    cases sources with
    | nil => simp at position
    | cons head rest =>
      cases headRun : inferStatementFuel fuel context head expected initial with
      | error error => simp [inferStatementsFuel,headRun,bind,Except.bind] at accepted
      | ok headResult =>
        have headProgress := inferStatementFuel_inferenceProperties ready formation canonical expectedBelow headRun
        have headWellFormed := (inferStatementFuel_direct_progress headRun).wellFormed wellFormed
        have headBelow := (inferStatementFuel_occurrenceBoundExtends headRun).nodesBelowNextOccurrence nodesBelow
        have afterExpected := expectedBelow.weaken headProgress.1.next_le
        cases rest with
        | nil =>
          simp only [inferStatementsFuel,headRun,bind,Except.bind,pure,Pure.pure,Except.pure,Except.ok.injEq] at accepted
          subst result
          cases index with
          | zero =>
            simp only [List.getElem?_cons_zero,Option.some.injEq] at position
            subst source
            refine ⟨{
              fuel := fuel, entry := initial, result := headResult, accepted := headRun,
              ready := ready, before := .refl ready.solved,
              continuation := .refl headProgress.2.1.solved,
              retained := List.prefix_refl _,
              entryInvariant := initialInvariant, entryWellFormed := wellFormed,
              entryNodesBelow := nodesBelow,
              resultReady := headProgress.2.1, resultWellFormed := headWellFormed,
              expectedBelow := afterExpected, resume := ?_ }⟩
            intro protectedVars bound live safe resultSafe olderSafe
            refine ⟨.refl _ _,?_,live,fun row member fresh => False.elim (fresh member)⟩
            dsimp
            split
            · exact resultSafe
            · exact safe_closed _ _ (by simp [Ty.VariablesBelow,Ty.freeVariables,Ty.unit])
          | succ index => simp at position
        | cons next remaining =>
          cases tailRun : inferStatementsFuel fuel context (next::remaining) expected headResult.state with
          | error error => simp [inferStatementsFuel,headRun,tailRun,bind,Except.bind] at accepted
          | ok tailResult =>
            simp only [inferStatementsFuel,headRun,tailRun,bind,Except.bind,pure,Pure.pure,Except.pure,Except.ok.injEq] at accepted
            subst result
            cases index with
            | zero =>
              simp only [List.getElem?_cons_zero,Option.some.injEq] at position
              subst source
              have tailProgress := inferStatementsFuel_inferenceProperties headProgress.2.1 formation canonical afterExpected tailRun
              refine ⟨{
                fuel := fuel, entry := initial, result := headResult, accepted := headRun,
                ready := ready, before := .refl ready.solved,
                continuation := tailProgress.1,
                retained := inferStatementsFuel_preserves_nodesPrefix (result := tailResult) tailRun
                  (List.prefix_refl _) headBelow (Nat.le_refl _),
                entryInvariant := initialInvariant, entryWellFormed := wellFormed,
                entryNodesBelow := nodesBelow,
                resultReady := headProgress.2.1, resultWellFormed := headWellFormed,
                expectedBelow := afterExpected, resume := ?_ }⟩
              intro protectedVars bound live safe resultSafe olderSafe
              have actual := inferStatementsFuel_private protectedVars fuel context (next::remaining) expected headResult.state
                headProgress.2.1 headWellFormed bound live catalog formation canonical afterExpected safe tailResult tailRun
              refine ⟨actual.1,?_,actual.2.2.1,actual.2.2.2⟩
              dsimp
              split
              · exact actual.2.1
              · split
                · exact actual.1 _ resultSafe
                · exact actual.2.1
            | succ index =>
              have restPosition : (next::remaining)[index]? = some source := position
              have tailProgress := inferStatementsFuel_inferenceProperties headProgress.2.1 formation canonical afterExpected tailRun
              have retainedHead := inferStatementsFuel_preserves_nodesPrefix (result := tailResult)
                tailRun (List.prefix_refl _) headBelow (Nat.le_refl _)
              have headInvariant := stepInvariant ready wellFormed expectedBelow tailProgress.1
                retainedHead headRun initialInvariant
              obtain ⟨found⟩ := ih headProgress.2.1 headWellFormed headBelow afterExpected tailRun restPosition
                headInvariant stepInvariant
              refine ⟨{
                fuel := found.fuel, entry := found.entry, result := found.result, accepted := found.accepted,
                ready := found.ready, before := headProgress.1.trans found.before,
                continuation := found.continuation, retained := found.retained,
                entryInvariant := found.entryInvariant, entryWellFormed := found.entryWellFormed,
                entryNodesBelow := found.entryNodesBelow,
                resultReady := found.resultReady, resultWellFormed := found.resultWellFormed,
                expectedBelow := found.expectedBelow, resume := ?_ }⟩
              intro protectedVars bound live safe resultSafe olderSafe
              have actual := found.resume protectedVars bound live safe resultSafe olderSafe
              refine ⟨actual.1,?_,actual.2.2.1,actual.2.2.2⟩
              dsimp
              split
              · exact actual.2.1
              · split
                · exact actual.1 _ (olderSafe headResult.type
                    (headProgress.2.2.weaken found.before.next_le))
                · exact actual.2.1

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end
