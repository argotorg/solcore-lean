import Solcore.SourceSemantics.Internal.Inference.LetCertificates
import Solcore.SourceSemantics.Internal.Inference.LedgerSoundness
import Solcore.SourceSemantics.Internal.Inference.ExpressionRetained
import Solcore.SourceSemantics.Internal.Inference.ExpressionInduction
import Solcore.SourceSemantics.Internal.Privacy.ProtectedVariables
import Solcore.SourceSemantics.Internal.Inference.Soundness

/-!
# State of the selected route

The state that selected soundness threads through expressions, lists, statements and lets, with its
support lemmas.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedExpressionState
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem RecursiveExpressionInvariant.ofExpression
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {finalized : Frontend.SourceInference.Result}
    {initial final : State} {inferred : InferredExpression}
    {expression : Syntax.Expr} {expected : Option Ty}
    {semanticContext : SourceSemantics.Context} {fuel : Nat}
    (invariant : RecursiveExpressionInvariant wholeContext finalized initial semanticContext)
    (signatureFormation : ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ signature ∈ inferenceContext.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (extension : finalized.substitution.SemanticallyExtends final.inference.substitution)
    (success : Detail.inferExprFuel fuel inferenceContext expression expected initial = .ok (inferred, final)) :
    RecursiveExpressionInvariant wholeContext finalized final semanticContext := by
  have properties := Detail.inferExprFuel_inferenceProperties invariant.ready
    signatureFormation functionsCanonical expectedBelow success
  refine {
    active := invariant.active.inferExprFuel success
    ready := properties.2.1
    bindersBelow := Detail.inferExprFuel_preserves_localBindersBelowNextLocal invariant.bindersBelow success
    nodesBelow := (Detail.inferExprFuel_occurrenceBoundExtends success).nodesBelowNextOccurrence invariant.nodesBelow
    schemeIsolation := ?_
    substitutionExtension := extension
    signaturesEq := invariant.signaturesEq
    typeParametersEq := invariant.typeParametersEq
    declarationEq := invariant.declarationEq
    residual := invariant.residual
    solvedRequirementsEq := invariant.solvedRequirementsEq
    assumptionsMono := invariant.assumptionsMono
  }
  apply activeSchemeQuantifierIsolation_transport invariant.schemeIsolation
  have scopeEq := Detail.inferExprFuel_success_lexicalScope_eq success
  simpa only [State.lexicalScope] using congrArg LexicalScope.binders scopeEq

theorem ActualStateInvariant.allocateExpressionId
    {initial final : State} {source : TypedSource} {id : ExpressionId}
    (invariant : ActualStateInvariant initial source)
    (allocation : initial.allocateExpressionId = (id, final)) : ActualStateInvariant final source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  have stateEq : initial.allocateExpressionId.2 = final := congrArg Prod.snd allocation
  refine ⟨⟨pending, ?_⟩, ?_, ?_, invariant.sourceMonomorphic⟩
  · rw [← stateEq]
    exact ledger.allocateExpressionId
  · apply invariant.origins.congr_localBinders
    rw [← stateEq]
    rfl
  · apply activeQuantifiersBelowNext_transport invariant.quantifiersBelow
    · rw [← stateEq]; rfl
    · rw [← stateEq]; exact Nat.le_refl _

theorem ActualStateInvariant.ofExpression
    {fuel : Nat}
    {context : Frontend.SourceInference.Context} {expression : Syntax.Expr} {expected : Option Ty}
    {initial final : State} {inferred : InferredExpression} {source : TypedSource}
    (invariant : ActualStateInvariant initial source)
    (success : Detail.inferExprFuel fuel context expression expected initial = .ok (inferred, final))
    (nextLe : initial.inference.next ≤ final.inference.next) :
    ActualStateInvariant final source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  refine ⟨⟨pending, (actualLedgerFamily fuel).expression success ledger⟩,
    invariant.origins.inferExprFuel success, ?_, invariant.sourceMonomorphic⟩
  exact activeQuantifiersBelowNext_transport invariant.quantifiersBelow
    (congrArg LexicalScope.binders (Detail.inferExprFuel_success_lexicalScope_eq success)) nextLe

theorem ActualStateInvariant.fresh
    {state : State} {source : TypedSource}
    (invariant : ActualStateInvariant state source) : ActualStateInvariant state.fresh.2 source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  exact ⟨⟨pending, ledger.fresh⟩, invariant.origins.congr_localBinders rfl,
    activeQuantifiersBelowNext_transport invariant.quantifiersBelow rfl (Nat.le_succ _), invariant.sourceMonomorphic⟩

theorem ActualStateInvariant.unify
    {initial final : State} {source : TypedSource} {left right : Ty}
    (invariant : ActualStateInvariant initial source)
    (success : Detail.unify initial left right = .ok final) : ActualStateInvariant final source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  have bindersEq := congrArg LexicalScope.binders (Detail.unify_preserves_lexicalScope success)
  refine ⟨⟨pending, ledger.unify success⟩, invariant.origins.congr_localBinders bindersEq,
    activeQuantifiersBelowNext_transport invariant.quantifiersBelow bindersEq ?_, invariant.sourceMonomorphic⟩
  unfold Detail.unify at success
  cases unification : initial.inference.unify left right with
  | error error => simp [Detail.liftUnification, unification, bind, Except.bind] at success
  | ok inference =>
    simp [Detail.liftUnification, unification, bind, Except.bind] at success
    cases success
    rw [InferState.unify_next unification]
    exact Nat.le_refl _

theorem ActualStateInvariant.allocateMonoBinder
    {state : State} {source : TypedSource}
    (invariant : ActualStateInvariant state source)
    (name : String) (type : Ty) (span : Option Syntax.SourceSpan) (comptime : Bool) :
    ActualStateInvariant (state.allocateBinder name (.mono type) span comptime []).2 source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  refine ⟨⟨pending, ledger.allocateBinderWithoutRequirements name (.mono type) span comptime⟩,
    invariant.origins.allocateBinder rfl (.inl rfl), ?_, invariant.sourceMonomorphic⟩
  exact activeQuantifiersBelowNext_allocateBinder state name (.mono type) span comptime []
    invariant.quantifiersBelow (by simp [Scheme.mono])

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedExpressionListState
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem RecursiveExpressionInvariant.ofExpressions
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {finalized : Frontend.SourceInference.Result}
    {initial final : State} {inferred : List InferredExpression}
    {expressions : List Syntax.Expr}
    {semanticContext : SourceSemantics.Context} {fuel : Nat}
    (invariant : RecursiveExpressionInvariant wholeContext finalized initial semanticContext)
    (signatureFormation : ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ signature ∈ inferenceContext.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (extension : finalized.substitution.SemanticallyExtends final.inference.substitution)
    (success : Detail.inferExprsFuel fuel inferenceContext expressions initial = .ok (inferred, final)) :
    RecursiveExpressionInvariant wholeContext finalized final semanticContext := by
  have properties := Detail.inferExprsFuel_inferenceProperties invariant.ready
    signatureFormation functionsCanonical success
  refine {
    active := invariant.active.inferExprsFuel success
    ready := properties.2.1
    bindersBelow := Detail.inferExprsFuel_preserves_localBindersBelowNextLocal invariant.bindersBelow success
    nodesBelow := (Detail.inferExprsFuel_occurrenceBoundExtends success).nodesBelowNextOccurrence invariant.nodesBelow
    schemeIsolation := ?_
    substitutionExtension := extension
    signaturesEq := invariant.signaturesEq
    typeParametersEq := invariant.typeParametersEq
    declarationEq := invariant.declarationEq
    residual := invariant.residual
    solvedRequirementsEq := invariant.solvedRequirementsEq
    assumptionsMono := invariant.assumptionsMono
  }
  apply activeSchemeQuantifierIsolation_transport invariant.schemeIsolation
  have scopeEq := Detail.inferExprsFuel_success_lexicalScope_eq success
  simpa only [State.lexicalScope] using congrArg LexicalScope.binders scopeEq

theorem ActualStateInvariant.ofExpressions
    {fuel : Nat}
    {context : Frontend.SourceInference.Context} {expressions : List Syntax.Expr}
    {initial final : State} {inferred : List InferredExpression} {source : TypedSource}
    (invariant : ActualStateInvariant initial source)
    (success : Detail.inferExprsFuel fuel context expressions initial = .ok (inferred, final))
    (nextLe : initial.inference.next ≤ final.inference.next) :
    ActualStateInvariant final source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  refine ⟨⟨pending, (actualLedgerFamily fuel).expressions success ledger⟩,
    invariant.origins.inferExprsFuel success, ?_, invariant.sourceMonomorphic⟩
  exact activeQuantifiersBelowNext_transport invariant.quantifiersBelow
    (congrArg LexicalScope.binders (Detail.inferExprsFuel_success_lexicalScope_eq success)) nextLe

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedInferenceSupport
/-! Old metavariables in live inference types remain supported by the same entry
roots while those roots are normalized by each genuine unifier update. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem
namespace InferenceSupport

def Supported (cutoff : Nat) (roots : List Ty) (type : Ty) : Prop :=
  ∀ metavariable, metavariable ∈ type.freeVariables → metavariable.index < cutoff →
    ∃ root ∈ roots, metavariable ∈ root.freeVariables

def Resolved (cutoff : Nat) (roots : List Ty) (state : State) (type : Ty) : Prop :=
  Supported cutoff (roots.map state.resolve) (state.resolve type)

def Transport (cutoff : Nat) (roots : List Ty) (before after : State) : Prop :=
  ∀ type, Resolved cutoff roots before type → Resolved cutoff roots after type

theorem mem_apply_of_lookup_none (substitution : Substitution)
    (metavariable : TypeVarId) (type : Ty)
    (found : substitution.lookup? metavariable = none)
    (member : metavariable ∈ type.freeVariables) :
    metavariable ∈ (substitution.apply type).freeVariables := by
  induction type with
  | «variable» source =>
    have same : metavariable = source := by simpa [Ty.freeVariables] using member
    subst source
    simp [Substitution.apply, found, Ty.freeVariables]
  | parameter name => simp [Ty.freeVariables] at member
  | constructor name => simp [Ty.freeVariables] at member
  | application left right leftIH rightIH =>
    rw [Ty.mem_freeVariables_application_iff] at member
    simp only [Substitution.apply, Ty.mem_freeVariables_application_iff]
    exact member.elim (fun occurs => Or.inl (leftIH occurs))
      (fun occurs => Or.inr (rightIH occurs))
  | function left right leftIH rightIH =>
    rw [Ty.mem_freeVariables_function_iff] at member
    simp only [Substitution.apply, Ty.mem_freeVariables_function_iff]
    exact member.elim (fun occurs => Or.inl (leftIH occurs))
      (fun occurs => Or.inr (rightIH occurs))
  | product left right leftIH rightIH =>
    rw [Ty.mem_freeVariables_product_iff] at member
    simp only [Substitution.apply, Ty.mem_freeVariables_product_iff]
    exact member.elim (fun occurs => Or.inl (leftIH occurs))
      (fun occurs => Or.inr (rightIH occurs))
  | mapping left right leftIH rightIH =>
    rw [Ty.mem_freeVariables_mapping_iff] at member
    simp only [Substitution.apply, Ty.mem_freeVariables_mapping_iff]
    exact member.elim (fun occurs => Or.inl (leftIH occurs))
      (fun occurs => Or.inr (rightIH occurs))
  | proxy inner induction => exact induction member
  | comptime inner induction => exact induction member
  | error => simp [Ty.freeVariables] at member

theorem range_supported_of_unifyTypes
    {cutoff : Nat} {roots : List Ty} {left right : Ty} {update : Substitution}
    (leftSupported : Supported cutoff roots left)
    (rightSupported : Supported cutoff roots right)
    (accepted : Unification.unifyTypes left right = .ok update) :
    ∀ {key replacement}, (key, replacement) ∈ update →
      Supported cutoff roots replacement := by
  intro key replacement entry metavariable member old
  classical
  by_cases supported : ∃ root ∈ roots, metavariable ∈ root.freeVariables
  · exact supported
  have absent := supported
  apply False.elim
  let guard : Substitution := [(metavariable, Ty.unit)]
  have outsideLeft : ∀ candidate, candidate ∈ left.freeVariables →
      candidate ∉ guard.domain := by
    intro candidate occurs guarded
    have same : candidate = metavariable := by
      simpa [guard, Substitution.domain] using guarded
    subst candidate
    exact absent (leftSupported metavariable occurs old)
  have outsideRight : ∀ candidate, candidate ∈ right.freeVariables →
      candidate ∉ guard.domain := by
    intro candidate occurs guarded
    have same : candidate = metavariable := by
      simpa [guard, Substitution.domain] using guarded
    subst candidate
    exact absent (rightSupported metavariable occurs old)
  have avoids : update.RangeAvoidsDomain guard := Unification.unifyTypes_rangeAvoidsDomain
    outsideLeft outsideRight accepted
  exact avoids entry metavariable member (by simp [guard, Substitution.domain])

theorem supported_apply {cutoff next : Nat} {roots : List Ty}
    {substitution : Substitution} (type : Ty)
    (solved : substitution.SolvedBelow next)
    (rangeSupported : ∀ {key replacement}, (key, replacement) ∈ substitution →
      Supported cutoff roots replacement)
    (supported : Supported cutoff roots type) :
    Supported cutoff (roots.map substitution.apply) (substitution.apply type) := by
  have retained : ∀ metavariable, metavariable ∉ substitution.domain →
      (∃ root ∈ roots, metavariable ∈ root.freeVariables) →
      ∃ root ∈ roots.map substitution.apply, metavariable ∈ root.freeVariables := by
    intro metavariable outside source
    obtain ⟨root, member, occurs⟩ := source
    refine ⟨substitution.apply root, List.mem_map.mpr ⟨root, member, rfl⟩, ?_⟩
    exact mem_apply_of_lookup_none substitution metavariable root
      ((Substitution.lookup?_eq_none_iff_not_mem_domain _ _).mpr outside) occurs
  induction type with
  | «variable» source =>
    intro metavariable member old
    cases found : substitution.lookup? source with
    | none =>
      have same : metavariable = source := by
        simpa [Substitution.apply, found, Ty.freeVariables] using member
      subst source
      exact retained metavariable
        ((Substitution.lookup?_eq_none_iff_not_mem_domain _ _).mp found)
        (supported metavariable (by simp [Ty.freeVariables]) old)
    | some replacement =>
      have occurs : metavariable ∈ replacement.freeVariables := by
        simpa [Substitution.apply, found] using member
      exact retained metavariable (solved.lookup_range_outside_domain found occurs)
        (rangeSupported (Substitution.lookup?_eq_some_mem found) metavariable occurs old)
  | parameter name => simp [Supported, Substitution.apply, Ty.freeVariables]
  | constructor name => simp [Supported, Substitution.apply, Ty.freeVariables]
  | application left right leftIH rightIH =>
    intro metavariable member old
    simp only [Substitution.apply, Ty.mem_freeVariables_application_iff] at member
    rcases member with occurs | occurs
    · exact leftIH (fun candidate member lower => supported candidate
        ((Ty.mem_freeVariables_application_iff _ _ _).mpr (Or.inl member)) lower)
        metavariable occurs old
    · exact rightIH (fun candidate member lower => supported candidate
        ((Ty.mem_freeVariables_application_iff _ _ _).mpr (Or.inr member)) lower)
        metavariable occurs old
  | function left right leftIH rightIH =>
    intro metavariable member old
    simp only [Substitution.apply, Ty.mem_freeVariables_function_iff] at member
    rcases member with occurs | occurs
    · exact leftIH (fun candidate member lower => supported candidate
        ((Ty.mem_freeVariables_function_iff _ _ _).mpr (Or.inl member)) lower)
        metavariable occurs old
    · exact rightIH (fun candidate member lower => supported candidate
        ((Ty.mem_freeVariables_function_iff _ _ _).mpr (Or.inr member)) lower)
        metavariable occurs old
  | product left right leftIH rightIH =>
    intro metavariable member old
    simp only [Substitution.apply, Ty.mem_freeVariables_product_iff] at member
    rcases member with occurs | occurs
    · exact leftIH (fun candidate member lower => supported candidate
        ((Ty.mem_freeVariables_product_iff _ _ _).mpr (Or.inl member)) lower)
        metavariable occurs old
    · exact rightIH (fun candidate member lower => supported candidate
        ((Ty.mem_freeVariables_product_iff _ _ _).mpr (Or.inr member)) lower)
        metavariable occurs old
  | mapping left right leftIH rightIH =>
    intro metavariable member old
    simp only [Substitution.apply, Ty.mem_freeVariables_mapping_iff] at member
    rcases member with occurs | occurs
    · exact leftIH (fun candidate member lower => supported candidate
        ((Ty.mem_freeVariables_mapping_iff _ _ _).mpr (Or.inl member)) lower)
        metavariable occurs old
    · exact rightIH (fun candidate member lower => supported candidate
        ((Ty.mem_freeVariables_mapping_iff _ _ _).mpr (Or.inr member)) lower)
        metavariable occurs old
  | proxy inner induction => exact induction supported
  | comptime inner induction => exact induction supported
  | error => simp [Supported, Substitution.apply, Ty.freeVariables]

theorem unify {cutoff : Nat} {roots : List Ty} {before after : State}
    {left right : Ty}
    (ready : before.InferenceReady)
    (leftBelow : left.VariablesBelow before.inference.next)
    (rightBelow : right.VariablesBelow before.inference.next)
    (leftSupported : Resolved cutoff roots before left)
    (rightSupported : Resolved cutoff roots before right)
    (accepted : Detail.unify before left right = .ok after) :
    Transport cutoff roots before after := by
  unfold Detail.unify at accepted
  cases unified : before.inference.unify left right with
  | error error => simp [unified, Detail.liftUnification, bind, Except.bind] at accepted
  | ok inference =>
    simp only [unified, Detail.liftUnification, bind, Except.bind,
      pure, Pure.pure, Except.pure] at accepted
    cases accepted
    unfold InferState.unify at unified
    cases update : Unification.unifyTypes (before.inference.resolve left)
        (before.inference.resolve right) with
    | error error => simp [update, bind, Except.bind] at unified
    | ok substitution =>
      simp only [update, bind, Except.bind, pure, Pure.pure, Except.pure] at unified
      cases unified
      have solved := Unification.unifyTypes_solvedBelow
        (ready.solved.variablesBelow_apply leftBelow)
        (ready.solved.variablesBelow_apply rightBelow) update
      have rangeSupported : ∀ {key replacement}, (key, replacement) ∈ substitution →
          Supported cutoff (roots.map before.resolve) replacement :=
        range_supported_of_unifyTypes leftSupported rightSupported update
      intro type supported
      have transported := supported_apply (before.resolve type) solved
        rangeSupported supported
      change Supported cutoff
        (roots.map fun type => (substitution.compose before.inference.substitution).apply type)
        ((substitution.compose before.inference.substitution).apply type)
      simpa only [State.resolve, InferState.resolve,
        Substitution.compose_apply, List.map_map, Function.comp_def] using transported

theorem Transport.refl (cutoff : Nat) (roots : List Ty) (state : State) :
    Transport cutoff roots state state := by intro _ supported; exact supported

theorem Transport.trans {cutoff : Nat} {roots : List Ty}
    {first second third : State}
    (left : Transport cutoff roots first second)
    (right : Transport cutoff roots second third) :
    Transport cutoff roots first third := by
  intro type supported
  exact right type (left type supported)

theorem Transport.of_substitution_eq {cutoff : Nat} {roots : List Ty}
    {before after : State}
    (same : after.inference.substitution = before.inference.substitution) :
    Transport cutoff roots before after := by
  intro type supported
  change Supported cutoff (roots.map fun type => after.inference.substitution.apply type)
    (after.inference.substitution.apply type)
  rw [same]
  exact supported


theorem Transport.of_resolve_eq {cutoff : Nat} {roots : List Ty}
    {before after : State}
    (same : ∀ type, after.resolve type = before.resolve type) :
    Transport cutoff roots before after := by
  intro type supported
  have functions : after.resolve = before.resolve := funext same
  simpa only [Resolved, functions] using supported

theorem resolved_normalized {cutoff : Nat} {roots : List Ty}
    {state : State} {type : Ty} (ready : state.InferenceReady)
    (supported : Resolved cutoff roots state type) :
    Resolved cutoff roots state (state.resolve type) := by
  simpa only [Resolved, State.resolve, InferState.resolve,
    ready.solved.apply_idempotent] using supported

theorem resolved_root {cutoff : Nat} {roots : List Ty}
    {state : State} {type : Ty} (member : type ∈ roots) :
    Resolved cutoff roots state type := by
  intro metavariable occurs _
  exact ⟨state.resolve type, List.mem_map.mpr ⟨type, member, rfl⟩, occurs⟩

theorem resolved_closed (cutoff : Nat) (roots : List Ty) (state : State)
    {type : Ty} (closed : type.freeVariables = []) :
    Resolved cutoff roots state type := by
  have fixed : state.resolve type = type := by
    apply Ty.apply_eq_self_of_domain_disjoint_freeVariables
    intro metavariable _ member
    simp only [closed, List.not_mem_nil] at member
  intro metavariable member _
  rw [fixed, closed] at member
  simp at member

theorem fresh {cutoff : Nat} {roots : List Ty} {state : State} :
    Transport cutoff roots state state.fresh.2 :=
  .of_substitution_eq rfl

theorem fresh_type {cutoff : Nat} {roots : List Ty} {state : State}
    (ready : state.InferenceReady) (bound : cutoff ≤ state.inference.next) :
    Resolved cutoff roots state.fresh.2 state.fresh.1 := by
  have notDomain : (TypeVarId.mk state.inference.next) ∉ state.inference.substitution.domain := by
    intro member
    exact Nat.lt_irrefl _ (ready.solved.domain_below _ member)
  have found : state.inference.substitution.lookup? ⟨state.inference.next⟩ = none :=
    (Substitution.lookup?_eq_none_iff_not_mem_domain _ _).mpr notDomain
  intro metavariable member old
  change metavariable ∈
    (state.inference.substitution.apply (.variable ⟨state.inference.next⟩)).freeVariables at member
  simp only [Substitution.apply, found, Option.getD_none,
    Ty.freeVariables, List.mem_singleton] at member
  subst metavariable
  exact False.elim ((Nat.not_lt.mpr bound) old)

theorem withExpected {cutoff : Nat} {roots : List Ty}
    {context : Frontend.SourceInference.Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : Detail.ExpectationResult}
    (ready : state.InferenceReady)
    (actualBelow : actual.type.VariablesBelow state.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (actualSupported : Resolved cutoff roots state actual.type)
    (expectedSupported : ∀ type ∈ expected, Resolved cutoff roots state type)
    (accepted : Detail.withExpected context state actual expected = .ok result) :
    Transport cutoff roots state result.state ∧
      Resolved cutoff roots result.state result.expression.type := by
  have properties := Detail.withExpected_inferenceProperties ready actualBelow
    expectedBelow accepted
  cases expected with
  | none =>
    simp only [Detail.withExpected] at accepted
    cases accepted
    exact ⟨.refl _ _ _, resolved_normalized ready actualSupported⟩
  | some expected =>
    have expectedBound := expectedBelow expected (by simp)
    have supported := expectedSupported expected (by simp)
    cases unification : state.inference.unify actual.type expected with
    | ok inference =>
      simp only [Detail.withExpected, unification] at accepted
      cases accepted
      have unified : Detail.unify state actual.type expected =
          .ok {state with inference} := by
        simp [Detail.unify, Detail.liftUnification, unification,
          bind, Except.bind, pure, Pure.pure, Except.pure]
      have transport := unify ready actualBelow expectedBound actualSupported
        supported unified
      exact ⟨transport, resolved_normalized properties.2.1
        (transport expected supported)⟩
    | error error =>
      cases error with
      | occursCheck metavariable type => simp [Detail.withExpected, unification] at accepted
      | exhausted => simp [Detail.withExpected, unification] at accepted
      | mismatch left right =>
        simp only [Detail.withExpected, unification] at accepted
        cases planResult : Detail.coercionPlan? context state
            (state.resolve actual.type) (state.resolve expected) with
        | error error => simp [planResult, bind, Except.bind] at accepted
        | ok planOption =>
          cases planOption with
          | none => simp [planResult, bind, Except.bind] at accepted
          | some plan =>
            simp only [planResult, bind, Except.bind] at accepted
            change Except.ok _ = Except.ok result at accepted
            cases accepted
            have transport : Transport cutoff roots state
                (Detail.commitCoercionPlan state plan).2 :=
              .of_resolve_eq (Detail.commitCoercionPlan_resolve state plan)
            exact ⟨transport, transport (state.resolve expected)
              (resolved_normalized ready supported)⟩

end InferenceSupport
end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedLambdaPrefix
/-! Lambda annotations and fresh parameters are admissible in the active
context from the actual catalog and final substitution range. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem substitutedVariable_admissible
    {active : SourceSemantics.Context} {substitution : Substitution}
    (binders : TypeParameterBindersWellFormed active)
    (residual : active.residualTypeVariables = true)
    (range : SubstitutionRangeAdmissible active substitution)
    (metavariable : TypeVarId) :
    TypeAdmissible active (substitution.apply (.variable metavariable)) := by
  cases found : substitution.lookup? metavariable with
  | none =>
    simp only [Substitution.apply, found, Option.getD_none]
    exact TypeAdmissible.variableOfResidual binders residual metavariable
  | some type =>
    simp only [Substitution.apply, found, Option.getD_some]
    exact range metavariable type (Substitution.lookup?_eq_some_mem found)

theorem bindLambdaParameters_success_typesAdmissible_in_active
    {inferenceContext : Frontend.SourceInference.Context}
    {sourceParameters : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String}
    {state : Frontend.SourceInference.State}
    {result : List TypedBinder × List TypeSystem.Ty ×
      Frontend.SourceInference.State}
    {substitution : TypeSystem.Substitution}
    {target : SourceSemantics.Context}
    (success : Detail.bindLambdaParameters inferenceContext sourceParameters
      index seen state = .ok result)
    (canonical : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (binders : TypeParameterBindersWellFormed target)
    (signatures_eq : target.signatures =
      inferenceContext.signatures)
    (parameters_eq : target.typeParameters =
      inferenceContext.typeParameters)
    (owner_eq : target.currentDeclaration =
      some inferenceContext.scope.genericOwner)
    (residual : target.residualTypeVariables = true)
    (range : SubstitutionRangeAdmissible target substitution) :
    ∀ type ∈ result.2.1,
      TypeAdmissible target (substitution.apply type) := by
  induction sourceParameters generalizing index seen state result with
  | nil =>
      simp only [Detail.bindLambdaParameters] at success
      injection success with resultEq
      subst result
      simp
  | cons parameter rest induction =>
      cases parameterValue : parameter.value with
      | error =>
          simp [Detail.bindLambdaParameters, parameterValue, bind,
            Except.bind, pure, Pure.pure, Except.pure] at success
      | inferred name =>
          by_cases duplicate : name.value ∈ seen
          · simp [Detail.bindLambdaParameters, parameterValue, duplicate,
              bind, Except.bind, pure, Pure.pure, Except.pure] at success
          · let type := state.fresh.1
            let freshState := state.fresh.2
            let binderState :=
              (freshState.allocateBinder name.value (.mono type)
                (some parameter.span) false []).2
            cases tailResult : Detail.bindLambdaParameters inferenceContext rest
                (index + 1) (name.value :: seen) binderState with
            | error error =>
                simp [Detail.bindLambdaParameters, parameterValue, duplicate,
                  type, freshState, binderState, tailResult, bind,
                  Except.bind, pure, Pure.pure, Except.pure] at success
            | ok tail =>
                rcases tail with ⟨tailBinders, tailTypes, finalState⟩
                have resultEq :
                    ((freshState.allocateBinder name.value (.mono type)
                        (some parameter.span) false []).1 :: tailBinders,
                      type :: tailTypes, finalState) = result := by
                  simpa [Detail.bindLambdaParameters, parameterValue,
                    duplicate, type, freshState, binderState, tailResult,
                    bind, Except.bind, pure, Pure.pure, Except.pure] using
                    success
                subst result
                intro candidate member
                rcases List.mem_cons.mp member with rfl | member
                · exact substitutedVariable_admissible binders residual range _
                · exact induction tailResult candidate member
      | typed marker name sourceType =>
          cases typeResult : Detail.resolveSourceType inferenceContext
              sourceType with
          | error error =>
              simp [Detail.bindLambdaParameters, parameterValue, typeResult,
                bind, Except.bind] at success
          | ok resolvedType =>
              by_cases duplicate : name.value ∈ seen
              · simp [Detail.bindLambdaParameters, parameterValue,
                  typeResult, duplicate, bind, Except.bind, pure, Pure.pure,
                  Except.pure] at success
              · let binderState :=
                  (state.allocateBinder name.value (.mono resolvedType)
                    (some parameter.span) marker.isSome []).2
                cases tailResult : Detail.bindLambdaParameters inferenceContext
                    rest (index + 1) (name.value :: seen) binderState with
                | error error =>
                    simp [Detail.bindLambdaParameters, parameterValue,
                      typeResult, duplicate, binderState, tailResult, bind,
                      Except.bind, pure, Pure.pure, Except.pure] at success
                | ok tail =>
                    rcases tail with ⟨tailBinders, tailTypes, finalState⟩
                    have resultEq :
                        ((state.allocateBinder name.value (.mono resolvedType)
                            (some parameter.span) marker.isSome []).1 ::
                            tailBinders,
                          resolvedType :: tailTypes, finalState) = result := by
                      simpa [Detail.bindLambdaParameters, parameterValue,
                        typeResult, duplicate, binderState, tailResult, bind,
                        Except.bind, pure, Pure.pure, Except.pure] using success
                    subst result
                    intro candidate member
                    rcases List.mem_cons.mp member with rfl | member
                    · rw [Detail.resolveSourceType_success_apply_eq_self substitution typeResult]
                      exact TypeAdmissible.ofWellFormed
                        (resolveSourceType_success_typeWellFormed canonical
                          signatures_eq parameters_eq owner_eq typeResult)
                    · exact induction tailResult candidate member

private theorem functionParts?_success_eq
    {type parameter result : Ty}
    (success : Detail.functionParts? type = some (parameter, result)) :
    type = .function parameter result := by
  cases type <;> simp_all [Detail.functionParts?]

theorem lambdaPrefixFacts_resultTypeAdmissible_in_active
    {inferenceContext : Frontend.SourceInference.Context}
    {expected : Option TypeSystem.Ty}
    {returnAnnotation : Option Syntax.TypeExpr}
    {parameterTypes : List TypeSystem.Ty}
    {parameterState resultState : Frontend.SourceInference.State}
    {resultType : TypeSystem.Ty}
    {active : SourceSemantics.Context}
    {substitution : TypeSystem.Substitution}
    (facts : Detail.LambdaPrefixFacts inferenceContext expected
      returnAnnotation parameterTypes parameterState resultType resultState)
    (canonical : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (binders : TypeParameterBindersWellFormed active)
    (signaturesEq : active.signatures = inferenceContext.signatures)
    (parametersEq : active.typeParameters =
      inferenceContext.typeParameters)
    (ownerEq : active.currentDeclaration =
      some inferenceContext.scope.genericOwner)
    (residual : active.residualTypeVariables = true)
    (range : SubstitutionRangeAdmissible active substitution)
    (substitutionExtends : substitution.SemanticallyExtends
      parameterState.inference.substitution)
    (expectedAdmissible : ∀ expectedType ∈ expected,
      TypeAdmissible active (substitution.apply expectedType)) :
    TypeAdmissible active (substitution.apply resultType) := by
  cases facts with
  | noExpectedPartsAnnotated _ _ resolution =>
      rw [Detail.resolveSourceType_success_apply_eq_self substitution resolution]
      exact TypeAdmissible.ofWellFormed
        (resolveSourceType_success_typeWellFormed canonical signaturesEq
          parametersEq ownerEq resolution)
  | noExpectedPartsFresh _ _ freshEq =>
      have resultEq : parameterState.fresh.1 = resultType :=
        congrArg Prod.fst freshEq
      rw [← resultEq]
      change TypeAdmissible active
        (substitution.apply
          (.variable ⟨parameterState.inference.next⟩))
      exact substitutedVariable_admissible binders residual range _
  | expectedPartsAnnotated _ _ _ resolution =>
      rw [Detail.resolveSourceType_success_apply_eq_self substitution resolution]
      exact TypeAdmissible.ofWellFormed
        (resolveSourceType_success_typeWellFormed canonical signaturesEq
          parametersEq ownerEq resolution)
  | @expectedPartsInferred expectedParameter _ _ partsEq _ _ =>
      simp only [Option.bind_eq_some_iff] at partsEq
      obtain ⟨expectedType, expectedEq, partsSuccess⟩ := partsEq
      have resolvedEq : parameterState.resolve expectedType =
          .function expectedParameter resultType :=
        functionParts?_success_eq partsSuccess
      have endpointEq : substitution.apply
          (parameterState.resolve expectedType) =
          substitution.apply expectedType := by
        simpa [Frontend.SourceInference.State.resolve,
          TypeSystem.InferState.resolve] using
            substitutionExtends expectedType
      have functionAdmissible : TypeAdmissible active
          (.function (substitution.apply expectedParameter)
            (substitution.apply resultType)) := by
        rw [← FlexibleSubstitution.apply_function, ← resolvedEq,
          endpointEq]
        exact expectedAdmissible expectedType (by simp [expectedEq])
      exact functionAdmissible.function_result


private theorem lambdaFreshParameter_isolated
    {state : State} (isolated : ActiveSchemeQuantifierIsolation state)
    (bound : ActiveQuantifiersBelowNext state) (name : String)
    (span : Option Syntax.SourceSpan) :
    ActiveSchemeQuantifierIsolation
      (state.fresh.2.allocateBinder name (.mono state.fresh.1) span false []).2 := by
  apply activeSchemeQuantifierIsolation_allocateMonoBinder
  · exact activeSchemeQuantifierIsolation_transport isolated rfl
  · intro metavariable free quantified
    have same : metavariable = ⟨state.inference.next⟩ := by
      simpa [State.fresh, InferState.fresh, Ty.freeVariables] using free
    subst metavariable
    obtain ⟨binder, member, quantified⟩ := List.mem_flatMap.mp quantified
    have below := bound binder member _ quantified
    exact Nat.lt_irrefl _ below

private theorem lambdaAnnotatedParameter_isolated
    {context : Frontend.SourceInference.Context} {sourceType : Syntax.TypeExpr}
    {state : State} {type : Ty}
    (isolated : ActiveSchemeQuantifierIsolation state)
    (resolved : Detail.resolveSourceType context sourceType = .ok type)
    (name : String) (span : Option Syntax.SourceSpan) (comptime : Bool) :
    ActiveSchemeQuantifierIsolation
      (state.allocateBinder name (.mono type) span comptime []).2 := by
  apply activeSchemeQuantifierIsolation_allocateBinder
  · exact isolated
  · intro metavariable free _
    have freeType : metavariable ∈ type.freeVariables := by
      simpa [Scheme.mono, Scheme.freeVariables] using free
    exact Nat.not_lt_zero _
      (Detail.resolveSourceType_success_variablesBelow resolved 0 metavariable freeType)
  · simp [Scheme.mono]

theorem bindLambdaParameters_preserves_actualScope
    {context : Frontend.SourceInference.Context}
    {parameters : List Syntax.LambdaParameter} {index : Nat}
    {seen : List String} {state : State}
    {result : List TypedBinder × List Ty × State} {source : TypedSource}
    (operational : ActualStateInvariant state source)
    (isolated : ActiveSchemeQuantifierIsolation state)
    (success : Detail.bindLambdaParameters context parameters index seen state = .ok result) :
    ActualStateInvariant result.2.2 source ∧
      ActiveSchemeQuantifierIsolation result.2.2 := by
  induction parameters generalizing index seen state result with
  | nil =>
    simp only [Detail.bindLambdaParameters] at success
    injection success with resultEq
    subst result
    exact ⟨operational, isolated⟩
  | cons parameter rest induction =>
    cases parameterValue : parameter.value with
    | error =>
      simp [Detail.bindLambdaParameters, parameterValue, bind, Except.bind] at success
    | inferred name =>
      simp only [Detail.bindLambdaParameters, parameterValue, bind, Except.bind] at success
      repeat' first | split at success
      all_goals try simp_all only [exceptPure_eq_ok]
      all_goals try simp_all
      all_goals
        subst result
        subst_vars
        exact induction _ _ _
          (operational.fresh.allocateMonoBinder name.value state.fresh.1 (some parameter.span) false)
          (lambdaFreshParameter_isolated isolated operational.quantifiersBelow name.value (some parameter.span))
          (by assumption)
    | typed marker name sourceType =>
      simp only [Detail.bindLambdaParameters, parameterValue] at success
      cases resolution : Detail.resolveSourceType context sourceType with
      | error error => simp [resolution, bind, Except.bind] at success
      | ok parameterType =>
        simp only [resolution, bind, Except.bind] at success
        repeat' first | split at success
        all_goals try simp_all only [exceptPure_eq_ok]
        all_goals try simp_all
        all_goals
          subst result
          subst_vars
          exact induction _ _ _
            (operational.allocateMonoBinder name.value parameterType (some parameter.span) marker.isSome)
            (lambdaAnnotatedParameter_isolated isolated resolution name.value (some parameter.span) marker.isSome)
            (by assumption)

theorem lambdaPrefixFacts_preserves_actualScope
    {context : Frontend.SourceInference.Context} {expected : Option Ty}
    {annotation : Option Syntax.TypeExpr} {types : List Ty}
    {initial final : State} {resultType : Ty} {source : TypedSource}
    (operational : ActualStateInvariant initial source)
    (isolated : ActiveSchemeQuantifierIsolation initial)
    (facts : Detail.LambdaPrefixFacts context expected annotation types initial resultType final) :
    ActualStateInvariant final source ∧ ActiveSchemeQuantifierIsolation final := by
  cases facts with
  | noExpectedPartsAnnotated => exact ⟨operational, isolated⟩
  | noExpectedPartsFresh _ _ fresh =>
    have stateEq : initial.fresh.2 = final := congrArg Prod.snd fresh
    rw [← stateEq]
    exact ⟨operational.fresh, activeSchemeQuantifierIsolation_transport isolated rfl⟩
  | expectedPartsAnnotated _ unified | expectedPartsInferred _ unified =>
    exact ⟨operational.unify unified, activeSchemeQuantifierIsolation_transport isolated
      (congrArg LexicalScope.binders (Detail.unify_preserves_lexicalScope unified))⟩

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedStatementState
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem ActualStateInvariant.allocateStatementId
    {initial final : State} {source : TypedSource} {id : StatementId}
    (invariant : ActualStateInvariant initial source)
    (allocation : initial.allocateStatementId = (id, final)) : ActualStateInvariant final source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  have stateEq : initial.allocateStatementId.2 = final := congrArg Prod.snd allocation
  refine ⟨⟨pending, ?_⟩, ?_, ?_, invariant.sourceMonomorphic⟩
  · rw [← stateEq]
    exact ledger.allocateStatementId
  · apply invariant.origins.congr_localBinders
    rw [← stateEq]
    rfl
  · apply activeQuantifiersBelowNext_transport invariant.quantifiersBelow
    · rw [← stateEq]; rfl
    · rw [← stateEq]; exact Nat.le_refl _

theorem ActualStateInvariant.ofStatementPreservingBinders
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {returnType : Ty} {initial : State}
    {result : Detail.StatementResult} {source : TypedSource}
    (invariant : ActualStateInvariant initial source)
    (success : Detail.inferStatementFuel fuel context statement returnType initial = .ok result)
    (bindersEq : result.state.localBinders = initial.localBinders)
    (nextLe : initial.inference.next ≤ result.state.inference.next) :
    ActualStateInvariant result.state source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  exact ⟨⟨pending, (actualLedgerFamily fuel).statements.statement success ledger⟩,
    invariant.origins.congr_localBinders bindersEq,
    activeQuantifiersBelowNext_transport invariant.quantifiersBelow bindersEq nextLe, invariant.sourceMonomorphic⟩

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedLetState
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem ActualStateInvariant.withLocals
    {state : State} {source : TypedSource}
    (invariant : ActualStateInvariant state source) (locals : Environment) :
    ActualStateInvariant (state.withLocals locals) source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  exact ⟨⟨pending, ⟨ledger.requirements,
    ⟨ledger.templates.classified, ledger.templates.unique, ledger.templates.covered⟩⟩⟩, invariant.origins.congr_localBinders rfl,
    activeQuantifiersBelowNext_transport invariant.quantifiersBelow rfl (Nat.le_refl _), invariant.sourceMonomorphic⟩

theorem ActualStateInvariant.ofStatementWithScope
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {returnType : Ty} {initial : State}
    {result : Detail.StatementResult} {source : TypedSource}
    (invariant : ActualStateInvariant initial source)
    (success : Detail.inferStatementFuel fuel context statement returnType initial = .ok result)
    (origins : ActiveBinderCaptureOrigins result.state source)
    (bound : ActiveQuantifiersBelowNext result.state) : ActualStateInvariant result.state source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  exact ⟨⟨pending, (actualLedgerFamily fuel).statements.statement success ledger⟩, origins, bound, invariant.sourceMonomorphic⟩

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedLocalSchemePrivacy
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem
namespace ProtectedVariables

/-- Every variable in a substituted type comes from the substituted image of
one variable that occurred in the original type. -/
theorem apply_variable_origin (substitution : Substitution) (type : Ty)
    (metavariable : TypeVarId)
    (occurs : metavariable ∈ (substitution.apply type).freeVariables) :
    ∃ source, source ∈ type.freeVariables ∧
      metavariable ∈ (substitution.apply (.variable source)).freeVariables := by
  induction type with
  | «variable» source => exact ⟨source, by simp [Ty.freeVariables], occurs⟩
  | parameter _ => simp [Substitution.apply, Ty.freeVariables] at occurs
  | constructor _ => simp [Substitution.apply, Ty.freeVariables] at occurs
  | error => simp [Substitution.apply, Ty.freeVariables] at occurs
  | proxy inner induction => exact induction occurs
  | comptime inner induction => exact induction occurs
  | application left right leftIH rightIH =>
    rcases (Ty.mem_freeVariables_application_iff _ _ _).mp occurs with h | h
    · obtain ⟨v, member, image⟩ := leftIH h
      exact ⟨v, (Ty.mem_freeVariables_application_iff _ _ _).mpr (.inl member), image⟩
    · obtain ⟨v, member, image⟩ := rightIH h
      exact ⟨v, (Ty.mem_freeVariables_application_iff _ _ _).mpr (.inr member), image⟩
  | function left right leftIH rightIH =>
    rcases (Ty.mem_freeVariables_function_iff _ _ _).mp occurs with h | h
    · obtain ⟨v, member, image⟩ := leftIH h
      exact ⟨v, (Ty.mem_freeVariables_function_iff _ _ _).mpr (.inl member), image⟩
    · obtain ⟨v, member, image⟩ := rightIH h
      exact ⟨v, (Ty.mem_freeVariables_function_iff _ _ _).mpr (.inr member), image⟩
  | product left right leftIH rightIH =>
    rcases (Ty.mem_freeVariables_product_iff _ _ _).mp occurs with h | h
    · obtain ⟨v, member, image⟩ := leftIH h
      exact ⟨v, (Ty.mem_freeVariables_product_iff _ _ _).mpr (.inl member), image⟩
    · obtain ⟨v, member, image⟩ := rightIH h
      exact ⟨v, (Ty.mem_freeVariables_product_iff _ _ _).mpr (.inr member), image⟩
  | mapping left right leftIH rightIH =>
    rcases (Ty.mem_freeVariables_mapping_iff _ _ _).mp occurs with h | h
    · obtain ⟨v, member, image⟩ := leftIH h
      exact ⟨v, (Ty.mem_freeVariables_mapping_iff _ _ _).mpr (.inl member), image⟩
    · obtain ⟨v, member, image⟩ := rightIH h
      exact ⟨v, (Ty.mem_freeVariables_mapping_iff _ _ _).mpr (.inr member), image⟩

/-- The current solved substitution cannot rewrite variables allocated after
its own allocation bound. -/
theorem resolve_fresh_variable {state : State} (ready : state.InferenceReady)
    (metavariable : TypeVarId) (fresh : state.inference.next ≤ metavariable.index) :
    state.resolve (.variable metavariable) = .variable metavariable := by
  have absent : metavariable ∉ state.inference.substitution.domain := by
    intro member
    exact (Nat.not_lt.mpr fresh) (ready.solved.domain_below _ member)
  have found := (Substitution.lookup?_eq_none_iff_not_mem_domain _ _).mpr absent
  simp [State.resolve, InferState.resolve, Substitution.apply, found]

/-- Local scheme instantiation exposes only an unquantified source variable's
resolved image or a variable from this allocation. This also applies to the
scheme's associated predicates. -/
theorem instantiated_variable_origin {state : State} (ready : state.InferenceReady)
    (scheme : Scheme) (unique : scheme.quantified.Nodup) (type : Ty)
    (metavariable : TypeVarId)
    (occurs : metavariable ∈ (state.resolve
      ((scheme.instantiateWithSubstitution state.inference.next).substitution.apply type)).freeVariables) :
    (∃ source, source ∈ type.freeVariables ∧ source ∉ scheme.quantified ∧
      metavariable ∈ (state.resolve (.variable source)).freeVariables) ∨
    (state.inference.next ≤ metavariable.index ∧
      metavariable.index < (scheme.instantiateWithSubstitution state.inference.next).next) := by
  let instantiated := scheme.instantiateWithSubstitution state.inference.next
  have domain := Scheme.instantiateWithSubstitution_substitution_domain_permutation
    scheme state.inference.next unique
  change metavariable ∈ (state.inference.substitution.apply
    (instantiated.substitution.apply type)).freeVariables at occurs
  rw [← Substitution.compose_apply] at occurs
  obtain ⟨source, sourceMember, image⟩ := apply_variable_origin _ _ _ occurs
  rw [Substitution.compose_apply] at image
  cases found : instantiated.substitution.lookup? source with
  | none =>
    apply Or.inl
    refine ⟨source, sourceMember, ?_, ?_⟩
    · intro quantified
      exact ((Substitution.lookup?_eq_none_iff_not_mem_domain _ _).mp found)
        (domain.mem_iff.mpr quantified)
    · simpa only [State.resolve, InferState.resolve, Substitution.apply, found, Option.getD_none] using image
  | some replacement =>
    obtain ⟨fresh, replacementEq, lower, upper⟩ :=
      Scheme.instantiateWithSubstitution_substitution_range_fresh scheme
        state.inference.next (Substitution.lookup?_eq_some_mem found)
    have same : metavariable = fresh := by
      change metavariable ∈ (state.resolve (instantiated.substitution.apply (.variable source))).freeVariables at image
      rw [Substitution.apply, found, Option.getD_some, replacementEq,
        resolve_fresh_variable ready fresh lower] at image
      simpa only [Ty.freeVariables, List.mem_singleton] using image
    subst metavariable
    exact Or.inr ⟨lower, upper⟩

/-- Privacy depends on live unquantified variables, never on dead substitution
entries or on the bound variables in a stored polymorphic scheme. -/
structure BinderSafe (protectedVars : List TypeVarId) (state : State)
    (binder : TypedBinder) : Prop where
  body : ∀ metavariable ∈ binder.scheme.freeVariables,
    Safe protectedVars state (.variable metavariable)
  requirements : ∀ requirement ∈ binder.schemeRequirements,
    ∀ type ∈ requirement.predicate.subject :: requirement.predicate.arguments,
      ∀ metavariable ∈ type.freeVariables, metavariable ∉ binder.scheme.quantified →
        Safe protectedVars state (.variable metavariable)

def LiveBindersSafe (protectedVars : List TypeVarId) (state : State) : Prop :=
  ∀ binder ∈ state.localBinders, BinderSafe protectedVars state binder

theorem safe_instantiated_type {protectedVars : List TypeVarId} {state : State}
    (ready : state.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (scheme : Scheme) (unique : scheme.quantified.Nodup) (type : Ty)
    (sourceSafe : ∀ metavariable ∈ type.freeVariables,
      metavariable ∉ scheme.quantified → Safe protectedVars state (.variable metavariable)) :
    Safe protectedVars state
      ((scheme.instantiateWithSubstitution state.inference.next).substitution.apply type) := by
  intro metavariable member protectedMember
  rcases instantiated_variable_origin ready scheme unique type metavariable member with old | fresh
  · obtain ⟨source, sourceMember, outside, image⟩ := old
    exact sourceSafe source sourceMember outside metavariable image protectedMember
  · exact (Nat.not_lt.mpr fresh.1) (bound metavariable protectedMember)

theorem BinderSafe.transport {protectedVars : List TypeVarId} {before after : State}
    {binder : TypedBinder} (safe : BinderSafe protectedVars before binder)
    (transport : SafeTransport protectedVars before after) :
    BinderSafe protectedVars after binder := by
  constructor
  · intro v member
    exact transport _ (safe.body v member)
  · intro requirement member type typeMember v occurs outside
    exact transport _ (safe.requirements requirement member type typeMember v occurs outside)

theorem LiveBindersSafe.transport {protectedVars : List TypeVarId} {before after : State}
    (safe : LiveBindersSafe protectedVars before)
    (same : after.localBinders = before.localBinders)
    (transport : SafeTransport protectedVars before after) :
    LiveBindersSafe protectedVars after := by
  intro binder member
  exact (safe binder (same ▸ member)).transport transport

theorem LiveBindersSafe.unify {protectedVars : List TypeVarId} {before after : State}
    {left right : Ty} (safe : LiveBindersSafe protectedVars before)
    (leftSafe : Safe protectedVars before left)
    (rightSafe : Safe protectedVars before right)
    (accepted : Detail.unify before left right = .ok after) :
    LiveBindersSafe protectedVars after := by
  apply safe.transport _ (ProtectedVariables.unify leftSafe rightSafe accepted)
  unfold Detail.unify at accepted
  cases unified : before.inference.unify left right with
  | error error => simp [unified, Detail.liftUnification, bind, Except.bind] at accepted
  | ok inference =>
    simp only [unified, Detail.liftUnification, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
    cases accepted
    rfl

/-- The allocator-only update used by the actual local identifier branch. -/
def instantiatedState (state : State) (scheme : Scheme) : State :=
  { state with inference := { state.inference with
      next := (scheme.instantiateWithSubstitution state.inference.next).next } }

theorem instantiate_transport (protectedVars : List TypeVarId) (state : State)
    (scheme : Scheme) : SafeTransport protectedVars state (instantiatedState state scheme) :=
  .of_substitution_eq rfl

def PredicateSafe (protectedVars : List TypeVarId) (state : State)
    (predicate : ProgramPredicate) : Prop :=
  ∀ type ∈ predicate.subject :: predicate.arguments, Safe protectedVars state type

theorem instantiated_predicate_safe {protectedVars : List TypeVarId} {state : State}
    (ready : state.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (scheme : Scheme) (unique : scheme.quantified.Nodup) (predicate : ProgramPredicate)
    (sourceSafe : ∀ type ∈ predicate.subject :: predicate.arguments,
      ∀ metavariable ∈ type.freeVariables,
        metavariable ∉ scheme.quantified → Safe protectedVars state (.variable metavariable)) :
    PredicateSafe protectedVars (instantiatedState state scheme)
      (Detail.applyPredicate (instantiatedState state scheme)
        (TypedTraitResolution.applySubstitution
          (scheme.instantiateWithSubstitution state.inference.next).substitution predicate)) := by
  have each (type : Ty) (member : type ∈ predicate.subject :: predicate.arguments) :
      Safe protectedVars (instantiatedState state scheme)
        (state.resolve ((scheme.instantiateWithSubstitution state.inference.next).substitution.apply type)) :=
    instantiate_transport _ _ _ _ (safe_resolved ready
      (safe_instantiated_type ready bound scheme unique type (sourceSafe type member)))
  intro type member
  change type ∈ state.resolve ((scheme.instantiateWithSubstitution state.inference.next).substitution.apply predicate.subject) ::
    (predicate.arguments.map (scheme.instantiateWithSubstitution state.inference.next).substitution.apply).map state.resolve at member
  rcases List.mem_cons.mp member with rfl | argument
  · exact each _ (by simp)
  · obtain ⟨instantiated, instMember, rfl⟩ := List.mem_map.mp argument
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp instMember
    exact each original (List.mem_cons.mpr (.inr originalMember))

/-- Both the returned type and every reissued scheme predicate remain private
through the exact allocator update and normalization of local lookup. -/
theorem local_instantiation_safe {protectedVars : List TypeVarId} {state : State}
    {binder : TypedBinder} (ready : state.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (unique : binder.scheme.quantified.Nodup) (safe : BinderSafe protectedVars state binder) :
    SafeTransport protectedVars state (instantiatedState state binder.scheme) ∧
    Safe protectedVars (instantiatedState state binder.scheme)
      ((instantiatedState state binder.scheme).resolve
        (binder.scheme.instantiateWithSubstitution state.inference.next).body) ∧
    ∀ predicate ∈ binder.schemeRequirements.map (fun requirement =>
      Detail.applyPredicate (instantiatedState state binder.scheme)
        (TypedTraitResolution.applySubstitution
          (binder.scheme.instantiateWithSubstitution state.inference.next).substitution requirement.predicate)),
      PredicateSafe protectedVars (instantiatedState state binder.scheme) predicate := by
  refine ⟨instantiate_transport _ _ _, ?_, ?_⟩
  · apply instantiate_transport protectedVars state binder.scheme
    apply safe_resolved ready
    apply safe_instantiated_type ready bound binder.scheme unique binder.scheme.body
    intro v member outside
    exact safe.body v (List.mem_filter.mpr ⟨member, by simp [outside]⟩)
  · intro predicate member
    obtain ⟨requirement, requirementMember, rfl⟩ := List.mem_map.mp member
    exact instantiated_predicate_safe ready bound binder.scheme unique requirement.predicate
      (safe.requirements requirement requirementMember)

theorem lookup_instantiation_safe {protectedVars : List TypeVarId} {state : State}
    {name : String} {binder : TypedBinder} (ready : state.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (unique : binder.scheme.quantified.Nodup)
    (safe : LiveBindersSafe protectedVars state)
    (found : state.lookupBinder? name = some binder) :
    SafeTransport protectedVars state (instantiatedState state binder.scheme) ∧
    Safe protectedVars (instantiatedState state binder.scheme)
      ((instantiatedState state binder.scheme).resolve
        (binder.scheme.instantiateWithSubstitution state.inference.next).body) ∧
    ∀ predicate ∈ binder.schemeRequirements.map (fun requirement =>
      Detail.applyPredicate (instantiatedState state binder.scheme)
        (TypedTraitResolution.applySubstitution
          (binder.scheme.instantiateWithSubstitution state.inference.next).substitution requirement.predicate)),
      PredicateSafe protectedVars (instantiatedState state binder.scheme) predicate :=
  local_instantiation_safe ready bound unique
    (safe binder (State.lookupBinder?_eq_some_facts found).1)

end ProtectedVariables
end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedMonomorphicGeneralization
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend SourceInference TypeSystem
namespace MonomorphicGeneralization

/-- An occurrence in a replacement survives at every occurrence of its source
 variable. No restriction on residual variables or substitution ranges is used. -/
theorem replacement_occurs (substitution : Substitution) (type : Ty)
    {original replacement : TypeVarId} (occurs : original ∈ type.freeVariables)
    (replaced : replacement ∈ (substitution.apply (.variable original)).freeVariables) :
    replacement ∈ (substitution.apply type).freeVariables := by
  induction type with
  | «variable» metavariable =>
    have same : original = metavariable := by simpa [Ty.freeVariables] using occurs
    simpa only [same] using replaced
  | parameter parameter => simp [Ty.freeVariables] at occurs
  | constructor constructor => simp [Ty.freeVariables] at occurs
  | application left right leftIH rightIH =>
    rcases (Ty.mem_freeVariables_application_iff _ _ _).mp occurs with left | right
    · exact (Ty.mem_freeVariables_application_iff _ _ _).mpr (.inl (leftIH left))
    · exact (Ty.mem_freeVariables_application_iff _ _ _).mpr (.inr (rightIH right))
  | function left right leftIH rightIH =>
    rcases (Ty.mem_freeVariables_function_iff _ _ _).mp occurs with left | right
    · exact (Ty.mem_freeVariables_function_iff _ _ _).mpr (.inl (leftIH left))
    · exact (Ty.mem_freeVariables_function_iff _ _ _).mpr (.inr (rightIH right))
  | product left right leftIH rightIH =>
    rcases (Ty.mem_freeVariables_product_iff _ _ _).mp occurs with left | right
    · exact (Ty.mem_freeVariables_product_iff _ _ _).mpr (.inl (leftIH left))
    · exact (Ty.mem_freeVariables_product_iff _ _ _).mpr (.inr (rightIH right))
  | mapping left right leftIH rightIH =>
    rcases (Ty.mem_freeVariables_mapping_iff _ _ _).mp occurs with left | right
    · exact (Ty.mem_freeVariables_mapping_iff _ _ _).mpr (.inl (leftIH left))
    · exact (Ty.mem_freeVariables_mapping_iff _ _ _).mpr (.inr (rightIH right))
  | proxy inner ih => exact ih occurs
  | comptime inner ih => exact ih occurs
  | error => simp [Ty.freeVariables] at occurs

theorem predicate_replacement_occurs (substitution : Substitution) (predicate : ProgramPredicate)
    {original replacement : TypeVarId}
    (occurs : original ∈ TypedTraitResolution.predicateVariables predicate)
    (replaced : replacement ∈ (substitution.apply (.variable original)).freeVariables) :
    replacement ∈ TypedTraitResolution.predicateVariables
      (TypedTraitResolution.applySubstitution substitution predicate) := by
  rcases TypedTraitResolution.mem_predicateVariables_iff.mp occurs with subject | ⟨argument, member, occurs⟩
  · exact TypedTraitResolution.mem_predicateVariables_iff.mpr
      (.inl (replacement_occurs substitution predicate.subject subject replaced))
  · exact TypedTraitResolution.mem_predicateVariables_iff.mpr
      (.inr ⟨substitution.apply argument, List.mem_map.mpr ⟨argument, member, rfl⟩,
        replacement_occurs substitution argument occurs replaced⟩)

private theorem solved_row {context : Frontend.SourceInference.Context} {state : State}
    {requirements : List Requirement} {solved : List SolvedRequirement}
    (rows : Forall₂ (fun requirement row => row.id = requirement.id ∧
      row.predicate = Detail.applyPredicate state requirement.predicate ∧
      Detail.solveRequirementEvidence context state requirement = .ok row.evidence) requirements solved)
    {requirement : Requirement} (member : requirement ∈ requirements) :
    ∃ row ∈ solved, row.predicate = Detail.applyPredicate state requirement.predicate := by
  induction rows with
  | nil => cases member
  | @cons head row tail rows relation rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨row, List.mem_cons_self, relation.2.1⟩
    · obtain ⟨selected, present, same⟩ := ih member
      exact ⟨selected, List.mem_cons_of_mem _ present, same⟩

/-- A monomorphic generalization needs only forward preservation of blockers.
All earlier rows are still in the actual solved ledger, and the final lexical
context retains the substituted old schemes. Later requirements cannot
invalidate this case. -/
theorem final_variables_blocked
    {wholeContext : Frontend.SourceInference.Context} {wholeReturn : Ty}
    {evidenceState state : State} {roots : List NodeId} {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    {target : SourceSemantics.Context} {locals : Environment} {requirementStart : Nat} {valueType : Ty}
    (monomorphic : (Detail.generalizeValue state locals requirementStart valueType).scheme.quantified = [])
    (localMonomorphic : ∀ entry ∈ locals, entry.2.quantified = [])
    (localPresent : ∀ entry ∈ locals, ∃ id,
      (id, entry.2.apply finalized.substitution) ∈ target.locals)
    (requirements : state.requirements ⊆ evidenceState.requirements)
    (extension : finalized.substitution.SemanticallyExtends state.inference.substitution)
    (solvedEq : target.solvedRequirements = finalized.solvedRequirements) :
    ∀ replacement ∈ (finalized.substitution.apply valueType).freeVariables,
      replacement ∈ GeneralizationBlockedVariablesExcept target [] := by
  intro replacement occurs
  obtain ⟨original, originalOccurs, replaced⟩ :=
    ProtectedVariables.apply_variable_origin finalized.substitution valueType replacement occurs
  have blocked : original ∈ Detail.generalizeValueBlockedVariables state locals requirementStart := by
    by_cases blocked : original ∈ Detail.generalizeValueBlockedVariables state locals requirementStart
    · exact blocked
    apply False.elim
    have quantified : original ∈ (Detail.generalizeValue state locals requirementStart valueType).scheme.quantified := by
      rw [Detail.generalizeValue_scheme_quantified]
      exact List.mem_filter.mpr ⟨originalOccurs, by simp only [List.contains_eq_mem, blocked, decide_false, Bool.not_false]⟩
    rw [monomorphic] at quantified
    cases quantified
  rcases (Detail.mem_generalizeValueBlockedVariables_iff _ _ _ _).mp blocked with
    ⟨entry, member, variableMember⟩ | ⟨requirement, member, variableMember⟩
  · obtain ⟨id, present⟩ := localPresent entry member
    have mono := localMonomorphic entry member
    have bodyMember : original ∈ entry.2.body.freeVariables := by
      exact (List.mem_filter.mp variableMember).1
    have finalMember : replacement ∈ (entry.2.apply finalized.substitution).freeVariables := by
      simpa [Scheme.freeVariables, Scheme.apply, mono, Substitution.without] using
        replacement_occurs finalized.substitution entry.2.body bodyMember replaced
    apply List.mem_append.mpr
    exact .inl (List.mem_append.mpr (.inr (List.mem_flatMap.mpr ⟨(id, entry.2.apply finalized.substitution), present, finalMember⟩)))
  · have inState : requirement ∈ state.requirements := by
      rcases (Detail.mem_generalizeValueBlockingRequirements_iff _ _ _).mp member with prior | ⟨introduced, _⟩
      · exact List.mem_of_mem_take prior
      · exact List.mem_of_mem_drop introduced
    have inFinal : requirement ∈ resources.finalState.requirements := by
      rw [resources.requirements_eq]
      exact requirements inState
    obtain ⟨row, rowMember, predicateEq⟩ := solved_row (solveRequirements_corresponds resources.solve_success) inFinal
    have predicateMember := predicate_replacement_occurs finalized.substitution
      (Detail.applyPredicate state requirement.predicate) variableMember replaced
    rw [Detail.applyPredicate, TypedTraitResolution.applySubstitution_semanticallyExtends extension] at predicateMember
    have rowOccurs : replacement ∈ TypedTraitResolution.predicateVariables row.predicate := by
      rw [predicateEq, Detail.applyPredicate, ← resources.substitution_eq]
      exact predicateMember
    apply List.mem_append.mpr
    apply Or.inr
    apply List.mem_flatMap.mpr
    refine ⟨row, ?_, rowOccurs⟩
    exact List.mem_filter.mpr ⟨by simpa only [solvedEq] using rowMember, rfl⟩

end MonomorphicGeneralization

/-- Actual monomorphic generalization remains exact after finalization even
when its body retains flexible variables. The old lexical environment and
original solved ledger supply every remaining blocker. -/
theorem unannotatedInitializedLetCertificate_of_finalMonomorphic
    {wholeContext : Frontend.SourceInference.Context} {wholeReturn : Ty}
    {evidenceState state final : State} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    {source : TypedSource} {target : SourceSemantics.Context}
    {locals : Environment} {requirementStart : Nat} {valueType : Ty}
    {generalized : Detail.GeneralizedValue} {name : Syntax.Identifier}
    {binder : TypedBinder} {initializer : ExpressionId}
    (generalizedEq : generalized = Detail.generalizeValue state locals requirementStart valueType)
    (allocated : (state.withLocals locals).allocateBinder name.value generalized.scheme
      (some name.span) false generalized.requirements = (binder, final))
    (monomorphic : (binder.applySubstitution finalized.substitution).scheme.quantified = [])
    (localMonomorphic : ∀ entry ∈ locals, entry.2.quantified = [])
    (localPresent : ∀ entry ∈ locals, ∃ id,
      (id, entry.2.apply finalized.substitution) ∈ target.locals)
    (requirements : state.requirements ⊆ evidenceState.requirements)
    (extension : finalized.substitution.SemanticallyExtends state.inference.substitution)
    (solvedEq : target.solvedRequirements = finalized.solvedRequirements)
    (initializerType : ExpressionHasType (source.applySubstitution finalized.substitution)
      (localSchemeInitializerContext target (binder.applySubstitution finalized.substitution))
      initializer (binder.applySubstitution finalized.substitution).scheme.body) :
    UnannotatedInitializedLetCertificate source target finalized.substitution binder initializer := by
  have binderEq :
      ((state.withLocals locals).allocateBinder name.value generalized.scheme
        (some name.span) false generalized.requirements).1 = binder := congrArg Prod.fst allocated
  have rawMonomorphic : binder.scheme.quantified = [] := monomorphic
  have generalizedMonomorphic :
      (Detail.generalizeValue state locals requirementStart valueType).scheme.quantified = [] := by
    rw [← generalizedEq]
    rw [← binderEq] at rawMonomorphic
    exact rawMonomorphic
  have rawRequirements : binder.schemeRequirements = [] := by
    rw [← binderEq]
    change generalized.requirements = []
    rw [generalizedEq]
    exact Detail.generalizeValue_requirements_empty_of_quantified_eq_nil
      state locals requirementStart valueType generalizedMonomorphic
  have rawBody : binder.scheme.body = valueType := by
    rw [← binderEq]
    change generalized.scheme.body = valueType
    rw [generalizedEq, Detail.generalizeValue_scheme_body]
  have finalBody : (binder.applySubstitution finalized.substitution).scheme.body =
      finalized.substitution.apply valueType := by
    simp only [TypedBinder.applySubstitution, Scheme.apply, rawMonomorphic]
    simp [Substitution.without, rawBody]
  have finalRequirements : (binder.applySubstitution finalized.substitution).schemeRequirements = [] := by
    simp [TypedBinder.applySubstitution, rawRequirements]
  have blocked := MonomorphicGeneralization.final_variables_blocked resources generalizedMonomorphic
    localMonomorphic localPresent requirements extension solvedEq
  exact {
    initializer_type := initializerType
    requirements_well_formed := LocalSchemeRequirementsWellFormed.empty target
      (binder.applySubstitution finalized.substitution) finalRequirements
    generalizes := by
      unfold SchemeGeneralizesExcept
      rw [monomorphic, finalBody]
      have templates : localSchemeTemplateIds (binder.applySubstitution finalized.substitution) = [] := by
        simp [localSchemeTemplateIds, rawRequirements]
      rw [templates]
      apply Eq.symm
      apply List.filter_eq_nil_iff.mpr
      intro metavariable member
      simp only [List.contains_eq_mem, blocked metavariable member, decide_true, Bool.not_true]
      decide
    quantified_fresh := by
      intro metavariable member
      rw [monomorphic] at member
      cases member
  }

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedMonomorphicLocalPresence
set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.SourceInferenceSoundness.MonomorphicGeneralization

open Frontend Frontend.SourceInference TypeSystem

/-- Closing a monomorphic scheme after an earlier inference substitution is
the same as closing its original scheme with the final extension. -/
theorem scheme_apply_extension
    {scheme : Scheme} {previous final : Substitution}
    (monomorphic : scheme.quantified = [])
    (extension : final.SemanticallyExtends previous) :
    (scheme.apply previous).apply final = scheme.apply final := by
  cases scheme with
  | mk quantified body =>
      simp only at monomorphic
      subst quantified
      simpa [Scheme.apply, Substitution.without] using
        congrArg (fun body => Scheme.mk [] body) (extension body)

/-- The canonical binder environment retains the empty quantifier lists of
all active binders after the initializer's current substitution. -/
theorem binderEnvironment_monomorphic
    {state : State} {substitution : Substitution}
    (monomorphic : ∀ binder ∈ state.localBinders,
      binder.scheme.quantified = []) :
    ∀ entry ∈ state.binderEnvironment.apply substitution,
      entry.2.quantified = [] := by
  intro entry member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨binder, binderMember, rfl⟩ := List.mem_map.mp originalMember
  exact monomorphic binder binderMember

/-- Each actual generalization-local scheme closes to the scheme at the
same stable binder identity in the final semantic context. -/
theorem binderEnvironment_localPresent
    {state : State} {previous final : Substitution}
    {target : SourceSemantics.Context}
    (aligned : LocalEnvironmentAligned state final target)
    (monomorphic : ∀ binder ∈ state.localBinders,
      binder.scheme.quantified = [])
    (extension : final.SemanticallyExtends previous) :
    ∀ entry ∈ state.binderEnvironment.apply previous,
      ∃ id, (id, entry.2.apply final) ∈ target.locals := by
  intro entry member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨binder, binderMember, rfl⟩ := List.mem_map.mp originalMember
  refine ⟨binder.id, aligned.locals_perm.mem_iff.mp ?_⟩
  have mono := monomorphic binder binderMember
  have same : (binder.scheme.apply previous).apply final =
      (binder.applySubstitution final).scheme := by
    rw [scheme_apply_extension mono extension]
    simp [TypedBinder.applySubstitution, Scheme.apply, mono,
      Substitution.without]
  change (binder.id, (binder.scheme.apply previous).apply final) ∈ _
  rw [same]
  exact List.mem_map.mpr ⟨binder, binderMember, rfl⟩

/-- Successful initializer inference restores the original active binder
stack. The environment that the checker really passes to generalization
therefore supplies both finite local premises of the blocker proof. -/
theorem initializer_locals
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {initializer : Syntax.Expr} {inferred : InferredExpression}
    {initial allocated initializerState : State} {id : StatementId}
    {final : Substitution} {target : SourceSemantics.Context}
    {locals : Environment}
    (allocation : initial.allocateStatementId = (id, allocated))
    (accepted : Detail.inferExprFuel fuel inferenceContext initializer none
      allocated = .ok (inferred, initializerState))
    (localsEq : locals = initializerState.binderEnvironment.apply
      initializerState.inference.substitution)
    (aligned : LocalEnvironmentAligned initial final target)
    (monomorphic : ∀ binder ∈ initial.localBinders,
      binder.scheme.quantified = [])
    (extension : final.SemanticallyExtends
      initializerState.inference.substitution) :
    (∀ entry ∈ locals, entry.2.quantified = []) ∧
    (∀ entry ∈ locals, ∃ id, (id, entry.2.apply final) ∈ target.locals) := by
  have childEq : initializerState.localBinders = allocated.localBinders := by
    exact congrArg LexicalScope.binders
      (Detail.inferExprFuel_success_lexicalScope_eq accepted)
  have allocatedEq : allocated.localBinders = initial.localBinders := by
    have same := congrArg (fun pair : StatementId × State => pair.2.localBinders)
      allocation
    exact same.symm
  have bindersEq := childEq.trans allocatedEq
  have childMonomorphic : ∀ binder ∈ initializerState.localBinders,
      binder.scheme.quantified = [] := by
    simpa only [bindersEq] using monomorphic
  rw [localsEq]
  exact ⟨binderEnvironment_monomorphic childMonomorphic,
    binderEnvironment_localPresent (aligned.congr_localBinders bindersEq)
      childMonomorphic extension⟩

end Solcore.SourceSemantics.SourceInferenceSoundness.MonomorphicGeneralization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedOperatorInterfaces
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem
open ExecutableCoercionInterfaces

/-- Exact executable names for the ordinary requirement prefix issued at one
operator occurrence. The list is independent of later output coercions. -/
def OperatorNamesAt (signatures : ProgramSignatures) (solved : List SolvedRequirement)
    (requirements : List RequirementId) (dispatch : String → Prop) : Prop :=
  ∀ primary companions name, requirements = primary :: companions → dispatch name →
    ∃ actual trait,
      solved.filter (fun row => decide (row.id = primary)) = [actual] ∧
      actual.predicate.trait = .declaration trait ∧
      (signatures.trait? trait).map (·.name) = some name

theorem OperatorNamesAt.of_retained
    {signatures : ProgramSignatures} {solved : List SolvedRequirement}
    {before after : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    {requirements : List RequirementId} {dispatch : String → Prop}
    (retained : ExpressionOperatorSiteRetainedAt before after id)
    (interfaces : SourceInterfaces signatures solved after)
    (found : ContainsExpression before id node)
    (layout : node.requirements = requirements ++ node.coercions.flatMap CoercionStep.requirements)
    (dispatchAt : ∀ name, dispatch name → operatorDispatch node name) :
    OperatorNamesAt signatures solved requirements dispatch := by
  intro primary companions name headEq selected
  obtain ⟨finalNode, finalFound, finalLayout, finalDispatch⟩ :=
    retained found primary companions name (by simpa only [headEq] using layout) (dispatchAt name selected)
  exact interfaces.operators finalNode finalFound.1 primary companions name finalLayout finalDispatch

theorem operatorTraitPredicates_primary
    {context : Frontend.SourceInference.Context} {trait : Resolved.DeclarationId}
    {method : String} {operand : Ty} {parameters returns : List Ty}
    {predicates : List ProgramPredicate}
    (accepted : Detail.operatorTraitPredicates context trait method operand parameters returns = .ok predicates) :
    ∃ companions, predicates = {trait := .declaration trait, subject := operand, arguments := []} :: companions := by
  unfold Detail.operatorTraitPredicates at accepted
  cases selected : Detail.exactOperatorTraitMethod context trait method with
  | error error => simp [selected, bind, Except.bind] at accepted
  | ok pair =>
    simp only [selected, bind, Except.bind] at accepted
    split at accepted
    · split at accepted
      · cases accepted
        exact ⟨_, rfl⟩
      · cases accepted
    · cases accepted

theorem RequirementPredicatesCorrespond.first
    {requirements : List Requirement} {predicate : ProgramPredicate}
    {predicates : List ProgramPredicate} {ids : List RequirementId}
    (corresponds : RequirementPredicatesCorrespond requirements (predicate :: predicates) ids) :
    ∃ primary companions, ids = primary :: companions ∧
      ({id := primary, predicate := predicate} : Requirement) ∈ requirements := by
  cases corresponds with
  | cons member _ => exact ⟨_, _, rfl, member⟩

private theorem selectedSolvedRow
    {inferenceContext : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {requirements : List Requirement}
    {solved : List SolvedRequirement}
    (corresponds : Forall₂ (fun requirement row =>
      row.id = requirement.id ∧
        row.predicate = Detail.applyPredicate state requirement.predicate ∧
        Detail.solveRequirementEvidence inferenceContext state requirement =
          .ok row.evidence) requirements solved)
    {requirement : Requirement}
    (member : requirement ∈ requirements) :
    ∃ row, row ∈ solved ∧
      row.id = requirement.id ∧
      row.predicate = Detail.applyPredicate state requirement.predicate := by
  induction corresponds with
  | nil => simp at member
  | @cons head row tail rows headCorresponds tailCorresponds induction =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨row, by simp, headCorresponds.1, headCorresponds.2.1⟩
      · obtain ⟨found, foundMember, idEq, predicateEq⟩ := induction member
        exact ⟨found, by simp [foundMember], idEq, predicateEq⟩

theorem OperatorNamesAt.traitName
    {context : Frontend.SourceInference.Context} {state : State}
    {signatures : ProgramSignatures} {solved : List SolvedRequirement}
    {ids : List RequirementId} {dispatch : String → Prop}
    (names : OperatorNamesAt signatures solved ids dispatch)
    (accepted : Detail.solveRequirements context state state.requirements = .ok solved)
    {trait : Resolved.DeclarationId} {operand : Ty} {companions : List ProgramPredicate}
    (corresponds : RequirementPredicatesCorrespond state.requirements
      ({trait := .declaration trait, subject := operand, arguments := []} :: companions) ids)
    {name : String} (selected : dispatch name) :
    (signatures.trait? trait).map (·.name) = some name := by
  obtain ⟨primary, companions, headEq, member⟩ := RequirementPredicatesCorrespond.first corresponds
  obtain ⟨row, present, identity, predicate⟩ :=
    selectedSolvedRow (solveRequirements_corresponds accepted) member
  obtain ⟨actual, actualTrait, unique, actualSelected, actualName⟩ :=
    names primary companions name headEq selected
  have inFilter : row ∈ solved.filter (fun row => decide (row.id = primary)) :=
    List.mem_filter.mpr ⟨present, by simp only [identity, decide_true]⟩
  rw [unique] at inFilter
  have same : row = actual := List.mem_singleton.mp inFilter
  subst actual
  have original : row.predicate.trait = .declaration trait := by
    rw [predicate]
    rfl
  have sameTrait : trait = actualTrait := by
    simpa only [original, ProgramTraitId.declaration.injEq] using actualSelected
  simpa only [sameTrait] using actualName

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedOperatorSupport
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem
namespace InferenceSupport
open Detail

theorem addRequirements_resolve (state : State) (predicates : List ProgramPredicate) (type : Ty) :
    (state.addRequirementsWithIds predicates).2.resolve type = state.resolve type := by
  induction predicates generalizing state with
  | nil => rfl
  | cons predicate rest induction =>
      simp only [State.addRequirementsWithIds]
      rw [induction]
      rfl

private abbrev finishOperator (context : Frontend.SourceInference.Context) (dispatch : OperatorDispatch)
    (operand builtin builtinResult resultType : Ty)
    (parameterTypes : List Ty) (hasOpenLiteralOperand : Bool)
    (state : State) : Except Error OperatorInferenceResult :=
  if operand = builtin then
    pure {
      type := builtinResult
      requirements := []
      state
    }
  else
    match dispatch with
    | .function name =>
        if isDeferredBuiltinOperatorTarget state hasOpenLiteralOperand
              builtin operand ||
            isStagedIntegerOperatorTarget state hasOpenLiteralOperand
              builtin operand then
          pure {
            type := resultType
            requirements := []
            state
          }
        else
          throw (.unknownVariable name)
    | .traitMethod traitName methodName => do
        match ← operatorTrait? context traitName with
        | some trait =>
            let predicates ← operatorTraitPredicates context trait methodName
              operand parameterTypes [resultType]
            let (requirements, state) :=
              state.addRequirementsWithIds predicates
            pure {
              type := resultType
              requirements
              state
            }
        | none =>
            if isDeferredBuiltinOperatorTarget state hasOpenLiteralOperand
                  builtin operand ||
                isStagedIntegerOperatorTarget state hasOpenLiteralOperand
                  builtin operand then
              pure {
                type := resultType
                requirements := []
                state
              }
            else
              throw (.operatorNotSupported traitName operand)

private theorem finishOperator_supported
    {cutoff : Nat} {roots : List Ty} {context : Frontend.SourceInference.Context} {dispatch : OperatorDispatch}
    {operand builtin builtinResult resultType : Ty}
    {parameterTypes : List Ty} {hasOpenLiteralOperand : Bool}
    {state : State} {result : OperatorInferenceResult}
    (builtinSupported : Resolved cutoff roots state builtinResult)
    (resultSupported : Resolved cutoff roots state resultType)
    (success : finishOperator context dispatch operand builtin builtinResult
      resultType parameterTypes hasOpenLiteralOperand state = .ok result) :
    Transport cutoff roots state result.state ∧
      Resolved cutoff roots result.state result.type := by
  unfold finishOperator at success
  by_cases builtinMatch : operand = builtin
  · simp only [builtinMatch, if_true] at success
    injection success with resultEq
    subst result
    exact ⟨.refl _ _ _, builtinSupported⟩
  · simp only [builtinMatch, if_false] at success
    cases dispatch with
    | function name =>
        cases deferredResult :
            (isDeferredBuiltinOperatorTarget state hasOpenLiteralOperand
                builtin operand ||
              isStagedIntegerOperatorTarget state hasOpenLiteralOperand
                builtin operand) with
        | false =>
          simp [deferredResult] at success
        | true =>
          simp only [deferredResult, if_true] at success
          injection success with resultEq
          subst result
          exact ⟨.refl _ _ _, resultSupported⟩
    | traitMethod traitName methodName =>
        cases traitResult : operatorTrait? context traitName with
        | error error =>
            simp [traitResult, bind, Except.bind] at success
        | ok traitOption =>
            cases traitOption with
            | none =>
                simp only [traitResult, bind, Except.bind] at success
                cases deferredResult :
                    (isDeferredBuiltinOperatorTarget state
                        hasOpenLiteralOperand builtin operand ||
                      isStagedIntegerOperatorTarget state
                        hasOpenLiteralOperand builtin operand) with
                | false =>
                  simp [deferredResult] at success
                | true =>
                  simp only [deferredResult, if_true] at success
                  injection success with resultEq
                  subst result
                  exact ⟨.refl _ _ _, resultSupported⟩
            | some trait =>
                simp only [traitResult, bind, Except.bind] at success
                cases predicatesResult : operatorTraitPredicates context trait
                    methodName operand parameterTypes [resultType] with
                | error error =>
                    simp [predicatesResult] at success
                | ok predicates =>
                    simp only [predicatesResult] at success
                    change Except.ok {
                      type := resultType
                      requirements :=
                        (state.addRequirementsWithIds predicates).1
                      state := (state.addRequirementsWithIds predicates).2
                    } = Except.ok result at success
                    injection success with resultEq
                    subst result
                    have transport : Transport cutoff roots state
                        (state.addRequirementsWithIds predicates).2 :=
                      .of_resolve_eq (addRequirements_resolve state predicates)
                    exact ⟨transport, transport resultType resultSupported⟩

private def unaryBuiltin : Syntax.UnaryOp → Ty
  | .logicalNot => .bool
  | .bitNot => .word

private abbrev finishUnaryOperator (context : Frontend.SourceInference.Context)
    (operator : Syntax.UnaryOp) (operandType : Ty)
    (hasOpenLiteralOperand : Bool) (state : State) :
    Except Error OperatorInferenceResult :=
  let operand := state.resolve operandType
  let builtin := unaryBuiltin operator
  finishOperator context (unaryOperatorDispatch operator) operand builtin
    builtin (if operator == Syntax.UnaryOp.logicalNot then .bool else operand)
    [operand] hasOpenLiteralOperand state

private abbrev finishBinaryOperator (context : Frontend.SourceInference.Context)
    (operator : Syntax.BinaryOp) (left : Ty)
    (hasOpenLiteralOperand : Bool) (state : State) :
    Except Error OperatorInferenceResult :=
  let operand := state.resolve left
  if fixedWordOperator operator operand then
    pure {
      type := if binaryResultIsBool operator then .bool else operand
      requirements := []
      state
    }
  else
    let builtin := binaryBuiltinType operator
    finishOperator context (binaryOperatorDispatch operator) operand builtin
      (if binaryResultIsBool operator then .bool else builtin)
      (if binaryResultIsBool operator then .bool else operand)
      [operand, operand] hasOpenLiteralOperand state

private theorem finishUnaryOperator_supported
    {cutoff : Nat} {roots : List Ty} {context : Frontend.SourceInference.Context} {operator : Syntax.UnaryOp}
    {operandType : Ty} {hasOpenLiteralOperand : Bool} {state : State}
    {result : OperatorInferenceResult}
    (ready : state.InferenceReady)
    (supported : Resolved cutoff roots state operandType)
    (success : finishUnaryOperator context operator operandType
      hasOpenLiteralOperand state = .ok result) :
    Transport cutoff roots state result.state ∧
      Resolved cutoff roots result.state result.type := by
  have builtin : Resolved cutoff roots state
      (unaryBuiltin operator) := by
    exact resolved_closed _ _ _ (by cases operator <;> rfl)
  have output : Resolved cutoff roots state
      (if operator == Syntax.UnaryOp.logicalNot then .bool else state.resolve operandType) := by
    split
    · exact resolved_closed _ _ _ rfl
    · exact resolved_normalized ready supported
  exact finishOperator_supported builtin output success

private theorem finishBinaryOperator_supported
    {cutoff : Nat} {roots : List Ty} {context : Frontend.SourceInference.Context} {operator : Syntax.BinaryOp}
    {left : Ty} {hasOpenLiteralOperand : Bool} {state : State}
    {result : OperatorInferenceResult}
    (ready : state.InferenceReady)
    (supported : Resolved cutoff roots state left)
    (success : finishBinaryOperator context operator left
      hasOpenLiteralOperand state = .ok result) :
    Transport cutoff roots state result.state ∧
      Resolved cutoff roots result.state result.type := by
  have builtin : Resolved cutoff roots state
      (if binaryResultIsBool operator then .bool else binaryBuiltinType operator) := by
    split
    · exact resolved_closed _ _ _ rfl
    · cases operator <;> exact resolved_closed _ _ _ rfl
  have output : Resolved cutoff roots state
      (if binaryResultIsBool operator then .bool else state.resolve left) := by
    split
    · exact resolved_closed _ _ _ rfl
    · exact resolved_normalized ready supported
  simp only [finishBinaryOperator] at success
  split at success
  · injection success with resultEq
    subst result
    exact ⟨.refl _ _ _, output⟩
  · exact finishOperator_supported (context := context) builtin output success

theorem inferUnaryOperator
    {cutoff : Nat} {roots : List Ty} {context : Frontend.SourceInference.Context} {operator : Syntax.UnaryOp} {operandType : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (ready : state.InferenceReady)
    (operandBelow : operandType.VariablesBelow state.inference.next)
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow state.inference.next)
    (operandSupported : Resolved cutoff roots state operandType)
    (expectedSupported : ∀ type ∈ expected, Resolved cutoff roots state type)
    (success : Detail.inferUnaryOperator context operator operandType expected
      integerLiterals state = .ok result) :
    Transport cutoff roots state result.state ∧
      Resolved cutoff roots result.state result.type := by
  let hasOpenLiteralOperand :=
    isOpenIntegerLiteralTarget state integerLiterals operandType
  unfold Detail.inferUnaryOperator at success
  cases expected with
  | none =>
      simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at success
      have tailSuccess : finishUnaryOperator context operator operandType
          hasOpenLiteralOperand state = .ok result := by
        change finishUnaryOperator context operator operandType
          hasOpenLiteralOperand state = .ok result at success
        exact success
      exact finishUnaryOperator_supported ready operandSupported
        tailSuccess
  | some expectedType =>
      have expectedTypeBelow := expectedBelow expectedType (by simp)
      cases skipResult :
          (operator == Syntax.UnaryOp.logicalNot ||
            (state.resolve operandType).freeVariables.isEmpty ||
              !hasOpenLiteralOperand) with
      | true =>
          simp only [hasOpenLiteralOperand, skipResult, if_true, bind,
            Except.bind, pure, Pure.pure, Except.pure] at success
          have tailSuccess : finishUnaryOperator context operator operandType
              hasOpenLiteralOperand state = .ok result := by
            change finishUnaryOperator context operator operandType
              hasOpenLiteralOperand state = .ok result at success
            exact success
          exact finishUnaryOperator_supported ready operandSupported
            tailSuccess
      | false =>
          simp only [hasOpenLiteralOperand, skipResult, Bool.false_eq_true,
            if_false] at success
          cases unifyResult : Detail.unify state (state.resolve operandType)
              expectedType with
          | error error =>
              simp [unifyResult, bind, Except.bind] at success
          | ok fittedState =>
              simp only [unifyResult, bind, Except.bind] at success
              have resolvedOperandBelow :
                  (state.resolve operandType).VariablesBelow
                    state.inference.next :=
                ready.solved.variablesBelow_apply operandBelow
              have transport := unify ready resolvedOperandBelow expectedTypeBelow
                (resolved_normalized ready operandSupported)
                (expectedSupported expectedType (by simp)) unifyResult
              have fittedReady := unify_preserves_inferenceReady ready
                resolvedOperandBelow expectedTypeBelow unifyResult
              have tailSuccess : finishUnaryOperator context operator
                  operandType hasOpenLiteralOperand fittedState = .ok result := by
                change finishUnaryOperator context operator operandType
                  hasOpenLiteralOperand fittedState = .ok result at success
                exact success
              have tailProperties :=
                finishUnaryOperator_supported fittedReady
                  (transport operandType operandSupported) tailSuccess
              exact ⟨transport.trans tailProperties.1, tailProperties.2⟩

theorem inferBinaryOperator
    {cutoff : Nat} {roots : List Ty} {context : Frontend.SourceInference.Context} {operator : Syntax.BinaryOp} {left right : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (ready : state.InferenceReady)
    (leftBelow : left.VariablesBelow state.inference.next)
    (rightBelow : right.VariablesBelow state.inference.next)
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow state.inference.next)
    (leftSupported : Resolved cutoff roots state left)
    (rightSupported : Resolved cutoff roots state right)
    (expectedSupported : ∀ type ∈ expected, Resolved cutoff roots state type)
    (success : Detail.inferBinaryOperator context operator left right expected
      integerLiterals state = .ok result) :
    Transport cutoff roots state result.state ∧
      Resolved cutoff roots result.state result.type := by
  let hasOpenLiteralOperand :=
    isOpenIntegerLiteralTarget state integerLiterals left ||
      isOpenIntegerLiteralTarget state integerLiterals right
  by_cases shift : Detail.isShiftOperator operator = true
  · obtain ⟨_, typeEq, valued, valueResult, amountResult⟩ :=
      Detail.inferBinaryOperator_shift_result shift success
    have wordResolved : ∀ any : State, Resolved cutoff roots any .word := by
      intro any metavariable member
      simp [Frontend.SourceInference.State.resolve, TypeSystem.InferState.resolve, TypeSystem.Ty.word,
        TypeSystem.Ty.freeVariables] at member
    have valueTransport := unify ready leftBelow (TypeSystem.Ty.variablesBelow_constructor _ _)
      leftSupported (wordResolved state) valueResult
    have valuedReady := Detail.unify_preserves_inferenceReady ready leftBelow
      (TypeSystem.Ty.variablesBelow_constructor _ _) valueResult
    have valueProgress := Detail.unify_inferenceProgress ready.solved leftBelow
      (TypeSystem.Ty.variablesBelow_constructor _ _) valueResult
    have amountTransport := unify valuedReady (rightBelow.weaken valueProgress.next_le)
      (TypeSystem.Ty.variablesBelow_constructor _ _) (valueTransport right rightSupported)
      (wordResolved valued) amountResult
    rw [typeEq]
    exact ⟨fun type supported => amountTransport type (valueTransport type supported),
      wordResolved result.state⟩
  by_cases unchecked : Detail.isUncheckedOperator operator = true
  · obtain ⟨unifiedState, prepared, unifyResult, prepare, tailSuccess⟩ :=
      Detail.inferBinaryOperator_unchecked_result unchecked success
    have unifyProgress := unify_inferenceProgress ready.solved leftBelow
      rightBelow unifyResult
    have transport := unify ready leftBelow rightBelow leftSupported rightSupported unifyResult
    have unifiedReady := unify_preserves_inferenceReady ready leftBelow
      rightBelow unifyResult
    have leftAtUnified :
        left.VariablesBelow unifiedState.inference.next :=
      leftBelow.weaken unifyProgress.next_le
    rcases prepare with preparedEq | wordResult
    · rw [preparedEq] at tailSuccess
      have tailProperties := finishBinaryOperator_supported
        unifiedReady (transport left leftSupported)
        (show finishBinaryOperator context operator left false unifiedState = .ok result
          from tailSuccess)
      exact ⟨transport.trans tailProperties.1, tailProperties.2⟩
    · have wordResolved : ∀ any : State, Resolved cutoff roots any .word := by
        intro any metavariable member
        simp [Frontend.SourceInference.State.resolve, TypeSystem.InferState.resolve, TypeSystem.Ty.word,
          TypeSystem.Ty.freeVariables] at member
      have resolvedLeftBelow :
          (unifiedState.resolve left).VariablesBelow
            unifiedState.inference.next :=
        unifiedReady.solved.variablesBelow_apply leftAtUnified
      have secondTransport := unify unifiedReady resolvedLeftBelow
        (TypeSystem.Ty.variablesBelow_constructor _ _)
        (resolved_normalized unifiedReady (transport left leftSupported))
        (wordResolved unifiedState) wordResult
      have preparedReady := unify_preserves_inferenceReady
        unifiedReady resolvedLeftBelow (TypeSystem.Ty.variablesBelow_constructor _ _) wordResult
      have tailProperties :=
        finishBinaryOperator_supported preparedReady
          (secondTransport left (transport left leftSupported))
          (show finishBinaryOperator context operator left false prepared = .ok result
            from tailSuccess)
      exact ⟨transport.trans (secondTransport.trans tailProperties.1),
        tailProperties.2⟩
  unfold Detail.inferBinaryOperator Detail.binaryOperatorTail at success
  rw [if_neg shift, if_neg unchecked] at success
  cases unifyResult : Detail.unify state left right with
  | error error =>
      simp [unifyResult, bind, Except.bind] at success
  | ok unifiedState =>
      simp only [unifyResult, bind, Except.bind] at success
      have unifyProgress := unify_inferenceProgress ready.solved leftBelow
        rightBelow unifyResult
      have transport := unify ready leftBelow rightBelow leftSupported rightSupported unifyResult
      have unifiedReady := unify_preserves_inferenceReady ready leftBelow
        rightBelow unifyResult
      have leftAtUnified :
          left.VariablesBelow unifiedState.inference.next :=
        leftBelow.weaken unifyProgress.next_le
      cases expected with
      | none =>
          simp only [pure, Pure.pure, Except.pure]
            at success
          have tailSuccess : finishBinaryOperator context operator left
              hasOpenLiteralOperand unifiedState = .ok result := by
            change finishBinaryOperator context operator left
              hasOpenLiteralOperand unifiedState = .ok result at success
            exact success
          have tailProperties := finishBinaryOperator_supported
            unifiedReady (transport left leftSupported) tailSuccess
          exact ⟨transport.trans tailProperties.1,
            tailProperties.2⟩
      | some expectedType =>
          have expectedTypeBelow : expectedType.VariablesBelow
              unifiedState.inference.next :=
            (expectedBelow expectedType (by simp)).weaken
              unifyProgress.next_le
          cases skipResult :
              (binaryResultIsBool operator ||
                (unifiedState.resolve left).freeVariables.isEmpty ||
                  !hasOpenLiteralOperand) with
          | true =>
              simp only [hasOpenLiteralOperand, skipResult, if_true,
                pure, Pure.pure, Except.pure] at success
              have tailSuccess : finishBinaryOperator context operator left
                  hasOpenLiteralOperand unifiedState = .ok result := by
                change finishBinaryOperator context operator left
                  hasOpenLiteralOperand unifiedState = .ok result at success
                exact success
              have tailProperties := finishBinaryOperator_supported
                unifiedReady (transport left leftSupported) tailSuccess
              exact ⟨transport.trans tailProperties.1,
                tailProperties.2⟩
          | false =>
              simp only [hasOpenLiteralOperand, skipResult,
                Bool.false_eq_true, if_false] at success
              have resolvedLeftBelow :
                  (unifiedState.resolve left).VariablesBelow
                    unifiedState.inference.next :=
                unifiedReady.solved.variablesBelow_apply leftAtUnified
              cases fittedResult : Detail.unify unifiedState
                  (unifiedState.resolve left) expectedType with
              | error error =>
                  simp [fittedResult] at success
              | ok fittedState =>
                  simp only [fittedResult] at success
                  have secondTransport := unify unifiedReady resolvedLeftBelow expectedTypeBelow
                    (resolved_normalized unifiedReady (transport left leftSupported))
                    (transport expectedType (expectedSupported expectedType (by simp))) fittedResult
                  have fittedReady := unify_preserves_inferenceReady
                    unifiedReady resolvedLeftBelow expectedTypeBelow fittedResult
                  have tailSuccess : finishBinaryOperator context operator left
                      hasOpenLiteralOperand fittedState = .ok result := by
                    change finishBinaryOperator context operator left
                      hasOpenLiteralOperand fittedState = .ok result at success
                    exact success
                  have tailProperties :=
                    finishBinaryOperator_supported fittedReady
                      (secondTransport left (transport left leftSupported)) tailSuccess
                  exact ⟨transport.trans (secondTransport.trans tailProperties.1),
                    tailProperties.2⟩

end InferenceSupport
end Solcore.SourceSemantics.SourceInferenceSoundness
end
