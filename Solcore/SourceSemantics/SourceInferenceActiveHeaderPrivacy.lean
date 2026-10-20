import Solcore.SourceSemantics.SourceInferenceActiveQuantifierPrivacy
import Solcore.SourceSemantics.SourceInferenceLiveTemplateHeaderBacking

/-! Header privacy uses the actual initialized item returned by inference.
The enclosing for node supplies its retained initialized-binder inventory. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

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
