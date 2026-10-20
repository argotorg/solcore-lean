import Solcore.SourceSemantics.SourceInferenceLiveTemplateStatementBacking

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
