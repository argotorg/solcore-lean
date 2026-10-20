import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceCompiledInitializedPrivacyProvenance
import Solcore.SourceSemantics.SourceInferenceActiveStatementPosition

/-! The actual prefix establishes privacy for every prior generalized binder.
Initializer inference therefore excludes their variables from its result, closing
the prior-quantifier blocking premise using the same actual finalizer witness. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness ProtectedVariables

private theorem return_owner {before after : State} {left right : Ty}
    (accepted : Detail.unify before left right = .ok after) : after.owner = before.owner := by
  unfold Detail.unify at accepted
  cases unified : before.inference.unify left right with
  | error error => simp [unified,Detail.liftUnification,bind,Except.bind] at accepted
  | ok inference =>
    simp only [unified,Detail.liftUnification,bind,Except.bind,pure,Pure.pure,Except.pure] at accepted
    cases accepted
    rfl

structure InitializedPriorPrivate
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : BodySelection compiled row fuel} {source : Syntax.Statement}
    (actual : InitializerContinuation selected source) : Prop extends InitializedStatementPrivate actual where
  priorAvoided : Avoids (activeSchemeQuantifiers actual.entry) (actual.receipt.ready.resolve actual.receipt.value.type)

theorem InitializedPriorPrivate.prior_blocked
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : BodySelection compiled row fuel} {source : Syntax.Statement}
    {actual : InitializerContinuation selected source} (privateVars : InitializedPriorPrivate actual)
    {target : SourceSemantics.Context} {outer : Substitution}
    (aligned : LocalEnvironmentAligned actual.entry outer target) :
    PriorQuantifiersBlockedAt actual.receipt.ready actual.receipt.locals actual.entry.nextRequirement
      (actual.receipt.ready.resolve actual.receipt.value.type) target :=
  priorQuantifiersBlockedAt_of_activeQuantifiersAvoided aligned privateVars.priorAvoided

/-- Both provenance invariants and the suffix privacy proof follow the same
actual source-position traversal. The finalizer checks apply to its exact binder. -/
theorem BodySelection.initializedPriorPrivate {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement}
    (position : selected.signature.source.value.body.value[index]? = some source)
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (form : source.value = .letDecl name annotation (some initializer)) :
    ∃ actual : InitializerContinuation selected source, InitializedPriorPrivate actual := by
  have progress := selected.inferenceProgress checked
  have formation := Frontend.checkProgram_success_signature_formation checked
  have catalog := SignatureCatalogWellFormed.ofCheckProgram checked
  have canonical : ∀ signature ∈ compiled.program.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes) := by
    intro signature member
    exact (Frontend.checkProgram_success_function_signature_shape checked member).2
  have closed : (Ty.productMany selected.signature.returnTypes).VariablesBelow 0 :=
    selected.returns_closed checked
  have monomorphic : ∀ entry ∈ (selected.signature.parameterNames.zip selected.signature.parameterTypes).map (fun parameter =>
      (parameter.1, Scheme.mono parameter.2)), entry.2.quantified = [] := by
    intro entry member
    obtain ⟨parameter,_,rfl⟩ := List.mem_map.mp member
    rfl
  let roots := selected.body.body.statements.map NodeId.statement
  have initialOrigins : ActiveBinderCaptureOrigins (initial selected.signature selected.body.declaration)
      (selected.body.returned.toTypedSource roots) := by
    apply activeBinderCaptureOrigins_initial_mono
    intro entry member
    obtain ⟨parameter,_,rfl⟩ := List.mem_map.mp member
    rfl
  have retained : TypingSourceExtends (selected.body.body.state.toTypedSource roots)
      (selected.body.returned.toTypedSource roots) := by
    refine ⟨return_owner selected.body.unified,?_⟩
    change selected.body.body.state.nodes <+: selected.body.returned.nodes
    rw [selected.body.returned_nodes]
    exact List.prefix_rfl
  obtain ⟨occurrence⟩ := activeStatementPrivacyOccurrence_of_position selected.body.resources progress.initialReady
    (State.initial_requirementsWellFormed _ _ _) (State.initial_nodesBelowNextOccurrence _ _ _)
    catalog formation canonical progress.returnBelow closed
    (ActiveQuantifiersPrivate.initial _ _ _ monomorphic)
    (activeQuantifiersBelowNext_initial_mono _ _ _ monomorphic)
    (LiveTemplatesBacked.initial _ _ _) initialOrigins retained
    progress.final_substitution selected.body.inferred position
  obtain ⟨childFuel,receipt,ready,bodyContinuation⟩ := occurrence.toBackedStatementPrivacyOccurrence.toStatementPrivacyOccurrence.toOccurrence.initialized form formation canonical
  let actual : InitializerContinuation selected source := {
    childFuel := childFuel,entry := occurrence.entry,result := occurrence.result,receipt := receipt,
    retained := occurrence.retained,ready := ready,bodyContinuation := bodyContinuation,
    finalContinuation := bodyContinuation.trans (progress.returnUnification.trans progress.finalization) }
  have readyOrigins : ActiveBinderCaptureOrigins receipt.ready (selected.body.returned.toTypedSource roots) :=
    occurrence.entryOrigins.congr_localBinders receipt.ready_binders
  have readyTemplates : ∀ older ∈ receipt.ready.localBinders,
      BinderTemplatesBefore receipt.ready occurrence.entry.nextRequirement older :=
    ProtectedVariables.LocalLetRequirementTiming.Receipt.templates_before receipt
      occurrence.entryTemplates occurrence.ready occurrence.entryWellFormed formation canonical
  have inferred := receipt.initializer_inference occurrence.ready formation canonical
  have live := actual.generalized_live readyOrigins readyTemplates
  have suffix := occurrence.privacy actual.receipt.binding.1.scheme.quantified
    (actual.quantified_below inferred.2.2) live (safe_closed _ _ closed)
  have priorAvoided := ProtectedVariables.LocalLetRequirementTiming.Receipt.value_avoids_active receipt
    occurrence.ready occurrence.entryWellFormed occurrence.entryBound occurrence.entryPrivate catalog formation canonical
  refine ⟨actual,⟨⟨readyOrigins,readyTemplates,?_,?_⟩,priorAvoided⟩⟩
  · intro type safe
    apply selected.finishPrivacy checked _ type
    apply suffix.1 type
    exact SafeTransport.of_substitution_eq (congrArg InferState.substitution receipt.inference_eq) type safe
  · intro requirement member fresh type typeMember
    apply selected.finishPrivacy checked _ type
    apply suffix.2 requirement member _ type typeMember
    have same : occurrence.result.state.requirements = receipt.ready.requirements :=
      congrArg (fun result : Detail.StatementResult => result.state.requirements) receipt.completed
    simpa only [same] using fresh

/-- Public compilation closes initialized-declaration privacy at every chosen
original top-level statement position using actual inference and finalization. -/
theorem compile_initialized_prior_private {raw : Workspace.RawWorkspace}
    {seeds : List SourceCoreCompiler.Seed} {options : SourceCoreCompiler.Options}
    {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction} (member : row ∈ compiled.plan.specializations) :
    ∃ selected : Selected compiled row options.checkingFuel,
      ∀ {index : Nat} {source : Syntax.Statement},
        selected.signature.source.value.body.value[index]? = some source →
        ∀ {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr},
          source.value = .letDecl name annotation (some initializer) →
          ∃ actual : InitializerContinuation selected.toBodySelection source, InitializedPriorPrivate actual := by
  obtain ⟨selected⟩ := of_compile accepted member
  refine ⟨selected,?_⟩
  intro index source position name annotation initializer form
  exact selected.toBodySelection.initializedPriorPrivate (SourceCoreCompiler.compile_checked_source accepted) position form


theorem Selected.initializedPriorPrivate {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : Selected compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement}
    (position : selected.signature.source.value.body.value[index]? = some source)
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (form : source.value = .letDecl name annotation (some initializer)) :
    ∃ actual : InitializerContinuation selected.toBodySelection source, InitializedPriorPrivate actual :=
  selected.toBodySelection.initializedPriorPrivate checked position form

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
