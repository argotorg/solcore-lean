import Solcore.SourceSemantics.SourceCompiledPrivateBlockRestoration
import Solcore.SourceSemantics.SourceInferenceForActiveStages

/-! An initialized header reached inside a private block keeps its exact item
and enclosing for node, together with privacy through the selected finalizer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness ProtectedVariables

/-- An exact returned header item occurs in a retained, real for statement. -/
def RetainedHeaderItem (whole : TypedSource) (item : ForItemForm) : Prop :=
  ∃ original : StatementNode, ∃ initializers test post body,
    .statement original ∈ whole.nodes ∧ original.form = .forLoop initializers test post body ∧
      item ∈ initializers ++ post

structure InitializedHeaderReceiptPrivate
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : Selected compiled row fuel)
    {childFuel : Nat} {inferenceContext : SourceInference.Context} {source : Syntax.ForItem}
    {entry : State} {result : ForItemForm × State}
    (receipt : LocalHeaderRequirementTiming.Receipt childFuel inferenceContext source entry result) : Prop where
  ready : receipt.ready.InferenceReady
  extension : selected.body.finalized.substitution.SemanticallyExtends receipt.ready.inference.substitution
  retained : receipt.binding.1 ∈
    (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)).initializedLetBinders
  recorded : RetainedHeaderItem
    (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement))
    (.letDecl receipt.binding.1 (some receipt.value.id))
  origins : ActiveBinderCaptureOrigins receipt.ready
    (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement))
  templates : ∀ older ∈ receipt.ready.localBinders, BinderTemplatesBefore receipt.ready entry.nextRequirement older
  priorAvoided : Avoids (activeSchemeQuantifiers entry) (receipt.ready.resolve receipt.value.type)
  transport : ∀ type, Safe receipt.binding.1.scheme.quantified receipt.ready type →
    Avoids receipt.binding.1.scheme.quantified (selected.body.finalized.substitution.apply type)
  newRows : ∀ requirement ∈ selected.body.body.state.requirements, requirement ∉ receipt.ready.requirements →
    ∀ type ∈ requirement.predicate.subject :: requirement.predicate.arguments,
      Avoids receipt.binding.1.scheme.quantified (selected.body.finalized.substitution.apply type)

private theorem RetainedHeaderItem.initialized
    {whole : TypedSource} {binder : TypedBinder} {value : ExpressionId}
    (retained : RetainedHeaderItem whole (.letDecl binder (some value))) :
    binder ∈ whole.initializedLetBinders := by
  obtain ⟨original,initializers,test,post,body,present,form,item⟩ := retained
  unfold TypedSource.initializedLetBinders
  refine List.mem_flatMap.mpr ⟨_,present,?_⟩
  change binder ∈ original.form.initializedLetBinders
  rw [form]
  rcases List.mem_append.mp item with left | right
  · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨_,left,List.mem_singleton_self _⟩)
  · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨_,right,List.mem_singleton_self _⟩)

private theorem initialized_header_of_occurrence
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat} {selected : Selected compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {headerFuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial final : State} {forms : List ForItemForm}
    (occurrence : HeaderPrivacyOccurrence headerFuel context source initial final selected.body.returned
      (selected.body.body.statements.map NodeId.statement) forms)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes))
    (continuation : final.InferenceProgress selected.body.body.state)
    (itemsRetained : ∀ item ∈ forms, RetainedHeaderItem
      (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)) item)
    (privacy : ∀ protectedVars,
      (∀ q ∈ protectedVars, q.index < final.inference.next) → LiveBindersSafe protectedVars final →
      SafeTransport protectedVars final selected.body.body.state ∧ LiveBindersSafe protectedVars selected.body.body.state ∧
        ∀ row ∈ selected.body.body.state.requirements, row ∉ final.requirements →
          PredicateSafe protectedVars selected.body.body.state row.predicate)
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (form : source.value = .letDecl name annotation (some initializer)) :
    ∃ childFuel, ∃ receipt : LocalHeaderRequirementTiming.Receipt childFuel context source occurrence.entry occurrence.result,
      InitializedHeaderReceiptPrivate selected receipt := by
  obtain ⟨childFuel,receipt,ready,_,member⟩ := occurrence.toOccurrence.initialized form formation canonical
  have retainedItem := itemsRetained _ member
  have retainedBinder := retainedItem.initialized
  have resultExtension := Substitution.SemanticallyExtends.trans (selected.inferenceProgress checked).final_substitution
    (occurrence.continuation.trans continuation).substitution_extends
  have readyExtension : selected.body.finalized.substitution.SemanticallyExtends receipt.ready.inference.substitution := by
    rwa [receipt.inference_eq] at resultExtension
  have live := ProtectedVariables.LocalHeaderRequirementTiming.Receipt.active_privacy selected.body.resources receipt
    occurrence.ready occurrence.entryWellFormed formation canonical occurrence.entryActive.backed occurrence.entryActive.origins
    retainedBinder resultExtension
  have properties := receipt.initializer_inference occurrence.ready formation canonical
  have bound : ∀ q ∈ receipt.binding.1.scheme.quantified, q.index < occurrence.result.2.inference.next := by
    intro q member
    have below := properties.2.1.solved.variablesBelow_apply properties.2.2
    have actual := below q (List.mem_filter.mp member).1
    rwa [receipt.inference_eq]
  have withinHeader := occurrence.privacy _ bound live
  have afterwards := privacy _
    (fun q member => Nat.lt_of_lt_of_le (bound q member) occurrence.continuation.next_le) withinHeader.2.1
  have transport := withinHeader.1.trans afterwards.1
  have newRows := new_requirements_trans withinHeader.2.2 afterwards.2.2 afterwards.1
  refine ⟨childFuel,receipt,{
    ready := ready, extension := readyExtension, retained := retainedBinder, recorded := retainedItem,
    origins := occurrence.entryActive.origins.congr_localBinders receipt.ready_binders,
    templates := ProtectedVariables.LocalHeaderRequirementTiming.Receipt.templates_before receipt
      occurrence.entryActive.backed occurrence.ready occurrence.entryWellFormed formation canonical,
    priorAvoided := ProtectedVariables.LocalHeaderRequirementTiming.Receipt.value_avoids_active receipt
      occurrence.ready occurrence.entryWellFormed occurrence.entryActive.bound occurrence.entryActive.privateVars
      catalog formation canonical,
    transport := ?_, newRows := ?_ }⟩
  · intro type safe
    apply selected.finishPrivacy checked _ type
    apply transport type
    exact SafeTransport.of_substitution_eq (congrArg InferState.substitution receipt.inference_eq) type safe
  · intro requirement member fresh type typeMember
    apply selected.finishPrivacy checked _ type
    apply newRows requirement member _ type typeMember
    have same : occurrence.result.2.requirements = receipt.ready.requirements :=
      congrArg (fun result : ForItemForm × State => result.2.requirements) receipt.completed
    simpa only [same] using fresh

namespace PrivateBlockContinuation
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat} {selected : Selected compiled row fuel}

/-- Both header lists are selected by original syntax positions. The returned
context is exactly the entering context, with only loop depth changed for post. -/
theorem initialized_for_header (block : PrivateBlockContinuation selected)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {statementIndex : Nat} {statement : Syntax.Statement} (statementPosition : block.sources[statementIndex]? = some statement)
    {initializers post : List Syntax.ForItem} {condition : Syntax.Expr}
    {body : Syntax.Located (List Syntax.Statement)} {headerSpan : Syntax.SourceSpan}
    (statementForm : statement.value = .forLoop headerSpan initializers condition post body)
    (isPost : Bool) {headerIndex : Nat} {source : Syntax.ForItem}
    (position : (if isPost then post else initializers)[headerIndex]? = some source)
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (form : source.value = .letDecl name annotation (some initializer)) :
    ∃ childFuel entry result, ∃ receipt : LocalHeaderRequirementTiming.Receipt childFuel
      (if isPost then ForStatementInferenceContinuation.loopContext block.inferenceContext else block.inferenceContext)
      source entry result, InitializedHeaderReceiptPrivate selected receipt := by
  obtain ⟨occurrence⟩ := block.position checked statementPosition
  have accepted := occurrence.accepted
  cases fuelEq : occurrence.fuel with
  | zero => simp [fuelEq,Detail.inferStatementFuel] at accepted
  | succ childFuel =>
    rw [fuelEq] at accepted
    obtain ⟨receipt⟩ := ForStatementInferenceContinuation.of_accepted statementForm accepted
    have formation := block.toBlockContinuation.formation checked
    have canonical := block.toBlockContinuation.canonical checked
    have catalog : SignatureCatalogWellFormed block.inferenceContext.signatures :=
      block.signatures.symm ▸ SignatureCatalogWellFormed.ofCheckProgram checked
    have parent := occurrence.continuation.trans block.continuation
    have resultExtension := Substitution.SemanticallyExtends.trans (selected.inferenceProgress checked).final_substitution
      parent.substitution_extends
    have resultSource : TypingSourceExtends
        (occurrence.result.state.toTypedSource (selected.body.body.statements.map NodeId.statement))
        (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)) := {
      owner_eq := block.retainedSource.owner_eq.trans occurrence.resultOwner,
      nodes_prefix := occurrence.retained.trans block.retainedSource.nodes_prefix }
    have active : ActiveHeaderState occurrence.entry
        (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)) :=
      ⟨occurrence.entryPrivate,occurrence.entryBound,occurrence.entryTemplates,occurrence.entryOrigins⟩
    have stages := ProtectedVariables.ForStatementInferenceContinuation.Receipt.active_stages receipt
      selected.body.resources occurrence.ready occurrence.entryWellFormed occurrence.entryNodesBelow catalog formation canonical
      block.expectedClosed active resultSource resultExtension
    have facts := receipt.inference occurrence.ready formation canonical (block.expectedBelow.weaken occurrence.before.next_le)
    have allRetained := ProtectedVariables.ForStatementInferenceContinuation.Receipt.headers_retained (roots := selected.body.body.statements.map NodeId.statement) receipt resultSource.nodes_prefix
    have afterFor := block.after_unchanged_occurrence occurrence rfl (List.Subset.refl _) rfl
    have retainedItems : ∀ item ∈ receipt.initialized.items ++ receipt.postResult.items,
        RetainedHeaderItem (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)) item := by
      intro item member
      exact ⟨_,_,_,_,_,resultSource.nodes_prefix.subset receipt.recorded,rfl,member⟩
    cases isPost with
    | false =>
      have continuation := facts.2.2.1.trans parent
      have extension := Substitution.SemanticallyExtends.trans (selected.inferenceProgress checked).final_substitution
        continuation.substitution_extends
      obtain ⟨header⟩ := headerPrivacyOccurrence_of_position
        (initial := occurrence.entry.allocateStatementId.2) (show ActiveHeaderState occurrence.entry.allocateStatementId.2
          (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)) from
            ⟨active.privateVars.congr rfl rfl,active.bound,active.backed.congr rfl rfl rfl,active.origins.congr_localBinders rfl⟩)
        selected.body.resources facts.1 occurrence.entryWellFormed
        (State.allocateStatementId_preserves_nodesBelowNextOccurrence occurrence.entry occurrence.entryNodesBelow)
        catalog formation canonical
        (fun _ member => allRetained (List.mem_append_left _ member)) extension receipt.initialization position
      obtain ⟨headerFuel,headerReceipt,privateReceipt⟩ := initialized_header_of_occurrence checked header catalog formation canonical
        continuation (fun _ member => retainedItems _ (List.mem_append_left _ member)) (by
          intro protectedVars bound live
          have withinFor := ProtectedVariables.ForStatementInferenceContinuation.Receipt.privacy_after_initialization receipt
            occurrence.ready occurrence.entryWellFormed catalog formation canonical block.expectedClosed bound live
          have outer := afterFor protectedVars
            (fun q member => Nat.lt_of_lt_of_le (bound q member) facts.2.2.1.next_le) withinFor.2.1
          exact ⟨withinFor.1.trans outer.1,outer.2.1,new_requirements_trans withinFor.2.2 outer.2.2 outer.1⟩) form
      exact ⟨headerFuel,header.entry,header.result,headerReceipt,privateReceipt⟩
    | true =>
      have initProperties := Detail.inferForItemsFuel_inferenceProperties occurrence.ready.allocateStatementId formation canonical receipt.initialization
      have initBelow := (Detail.inferForItemsFuel_occurrenceBoundExtends receipt.initialization).nodesBelowNextOccurrence
        (State.allocateStatementId_preserves_nodesBelowNextOccurrence occurrence.entry occurrence.entryNodesBelow)
      have initWellFormed := (Detail.inferForItemsFuel_direct_progress receipt.initialization).wellFormed occurrence.entryWellFormed
      have testProperties := Detail.inferExprFuel_inferenceProperties initProperties.2 formation canonical
        (by intro type member; cases Option.mem_def.mp member; exact Ty.variablesBelow_constructor _ _) receipt.tested
      have testBelow := (Detail.inferExprFuel_occurrenceBoundExtends receipt.tested).nodesBelowNextOccurrence initBelow
      have testWellFormed := (Detail.inferExprFuel_direct_progress receipt.tested).wellFormed initWellFormed
      have bodyBelow := (Detail.inferStatementsFuel_occurrenceBoundExtends receipt.bodyAccepted).nodesBelowNextOccurrence testBelow
      have bodyWellFormed := (Detail.inferStatementsFuel_direct_progress receipt.bodyAccepted).wellFormed testWellFormed
      have continuation := facts.2.2.2.trans parent
      have extension := Substitution.SemanticallyExtends.trans (selected.inferenceProgress checked).final_substitution
        continuation.substitution_extends
      obtain ⟨header⟩ := headerPrivacyOccurrence_of_position
        (context := ForStatementInferenceContinuation.loopContext block.inferenceContext)
        stages.2 selected.body.resources facts.2.1 bodyWellFormed bodyBelow catalog formation canonical
        (fun _ member => allRetained (List.mem_append_right _ member)) extension receipt.postAccepted position
      obtain ⟨headerFuel,headerReceipt,privateReceipt⟩ := initialized_header_of_occurrence checked header catalog formation canonical
        continuation (fun _ member => retainedItems _ (List.mem_append_right _ member)) (by
          intro protectedVars bound live
          have withinFor := ProtectedVariables.ForStatementInferenceContinuation.Receipt.privacy_after_post receipt live
          have outer := afterFor protectedVars
            (fun q member => Nat.lt_of_lt_of_le (bound q member) facts.2.2.2.next_le) withinFor.2.1
          exact ⟨withinFor.1.trans outer.1,outer.2.1,new_requirements_trans withinFor.2.2 outer.2.2 outer.1⟩) form
      exact ⟨headerFuel,header.entry,header.result,headerReceipt,privateReceipt⟩

end PrivateBlockContinuation
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
