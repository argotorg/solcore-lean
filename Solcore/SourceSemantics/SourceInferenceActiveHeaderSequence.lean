import Solcore.SourceSemantics.SourceInferenceActiveHeaderPrivacy
import Solcore.Frontend.SourceInference.ForItemInferenceContinuation

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
