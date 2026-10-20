import Solcore.SourceSemantics.SourceInferenceActiveStatementPrivacy

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
