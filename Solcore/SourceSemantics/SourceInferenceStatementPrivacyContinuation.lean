import Solcore.SourceSemantics.SourceInferenceSelectedPrivacyInference
import Solcore.Frontend.SourceInference.StatementInferenceContinuation

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
