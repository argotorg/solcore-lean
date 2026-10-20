import Solcore.SourceSemantics.SourceInferenceStatementPrivacyContinuation

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
