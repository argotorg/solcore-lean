import Solcore.SourceSemantics.SourceCompiledPrivateForHeaderPrivacy
import Solcore.SourceSemantics.SourceInferenceForBodySuffixPrivacy

/-! A nested for body receives the actual generalized initializer scope. Its
continuation follows post inference and both real saved-scope restorations. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization.PrivateBlockContinuation
open Frontend SourceInference TypeSystem SourceInferenceSoundness ProtectedVariables
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat} {selected : BodySelection compiled row fuel}

theorem enter_for_body (block : PrivateBlockContinuation selected)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement} (position : block.sources[index]? = some source)
    {initializers post : List Syntax.ForItem} {condition : Syntax.Expr}
    {body : Syntax.Located (List Syntax.Statement)} {headerSpan : Syntax.SourceSpan}
    (form : source.value = .forLoop headerSpan initializers condition post body) :
    ∃ child : PrivateBlockContinuation selected, child.sources = body.value ∧
      child.inferenceContext = ForStatementInferenceContinuation.loopContext block.inferenceContext := by
  obtain ⟨occurrence⟩ := block.position checked position
  have accepted := occurrence.accepted
  cases fuelEq : occurrence.fuel with
  | zero => simp [fuelEq,Detail.inferStatementFuel] at accepted
  | succ childFuel =>
    rw [fuelEq] at accepted
    obtain ⟨receipt⟩ := ForStatementInferenceContinuation.of_accepted form accepted
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
    have initProperties := Detail.inferForItemsFuel_inferenceProperties occurrence.ready.allocateStatementId formation canonical receipt.initialization
    have initWellFormed := (Detail.inferForItemsFuel_direct_progress receipt.initialization).wellFormed occurrence.entryWellFormed
    have initBelow := (Detail.inferForItemsFuel_occurrenceBoundExtends receipt.initialization).nodesBelowNextOccurrence
      (State.allocateStatementId_preserves_nodesBelowNextOccurrence occurrence.entry occurrence.entryNodesBelow)
    have boolClosed : ∀ type ∈ some Ty.bool, type.VariablesBelow 0 := by
      intro type member
      cases Option.mem_def.mp member
      exact Ty.variablesBelow_constructor _ _
    have testProperties := Detail.inferExprFuel_inferenceProperties initProperties.2 formation canonical
      (fun type member => (boolClosed type member).weaken (Nat.zero_le _)) receipt.tested
    have testBelow := (Detail.inferExprFuel_occurrenceBoundExtends receipt.tested).nodesBelowNextOccurrence initBelow
    have bodyProperties := Detail.inferStatementsFuel_inferenceProperties
      (context := ForStatementInferenceContinuation.loopContext block.inferenceContext)
      testProperties.2.1 formation canonical (block.expectedClosed.weaken (Nat.zero_le _)) receipt.bodyAccepted
    have bodyBelow := (Detail.inferStatementsFuel_occurrenceBoundExtends receipt.bodyAccepted).nodesBelowNextOccurrence testBelow
    have restored := State.restoreLexicalScope_inferenceProperties initProperties.2 (testProperties.1.trans bodyProperties.1)
    have postProperties := Detail.inferForItemsFuel_inferenceProperties
      (context := ForStatementInferenceContinuation.loopContext block.inferenceContext)
      restored.2 formation canonical receipt.postAccepted
    have last := State.InferenceProgress.of_inference_eq postProperties.2.solved receipt.inference_eq
    have bodyContinuation := (State.InferenceProgress.restoreLexicalScope receipt.bodyResult.state
      receipt.initialized.state.lexicalScope bodyProperties.2.1.solved).trans (postProperties.1.trans last)
    have bodyNodes : receipt.bodyResult.state.nodes <+: occurrence.result.state.nodes := by
      have beforePost := Detail.inferForItemsFuel_preserves_nodesPrefix receipt.postAccepted
        (List.prefix_refl _) bodyBelow (Nat.le_refl _)
      have postNodes : receipt.postResult.state.nodes <+: occurrence.result.state.nodes := by
        rw [congrArg (fun result : Detail.StatementResult => result.state.nodes) receipt.completed]
        exact List.prefix_append _ _
      exact beforePost.trans postNodes
    have bodySource : TypingSourceExtends
        (receipt.bodyResult.state.toTypedSource (selected.body.body.statements.map NodeId.statement))
        (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)) := {
      owner_eq := resultSource.owner_eq.trans ((congrArg (fun result : Detail.StatementResult => result.state.owner)
        receipt.completed).trans (Detail.inferForItemsFuel_preserves_owner
          (state := receipt.bodyResult.state.restoreLexicalScope receipt.initialized.state.lexicalScope) receipt.postAccepted)),
      nodes_prefix := bodyNodes.trans resultSource.nodes_prefix }
    have afterFor := block.after_unchanged_occurrence occurrence rfl (List.Subset.refl _) rfl
    refine ⟨{
      checkingFuel := childFuel, inferenceContext := ForStatementInferenceContinuation.loopContext block.inferenceContext,
      sources := body.value, expected := block.expected, entry := receipt.testState, result := receipt.bodyResult,
      signatures := block.signatures, accepted := receipt.bodyAccepted, ready := testProperties.2.1,
      nodesBelow := testBelow, expectedBelow := block.expectedClosed.weaken (Nat.zero_le _),
      continuation := bodyContinuation.trans parent,
      retained := bodyNodes.trans (occurrence.retained.trans block.retained),
      entryWellFormed := (Detail.inferExprFuel_direct_progress receipt.tested).wellFormed initWellFormed,
      entryTemplates := stages.1.backed.inferExprFuel initProperties.2 formation canonical
        (fun type member => (boolClosed type member).weaken (Nat.zero_le _)) receipt.tested,
      entryOrigins := stages.1.origins.inferExprFuel receipt.tested,
      entryPrivate := stages.1.privateVars.inferExprFuel initProperties.2 initWellFormed stages.1.bound catalog
        formation canonical boolClosed receipt.tested,
      entryBound := activeQuantifiersBelowNext_inferExprFuel stages.1.bound initProperties.2 formation canonical
        (fun type member => (boolClosed type member).weaken (Nat.zero_le _)) receipt.tested,
      expectedClosed := block.expectedClosed, retainedSource := bodySource, privacy := ?_
    },rfl,rfl⟩
    intro protectedVars bound live
    have withinFor := ProtectedVariables.ForStatementInferenceContinuation.Receipt.privacy_after_body receipt
      occurrence.ready occurrence.entryWellFormed catalog formation canonical block.expectedClosed bound live
    have outer := afterFor protectedVars
      (fun q member => Nat.lt_of_lt_of_le (bound q member) bodyContinuation.next_le) withinFor.2.1
    exact ⟨withinFor.1.trans outer.1,outer.2.1,new_requirements_trans withinFor.2.2 outer.2.2 outer.1⟩

end Solcore.SourceSemantics.SourceCompiledLocalFinalization.PrivateBlockContinuation
