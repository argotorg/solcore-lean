import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceCompiledForHeaderContinuation
import Solcore.SourceSemantics.SourceInferenceSoundness

/-! Actual nested block calls retain one selected body and finalizer. A block
can pass its continuation to a child without imposing body typing or a semantic
law for the child. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem

structure BlockContinuation {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : BodySelection compiled row fuel) where
  checkingFuel : Nat
  inferenceContext : SourceInference.Context
  sources : List Syntax.Statement
  expected : Ty
  entry : State
  result : Detail.BlockResult
  signatures : inferenceContext.signatures = compiled.program.signatures
  accepted : Detail.inferStatementsFuel checkingFuel inferenceContext sources expected entry = .ok result
  ready : entry.InferenceReady
  nodesBelow : entry.NodesBelowNextOccurrence
  expectedBelow : expected.VariablesBelow entry.inference.next
  continuation : result.state.InferenceProgress selected.body.body.state
  retained : result.state.nodes <+: selected.body.body.state.nodes

namespace BlockContinuation
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat} {selected : BodySelection compiled row fuel}

def of_selected (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program) : BlockContinuation selected :=
  { checkingFuel := fuel
    inferenceContext := context compiled.program.environment compiled.program.signatures
      selected.signature selected.body.declaration
    sources := selected.signature.source.value.body.value
    expected := Ty.productMany selected.signature.returnTypes
    entry := initial selected.signature selected.body.declaration
    result := selected.body.body
    signatures := rfl
    accepted := selected.body.inferred
    ready := (selected.inferenceProgress checked).initialReady
    nodesBelow := State.initial_nodesBelowNextOccurrence _ _ _
    expectedBelow := (selected.inferenceProgress checked).returnBelow
    continuation := .refl (selected.inferenceProgress checked).bodyReady.solved
    retained := List.prefix_refl _ }

theorem formation (block : BlockContinuation selected)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program) :
    ProgramSignatureFormationValidated block.inferenceContext.signatures :=
  block.signatures.symm ▸ Frontend.checkProgram_success_signature_formation checked

theorem canonical (block : BlockContinuation selected)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program) :
    ∀ signature ∈ block.inferenceContext.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes) := by
  intro signature member
  rw [block.signatures] at member
  exact (Frontend.checkProgram_success_function_signature_shape checked member).2

/-- A block reached from the selected check supplies a real initialized-let
receipt and the final solver's continuation and no-capture facts for its binder. -/
theorem initialized (block : BlockContinuation selected)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement} (position : block.sources[index]? = some source)
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (form : source.value = .letDecl name annotation (some initializer)) :
    ∃ childFuel entry result, ∃ receipt : LocalLetRequirementTiming.Receipt childFuel block.inferenceContext source entry result,
      receipt.ready.InferenceReady ∧
        selected.body.finalized.substitution.SemanticallyExtends receipt.ready.inference.substitution ∧
        Detail.LocalBinderInstantiationNoCapture selected.body.finalized.substitution receipt.binding.1 := by
  obtain ⟨occurrence⟩ := StatementInferenceContinuation.of_position block.ready block.nodesBelow
    (block.formation checked) (block.canonical checked) block.expectedBelow block.accepted position
  obtain ⟨childFuel, receipt, ready, continued⟩ := occurrence.initialized form
    (block.formation checked) (block.canonical checked)
  have progress := selected.inferenceProgress checked
  refine ⟨childFuel, occurrence.entry, occurrence.result, receipt, ready, ?_, ?_⟩
  · rw [selected.body.resources.substitution_eq]
    exact (continued.trans (block.continuation.trans
      (progress.returnUnification.trans progress.finalization))).substitution_extends
  · apply selected.body.resources.local_no_capture
    unfold TypedSource.initializedLetBinders
    apply List.mem_flatMap.mpr
    refine ⟨.statement {
      id := occurrence.entry.allocateStatementId.1, span := source.span, type := .unit,
      form := .letDecl receipt.binding.1 (some receipt.value.id)
    }, ?_, List.mem_singleton_self _⟩
    change _ ∈ selected.body.returned.nodes
    rw [selected.body.returned_nodes]
    exact block.retained.subset (occurrence.retained.subset receipt.recorded)

/-- Descend through the actual scoped-block statement. Arbitrary later
statements and outer blocks are already carried by the parent continuation. -/
theorem enter_block (block : BlockContinuation selected)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement} (position : block.sources[index]? = some source)
    {body : List Syntax.Statement} (form : source.value = .block body) :
    ∃ child : BlockContinuation selected, child.sources = body ∧
      child.inferenceContext = block.inferenceContext := by
  obtain ⟨occurrence, occurrenceBelow⟩ := StatementInferenceContinuation.of_position_with_bounds block.ready block.nodesBelow
    (block.formation checked) (block.canonical checked) block.expectedBelow block.accepted position
  have accepted := occurrence.accepted
  cases fuelEq : occurrence.fuel with
  | zero => simp [fuelEq, Detail.inferStatementFuel] at accepted
  | succ childFuel =>
      rw [fuelEq] at accepted
      obtain ⟨bodyResult, bodyAccepted, completed, _⟩ :=
        SourceInferenceSoundness.inferStatementFuel_success_block_facts form rfl accepted
      have expectedAtEntry := block.expectedBelow.weaken occurrence.before.next_le
      have bodyProperties := Detail.inferStatementsFuel_inferenceProperties occurrence.ready.allocateStatementId
        (block.formation checked) (block.canonical checked) expectedAtEntry bodyAccepted
      have unchanged : occurrence.result.state.inference = bodyResult.state.inference :=
        congrArg (fun result : Detail.StatementResult => result.state.inference) completed
      have nodes : bodyResult.state.nodes <+: occurrence.result.state.nodes := by
        have same := congrArg (fun result : Detail.StatementResult => result.state.nodes) completed
        rw [same]
        exact List.prefix_append _ _
      refine ⟨{
        checkingFuel := childFuel, inferenceContext := block.inferenceContext, sources := body,
        expected := block.expected, entry := occurrence.entry.allocateStatementId.2, result := bodyResult,
        signatures := block.signatures, accepted := bodyAccepted, ready := occurrence.ready.allocateStatementId,
        nodesBelow := ?_, expectedBelow := expectedAtEntry,
        continuation := (State.InferenceProgress.of_inference_eq bodyProperties.2.1.solved unchanged).trans
          (occurrence.continuation.trans block.continuation),
        retained := nodes.trans (occurrence.retained.trans block.retained)
      }, rfl, rfl⟩
      exact State.allocateStatementId_preserves_nodesBelowNextOccurrence occurrence.entry
        occurrenceBelow

/-- A while body inherits the actual condition's inference state. Its lexical
restoration retains that body's inference result before the outer continuation. -/
theorem enter_while_body (block : BlockContinuation selected)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement} (position : block.sources[index]? = some source)
    {condition : Syntax.Expr} {body : Syntax.Block} (form : source.value = .whileLoop condition body) :
    ∃ child : BlockContinuation selected, child.sources = body.value ∧
      child.inferenceContext = { block.inferenceContext with loopDepth := block.inferenceContext.loopDepth + 1 } := by
  obtain ⟨occurrence, occurrenceBelow⟩ := StatementInferenceContinuation.of_position_with_bounds
    block.ready block.nodesBelow (block.formation checked) (block.canonical checked)
    block.expectedBelow block.accepted position
  have accepted := occurrence.accepted
  cases fuelEq : occurrence.fuel with
  | zero => simp [fuelEq, Detail.inferStatementFuel] at accepted
  | succ childFuel =>
      rw [fuelEq] at accepted
      obtain ⟨test, testState, bodyResult, testAccepted, bodyAccepted, completed, _⟩ :=
        SourceInferenceSoundness.inferStatementFuel_success_whileLoop_facts form rfl accepted
      have testProperties := Detail.inferExprFuel_inferenceProperties occurrence.ready.allocateStatementId
        (block.formation checked) (block.canonical checked)
        (by intro type member; cases Option.some.inj member; simp [Ty.VariablesBelow, Ty.freeVariables, Ty.bool]) testAccepted
      have expectedAtTest := (block.expectedBelow.weaken occurrence.before.next_le).weaken
        testProperties.1.next_le
      have bodyProperties := Detail.inferStatementsFuel_inferenceProperties
        (context := { block.inferenceContext with loopDepth := block.inferenceContext.loopDepth + 1 })
        testProperties.2.1 (block.formation checked) (block.canonical checked) expectedAtTest bodyAccepted
      have unchanged : occurrence.result.state.inference = bodyResult.state.inference :=
        congrArg (fun result : Detail.StatementResult => result.state.inference) completed
      have nodes : bodyResult.state.nodes <+: occurrence.result.state.nodes := by
        have same := congrArg (fun result : Detail.StatementResult => result.state.nodes) completed
        rw [same]
        exact List.prefix_append _ _
      refine ⟨{
        checkingFuel := childFuel,
        inferenceContext := { block.inferenceContext with loopDepth := block.inferenceContext.loopDepth + 1 },
        sources := body.value, expected := block.expected, entry := testState, result := bodyResult,
        signatures := block.signatures, accepted := bodyAccepted, ready := testProperties.2.1,
        nodesBelow := ?_, expectedBelow := expectedAtTest,
        continuation := (State.InferenceProgress.of_inference_eq bodyProperties.2.1.solved unchanged).trans
          (occurrence.continuation.trans block.continuation),
        retained := nodes.trans (occurrence.retained.trans block.retained)
      }, rfl, rfl⟩
      exact (Detail.inferExprFuel_occurrenceBoundExtends testAccepted).nodesBelowNextOccurrence
        (State.allocateStatementId_preserves_nodesBelowNextOccurrence occurrence.entry occurrenceBelow)

/-- Enter the actual for body after its header and condition. The real post
sequence and saved scopes preserve the child through the outer continuation. -/
theorem enter_for_body (block : BlockContinuation selected)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement} (position : block.sources[index]? = some source)
    {initializers post : List Syntax.ForItem} {condition : Syntax.Expr}
    {body : Syntax.Block} {headerSpan : Syntax.SourceSpan}
    (form : source.value = .forLoop headerSpan initializers condition post body) :
    ∃ child : BlockContinuation selected, child.sources = body.value ∧
      child.inferenceContext = ForStatementInferenceContinuation.loopContext block.inferenceContext := by
  obtain ⟨occurrence, occurrenceBelow⟩ := StatementInferenceContinuation.of_position_with_bounds
    block.ready block.nodesBelow (block.formation checked) (block.canonical checked)
    block.expectedBelow block.accepted position
  have accepted := occurrence.accepted
  cases fuelEq : occurrence.fuel with
  | zero => simp [fuelEq, Detail.inferStatementFuel] at accepted
  | succ childFuel =>
      rw [fuelEq] at accepted
      obtain ⟨receipt⟩ := ForStatementInferenceContinuation.of_accepted form accepted
      have expectedAtEntry := block.expectedBelow.weaken occurrence.before.next_le
      have facts := receipt.inference occurrence.ready (block.formation checked) (block.canonical checked) expectedAtEntry
      have initProperties := Detail.inferForItemsFuel_inferenceProperties occurrence.ready.allocateStatementId
        (block.formation checked) (block.canonical checked) receipt.initialization
      have testProperties := Detail.inferExprFuel_inferenceProperties initProperties.2
        (block.formation checked) (block.canonical checked)
        (by intro type member; cases Option.some.inj member; simp [Ty.VariablesBelow, Ty.freeVariables, Ty.bool]) receipt.tested
      have expectedAtTest := expectedAtEntry.weaken (initProperties.1.trans testProperties.1).next_le
      have bodyProperties := Detail.inferStatementsFuel_inferenceProperties
        (context := ForStatementInferenceContinuation.loopContext block.inferenceContext)
        testProperties.2.1 (block.formation checked) (block.canonical checked) expectedAtTest receipt.bodyAccepted
      have postProperties := Detail.inferForItemsFuel_inferenceProperties
        (context := ForStatementInferenceContinuation.loopContext block.inferenceContext)
        facts.2.1 (block.formation checked) (block.canonical checked) receipt.postAccepted
      have testBelow := (Detail.inferExprFuel_occurrenceBoundExtends receipt.tested).nodesBelowNextOccurrence
        ((Detail.inferForItemsFuel_occurrenceBoundExtends receipt.initialization).nodesBelowNextOccurrence
          (State.allocateStatementId_preserves_nodesBelowNextOccurrence occurrence.entry occurrenceBelow))
      have bodyBelow := (Detail.inferStatementsFuel_occurrenceBoundExtends receipt.bodyAccepted).nodesBelowNextOccurrence testBelow
      have postNodes : receipt.bodyResult.state.nodes <+: receipt.postResult.state.nodes :=
        Detail.inferForItemsFuel_preserves_nodesPrefix receipt.postAccepted (List.prefix_refl _) bodyBelow (Nat.le_refl _)
      have nodes : receipt.postResult.state.nodes <+: occurrence.result.state.nodes := by
        have same := congrArg (fun result : Detail.StatementResult => result.state.nodes) receipt.completed
        rw [same]
        exact List.prefix_append _ _
      exact ⟨{
        checkingFuel := childFuel, inferenceContext := ForStatementInferenceContinuation.loopContext block.inferenceContext,
        sources := body.value, expected := block.expected, entry := receipt.testState, result := receipt.bodyResult,
        signatures := block.signatures, accepted := receipt.bodyAccepted, ready := testProperties.2.1,
        nodesBelow := testBelow, expectedBelow := expectedAtTest,
        continuation := (State.InferenceProgress.restoreLexicalScope receipt.bodyResult.state
          receipt.initialized.state.lexicalScope bodyProperties.2.1.solved).trans
          (postProperties.1.trans (facts.2.2.2.trans (occurrence.continuation.trans block.continuation))),
        retained := postNodes.trans (nodes.trans (occurrence.retained.trans block.retained))
      }, rfl, rfl⟩

/-- Header initializers inside any reached block retain their original for
node and inherit that block's complete continuation to the selected finalizer. -/
theorem for_header (block : BlockContinuation selected)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {statement : Syntax.Statement} (position : block.sources[index]? = some statement)
    {initializers post : List Syntax.ForItem} {condition : Syntax.Expr}
    {body : Syntax.Block} {headerSpan : Syntax.SourceSpan}
    (statementForm : statement.value = .forLoop headerSpan initializers condition post body)
    (isPost : Bool) {headerIndex : Nat} {source : Syntax.ForItem}
    (headerPosition : (if isPost then post else initializers)[headerIndex]? = some source)
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (form : source.value = .letDecl name annotation (some initializer)) :
    Nonempty (HeaderInitializerContinuation selected source) := by
  obtain ⟨occurrence⟩ := StatementInferenceContinuation.of_position block.ready block.nodesBelow
    (block.formation checked) (block.canonical checked) block.expectedBelow block.accepted position
  have accepted := occurrence.accepted
  cases fuelEq : occurrence.fuel with
  | zero => simp [fuelEq, Detail.inferStatementFuel] at accepted
  | succ childFuel =>
      rw [fuelEq] at accepted
      obtain ⟨receipt⟩ := ForStatementInferenceContinuation.of_accepted statementForm accepted
      obtain ⟨header⟩ := receipt.initialized_header occurrence.ready (block.formation checked) (block.canonical checked)
        (block.expectedBelow.weaken occurrence.before.next_le) isPost headerPosition form
      have progress := selected.inferenceProgress checked
      let continued := header.continuation.trans (occurrence.continuation.trans block.continuation)
      exact ⟨{
        inferenceContext := _
        original := _
        originalPresent := block.retained.subset (occurrence.retained.subset receipt.recorded)
        header := {
          childFuel := header.childFuel, entry := header.entry, result := header.result,
          receipt := header.receipt, ready := header.ready, continuation := continued,
          retained := header.retained }
        finalContinuation := continued.trans (progress.returnUnification.trans progress.finalization)
      }⟩

end BlockContinuation
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
