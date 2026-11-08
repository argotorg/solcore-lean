import Solcore.SourceSemantics.Internal.Compiled.BodySelection
import Solcore.SourceSemantics.Internal.Compiled.InitializerPrivacy
import Solcore.SourceSemantics.Internal.Inference.Soundness
import Solcore.SourceSemantics.Internal.Privacy.Active

/-!
# Privacy through blocks and branches

A reached block carries its prefix invariants and the privacy of its real continuation. Scoped
children, branches, conditions and nested initializers restore that privacy on return.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledBlockContinuations
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
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledBranchContinuations
/-! Branch calls share the actual condition state. Else inference starts from
the real restored then state, and both children retain the selected finalizer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization.BlockContinuation
open Frontend SourceInference TypeSystem
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat} {selected : BodySelection compiled row fuel}

theorem enter_if_without_else (block : BlockContinuation selected)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement} (position : block.sources[index]? = some source)
    {condition : Syntax.Expr} {body : Syntax.Block} (form : source.value = .ifThen condition body none) :
    ∃ child : BlockContinuation selected, child.sources = body.value ∧
      child.inferenceContext = block.inferenceContext := by
  obtain ⟨occurrence, occurrenceBelow⟩ := StatementInferenceContinuation.of_position_with_bounds
    block.ready block.nodesBelow (block.formation checked) (block.canonical checked)
    block.expectedBelow block.accepted position
  have accepted := occurrence.accepted
  cases fuelEq : occurrence.fuel with
  | zero => simp [fuelEq, Detail.inferStatementFuel] at accepted
  | succ childFuel =>
      rw [fuelEq] at accepted
      obtain ⟨test, testState, bodyResult, testAccepted, bodyAccepted, completed, _⟩ :=
        SourceInferenceSoundness.inferStatementFuel_success_ifWithoutElse_facts form rfl accepted
      have testProperties := Detail.inferExprFuel_inferenceProperties occurrence.ready.allocateStatementId
        (block.formation checked) (block.canonical checked)
        (by intro type member; cases Option.some.inj member; simp [Ty.VariablesBelow, Ty.freeVariables, Ty.bool]) testAccepted
      have expectedAtTest := (block.expectedBelow.weaken occurrence.before.next_le).weaken
        testProperties.1.next_le
      have bodyProperties := Detail.inferStatementsFuel_inferenceProperties
        (context := block.inferenceContext)
        testProperties.2.1 (block.formation checked) (block.canonical checked) expectedAtTest bodyAccepted
      have unchanged : occurrence.result.state.inference = bodyResult.state.inference :=
        congrArg (fun result : Detail.StatementResult => result.state.inference) completed
      have nodes : bodyResult.state.nodes <+: occurrence.result.state.nodes := by
        have same := congrArg (fun result : Detail.StatementResult => result.state.nodes) completed
        rw [same]
        exact List.prefix_append _ _
      refine ⟨{
        checkingFuel := childFuel,
        inferenceContext := block.inferenceContext,
        sources := body.value, expected := block.expected, entry := testState, result := bodyResult,
        signatures := block.signatures, accepted := bodyAccepted, ready := testProperties.2.1,
        nodesBelow := ?_, expectedBelow := expectedAtTest,
        continuation := (State.InferenceProgress.of_inference_eq bodyProperties.2.1.solved unchanged).trans
          (occurrence.continuation.trans block.continuation),
        retained := nodes.trans (occurrence.retained.trans block.retained)
      }, rfl, rfl⟩
      exact (Detail.inferExprFuel_occurrenceBoundExtends testAccepted).nodesBelowNextOccurrence
        (State.allocateStatementId_preserves_nodesBelowNextOccurrence occurrence.entry occurrenceBelow)

/-- Select either actual branch; both follow checker order and then inherit
the same outer continuation and finalizer. -/
theorem enter_if_with_else (block : BlockContinuation selected)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement} (position : block.sources[index]? = some source)
    {condition : Syntax.Expr} {thenBody elseBody : Syntax.Block}
    (form : source.value = .ifThen condition thenBody (some elseBody)) (isElse : Bool) :
    ∃ child : BlockContinuation selected,
      child.sources = (if isElse then elseBody else thenBody).value ∧
      child.inferenceContext = block.inferenceContext := by
  obtain ⟨occurrence, occurrenceBelow⟩ := StatementInferenceContinuation.of_position_with_bounds
    block.ready block.nodesBelow (block.formation checked) (block.canonical checked)
    block.expectedBelow block.accepted position
  have accepted := occurrence.accepted
  cases fuelEq : occurrence.fuel with
  | zero => simp [fuelEq, Detail.inferStatementFuel] at accepted
  | succ childFuel =>
      rw [fuelEq] at accepted
      obtain ⟨test, testState, thenResult, elseResult, testAccepted, thenAccepted, elseAccepted, completed, _⟩ :=
        SourceInferenceSoundness.inferStatementFuel_success_ifWithElse_facts form rfl accepted
      have testProperties := Detail.inferExprFuel_inferenceProperties occurrence.ready.allocateStatementId
        (block.formation checked) (block.canonical checked)
        (by intro type member; cases Option.some.inj member; simp [Ty.VariablesBelow, Ty.freeVariables, Ty.bool]) testAccepted
      have expectedAtTest := (block.expectedBelow.weaken occurrence.before.next_le).weaken testProperties.1.next_le
      have thenProperties := Detail.inferStatementsFuel_inferenceProperties testProperties.2.1
        (block.formation checked) (block.canonical checked) expectedAtTest thenAccepted
      have restored := State.restoreLexicalScope_inferenceProperties testProperties.2.1 thenProperties.1
      have expectedAtElse := expectedAtTest.weaken restored.1.next_le
      have elseProperties := Detail.inferStatementsFuel_inferenceProperties restored.2
        (block.formation checked) (block.canonical checked) expectedAtElse elseAccepted
      have testBelow := (Detail.inferExprFuel_occurrenceBoundExtends testAccepted).nodesBelowNextOccurrence
        (State.allocateStatementId_preserves_nodesBelowNextOccurrence occurrence.entry occurrenceBelow)
      have thenBelow := (Detail.inferStatementsFuel_occurrenceBoundExtends thenAccepted).nodesBelowNextOccurrence testBelow
      have branchNodes : thenResult.state.nodes <+: elseResult.state.nodes :=
        Detail.inferStatementsFuel_preserves_nodesPrefix elseAccepted (List.prefix_refl _) thenBelow (Nat.le_refl _)
      have nodes : elseResult.state.nodes <+: occurrence.result.state.nodes := by
        have same := congrArg (fun result : Detail.StatementResult => result.state.nodes) completed
        rw [same]
        exact List.prefix_append _ _
      have unchanged : occurrence.result.state.inference = elseResult.state.inference :=
        congrArg (fun result : Detail.StatementResult => result.state.inference) completed
      have last := (State.InferenceProgress.of_inference_eq elseProperties.2.1.solved unchanged).trans
        (occurrence.continuation.trans block.continuation)
      have retained := nodes.trans (occurrence.retained.trans block.retained)
      cases isElse with
      | false =>
          exact ⟨{
            checkingFuel := childFuel, inferenceContext := block.inferenceContext,
            sources := thenBody.value, expected := block.expected, entry := testState, result := thenResult,
            signatures := block.signatures, accepted := thenAccepted, ready := testProperties.2.1,
            nodesBelow := testBelow, expectedBelow := expectedAtTest,
            continuation := (State.InferenceProgress.restoreLexicalScope thenResult.state
              testState.lexicalScope thenProperties.2.1.solved).trans (elseProperties.1.trans last),
            retained := branchNodes.trans retained
          }, rfl, rfl⟩
      | true =>
          exact ⟨{
            checkingFuel := childFuel, inferenceContext := block.inferenceContext,
            sources := elseBody.value, expected := block.expected,
            entry := thenResult.state.restoreLexicalScope testState.lexicalScope, result := elseResult,
            signatures := block.signatures, accepted := elseAccepted, ready := restored.2,
            nodesBelow := thenBelow, expectedBelow := expectedAtElse,
            continuation := last, retained := retained
          }, rfl, rfl⟩

end Solcore.SourceSemantics.SourceCompiledLocalFinalization.BlockContinuation
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledInitializedPriorCertificate
/-! The actual selected prefix supplies prior-quantifier privacy to the
initializer certificate consumer. The remaining inputs describe the exact child
and its selected-scope generalization barrier. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness

variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : BodySelection compiled row fuel} {source : Syntax.Statement}

/-- The real prefix closes the prior blocker using the same child entry's local
alignment. The certificate uses actual whole-body predicate formation. -/
theorem InitializedPriorPrivate.certificate_of_child
    {continuation : InitializerContinuation selected source}
    (privateVars : InitializedPriorPrivate continuation)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {target : SourceSemantics.Context} {frames : List InitializedLetBinding}
    (invariant : RecursiveExpressionInvariant
      (context compiled.program.environment compiled.program.signatures
        selected.signature selected.body.declaration)
      selected.body.finalized continuation.entry target)
    (actual : ActualContext
      (context compiled.program.environment compiled.program.signatures
        selected.signature selected.body.declaration)
      selected.body.finalized frames target)
    (covered : ActualContext.Covers selected.body.finalized frames
      (.statement continuation.entry.allocateStatementId.1))
    (barrier : GeneralizationBarrierTransport continuation.receipt.ready continuation.receipt.locals
      continuation.entry.nextRequirement (continuation.receipt.ready.resolve continuation.receipt.value.type)
      selected.body.finalized.substitution target
      (localSchemeTemplateIds (continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution)))
    (child :
      RecursiveExpressionInvariant
        (context compiled.program.environment compiled.program.signatures
          selected.signature selected.body.declaration)
        selected.body.finalized continuation.entry.allocateStatementId.2
        (localSchemeInitializerContext target continuation.initializerBinding.binder) →
      ActualContext
        (context compiled.program.environment compiled.program.signatures
          selected.signature selected.body.declaration)
        selected.body.finalized (frames ++ [continuation.initializerBinding])
        (localSchemeInitializerContext target continuation.initializerBinding.binder) →
      ActualContext.Covers selected.body.finalized (frames ++ [continuation.initializerBinding])
        (.expression continuation.receipt.value.id) →
      ExpressionHasType selected.body.finalized.typedSource
        (localSchemeInitializerContext target continuation.initializerBinding.binder)
        continuation.receipt.value.id
        (selected.body.finalized.substitution.apply continuation.receipt.value.type)) :
    UnannotatedInitializedLetCertificate
      (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement))
      target selected.body.finalized.substitution continuation.receipt.binding.1 continuation.receipt.value.id := by
  exact continuation.certificate_of_child checked invariant actual covered barrier
    (privateVars.prior_blocked invariant.active.aligned) child

/-- At an actual selected top-level declaration, prior privacy and predicate
formation are generated internally. The callback is only the exact smaller child
in the scope opened by that same declaration. -/
theorem BodySelection.initializedCertificate_of_child
    (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement}
    (position : selected.signature.source.value.body.value[index]? = some source)
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (form : source.value = .letDecl name annotation (some initializer)) :
    ∃ continuation : InitializerContinuation selected source,
      ∀ {target : SourceSemantics.Context} {frames : List InitializedLetBinding},
        RecursiveExpressionInvariant
          (context compiled.program.environment compiled.program.signatures
            selected.signature selected.body.declaration)
          selected.body.finalized continuation.entry target →
        ActualContext
          (context compiled.program.environment compiled.program.signatures
            selected.signature selected.body.declaration)
          selected.body.finalized frames target →
        ActualContext.Covers selected.body.finalized frames
          (.statement continuation.entry.allocateStatementId.1) →
        GeneralizationBarrierTransport continuation.receipt.ready continuation.receipt.locals
          continuation.entry.nextRequirement (continuation.receipt.ready.resolve continuation.receipt.value.type)
          selected.body.finalized.substitution target
          (localSchemeTemplateIds (continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution)) →
        (RecursiveExpressionInvariant
            (context compiled.program.environment compiled.program.signatures
              selected.signature selected.body.declaration)
            selected.body.finalized continuation.entry.allocateStatementId.2
            (localSchemeInitializerContext target continuation.initializerBinding.binder) →
          ActualContext
            (context compiled.program.environment compiled.program.signatures
              selected.signature selected.body.declaration)
            selected.body.finalized (frames ++ [continuation.initializerBinding])
            (localSchemeInitializerContext target continuation.initializerBinding.binder) →
          ActualContext.Covers selected.body.finalized (frames ++ [continuation.initializerBinding])
            (.expression continuation.receipt.value.id) →
          ExpressionHasType selected.body.finalized.typedSource
            (localSchemeInitializerContext target continuation.initializerBinding.binder)
            continuation.receipt.value.id
            (selected.body.finalized.substitution.apply continuation.receipt.value.type)) →
        UnannotatedInitializedLetCertificate
          (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement))
          target selected.body.finalized.substitution continuation.receipt.binding.1 continuation.receipt.value.id := by
  obtain ⟨continuation,privateVars⟩ := selected.initializedPriorPrivate checked position form
  refine ⟨continuation,?_⟩
  intro target frames invariant actual covered barrier child
  exact privateVars.certificate_of_child checked invariant actual covered barrier child

/-- Successful public compilation selects the same original body and finalizer
used by each conditional initializer certificate. The selected-scope barrier and
concrete child typing are the remaining semantic inputs. -/
theorem compile_initialized_certificate_of_child
    {seeds : List SourceCoreCompiler.Seed} {options : SourceCoreCompiler.Options}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    (member : row ∈ compiled.plan.specializations) :
    ∃ selected : Selected compiled row options.checkingFuel,
      ∀ {index : Nat} {source : Syntax.Statement},
        selected.signature.source.value.body.value[index]? = some source →
        ∀ {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr},
          source.value = .letDecl name annotation (some initializer) →
    ∃ continuation : InitializerContinuation selected.toBodySelection source,
      ∀ {target : SourceSemantics.Context} {frames : List InitializedLetBinding},
        RecursiveExpressionInvariant
          (context compiled.program.environment compiled.program.signatures
            selected.signature selected.body.declaration)
          selected.body.finalized continuation.entry target →
        ActualContext
          (context compiled.program.environment compiled.program.signatures
            selected.signature selected.body.declaration)
          selected.body.finalized frames target →
        ActualContext.Covers selected.body.finalized frames
          (.statement continuation.entry.allocateStatementId.1) →
        GeneralizationBarrierTransport continuation.receipt.ready continuation.receipt.locals
          continuation.entry.nextRequirement (continuation.receipt.ready.resolve continuation.receipt.value.type)
          selected.body.finalized.substitution target
          (localSchemeTemplateIds (continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution)) →
        (RecursiveExpressionInvariant
            (context compiled.program.environment compiled.program.signatures
              selected.signature selected.body.declaration)
            selected.body.finalized continuation.entry.allocateStatementId.2
            (localSchemeInitializerContext target continuation.initializerBinding.binder) →
          ActualContext
            (context compiled.program.environment compiled.program.signatures
              selected.signature selected.body.declaration)
            selected.body.finalized (frames ++ [continuation.initializerBinding])
            (localSchemeInitializerContext target continuation.initializerBinding.binder) →
          ActualContext.Covers selected.body.finalized (frames ++ [continuation.initializerBinding])
            (.expression continuation.receipt.value.id) →
          ExpressionHasType selected.body.finalized.typedSource
            (localSchemeInitializerContext target continuation.initializerBinding.binder)
            continuation.receipt.value.id
            (selected.body.finalized.substitution.apply continuation.receipt.value.type)) →
        UnannotatedInitializedLetCertificate
          (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement))
          target selected.body.finalized.substitution continuation.receipt.binding.1 continuation.receipt.value.id := by
  obtain ⟨selected⟩ := of_compile accepted member
  refine ⟨selected,?_⟩
  intro index source position name annotation initializer form
  exact selected.toBodySelection.initializedCertificate_of_child
    (SourceCoreCompiler.compile_checked_source accepted) position form


theorem Selected.initializedCertificate_of_child
    (selected : Selected compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement}
    (position : selected.signature.source.value.body.value[index]? = some source)
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (form : source.value = .letDecl name annotation (some initializer)) :
    ∃ continuation : InitializerContinuation selected.toBodySelection source,
      ∀ {target : SourceSemantics.Context} {frames : List InitializedLetBinding},
        RecursiveExpressionInvariant
          (context compiled.program.environment compiled.program.signatures
            selected.signature selected.body.declaration)
          selected.body.finalized continuation.entry target →
        ActualContext
          (context compiled.program.environment compiled.program.signatures
            selected.signature selected.body.declaration)
          selected.body.finalized frames target →
        ActualContext.Covers selected.body.finalized frames
          (.statement continuation.entry.allocateStatementId.1) →
        GeneralizationBarrierTransport continuation.receipt.ready continuation.receipt.locals
          continuation.entry.nextRequirement (continuation.receipt.ready.resolve continuation.receipt.value.type)
          selected.body.finalized.substitution target
          (localSchemeTemplateIds (continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution)) →
        (RecursiveExpressionInvariant
            (context compiled.program.environment compiled.program.signatures
              selected.signature selected.body.declaration)
            selected.body.finalized continuation.entry.allocateStatementId.2
            (localSchemeInitializerContext target continuation.initializerBinding.binder) →
          ActualContext
            (context compiled.program.environment compiled.program.signatures
              selected.signature selected.body.declaration)
            selected.body.finalized (frames ++ [continuation.initializerBinding])
            (localSchemeInitializerContext target continuation.initializerBinding.binder) →
          ActualContext.Covers selected.body.finalized (frames ++ [continuation.initializerBinding])
            (.expression continuation.receipt.value.id) →
          ExpressionHasType selected.body.finalized.typedSource
            (localSchemeInitializerContext target continuation.initializerBinding.binder)
            continuation.receipt.value.id
            (selected.body.finalized.substitution.apply continuation.receipt.value.type)) →
        UnannotatedInitializedLetCertificate
          (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement))
          target selected.body.finalized.substitution continuation.receipt.binding.1 continuation.receipt.value.id :=
  selected.toBodySelection.initializedCertificate_of_child checked position form

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledPrivateBlockContinuation
/-! A reached block carries its actual prefix invariants and the privacy of
its real continuation. The selected check constructs the initial carrier. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness ProtectedVariables

structure PrivateBlockContinuation {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : BodySelection compiled row fuel) extends BlockContinuation selected where
  entryWellFormed : entry.RequirementsWellFormed
  entryTemplates : LiveTemplatesBacked entry
  entryOrigins : ActiveBinderCaptureOrigins entry
    (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement))
  entryPrivate : ActiveQuantifiersPrivate entry
  entryBound : ActiveQuantifiersBelowNext entry
  expectedClosed : expected.VariablesBelow 0
  retainedSource : TypingSourceExtends
    (result.state.toTypedSource (selected.body.body.statements.map NodeId.statement))
    (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement))
  privacy : ∀ protectedVars,
    (∀ v ∈ protectedVars, v.index < result.state.inference.next) →
    LiveBindersSafe protectedVars result.state →
    SafeTransport protectedVars result.state selected.body.body.state ∧
      LiveBindersSafe protectedVars selected.body.body.state ∧
      ∀ requirement ∈ selected.body.body.state.requirements, requirement ∉ result.state.requirements →
        PredicateSafe protectedVars selected.body.body.state requirement.predicate

private theorem return_owner {before after : State} {left right : Ty}
    (accepted : Detail.unify before left right = .ok after) : after.owner = before.owner := by
  unfold Detail.unify at accepted
  cases unified : before.inference.unify left right with
  | error error => simp [unified,Detail.liftUnification,bind,Except.bind] at accepted
  | ok inference =>
    simp only [unified,Detail.liftUnification,bind,Except.bind,pure,Pure.pure,Except.pure] at accepted
    cases accepted
    rfl

namespace PrivateBlockContinuation
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat} {selected : BodySelection compiled row fuel}

def of_selected (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program) : PrivateBlockContinuation selected := by
  have monomorphic : ∀ entry ∈ (selected.signature.parameterNames.zip selected.signature.parameterTypes).map
      (fun parameter => (parameter.1,Scheme.mono parameter.2)), entry.2.quantified = [] := by
    intro entry member
    obtain ⟨parameter,_,rfl⟩ := List.mem_map.mp member
    rfl
  have formation := Frontend.checkProgram_success_signature_formation checked
  refine {
    toBlockContinuation := BlockContinuation.of_selected selected checked
    entryWellFormed := State.initial_requirementsWellFormed _ _ _
    entryTemplates := LiveTemplatesBacked.initial _ _ _
    entryOrigins := activeBinderCaptureOrigins_initial_mono _ _ _ _ monomorphic
    entryPrivate := ActiveQuantifiersPrivate.initial _ _ _ monomorphic
    entryBound := activeQuantifiersBelowNext_initial_mono _ _ _ monomorphic
    expectedClosed := selected.returns_closed checked
    retainedSource := ?_
    privacy := ?_ }
  · refine ⟨return_owner selected.body.unified,?_⟩
    change selected.body.body.state.nodes <+: selected.body.returned.nodes
    rw [selected.body.returned_nodes]
    exact List.prefix_rfl
  · intro protectedVars bound live
    exact ⟨.refl _ _,live,fun requirement member fresh => False.elim (fresh member)⟩

theorem position (block : PrivateBlockContinuation selected)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement} (position : block.sources[index]? = some source) :
    Nonempty (LiveStatementPrivacyOccurrence block.inferenceContext source block.expected block.entry block.result.state
      selected.body.returned (selected.body.body.statements.map NodeId.statement)) := by
  have progress := selected.inferenceProgress checked
  exact liveStatementPrivacyOccurrence_of_position selected.body.resources block.ready block.entryWellFormed block.nodesBelow
    (block.signatures.symm ▸ SignatureCatalogWellFormed.ofCheckProgram checked)
    (block.toBlockContinuation.formation checked) (block.toBlockContinuation.canonical checked)
    block.expectedBelow block.expectedClosed block.entryPrivate block.entryBound block.entryTemplates block.entryOrigins
    block.retainedSource (Substitution.SemanticallyExtends.trans progress.final_substitution block.continuation.substitution_extends)
    block.accepted position

end PrivateBlockContinuation
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledPrivateBlockRestoration
/-! The actual statement suffix and containing block carry privacy after a
scoped child returns. Restoring binders consumes real child-scope membership. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization.PrivateBlockContinuation
open Frontend SourceInference TypeSystem SourceInferenceSoundness ProtectedVariables
variable {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction}
    {fuel : Nat} {selected : BodySelection compiled row fuel}

theorem after_unchanged_occurrence (block : PrivateBlockContinuation selected)
    {source : Syntax.Statement}
    (occurrence : LiveStatementPrivacyOccurrence block.inferenceContext source block.expected block.entry block.result.state
      selected.body.returned (selected.body.body.statements.map NodeId.statement))
    {before : State}
    (inference : occurrence.result.state.inference = before.inference)
    (binders : occurrence.result.state.localBinders ⊆ before.localBinders)
    (requirements : occurrence.result.state.requirements = before.requirements) :
    ∀ protectedVars,
      (∀ v ∈ protectedVars, v.index < before.inference.next) →
      LiveBindersSafe protectedVars before →
      SafeTransport protectedVars before selected.body.body.state ∧
        LiveBindersSafe protectedVars selected.body.body.state ∧
        ∀ requirement ∈ selected.body.body.state.requirements, requirement ∉ before.requirements →
          PredicateSafe protectedVars selected.body.body.state requirement.predicate := by
  intro protectedVars bound live
  have boundAtStatement : ∀ v ∈ protectedVars, v.index < occurrence.result.state.inference.next := by
    simpa only [inference] using bound
  have same := SafeTransport.of_substitution_eq (protectedVars := protectedVars) (congrArg InferState.substitution inference)
  have liveAtStatement := live.restrict binders (congrArg InferState.substitution inference)
  have tail := occurrence.privacy protectedVars boundAtStatement liveAtStatement (safe_closed _ _ block.expectedClosed)
  have liveAtBlock := occurrence.liveAfter protectedVars boundAtStatement liveAtStatement (safe_closed _ _ block.expectedClosed)
  have boundAtBlock : ∀ v ∈ protectedVars, v.index < block.result.state.inference.next :=
    fun v member => Nat.lt_of_lt_of_le (boundAtStatement v member) occurrence.continuation.next_le
  have parent := block.privacy protectedVars boundAtBlock liveAtBlock
  refine ⟨same.trans (tail.1.trans parent.1),parent.2.1,?_⟩
  intro requirement member fresh
  by_cases inBlock : requirement ∈ block.result.state.requirements
  · have fromTail := tail.2 requirement inBlock (by simpa only [requirements] using fresh)
    intro type typeMember
    exact parent.1 type (fromTail type typeMember)
  · exact parent.2.2 requirement member inBlock

end Solcore.SourceSemantics.SourceCompiledLocalFinalization.PrivateBlockContinuation
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledNestedInitializerPrivacy
/-! Every reached block supplies an actual initialized-let receipt with prior
variable avoidance and privacy through the selected body's real finalizer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness ProtectedVariables

structure InitializedReceiptPrivate
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : BodySelection compiled row fuel)
    {childFuel : Nat} {inferenceContext : SourceInference.Context} {source : Syntax.Statement}
    {entry : State} {result : Detail.StatementResult}
    (receipt : LocalLetRequirementTiming.Receipt childFuel inferenceContext source entry result) : Prop where
  ready : receipt.ready.InferenceReady
  extension : selected.body.finalized.substitution.SemanticallyExtends receipt.ready.inference.substitution
  retained : receipt.binding.1 ∈
    (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)).initializedLetBinders
  origins : ActiveBinderCaptureOrigins receipt.ready
    (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement))
  templates : ∀ older ∈ receipt.ready.localBinders, BinderTemplatesBefore receipt.ready entry.nextRequirement older
  priorAvoided : Avoids (activeSchemeQuantifiers entry) (receipt.ready.resolve receipt.value.type)
  transport : ∀ type, Safe receipt.binding.1.scheme.quantified receipt.ready type →
    Avoids receipt.binding.1.scheme.quantified (selected.body.finalized.substitution.apply type)
  newRows : ∀ requirement ∈ selected.body.body.state.requirements, requirement ∉ receipt.ready.requirements →
    ∀ type ∈ requirement.predicate.subject :: requirement.predicate.arguments,
      Avoids receipt.binding.1.scheme.quantified (selected.body.finalized.substitution.apply type)

namespace PrivateBlockContinuation
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat} {selected : BodySelection compiled row fuel}

theorem initialized (block : PrivateBlockContinuation selected)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement} (position : block.sources[index]? = some source)
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (form : source.value = .letDecl name annotation (some initializer)) :
    ∃ childFuel entry result, ∃ receipt : LocalLetRequirementTiming.Receipt childFuel block.inferenceContext source entry result,
      InitializedReceiptPrivate selected receipt := by
  obtain ⟨occurrence⟩ := block.position checked position
  have formation := block.toBlockContinuation.formation checked
  have canonical := block.toBlockContinuation.canonical checked
  obtain ⟨childFuel,receipt,ready,bodyContinuation⟩ :=
    occurrence.toActiveStatementPrivacyOccurrence.toBackedStatementPrivacyOccurrence.toStatementPrivacyOccurrence.toOccurrence.initialized
      form formation canonical
  have progress := selected.inferenceProgress checked
  have resultExtension := Substitution.SemanticallyExtends.trans progress.final_substitution
    (occurrence.continuation.trans block.continuation).substitution_extends
  have readyExtension : selected.body.finalized.substitution.SemanticallyExtends receipt.ready.inference.substitution := by
    rwa [receipt.inference_eq] at resultExtension
  have retainedNodes := occurrence.retained.trans block.retainedSource.nodes_prefix
  have retainedBinder : receipt.binding.1 ∈
      (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)).initializedLetBinders := by
    unfold TypedSource.initializedLetBinders
    exact List.mem_flatMap.mpr ⟨_,retainedNodes.subset receipt.recorded,List.mem_singleton_self _⟩
  have live := ProtectedVariables.LocalLetRequirementTiming.Receipt.active_privacy selected.body.resources receipt
    occurrence.ready occurrence.entryWellFormed formation canonical occurrence.entryTemplates occurrence.entryOrigins
    retainedNodes resultExtension
  have properties := receipt.initializer_inference occurrence.ready formation canonical
  have bound : ∀ q ∈ receipt.binding.1.scheme.quantified, q.index < occurrence.result.state.inference.next := by
    intro q member
    have below := properties.2.1.solved.variablesBelow_apply properties.2.2
    have actual := below q (List.mem_filter.mp member).1
    rwa [receipt.inference_eq]
  have tail := block.after_unchanged_occurrence occurrence rfl (List.Subset.refl _) rfl
    receipt.binding.1.scheme.quantified bound live
  have templates := ProtectedVariables.LocalLetRequirementTiming.Receipt.templates_before receipt
    occurrence.entryTemplates occurrence.ready occurrence.entryWellFormed formation canonical
  have prior := ProtectedVariables.LocalLetRequirementTiming.Receipt.value_avoids_active receipt occurrence.ready
    occurrence.entryWellFormed occurrence.entryBound occurrence.entryPrivate
    (block.signatures.symm ▸ SignatureCatalogWellFormed.ofCheckProgram checked) formation canonical
  refine ⟨childFuel,occurrence.entry,occurrence.result,receipt,
    ⟨ready,readyExtension,retainedBinder,occurrence.entryOrigins.congr_localBinders receipt.ready_binders,
      templates,prior,?_,?_⟩⟩
  · intro type safe
    apply selected.finishPrivacy checked _ type
    apply tail.1 type
    exact SafeTransport.of_substitution_eq (congrArg InferState.substitution receipt.inference_eq) type safe
  · intro requirement member fresh type typeMember
    apply selected.finishPrivacy checked _ type
    apply tail.2.2 requirement member _ type typeMember
    have same : occurrence.result.state.requirements = receipt.ready.requirements :=
      congrArg (fun result : Detail.StatementResult => result.state.requirements) receipt.completed
    simpa only [same] using fresh

end PrivateBlockContinuation
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledNestedInitializerStatementPrivacy
/-! The exact initialized statement is retained alongside its private receipt,
so later consumers use the same initializer occurrence and binder allocation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness ProtectedVariables

structure InitializedStatementReceiptPrivate
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : BodySelection compiled row fuel)
    {childFuel : Nat} {inferenceContext : SourceInference.Context} {source : Syntax.Statement}
    {entry : State} {result : Detail.StatementResult}
    (receipt : LocalLetRequirementTiming.Receipt childFuel inferenceContext source entry result) : Prop
    extends InitializedReceiptPrivate selected receipt where
  recorded : Node.statement {
    id := entry.allocateStatementId.1
    span := source.span
    type := .unit
    form := .letDecl receipt.binding.1 (some receipt.value.id) } ∈ selected.body.returned.nodes

namespace PrivateBlockContinuation
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat} {selected : BodySelection compiled row fuel}

theorem initialized_statement (block : PrivateBlockContinuation selected)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement} (position : block.sources[index]? = some source)
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (form : source.value = .letDecl name annotation (some initializer)) :
    ∃ childFuel entry result, ∃ receipt : LocalLetRequirementTiming.Receipt childFuel block.inferenceContext source entry result,
      InitializedStatementReceiptPrivate selected receipt := by
  obtain ⟨occurrence⟩ := block.position checked position
  have formation := block.toBlockContinuation.formation checked
  have canonical := block.toBlockContinuation.canonical checked
  obtain ⟨childFuel,receipt,ready,bodyContinuation⟩ :=
    occurrence.toActiveStatementPrivacyOccurrence.toBackedStatementPrivacyOccurrence.toStatementPrivacyOccurrence.toOccurrence.initialized
      form formation canonical
  have progress := selected.inferenceProgress checked
  have resultExtension := Substitution.SemanticallyExtends.trans progress.final_substitution
    (occurrence.continuation.trans block.continuation).substitution_extends
  have readyExtension : selected.body.finalized.substitution.SemanticallyExtends receipt.ready.inference.substitution := by
    rwa [receipt.inference_eq] at resultExtension
  have retainedNodes := occurrence.retained.trans block.retainedSource.nodes_prefix
  have retainedBinder : receipt.binding.1 ∈
      (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)).initializedLetBinders := by
    unfold TypedSource.initializedLetBinders
    exact List.mem_flatMap.mpr ⟨_,retainedNodes.subset receipt.recorded,List.mem_singleton_self _⟩
  have live := ProtectedVariables.LocalLetRequirementTiming.Receipt.active_privacy selected.body.resources receipt
    occurrence.ready occurrence.entryWellFormed formation canonical occurrence.entryTemplates occurrence.entryOrigins
    retainedNodes resultExtension
  have properties := receipt.initializer_inference occurrence.ready formation canonical
  have bound : ∀ q ∈ receipt.binding.1.scheme.quantified, q.index < occurrence.result.state.inference.next := by
    intro q member
    have below := properties.2.1.solved.variablesBelow_apply properties.2.2
    have actual := below q (List.mem_filter.mp member).1
    rwa [receipt.inference_eq]
  have tail := block.after_unchanged_occurrence occurrence rfl (List.Subset.refl _) rfl
    receipt.binding.1.scheme.quantified bound live
  have templates := ProtectedVariables.LocalLetRequirementTiming.Receipt.templates_before receipt
    occurrence.entryTemplates occurrence.ready occurrence.entryWellFormed formation canonical
  have prior := ProtectedVariables.LocalLetRequirementTiming.Receipt.value_avoids_active receipt occurrence.ready
    occurrence.entryWellFormed occurrence.entryBound occurrence.entryPrivate
    (block.signatures.symm ▸ SignatureCatalogWellFormed.ofCheckProgram checked) formation canonical
  refine ⟨childFuel,occurrence.entry,occurrence.result,receipt,
    { toInitializedReceiptPrivate :=
        ⟨ready,readyExtension,retainedBinder,occurrence.entryOrigins.congr_localBinders receipt.ready_binders,
          templates,prior,?_,?_⟩
      recorded := retainedNodes.subset receipt.recorded }⟩
  · intro type safe
    apply selected.finishPrivacy checked _ type
    apply tail.1 type
    exact SafeTransport.of_substitution_eq (congrArg InferState.substitution receipt.inference_eq) type safe
  · intro requirement member fresh type typeMember
    apply selected.finishPrivacy checked _ type
    apply tail.2.2 requirement member _ type typeMember
    have same : occurrence.result.state.requirements = receipt.ready.requirements :=
      congrArg (fun result : Detail.StatementResult => result.state.requirements) receipt.completed
    simpa only [same] using fresh

end PrivateBlockContinuation
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledPrivateBlockDescent
/-! Actual scoped blocks pass the established active-variable invariants to
their child, then restore the genuine entering scope on the path to finalization. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization.PrivateBlockContinuation
open Frontend SourceInference TypeSystem SourceInferenceSoundness ProtectedVariables
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat} {selected : BodySelection compiled row fuel}

theorem enter_block (block : PrivateBlockContinuation selected)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement} (position : block.sources[index]? = some source)
    {body : List Syntax.Statement} (form : source.value = .block body) :
    ∃ child : PrivateBlockContinuation selected, child.sources = body ∧
      child.inferenceContext = block.inferenceContext := by
  obtain ⟨occurrence⟩ := block.position checked position
  have accepted := occurrence.accepted
  cases fuelEq : occurrence.fuel with
  | zero => simp [fuelEq, Detail.inferStatementFuel] at accepted
  | succ childFuel =>
    rw [fuelEq] at accepted
    obtain ⟨bodyResult,bodyAccepted,completed,_⟩ := inferStatementFuel_success_block_facts form rfl accepted
    have expectedAtEntry := block.expectedBelow.weaken occurrence.before.next_le
    have properties := Detail.inferStatementsFuel_inferenceProperties occurrence.ready.allocateStatementId
      (block.toBlockContinuation.formation checked) (block.toBlockContinuation.canonical checked) expectedAtEntry bodyAccepted
    have unchanged : occurrence.result.state.inference = bodyResult.state.inference :=
      congrArg (fun result : Detail.StatementResult => result.state.inference) completed
    have nodes : bodyResult.state.nodes <+: occurrence.result.state.nodes := by
      have same := congrArg (fun result : Detail.StatementResult => result.state.nodes) completed
      rw [same]
      exact List.prefix_append _ _
    have boundScope : occurrence.result.state.localBinders ⊆ bodyResult.state.localBinders := by
      have same := congrArg (fun result : Detail.StatementResult => result.state.localBinders) completed
      rw [same]
      exact inferStatementsFuel_binders_subset (initial := occurrence.entry.allocateStatementId.2) bodyAccepted
    have reqs : occurrence.result.state.requirements = bodyResult.state.requirements :=
      congrArg (fun result : Detail.StatementResult => result.state.requirements) completed
    refine ⟨{
      checkingFuel := childFuel, inferenceContext := block.inferenceContext, sources := body,
      expected := block.expected, entry := occurrence.entry.allocateStatementId.2, result := bodyResult,
      signatures := block.signatures, accepted := bodyAccepted, ready := occurrence.ready.allocateStatementId,
      nodesBelow := State.allocateStatementId_preserves_nodesBelowNextOccurrence occurrence.entry occurrence.entryNodesBelow,
      expectedBelow := expectedAtEntry,
      continuation := (State.InferenceProgress.of_inference_eq properties.2.1.solved unchanged).trans
        (occurrence.continuation.trans block.continuation),
      retained := nodes.trans (occurrence.retained.trans block.retained),
      entryWellFormed := occurrence.entryWellFormed,
      entryTemplates := occurrence.entryTemplates.congr rfl rfl rfl,
      entryOrigins := occurrence.entryOrigins.congr_localBinders rfl,
      entryPrivate := occurrence.entryPrivate.congr rfl rfl,
      entryBound := occurrence.entryBound,
      expectedClosed := block.expectedClosed,
      retainedSource := ?_,
      privacy := block.after_unchanged_occurrence occurrence unchanged boundScope reqs
    },rfl,rfl⟩
    refine ⟨?_,nodes.trans (occurrence.retained.trans block.retainedSource.nodes_prefix)⟩
    exact block.retainedSource.owner_eq.trans (occurrence.resultOwner.trans
      (congrArg (fun result : Detail.StatementResult => result.state.owner) completed))

end Solcore.SourceSemantics.SourceCompiledLocalFinalization.PrivateBlockContinuation
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledPrivateConditionalDescent
/-! Conditions are evaluated by the actual checker before entering a branch
or loop body. Their scope-preserving results carry every active privacy invariant. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization.PrivateBlockContinuation
open Frontend SourceInference TypeSystem SourceInferenceSoundness ProtectedVariables
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat} {selected : BodySelection compiled row fuel}

theorem enter_while_body (block : PrivateBlockContinuation selected)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement} (position : block.sources[index]? = some source)
    {condition : Syntax.Expr} {body : Syntax.Block} (form : source.value = .whileLoop condition body) :
    ∃ child : PrivateBlockContinuation selected, child.sources = body.value ∧
      child.inferenceContext = { block.inferenceContext with loopDepth := block.inferenceContext.loopDepth + 1 } := by
  obtain ⟨occurrence⟩ := block.position checked position
  have occurrenceBelow := occurrence.entryNodesBelow
  have accepted := occurrence.accepted
  cases fuelEq : occurrence.fuel with
  | zero => simp [fuelEq, Detail.inferStatementFuel] at accepted
  | succ childFuel =>
      rw [fuelEq] at accepted
      obtain ⟨test, testState, bodyResult, testAccepted, bodyAccepted, completed, _⟩ :=
        SourceInferenceSoundness.inferStatementFuel_success_whileLoop_facts form rfl accepted
      have testProperties := Detail.inferExprFuel_inferenceProperties occurrence.ready.allocateStatementId
        (block.toBlockContinuation.formation checked) (block.toBlockContinuation.canonical checked)
        (by intro type member; cases Option.some.inj member; simp [Ty.VariablesBelow, Ty.freeVariables, Ty.bool]) testAccepted
      have expectedAtTest := (block.expectedBelow.weaken occurrence.before.next_le).weaken
        testProperties.1.next_le
      have bodyProperties := Detail.inferStatementsFuel_inferenceProperties
        (context := { block.inferenceContext with loopDepth := block.inferenceContext.loopDepth + 1 })
        testProperties.2.1 (block.toBlockContinuation.formation checked) (block.toBlockContinuation.canonical checked) expectedAtTest bodyAccepted
      have unchanged : occurrence.result.state.inference = bodyResult.state.inference :=
        congrArg (fun result : Detail.StatementResult => result.state.inference) completed
      have nodes : bodyResult.state.nodes <+: occurrence.result.state.nodes := by
        have same := congrArg (fun result : Detail.StatementResult => result.state.nodes) completed
        rw [same]
        exact List.prefix_append _ _
      have closed : ∀ type ∈ (some Ty.bool : Option Ty), type.VariablesBelow 0 := by
        intro type member
        cases Option.some.inj member
        simp [Ty.VariablesBelow,Ty.freeVariables,Ty.bool]
      have binders : occurrence.result.state.localBinders ⊆ bodyResult.state.localBinders := by
        have same := congrArg (fun result : Detail.StatementResult => result.state.localBinders) completed
        rw [same]
        exact inferStatementsFuel_binders_subset (initial := testState) bodyAccepted
      have requirements : occurrence.result.state.requirements = bodyResult.state.requirements :=
        congrArg (fun result : Detail.StatementResult => result.state.requirements) completed
      refine ⟨{
        checkingFuel := childFuel,
        inferenceContext := { block.inferenceContext with loopDepth := block.inferenceContext.loopDepth + 1 },
        sources := body.value, expected := block.expected, entry := testState, result := bodyResult,
        signatures := block.signatures, accepted := bodyAccepted, ready := testProperties.2.1,
        nodesBelow := ?_, expectedBelow := expectedAtTest,
        continuation := (State.InferenceProgress.of_inference_eq bodyProperties.2.1.solved unchanged).trans
          (occurrence.continuation.trans block.continuation),
        retained := nodes.trans (occurrence.retained.trans block.retained),
        entryWellFormed := (Detail.inferExprFuel_direct_progress testAccepted).wellFormed occurrence.entryWellFormed,
        entryTemplates := (show LiveTemplatesBacked occurrence.entry.allocateStatementId.2 from occurrence.entryTemplates.congr rfl rfl rfl).inferExprFuel occurrence.ready.allocateStatementId
          (block.toBlockContinuation.formation checked) (block.toBlockContinuation.canonical checked)
          (fun type member => (closed type member).weaken (Nat.zero_le _)) testAccepted,
        entryOrigins := (occurrence.entryOrigins.congr_localBinders (final := occurrence.entry.allocateStatementId.2) rfl).inferExprFuel testAccepted,
        entryPrivate := (show ActiveQuantifiersPrivate occurrence.entry.allocateStatementId.2 from occurrence.entryPrivate.congr rfl rfl).inferExprFuel occurrence.ready.allocateStatementId
          occurrence.entryWellFormed occurrence.entryBound (block.signatures.symm ▸ SignatureCatalogWellFormed.ofCheckProgram checked)
          (block.toBlockContinuation.formation checked) (block.toBlockContinuation.canonical checked) closed testAccepted,
        entryBound := activeQuantifiersBelowNext_inferExprFuel (initial := occurrence.entry.allocateStatementId.2) occurrence.entryBound occurrence.ready.allocateStatementId
          (block.toBlockContinuation.formation checked) (block.toBlockContinuation.canonical checked)
          (fun type member => (closed type member).weaken (Nat.zero_le _)) testAccepted,
        expectedClosed := block.expectedClosed,
        retainedSource := ⟨block.retainedSource.owner_eq.trans (occurrence.resultOwner.trans
          (congrArg (fun result : Detail.StatementResult => result.state.owner) completed)),
          nodes.trans (occurrence.retained.trans block.retainedSource.nodes_prefix)⟩,
        privacy := block.after_unchanged_occurrence occurrence unchanged binders requirements
      }, rfl, rfl⟩
      exact (Detail.inferExprFuel_occurrenceBoundExtends testAccepted).nodesBelowNextOccurrence
        (State.allocateStatementId_preserves_nodesBelowNextOccurrence occurrence.entry occurrenceBelow)


theorem enter_if_without_else (block : PrivateBlockContinuation selected)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement} (position : block.sources[index]? = some source)
    {condition : Syntax.Expr} {body : Syntax.Block} (form : source.value = .ifThen condition body none) :
    ∃ child : PrivateBlockContinuation selected, child.sources = body.value ∧
      child.inferenceContext = block.inferenceContext := by
  obtain ⟨occurrence⟩ := block.position checked position
  have occurrenceBelow := occurrence.entryNodesBelow
  have accepted := occurrence.accepted
  cases fuelEq : occurrence.fuel with
  | zero => simp [fuelEq, Detail.inferStatementFuel] at accepted
  | succ childFuel =>
      rw [fuelEq] at accepted
      obtain ⟨test, testState, bodyResult, testAccepted, bodyAccepted, completed, _⟩ :=
        SourceInferenceSoundness.inferStatementFuel_success_ifWithoutElse_facts form rfl accepted
      have testProperties := Detail.inferExprFuel_inferenceProperties occurrence.ready.allocateStatementId
        (block.toBlockContinuation.formation checked) (block.toBlockContinuation.canonical checked)
        (by intro type member; cases Option.some.inj member; simp [Ty.VariablesBelow, Ty.freeVariables, Ty.bool]) testAccepted
      have expectedAtTest := (block.expectedBelow.weaken occurrence.before.next_le).weaken
        testProperties.1.next_le
      have bodyProperties := Detail.inferStatementsFuel_inferenceProperties
        (context := block.inferenceContext)
        testProperties.2.1 (block.toBlockContinuation.formation checked) (block.toBlockContinuation.canonical checked) expectedAtTest bodyAccepted
      have unchanged : occurrence.result.state.inference = bodyResult.state.inference :=
        congrArg (fun result : Detail.StatementResult => result.state.inference) completed
      have nodes : bodyResult.state.nodes <+: occurrence.result.state.nodes := by
        have same := congrArg (fun result : Detail.StatementResult => result.state.nodes) completed
        rw [same]
        exact List.prefix_append _ _
      have closed : ∀ type ∈ (some Ty.bool : Option Ty), type.VariablesBelow 0 := by
        intro type member
        cases Option.some.inj member
        simp [Ty.VariablesBelow,Ty.freeVariables,Ty.bool]
      have binders : occurrence.result.state.localBinders ⊆ bodyResult.state.localBinders := by
        have same := congrArg (fun result : Detail.StatementResult => result.state.localBinders) completed
        rw [same]
        exact inferStatementsFuel_binders_subset (initial := testState) bodyAccepted
      have requirements : occurrence.result.state.requirements = bodyResult.state.requirements :=
        congrArg (fun result : Detail.StatementResult => result.state.requirements) completed
      refine ⟨{
        checkingFuel := childFuel,
        inferenceContext := block.inferenceContext,
        sources := body.value, expected := block.expected, entry := testState, result := bodyResult,
        signatures := block.signatures, accepted := bodyAccepted, ready := testProperties.2.1,
        nodesBelow := ?_, expectedBelow := expectedAtTest,
        continuation := (State.InferenceProgress.of_inference_eq bodyProperties.2.1.solved unchanged).trans
          (occurrence.continuation.trans block.continuation),
        retained := nodes.trans (occurrence.retained.trans block.retained),
        entryWellFormed := (Detail.inferExprFuel_direct_progress testAccepted).wellFormed occurrence.entryWellFormed,
        entryTemplates := (show LiveTemplatesBacked occurrence.entry.allocateStatementId.2 from occurrence.entryTemplates.congr rfl rfl rfl).inferExprFuel occurrence.ready.allocateStatementId
          (block.toBlockContinuation.formation checked) (block.toBlockContinuation.canonical checked)
          (fun type member => (closed type member).weaken (Nat.zero_le _)) testAccepted,
        entryOrigins := (occurrence.entryOrigins.congr_localBinders (final := occurrence.entry.allocateStatementId.2) rfl).inferExprFuel testAccepted,
        entryPrivate := (show ActiveQuantifiersPrivate occurrence.entry.allocateStatementId.2 from occurrence.entryPrivate.congr rfl rfl).inferExprFuel occurrence.ready.allocateStatementId
          occurrence.entryWellFormed occurrence.entryBound (block.signatures.symm ▸ SignatureCatalogWellFormed.ofCheckProgram checked)
          (block.toBlockContinuation.formation checked) (block.toBlockContinuation.canonical checked) closed testAccepted,
        entryBound := activeQuantifiersBelowNext_inferExprFuel (initial := occurrence.entry.allocateStatementId.2) occurrence.entryBound occurrence.ready.allocateStatementId
          (block.toBlockContinuation.formation checked) (block.toBlockContinuation.canonical checked)
          (fun type member => (closed type member).weaken (Nat.zero_le _)) testAccepted,
        expectedClosed := block.expectedClosed,
        retainedSource := ⟨block.retainedSource.owner_eq.trans (occurrence.resultOwner.trans
          (congrArg (fun result : Detail.StatementResult => result.state.owner) completed)),
          nodes.trans (occurrence.retained.trans block.retainedSource.nodes_prefix)⟩,
        privacy := block.after_unchanged_occurrence occurrence unchanged binders requirements
      }, rfl, rfl⟩
      exact (Detail.inferExprFuel_occurrenceBoundExtends testAccepted).nodesBelowNextOccurrence
        (State.allocateStatementId_preserves_nodesBelowNextOccurrence occurrence.entry occurrenceBelow)


end Solcore.SourceSemantics.SourceCompiledLocalFinalization.PrivateBlockContinuation
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledPrivateBranchDescent
/-! Both branches follow the checker's actual order. Else starts after the
then scope is restored, and both continuations reach the same finalizer. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization.PrivateBlockContinuation
open Frontend SourceInference TypeSystem SourceInferenceSoundness ProtectedVariables
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat} {selected : BodySelection compiled row fuel}

theorem enter_if_with_else (block : PrivateBlockContinuation selected)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement} (position : block.sources[index]? = some source)
    {condition : Syntax.Expr} {thenBody elseBody : Syntax.Block}
    (form : source.value = .ifThen condition thenBody (some elseBody)) (isElse : Bool) :
    ∃ child : PrivateBlockContinuation selected,
      child.sources = (if isElse then elseBody else thenBody).value ∧
      child.inferenceContext = block.inferenceContext := by
  obtain ⟨occurrence⟩ := block.position checked position
  have accepted := occurrence.accepted
  cases fuelEq : occurrence.fuel with
  | zero => simp [fuelEq, Detail.inferStatementFuel] at accepted
  | succ childFuel =>
    rw [fuelEq] at accepted
    obtain ⟨test, testState, thenResult, elseResult, testAccepted, thenAccepted, elseAccepted, completed, _⟩ :=
      inferStatementFuel_success_ifWithElse_facts form rfl accepted
    have formation := block.toBlockContinuation.formation checked
    have canonical := block.toBlockContinuation.canonical checked
    have catalog : SignatureCatalogWellFormed block.inferenceContext.signatures :=
      block.signatures.symm ▸ SignatureCatalogWellFormed.ofCheckProgram checked
    have closed : ∀ type ∈ (some Ty.bool : Option Ty), type.VariablesBelow 0 := by
      intro type member
      cases Option.some.inj member
      simp [Ty.VariablesBelow, Ty.freeVariables, Ty.bool]
    have testProperties := Detail.inferExprFuel_inferenceProperties occurrence.ready.allocateStatementId
      formation canonical (fun type member => (closed type member).weaken (Nat.zero_le _)) testAccepted
    have expectedAtTest := (block.expectedBelow.weaken occurrence.before.next_le).weaken testProperties.1.next_le
    have thenProperties := Detail.inferStatementsFuel_inferenceProperties testProperties.2.1
      formation canonical expectedAtTest thenAccepted
    have restored := State.restoreLexicalScope_inferenceProperties testProperties.2.1 thenProperties.1
    have expectedAtElse := expectedAtTest.weaken restored.1.next_le
    have elseProperties := Detail.inferStatementsFuel_inferenceProperties restored.2
      formation canonical expectedAtElse elseAccepted
    have testBelow := (Detail.inferExprFuel_occurrenceBoundExtends testAccepted).nodesBelowNextOccurrence
      (State.allocateStatementId_preserves_nodesBelowNextOccurrence occurrence.entry occurrence.entryNodesBelow)
    have thenBelow := (Detail.inferStatementsFuel_occurrenceBoundExtends thenAccepted).nodesBelowNextOccurrence testBelow
    have branchNodes : thenResult.state.nodes <+: elseResult.state.nodes :=
      Detail.inferStatementsFuel_preserves_nodesPrefix elseAccepted (List.prefix_refl _) thenBelow (Nat.le_refl _)
    have nodes : elseResult.state.nodes <+: occurrence.result.state.nodes := by
      rw [congrArg (fun result : Detail.StatementResult => result.state.nodes) completed]
      exact List.prefix_append _ _
    have unchanged : occurrence.result.state.inference = elseResult.state.inference :=
      congrArg (fun result : Detail.StatementResult => result.state.inference) completed
    have last := (State.InferenceProgress.of_inference_eq elseProperties.2.1.solved unchanged).trans
      (occurrence.continuation.trans block.continuation)
    have retained := nodes.trans (occurrence.retained.trans block.retained)
    have elseSource : TypingSourceExtends
        (elseResult.state.toTypedSource (selected.body.body.statements.map NodeId.statement))
        (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)) :=
      ⟨block.retainedSource.owner_eq.trans (occurrence.resultOwner.trans
        (congrArg (fun result : Detail.StatementResult => result.state.owner) completed)),
        nodes.trans (occurrence.retained.trans block.retainedSource.nodes_prefix)⟩
    have thenSource : TypingSourceExtends
        (thenResult.state.toTypedSource (selected.body.body.statements.map NodeId.statement))
        (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)) :=
      (inferStatementsFuel_success_typingSourceExtends elseAccepted thenBelow _).trans elseSource
    have testWellFormed := (Detail.inferExprFuel_direct_progress testAccepted).wellFormed occurrence.entryWellFormed
    have testTemplates :=
      (show LiveTemplatesBacked occurrence.entry.allocateStatementId.2 from occurrence.entryTemplates.congr rfl rfl rfl).inferExprFuel
        occurrence.ready.allocateStatementId formation canonical
        (fun type member => (closed type member).weaken (Nat.zero_le _)) testAccepted
    have testOrigins :=
      (occurrence.entryOrigins.congr_localBinders (final := occurrence.entry.allocateStatementId.2) rfl).inferExprFuel testAccepted
    have testPrivate :=
      (show ActiveQuantifiersPrivate occurrence.entry.allocateStatementId.2 from occurrence.entryPrivate.congr rfl rfl).inferExprFuel
        occurrence.ready.allocateStatementId occurrence.entryWellFormed occurrence.entryBound catalog formation canonical closed testAccepted
    have testBound := activeQuantifiersBelowNext_inferExprFuel (initial := occurrence.entry.allocateStatementId.2)
      occurrence.entryBound occurrence.ready.allocateStatementId formation canonical
      (fun type member => (closed type member).weaken (Nat.zero_le _)) testAccepted
    have thenWellFormed := (Detail.inferStatementsFuel_direct_progress thenAccepted).wellFormed testWellFormed
    have thenExtension := Substitution.SemanticallyExtends.trans
      (selected.inferenceProgress checked).final_substitution
      (elseProperties.1.trans last).substitution_extends
    have thenActive := activeState_inferStatementsFuel selected.body.resources testProperties.2.1
      testWellFormed testBelow catalog formation canonical block.expectedClosed testPrivate testBound
      testTemplates testOrigins thenSource thenExtension thenAccepted
    have savedSubset : testState.localBinders ⊆ thenResult.state.localBinders :=
      inferStatementsFuel_binders_subset thenAccepted
    have elseSavedSubset : occurrence.result.state.localBinders ⊆ elseResult.state.localBinders := by
      rw [congrArg (fun result : Detail.StatementResult => result.state.localBinders) completed]
      exact inferStatementsFuel_binders_subset
        (initial := thenResult.state.restoreLexicalScope testState.lexicalScope) elseAccepted
    have requirements : occurrence.result.state.requirements = elseResult.state.requirements :=
      congrArg (fun result : Detail.StatementResult => result.state.requirements) completed
    have afterElse := block.after_unchanged_occurrence occurrence unchanged elseSavedSubset requirements
    cases isElse with
    | false =>
      refine ⟨{
        checkingFuel := childFuel, inferenceContext := block.inferenceContext,
        sources := thenBody.value, expected := block.expected, entry := testState, result := thenResult,
        signatures := block.signatures, accepted := thenAccepted, ready := testProperties.2.1,
        nodesBelow := testBelow, expectedBelow := expectedAtTest,
        continuation := (State.InferenceProgress.restoreLexicalScope thenResult.state
          testState.lexicalScope thenProperties.2.1.solved).trans (elseProperties.1.trans last),
        retained := branchNodes.trans retained, entryWellFormed := testWellFormed,
        entryTemplates := testTemplates, entryOrigins := testOrigins, entryPrivate := testPrivate,
        entryBound := testBound, expectedClosed := block.expectedClosed, retainedSource := thenSource,
        privacy := ?_
      }, rfl, rfl⟩
      intro protectedVars bound live
      have restoredLive : LiveBindersSafe protectedVars
          (thenResult.state.restoreLexicalScope testState.lexicalScope) :=
        live.restrict savedSubset rfl
      have sibling := inferStatementsFuel_private protectedVars childFuel block.inferenceContext
        elseBody.value block.expected (thenResult.state.restoreLexicalScope testState.lexicalScope)
        restored.2 thenWellFormed bound restoredLive catalog formation canonical expectedAtElse
        (safe_closed _ _ block.expectedClosed) elseResult elseAccepted
      have outer := afterElse protectedVars
        (fun v member => Nat.lt_of_lt_of_le (bound v member) elseProperties.1.next_le) sibling.2.2.1
      exact ⟨sibling.1.trans outer.1, outer.2.1,
        new_requirements_trans sibling.2.2.2 outer.2.2 outer.1⟩
    | true =>
      exact ⟨{
        checkingFuel := childFuel, inferenceContext := block.inferenceContext,
        sources := elseBody.value, expected := block.expected,
        entry := thenResult.state.restoreLexicalScope testState.lexicalScope, result := elseResult,
        signatures := block.signatures, accepted := elseAccepted, ready := restored.2,
        nodesBelow := thenBelow, expectedBelow := expectedAtElse,
        continuation := last, retained := retained, entryWellFormed := thenWellFormed,
        entryTemplates := testTemplates.transport (List.Subset.refl _)
          (Detail.inferStatementsFuel_requirements_subset thenAccepted) thenProperties.1.substitution_extends,
        entryOrigins := testOrigins.congr_localBinders rfl,
        entryPrivate := thenActive.1.restrict savedSubset rfl,
        entryBound := activeQuantifiersBelowNext_transport testBound rfl thenProperties.1.next_le,
        expectedClosed := block.expectedClosed, retainedSource := elseSource, privacy := afterElse
      }, rfl, rfl⟩

end Solcore.SourceSemantics.SourceCompiledLocalFinalization.PrivateBlockContinuation
end
