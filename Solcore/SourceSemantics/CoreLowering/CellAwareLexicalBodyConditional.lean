import Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyBlock
import Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryContinuation

/-! Ordinary declaration prefixes compose actual marked allocation with the
rest of the lexical body. Restoring bindings keeps new Source and native cells
and every earlier captured generalized descriptor. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyConditional
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CellAwareLexicalBodyState

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  {functions : FunctionModel checked.catalog ambient}
  {rawRegistry : SourceCoreRawMetadata.Registry}
  {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
  {program : Program} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {faults : RecursiveStageMeaning.FaultRep}

local notation "model" => CompatibleAmbientHeap.payloadModel checked rawRegistry functions
local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel model instances

variable (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial checked).registry rawRegistry)
  {reasonAt : ExpressionId → Word} {semanticFaults : FunctionCalls.FaultRep}
  (uninitialized : ∀ context fuel scope id lowered,
    CompatibleExpressionReads.LoweredRead fuel (.initial checked) invocation.source context reasonAt scope id lowered →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id))
  (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)
  (wellFormed : ProgramWellFormed program)

include extension uninitialized semantic wellFormed in
theorem completes {context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body}
    (entry : Entry functions rawRegistry instances program invocation frame globals context scope)
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
    (conditionFound : invocation.source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (certificate : CellAwareLexicalBodyExpressions.Certificate (checked := checked) (invocation := invocation)
      (reasonAt := reasonAt) context scope condition ⟨.bool,conditionCode⟩)
    (left : ∀ start : Entry functions rawRegistry instances program invocation frame globals context scope,
      Nonempty (Result start registry faults false thenBody expected type thenCode))
    (right : ∀ start : Entry functions rawRegistry instances program invocation frame globals context scope,
      Nonempty (Result start registry faults false (elseBody.getD []) expected type elseCode))
    (continuation : (∀ next : Entry functions rawRegistry instances program invocation frame globals context scope,
        Nonempty (Result next registry faults mode rest expected type body)) ∨
      (GenericLexicalStatements.Stopped invocation.source thenBody ∧
        GenericLexicalStatements.Stopped invocation.source (elseBody.getD []))) :
    Nonempty (Result entry registry faults mode (id :: rest) expected type
      (LocalLoop.sequence type (LocalLoop.conditional type conditionCode thenCode elseCode) body)) := by
  obtain ⟨testSize,outcome,middle,value,middleStore,testTrace,testEval,testRep,testHeaps,testFrame,testEffect,valueTyped,testDetermines⟩ :=
    CellAwareLexicalBodyExpressions.expression functions extension uninitialized semantic wellFormed entry certificate conditionFound
  cases outcome with
  | fault reason =>
    cases testRep with
    | fault matched =>
      exact ⟨{
        size := _
        finalContext := context
        outcome := .fault reason
        after := middle
        value := _
        store := middleStore
        mapping := entry.mapping
        world := entry.world
        determines := CellAwareLexicalBodyDeterminacy.conditionalFault entry.runtime.graph.nodeOccurrencesUnique found form testDetermines
        trace := .ifConditionFault (lookupStatement?_sound found) form testTrace
        evaluated := by
          rw [LoopRenaming.sequence,LoopRenaming.conditional]
          exact LocalLoop.sequence_failure _ (LocalControl.choose_failure _ testEval)
        represented := .fault matched
        heaps := testHeaps
        preserved := testFrame
        effect := testEffect
        fallthroughTyped := by intro _ impossible; cases impossible }⟩
  | value sourceValue =>
    cases testRep with
    | @value _ nativeValue payload =>
      obtain ⟨truth,sourceEq,nativeEq⟩ := CompatibleExpressionPrimitives.bool_fields (conditionType ▸ payload)
      subst sourceValue nativeValue
      have middleTyped := (valueTyped (.bool truth) rfl).1
      let reached := entry.advance testHeaps middleTyped testFrame testEffect
      let branched := reached.prefix (.bool truth) .bool .bool
      have selected : ∀ start : Entry functions rawRegistry instances program invocation frame globals context scope,
          Nonempty (Result start registry faults false (if truth then thenBody else elseBody.getD []) expected type
            (if truth then thenCode else elseCode)) := by
        cases truth <;> assumption
      obtain ⟨⟨branchSize,innerContext,outcome,after,value,store,mapping,world,branchTrace,branchEval,represented,heaps,preserved,effect,heapTyped,branchDetermines⟩⟩ := selected branched
      have branchEval' : Evaluates (.bool truth :: entry.actual) middleStore
          (((if truth then thenCode else elseCode).rename entry.embedding).weakenAt 0) value store := by
        simpa only [branched,Entry.prefix,reached,Entry.advance,GenericExpressionMeaning.rename_prefix] using branchEval
      have conditionalEval : Evaluates entry.actual entry.store
          ((LocalLoop.conditional type conditionCode thenCode elseCode).rename entry.embedding) value store := by
        rw [LoopRenaming.conditional]
        cases truth with
        | false => exact LocalControl.choose_false _ testEval branchEval'
        | true => exact LocalControl.choose_true _ testEval branchEval'
      cases outcome with
      | returned sourceValue =>
        cases represented with
        | returned payload =>
          exact ⟨{
            size := _
            finalContext := context
            outcome := .returned sourceValue
            after := after
            value := _
            store := store
            mapping := mapping
            world := world
            determines := CellAwareLexicalBodyDeterminacy.conditionalReturned entry.runtime.graph.nodeOccurrencesUnique found form testDetermines branchDetermines
            trace := .ifReturned (lookupStatement?_sound found) form testTrace branchTrace
            evaluated := by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_returned _ conditionalEval
            represented := .returned payload
            heaps := heaps
            preserved := testFrame.trans preserved
            effect := testEffect.trans effect
            fallthroughTyped := by intro _ impossible; cases impossible }⟩
      | fault reason =>
        cases represented with
        | fault matched =>
          exact ⟨{
            size := _
            finalContext := context
            outcome := .fault reason
            after := after
            value := _
            store := store
            mapping := mapping
            world := world
            determines := CellAwareLexicalBodyDeterminacy.conditionalBranchFault entry.runtime.graph.nodeOccurrencesUnique found form testDetermines branchDetermines
            trace := .ifFault (lookupStatement?_sound found) form testTrace branchTrace
            evaluated := by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_failure _ conditionalEval
            represented := .fault matched
            heaps := heaps
            preserved := testFrame.trans preserved
            effect := testEffect.trans effect
            fallthroughTyped := by intro _ impossible; cases impossible }⟩
      | fallthrough innerEnvironment =>
        cases represented with
        | fallthrough _ _ =>
          rcases continuation with remaining | ⟨leftStops,rightStops⟩
          · let afterBranch := entry.advance heaps (heapTyped innerEnvironment rfl)
              (testFrame.trans preserved) (testEffect.trans effect)
            let next := ((afterBranch.prefix (.inLeft LocalLoop.transferType (.inLeft type .unit))
              (LocalLoop.controlType type) (.inLeft (.inLeft .unit))).prefix (.inLeft type .unit)
              (LocalControl.controlType type) (.inLeft .unit)).prefix .unit .unit .unit
            obtain ⟨tail⟩ := remaining next
            have tailEval : Evaluates
                (.unit :: .inLeft type .unit :: .inLeft LocalLoop.transferType (.inLeft type .unit) :: entry.actual)
                store (((body.rename entry.embedding).weakenAt 0).weakenAt 0 |>.weakenAt 0) tail.value tail.store := by
              simpa only [next,Entry.prefix,afterBranch,Entry.advance,GenericExpressionMeaning.rename_prefix] using tail.evaluated
            exact ⟨{
              size := _
              finalContext := tail.finalContext
              outcome := tail.outcome
              after := tail.after
              value := tail.value
              store := tail.store
              mapping := tail.mapping
              world := tail.world
              determines := CellAwareLexicalBodyDeterminacy.conditionalFallthrough entry.runtime.graph.nodeOccurrencesUnique found form testDetermines branchDetermines tail.determines
              trace := .ifFallthrough (lookupStatement?_sound found) form testTrace branchTrace tail.trace
              evaluated := by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_fallthrough _ conditionalEval tailEval
              represented := tail.represented
              heaps := tail.heaps
              preserved := testFrame.trans (preserved.trans tail.preserved)
              effect := testEffect.trans (effect.trans tail.effect)
              fallthroughTyped := tail.fallthroughTyped }⟩
          · have stopped : GenericLexicalStatements.Stopped invocation.source (if truth then thenBody else elseBody.getD []) := by
              cases truth <;> assumption
            have impossible := stopped.terminates entry.runtime.graph.nodeOccurrencesUnique false branchTrace.sound.fallthrough_scoped
            cases impossible

end Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyConditional
