import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionTypedLiteralEvidence
import Solcore.SourceSemantics.CoreLowering.CellAwareSourceReadProductLifting
import Solcore.SourceSemantics.CoreLowering.CellAwareReadMeaningEffects
import Solcore.SourceSemantics.CoreLowering.CellAwareSelectedReadBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareSelectedLiteralBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareSelectedPairBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareStagedGroupBounds
import Solcore.SourceSemantics.Dynamic.WholeLanguagePreservation

/-! The actual finite ordinary expression tree completes in a mixed heap.
Every child keeps its original compiler receipt and actual reached state;
source uniqueness and descriptor effects are derived along the same tree. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CellAwareReadProductCompletion
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open Staging.Recursive.Lifting (embed)
open CallableIndexedOwnedPreparedStagedReadProductTreeBounds (Certificate)
open GenericExpressionMeaning (agree_prefix rename_prefix)

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  (functions : FunctionModel checked.catalog ambient)
  {rawRegistry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial checked).registry rawRegistry)
  {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
  (ordinaryCells : GenericHeap.OrdinaryCells
    (CompatibleAmbientHeap.payloadModel checked rawRegistry functions)
    (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel checked rawRegistry functions) instances))
  {program : Program} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {context : SourceSemantics.Context} {readFuel : Nat} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {semanticFaults : FunctionCalls.FaultRep} {faults : RecursiveStageMeaning.FaultRep}
  (uninitialized : ∀ scope id lowered,
    CompatibleExpressionReads.LoweredRead readFuel (.initial checked)
      invocation.source context reasonAt scope id lowered →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id))
  (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)
  (unique : NodeOccurrencesUnique invocation.source)
  (wellFormed : ProgramWellFormed program)
  (runtime : Dynamic.SourceRuntimeValid program context invocation.source)
  (covers : invocation.evidence.Covers context)

local notation "model" => CompatibleAmbientHeap.payloadModel checked rawRegistry functions
local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel model instances

include extension ordinaryCells uninitialized semantic unique wellFormed runtime covers in
theorem completes {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (certificate : Certificate readFuel (.initial checked) invocation.source context solved reasonAt scope id lowered)
    {node : ExpressionNode} (found : invocation.source.lookupExpression? id = some node)
    (typed : ExpressionHasType invocation.source context id node.type)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store : Store} {embedding : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world
      administrative scope environment canonical ambient.definitions)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree embedding canonical actual) :
    ∃ size outcome after value finalStore,
      Staging.Recursive.Size.Expression program registry size invocation context environment before id (embed outcome) after ∧
      Evaluates actual store (lowered.expression.rename embedding) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model mapping world node.type lowered.type faults (embed outcome) value ∧
      GenericHeap.CellHeapRepresents cells mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect instances mapping world before store mapping world after finalStore ∧
      ∀ {otherSize otherOutcome otherHeap},
        Staging.Recursive.Size.Expression program registry otherSize invocation context environment before id otherOutcome otherHeap →
        otherOutcome = embed outcome ∧ otherHeap = after := by
  obtain ⟨tree, sites⟩ := certificate
  induction sites generalizing node before store actual embedding with
  | literal _ receipt =>
    obtain ⟨other, otherFound, literal, _selected⟩ := receipt
    cases Option.some.inj (otherFound.symm.trans found)
    have valid := CompatibleExpressionTypedLiteralEvidence.of_typed unique found typed runtime.requirements.idsUnique covers
    obtain ⟨sourceValue, coreValue, raw, represented, evaluated⟩ :=
      literal.evaluates_with_evidence functions program context invocation.evidence valid invocation.source
        environment before mapping world actual store embedding
    have staged : Staging.Recursive.Size.Expression program registry (Staging.Recursive.Size.stepSize [])
        invocation context environment before _ (.value sourceValue) before :=
      .atomicValue (lookupExpression?_sound found) (CellAwareSelectedLiteralBounds.literal_atomic_staged literal)
        (CellAwareSelectedLiteralBounds.literal_coercions literal)
        (by simpa only [CellAwareSelectedLiteralBounds.literal_coercions literal] using raw)
    refine ⟨_, .value sourceValue, before, _, store, staged, evaluated, .value represented,
      heaps, .refl _ _, .refl _, .refl _ _ _ _, ?_⟩
    intro otherSize outcome after trace
    cases outcome with
    | value value =>
      have otherRaw := CellAwareSelectedLiteralBounds.evaluation_raw unique (lookupExpression?_sound found)
        (CellAwareSelectedLiteralBounds.literal_atomic literal) (CellAwareSelectedLiteralBounds.literal_coercions literal)
        trace.sound.value_plain
      obtain ⟨rfl, rfl⟩ := CellAwareSelectedLiteralBounds.literal_form_unique literal otherRaw raw
      exact ⟨rfl, rfl⟩
    | fault failure =>
      cases failure with
      | semantic reason => exact False.elim (CellAwareSelectedLiteralBounds.literal_excludes_fault_with_evidence literal valid
          (CellAwareSelectedLiteralBounds.fault_raw unique (lookupExpression?_sound found)
            (CellAwareSelectedLiteralBounds.literal_atomic literal) (CellAwareSelectedLiteralBounds.literal_coercions literal)
            trace.sound.semanticFault_plain))
      | stage failedScope call reason => exact False.elim (CellAwareSelectedLiteralBounds.no_stage unique found literal trace)
  | @read readId readCode receipt =>
    have readReceipt := receipt
    obtain ⟨read, sameType, binding⟩ := receipt
    cases Option.some.inj (read.metadata.found.symm.trans found)
    obtain ⟨value, finalStore, evaluated⟩ := read.cell_native_terminates functions extension ordinaryCells
      binding environments heaps heapTyped locals agrees
    obtain ⟨outcome, after, sourceTrace, represented, finalHeaps, frame, metadata, effect⟩ :=
      read.scoped_completed functions extension ordinaryCells program context invocation.evidence binding
        environments heaps heapTyped locals agrees (uninitialized _ _ _ readReceipt) evaluated
    obtain ⟨location, cell, lookup, sourceRead, _, _⟩ := locals.lookup binding.declared
    have ordinary := locals.descriptor_empty_of_monomorphic heapTyped binding.declared lookup sourceRead read.monomorphic
    have staged := CellAwareSelectedReadBounds.staged_of_read (registry := registry)
      read unique lookup sourceRead ordinary sourceTrace
    have staged' : Staging.Recursive.Size.Expression program registry (Staging.Recursive.Size.stepSize [])
        invocation context environment before readId (embed outcome) after := by
      cases outcome <;> exact staged
    have result : RecursiveStageMeaning.ResultRepresentsFor model mapping world read.node.type readCode.type faults (embed outcome) value := by
      simp only [SourceCoreCompatibleValues.Context.initial, sameType] at represented
      cases represented with
      | value payload => exact .value payload
      | fault matched => exact .fault (semantic _ _ matched)
    refine ⟨_, outcome, after, value, finalStore, staged', evaluated, result, finalHeaps, frame, metadata, effect, ?_⟩
    intro otherSize otherOutcome otherHeap trace
    have plain : ∃ plainOutcome : Dynamic.ExpressionOutcome,
        Dynamic.ExpressionEvaluatesOutcome program context invocation.evidence invocation.source environment before readId plainOutcome otherHeap ∧
        otherOutcome = embed plainOutcome := by
      cases otherOutcome with
      | value value => exact ⟨.value value, .value trace.sound.value_plain, rfl⟩
      | fault failure => cases failure with
        | semantic reason => exact ⟨.fault reason, .fault trace.sound.semanticFault_plain, rfl⟩
        | stage failedScope call reason => exact False.elim (CellAwareSelectedReadBounds.no_stage unique read.metadata.found read.form read.metadata.coercions trace)
    obtain ⟨plainOutcome, plainTrace, outcomeEq⟩ := plain
    obtain ⟨rfl, rfl⟩ := CompatibleExpressionReads.source_outcome_unique unique
      (lookupExpression?_sound read.metadata.found) read.form read.metadata.coercions lookup sourceRead ordinary sourceTrace plainTrace
    exact ⟨outcomeEq, rfl⟩
  | @group id parent inner innerNode lowered metadata form innerFound sourceType child childSites ih =>
    cases Option.some.inj (metadata.found.symm.trans found)
    have childTyped := CellAwareStagedGroupBounds.child_typed metadata form innerFound unique typed
    obtain ⟨size, outcome, after, value, finalStore, trace, evaluated, represented, finalHeaps, frame, heapMetadata, effect, determines⟩ :=
      ih innerFound childTyped heaps heapTyped locals agrees
    refine ⟨_, outcome, after, value, finalStore,
      .group ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩ trace,
      evaluated, sourceType ▸ represented, finalHeaps, frame, heapMetadata, effect, ?_⟩
    intro otherSize otherOutcome otherHeap otherTrace
    obtain ⟨_, _, child⟩ := CellAwareStagedGroupBounds.source_group_inv unique metadata.found form otherTrace
    exact determines child
  | @pair id parent left right leftNode rightNode first second metadata form leftFound rightFound sourceType
      leftTree rightTree leftSites rightSites leftIH rightIH =>
    cases Option.some.inj (metadata.found.symm.trans found)
    obtain ⟨leftTyped, rightTyped⟩ := CellAwareSelectedPairBounds.child_typing metadata form leftFound rightFound unique typed
    have occurrence : Staging.Recursive.Occurrence invocation id (.tuple [left,right]) :=
      ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
    obtain ⟨firstSize, firstOutcome, middle, firstValue, middleStore, firstTrace, firstEval, firstRep,
      middleHeaps, firstFrame, firstMetadata, firstEffect, firstDetermines⟩ :=
      leftIH leftFound leftTyped heaps heapTyped locals agrees
    cases firstOutcome with
    | fault reason =>
      cases firstRep with
      | fault matched =>
        refine ⟨_, .fault reason, middle, _, middleStore, .pairLeftFault occurrence firstTrace, ?_,
          .fault matched, middleHeaps, firstFrame, firstMetadata, firstEffect, ?_⟩
        · rw [DataExpressionSequence.pair_rename]
          exact LocalSequence.pair_left_failure _ _ firstEval
        · intro otherSize otherOutcome otherHeap otherTrace
          have children := CellAwareSelectedPairBounds.source_children unique metadata.found form otherTrace
          cases children with
          | leftFault _ child => exact firstDetermines child
          | rightFault _ _ first _ | values _ _ first _ =>
            have impossible := (firstDetermines first).1
            cases impossible
    | value firstSource =>
      cases firstRep with
      | @value _ firstNative firstPayload =>
        have preserved := wellFormed.wholeLanguagePreservation.expression _ _ _ _ _ _ _ _ _
          runtime covers locals heapTyped leftTyped firstTrace.sound.value_plain
        obtain ⟨secondSize, secondOutcome, after, secondValue, finalStore, secondTrace, secondEval, secondRep,
          finalHeaps, secondFrame, secondMetadata, secondEffect, secondDetermines⟩ :=
          rightIH rightFound rightTyped middleHeaps preserved.heap_typed (locals.mono firstMetadata)
            (agree_prefix agrees firstNative)
        cases secondOutcome with
        | fault reason =>
          cases secondRep with
          | fault matched =>
            refine ⟨_, .fault reason, after, _, finalStore, .pairRightFault occurrence firstTrace secondTrace, ?_,
              .fault matched, finalHeaps, firstFrame.trans secondFrame, firstMetadata.trans secondMetadata,
              firstEffect.trans secondEffect, ?_⟩
            · rw [DataExpressionSequence.pair_rename]
              rw [rename_prefix] at secondEval
              exact LocalSequence.pair_right_failure _ _ firstEval secondEval
            · intro otherSize otherOutcome otherHeap otherTrace
              have children := CellAwareSelectedPairBounds.source_children unique metadata.found form otherTrace
              cases children with
              | leftFault _ child => have impossible := (firstDetermines child).1; cases impossible
              | rightFault _ _ first second =>
                obtain ⟨same, heapEq⟩ := firstDetermines first
                cases same; subst heapEq
                exact secondDetermines second
              | values _ _ first second =>
                obtain ⟨same, heapEq⟩ := firstDetermines first
                cases same; subst heapEq
                have impossible := (secondDetermines second).1; cases impossible
        | value secondSource =>
          cases secondRep with
          | @value _ secondNative secondPayload =>
            refine ⟨_, .value (.product firstSource secondSource), after, _, finalStore,
              .pair occurrence firstTrace secondTrace, ?_, .value (by rw [sourceType]; exact .product firstPayload secondPayload),
              finalHeaps, firstFrame.trans secondFrame, firstMetadata.trans secondMetadata,
              firstEffect.trans secondEffect, ?_⟩
            · rw [DataExpressionSequence.pair_rename]
              rw [rename_prefix] at secondEval
              exact LocalSequence.pair_success _ _ firstEval secondEval
            · intro otherSize otherOutcome otherHeap otherTrace
              have children := CellAwareSelectedPairBounds.source_children unique metadata.found form otherTrace
              cases children with
              | leftFault _ child => have impossible := (firstDetermines child).1; cases impossible
              | rightFault _ _ first second =>
                obtain ⟨same, heapEq⟩ := firstDetermines first
                cases same; subst heapEq
                have impossible := (secondDetermines second).1; cases impossible
              | values _ _ first second =>
                obtain ⟨same, heapEq⟩ := firstDetermines first
                cases same; subst heapEq
                obtain ⟨same, heapEq⟩ := secondDetermines second
                cases same; subst heapEq
                exact ⟨rfl,rfl⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareReadProductCompletion
