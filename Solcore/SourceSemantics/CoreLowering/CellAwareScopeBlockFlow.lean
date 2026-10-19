import Solcore.SourceSemantics.CoreLowering.CellAwareScopeFlowBounds
import Solcore.SourceSemantics.CoreLowering.LoopRenaming
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedBlockSourceInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedBlockSourceTyping

/-! A scoped block restores its lexical observations while keeping the
actual mixed heap, every retained descriptor, and its original control outcome. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeBlockFlow
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (context : SourceSemantics.Context)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)
  (named : SourceCoreGeneralFunctions.Function)
  (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)))
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep) (administrative : Core.Context)
  (scope : SourceCoreLocalCell.Scope) (mode : Bool)
  (expected : TypeSystem.Ty) (type : Ty)


variable {id : StatementId} {statement : StatementNode} {statements rest : List StatementId}
  {innerCode body : Expr}
  (sourceEq : invocation.source = CallableIndexedNamedGeneration.source named)
  (unique : NodeOccurrencesUnique invocation.source)
  (statementFound : invocation.source.lookupStatement? id = some statement)
  (form : statement.form = .block statements)

include sourceEq unique statementFound form in
theorem reflects (budget : Nat)
    (innerCorrect : CellAwareScopeFlowBounds.ReflectsAtMost bridge context model named producer registry invocation faults
      administrative scope false statements expected type innerCode budget)
    (remaining : CellAwareScopeFlowBounds.ReflectsAtMost bridge context model named producer registry invocation faults
      administrative scope mode rest expected type body budget) :
    ∀ size, size ≤ budget → CellAwareScopeFlowBounds.ReflectsAt bridge context model named producer registry invocation faults
      administrative scope mode (id :: rest) expected type (LocalLoop.sequence type innerCode body) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation ready completed
  have innerTyped := CallableIndexedOwnedPreparedStagedScopedBlockSourceTyping.inner
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ statementFound) form
  have suffixTyped := CallableIndexedOwnedPreparedStagedScopedBlockSourceTyping.suffix
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ statementFound) form
  rw [LoopRenaming.sequence] at completed
  obtain ⟨headSize, middleStore, headValue, headSmaller, headEval⟩ := completed.bind_computation
  obtain ⟨headSourceSize, innerContext, headOutcome, middle, middleMap, middleWorld, headTrace, represented,
      middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, headRelated, headPost⟩ :=
    innerCorrect _ (Nat.le_trans (Nat.le_of_lt headSmaller) within)
      environments heaps locals agrees actualTyped runtime covers sameLedger innerTyped
      initial admitted authority physical owner sameLocation ready headEval
  cases represented with
  | returned payload =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_returned _ headEval.sound)
      exact ⟨_, context, _, middle, middleMap, middleWorld,
        .blockReturned (lookupStatement?_sound statementFound) form headTrace,
        .returned payload, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect,
        middleState, headRelated, headPost⟩
  | breaking innerEnvironment =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_transfer _ headEval.sound)
      exact ⟨_, context, _, middle, middleMap, middleWorld,
        .blockBreaking (lookupStatement?_sound statementFound) form headTrace,
        .breaking environment, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect,
        middleState, headRelated, headPost⟩
  | continuing innerEnvironment =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_transfer _ headEval.sound)
      exact ⟨_, context, _, middle, middleMap, middleWorld,
        .blockContinuing (lookupStatement?_sound statementFound) form headTrace,
        .continuing environment, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect,
        middleState, headRelated, headPost⟩
  | fault matched =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_failure _ headEval.sound)
      exact ⟨_, context, _, middle, middleMap, middleWorld,
        .blockFault (lookupStatement?_sound statementFound) form headTrace,
        .fault matched, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect,
        middleState, headRelated, headPost⟩
  | fallthrough innerEnvironment _ =>
      obtain ⟨tailSize, smaller, tailEval⟩ := completed.sequence_fallthrough headEval.sound
      obtain ⟨tailSourceSize, finalContext, outcome, after, finalMap, finalWorld, tailTrace, represented,
          finalHeaps, maps, worlds, framePreserved, metadata, effect, reached, tailRelated, post⟩ :=
        remaining _ (Nat.le_trans (Nat.le_of_lt smaller) within)
          (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
          (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix
            (GenericExpressionMeaning.agree_prefix agrees (.inLeft LocalLoop.transferType (.inLeft type .unit))) (.inLeft type .unit)) .unit)
          (.cons .unit (.cons (.inLeft .unit) (.cons (.inLeft (.inLeft .unit)) (actualTyped.weaken firstWorlds)))) runtime covers sameLedger suffixTyped
          middleState headPost (authority.transport firstEffect) (physical.transport firstEffect firstFrame)
          owner sameLocation ready
          (by simpa only [GenericExpressionMeaning.rename_prefix] using tailEval)
      exact ⟨_, finalContext, outcome, after, finalMap, finalWorld,
        .blockFallthrough (lookupStatement?_sound statementFound) form headTrace tailTrace,
        represented, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
        firstFrame.trans framePreserved, firstMetadata.trans metadata, firstEffect.trans effect, reached,
        protocol.trans headRelated tailRelated, post⟩

include sourceEq unique statementFound form in
theorem preserves (budget : Nat)
    (innerCorrect : CellAwareScopeFlowBounds.PreservesAtMost bridge context model named producer registry invocation faults
      administrative scope false statements expected type innerCode budget)
    (remaining : CellAwareScopeFlowBounds.PreservesAtMost bridge context model named producer registry invocation faults
      administrative scope mode rest expected type body budget) :
    ∀ size, size ≤ budget → CellAwareScopeFlowBounds.PreservesAt bridge context model named producer registry invocation faults
      administrative scope mode (id :: rest) expected type (LocalLoop.sequence type innerCode body) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation ready finalContext outcome after trace
  have innerTyped := CallableIndexedOwnedPreparedStagedScopedBlockSourceTyping.inner
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ statementFound) form
  have suffixTyped := CallableIndexedOwnedPreparedStagedScopedBlockSourceTyping.suffix
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ statementFound) form
  have finish {headSize : Nat} {innerContext : SourceSemantics.Context}
      {headOutcome : Staging.Recursive.BodyOutcome}
      (headTrace : Staging.Recursive.Size.StatementsIn program registry false headSize invocation context
        environment before statements innerContext headOutcome after)
      (terminal : ∀ innerEnvironment, headOutcome ≠ .fallthrough innerEnvironment)
      (bounded : headSize ≤ budget) :
      ∃ value finalStore finalMap finalWorld,
        Evaluates actual store ((LocalLoop.sequence type innerCode body).rename embedding) value finalStore ∧
        Represents model finalMap finalWorld mode expected type faults (headOutcome.restore environment) value ∧
        GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
          protocol.Relates initial reached ∧ Post bridge context expected (headOutcome.restore environment) reached := by
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, preservation, metadata, effect, reached, related, post⟩ :=
      innerCorrect _ bounded environments heaps locals agrees actualTyped runtime covers sameLedger innerTyped
        initial admitted authority physical owner sameLocation ready headTrace
    cases represented with
    | returned payload =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .returned payload, finalHeaps,
          maps, worlds, preservation, metadata, effect, reached, related, post⟩
        rw [LoopRenaming.sequence]
        exact LocalLoop.sequence_returned _ evaluated
    | breaking innerEnvironment =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .breaking environment, finalHeaps,
          maps, worlds, preservation, metadata, effect, reached, related, post⟩
        rw [LoopRenaming.sequence]
        exact LocalLoop.sequence_transfer _ evaluated
    | continuing innerEnvironment =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .continuing environment, finalHeaps,
          maps, worlds, preservation, metadata, effect, reached, related, post⟩
        rw [LoopRenaming.sequence]
        exact LocalLoop.sequence_transfer _ evaluated
    | fault matched =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
          maps, worlds, preservation, metadata, effect, reached, related, post⟩
        rw [LoopRenaming.sequence]
        exact LocalLoop.sequence_failure _ evaluated
    | fallthrough innerEnvironment _ => exact False.elim (terminal innerEnvironment rfl)
  rcases CallableIndexedOwnedPreparedStagedScopedBlockSourceInversion.block_and_tail unique statementFound form trace with
    ⟨innerSize, innerContext, sourceValue, sameSize, contextEq, outcomeEq, innerTrace⟩ |
    ⟨innerSize, innerContext, failure, sameSize, contextEq, outcomeEq, innerTrace⟩ |
    ⟨innerSize, innerContext, innerEnvironment, sameSize, contextEq, outcomeEq, innerTrace⟩ |
    ⟨innerSize, innerContext, innerEnvironment, sameSize, contextEq, outcomeEq, innerTrace⟩ |
    ⟨innerSize, tailSize, innerContext, innerEnvironment, middle, sameSize, innerTrace, tailTrace⟩
  · subst outcome
    exact finish innerTrace (by intros; intro impossible; cases impossible)
      (Nat.le_trans (Nat.le_of_lt (sameSize ▸ Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
  · subst outcome
    exact finish innerTrace (by intros; intro impossible; cases impossible)
      (Nat.le_trans (Nat.le_of_lt (sameSize ▸ Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
  · subst outcome
    exact finish innerTrace (by intros; intro impossible; cases impossible)
      (Nat.le_trans (Nat.le_of_lt (sameSize ▸ Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
  · subst outcome
    exact finish innerTrace (by intros; intro impossible; cases impossible)
      (Nat.le_trans (Nat.le_of_lt (sameSize ▸ Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
  · have headWithin : innerSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
    obtain ⟨value, middleStore, middleMap, middleWorld, headEval, represented, middleHeaps,
        maps, worlds, preservation, metadata, firstEffect, middleState, headRelated, headPost⟩ :=
      innerCorrect _ headWithin environments heaps locals agrees actualTyped runtime covers sameLedger innerTyped
        initial admitted authority physical owner sameLocation ready innerTrace
    cases represented with
    | fallthrough innerEnvironment _ =>
        have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
          rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
        obtain ⟨value, finalStore, finalMap, finalWorld, tailEval, represented, finalHeaps,
            lastMaps, lastWorlds, lastFrame, lastMetadata, lastEffect, reached, tailRelated, post⟩ :=
          remaining _ tailWithin (environments.extend maps worlds) middleHeaps (locals.mono metadata)
            (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix
              (GenericExpressionMeaning.agree_prefix agrees (.inLeft LocalLoop.transferType (.inLeft type .unit))) (.inLeft type .unit)) .unit)
            (.cons .unit (.cons (.inLeft .unit) (.cons (.inLeft (.inLeft .unit)) (actualTyped.weaken worlds)))) runtime covers sameLedger suffixTyped
            middleState headPost (authority.transport firstEffect) (physical.transport firstEffect preservation)
            owner sameLocation ready tailTrace
        refine ⟨value, finalStore, finalMap, finalWorld, ?_, represented, finalHeaps,
          maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame,
          metadata.trans lastMetadata, firstEffect.trans lastEffect, reached, protocol.trans headRelated tailRelated, post⟩
        rw [LoopRenaming.sequence]
        simp only [GenericExpressionMeaning.rename_prefix] at tailEval
        exact LocalLoop.sequence_fallthrough _ headEval tailEval

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeBlockFlow
