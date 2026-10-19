import Solcore.SourceSemantics.CoreLowering.CellAwareScopeFlowBounds
import Solcore.SourceSemantics.CoreLowering.LoopRenaming
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeConditionalHead
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedConditionalSourceInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedBranchSourceTyping

/-! An actual Boolean condition chooses exactly one mixed scoped branch.
Both phases retain their concrete descriptor effects and reached admission. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeConditionalFlow
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
  (scope : SourceCoreLocalCell.Scope)
  (expected : TypeSystem.Ty) (type : Ty)


open CallableIndexedOwnedAdmittedStagedConditionalHeads (Trace)
variable {test : ExpressionId} {node : ExpressionNode}
  {left : List StatementId} {right : Option (List StatementId)}
  {testCode leftCode rightCode : Expr} {certificate : GenericExpressionMeaning.Certificate}
  (booleans : ∀ {mapping world sourceValue nativeValue},
    model.Represents mapping world .bool sourceValue nativeValue .bool →
    ∃ truth, sourceValue = .bool truth ∧ nativeValue = .bool truth)
  (found : invocation.source.lookupExpression? test = some node)
  (nodeType : node.type = .bool)
  (typed : ExpressionHasType invocation.source context test node.type)
  (generated : certificate scope test ⟨.bool, testCode⟩)

  {mode : Bool} {id : StatementId} {statement : StatementNode} {rest : List StatementId} {body : Expr}
  (sourceEq : invocation.source = CallableIndexedNamedGeneration.source named)
  (unique : NodeOccurrencesUnique invocation.source)
  (statementFound : invocation.source.lookupStatement? id = some statement)
  (form : statement.form = .ifThen test left right)


include sourceEq unique statementFound form booleans found nodeType typed generated in
theorem reflects (budget : Nat)
    (children : CellAwareScopeExpressionBounds.ReflectsBelow bridge context model named registry invocation certificate faults budget)
    (leftCorrect : CellAwareScopeFlowBounds.ReflectsAtMost bridge context model named producer registry invocation faults
      administrative scope false left expected type leftCode budget)
    (rightCorrect : CellAwareScopeFlowBounds.ReflectsAtMost bridge context model named producer registry invocation faults
      administrative scope false (right.getD []) expected type rightCode budget)
    (remaining : CellAwareScopeFlowBounds.ReflectsAtMost bridge context model named producer registry invocation faults
      administrative scope mode rest expected type body budget) :
    ∀ size, size ≤ budget → CellAwareScopeFlowBounds.ReflectsAt bridge context model named producer registry invocation faults
      administrative scope mode (id :: rest) expected type
      (LocalLoop.sequence type (LocalLoop.conditional type testCode leftCode rightCode) body) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation ready completed
  have leftTyped := ProtectedStateImperativeTypedSourceSites.branch_typed true (sourceEq ▸ unique)
    (ProtectedStateImperativeTypedSourceSites.head sourceTyped) (sourceEq ▸ statementFound) form
  have rightTyped := ProtectedStateImperativeTypedSourceSites.branch_typed false (sourceEq ▸ unique)
    (ProtectedStateImperativeTypedSourceSites.head sourceTyped) (sourceEq ▸ statementFound) form
  have suffixTyped := CallableIndexedOwnedPreparedStagedScopedBranchSourceTyping.suffix
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ statementFound) form
  rw [LoopRenaming.sequence] at completed
  obtain ⟨headSize, middleStore, headValue, headSmaller, headEval⟩ := completed.bind_computation
  obtain ⟨headSourceSize, headOutcome, middle, middleMap, middleWorld, headTrace, represented,
      middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, headRelated, headPost⟩ :=
    CellAwareScopeConditionalHead.reflects bridge context model named producer registry invocation faults
      administrative scope expected type booleans found nodeType typed generated leftTyped rightTyped
      budget children leftCorrect rightCorrect (Nat.le_trans (Nat.le_of_lt headSmaller) within)
      environments heaps locals agrees actualTyped runtime covers sameLedger
      initial admitted authority physical owner sameLocation ready headEval
  cases represented with
  | returned payload =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_returned _ headEval.sound)
      cases headTrace with
      | branch testTrace branchTrace =>
          exact ⟨_, context, _, middle, middleMap, middleWorld,
            .ifReturned (lookupStatement?_sound statementFound) form testTrace branchTrace,
            .returned payload, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect,
            middleState, headRelated, headPost⟩
  | breaking innerEnvironment =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_transfer _ headEval.sound)
      cases headTrace with
      | branch testTrace branchTrace =>
          exact ⟨_, context, _, middle, middleMap, middleWorld,
            .ifBreaking (lookupStatement?_sound statementFound) form testTrace branchTrace,
            .breaking environment, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect,
            middleState, headRelated, headPost⟩
  | continuing innerEnvironment =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_transfer _ headEval.sound)
      cases headTrace with
      | branch testTrace branchTrace =>
          exact ⟨_, context, _, middle, middleMap, middleWorld,
            .ifContinuing (lookupStatement?_sound statementFound) form testTrace branchTrace,
            .continuing environment, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect,
            middleState, headRelated, headPost⟩
  | fault matched =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_failure _ headEval.sound)
      cases headTrace with
      | fault testTrace =>
          exact ⟨_, context, _, middle, middleMap, middleWorld,
            .ifConditionFault (lookupStatement?_sound statementFound) form testTrace,
            .fault matched, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect,
            middleState, headRelated, headPost⟩
      | branch testTrace branchTrace =>
          exact ⟨_, context, _, middle, middleMap, middleWorld,
            .ifFault (lookupStatement?_sound statementFound) form testTrace branchTrace,
            .fault matched, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect,
            middleState, headRelated, headPost⟩
  | fallthrough innerEnvironment _ =>
      cases headTrace with
      | @branch testSize branchSize truth tested innerContext outcome after testTrace branchTrace =>
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
          .ifFallthrough (lookupStatement?_sound statementFound) form testTrace branchTrace tailTrace,
          represented, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
          firstFrame.trans framePreserved, firstMetadata.trans metadata, firstEffect.trans effect, reached,
          protocol.trans headRelated tailRelated, post⟩

include sourceEq unique statementFound form booleans found nodeType typed generated in
theorem preserves (budget : Nat)
    (children : CellAwareScopeExpressionBounds.PreservesBelow bridge context model named registry invocation certificate faults budget)
    (leftCorrect : CellAwareScopeFlowBounds.PreservesAtMost bridge context model named producer registry invocation faults
      administrative scope false left expected type leftCode budget)
    (rightCorrect : CellAwareScopeFlowBounds.PreservesAtMost bridge context model named producer registry invocation faults
      administrative scope false (right.getD []) expected type rightCode budget)
    (remaining : CellAwareScopeFlowBounds.PreservesAtMost bridge context model named producer registry invocation faults
      administrative scope mode rest expected type body budget) :
    ∀ size, size ≤ budget → CellAwareScopeFlowBounds.PreservesAt bridge context model named producer registry invocation faults
      administrative scope mode (id :: rest) expected type
      (LocalLoop.sequence type (LocalLoop.conditional type testCode leftCode rightCode) body) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation ready finalContext outcome after trace
  have leftTyped := ProtectedStateImperativeTypedSourceSites.branch_typed true (sourceEq ▸ unique)
    (ProtectedStateImperativeTypedSourceSites.head sourceTyped) (sourceEq ▸ statementFound) form
  have rightTyped := ProtectedStateImperativeTypedSourceSites.branch_typed false (sourceEq ▸ unique)
    (ProtectedStateImperativeTypedSourceSites.head sourceTyped) (sourceEq ▸ statementFound) form
  have suffixTyped := CallableIndexedOwnedPreparedStagedScopedBranchSourceTyping.suffix
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ statementFound) form
  have finish {headSize : Nat} {headOutcome : Staging.Recursive.BodyOutcome}
      (headTrace : Trace program registry invocation context environment before test left right headSize headOutcome after)
      (terminal : ∀ innerEnvironment, headOutcome ≠ .fallthrough innerEnvironment)
      (bounded : headSize ≤ budget) :
      ∃ value finalStore finalMap finalWorld,
        Evaluates actual store ((LocalLoop.sequence type (LocalLoop.conditional type testCode leftCode rightCode) body).rename embedding) value finalStore ∧
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
      CellAwareScopeConditionalHead.preserves bridge context model named producer registry invocation faults
        administrative scope expected type booleans found nodeType typed generated leftTyped rightTyped
        budget children leftCorrect rightCorrect bounded environments heaps locals agrees actualTyped runtime covers sameLedger
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
  rcases CallableIndexedOwnedPreparedStagedScopedConditionalSourceInversion.children unique statementFound form trace with
    ⟨testSize, failure, sameSize, contextEq, outcomeEq, testTrace⟩ |
    ⟨testSize, branchSize, truth, sourceValue, middle, innerContext, sameSize, contextEq, outcomeEq, testTrace, branchTrace⟩ |
    ⟨testSize, branchSize, truth, failure, middle, innerContext, sameSize, contextEq, outcomeEq, testTrace, branchTrace⟩ |
    ⟨testSize, branchSize, truth, innerEnvironment, middle, innerContext, sameSize, contextEq, outcomeEq, testTrace, branchTrace⟩ |
    ⟨testSize, branchSize, truth, innerEnvironment, middle, innerContext, sameSize, contextEq, outcomeEq, testTrace, branchTrace⟩ |
    ⟨testSize, branchSize, tailSize, truth, middle, branchHeap, innerContext, innerEnvironment, sameSize, testTrace, branchTrace, tailTrace⟩
  · subst outcome
    exact finish (.fault testTrace) (by intros; intro impossible; cases impossible) (sameSize ▸ within)
  · subst outcome
    exact finish (.branch testTrace branchTrace) (by intros; intro impossible; cases impossible) (sameSize ▸ within)
  · subst outcome
    exact finish (.branch testTrace branchTrace) (by intros; intro impossible; cases impossible) (sameSize ▸ within)
  · subst outcome
    exact finish (.branch testTrace branchTrace) (by intros; intro impossible; cases impossible) (sameSize ▸ within)
  · subst outcome
    exact finish (.branch testTrace branchTrace) (by intros; intro impossible; cases impossible) (sameSize ▸ within)
  · have headWithin : Staging.Recursive.Size.stepSize [testSize, branchSize] ≤ budget := by
      rw [sameSize] at within
      simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil] at within ⊢
      omega
    obtain ⟨value, middleStore, middleMap, middleWorld, headEval, represented, middleHeaps,
        maps, worlds, preservation, metadata, firstEffect, middleState, headRelated, headPost⟩ :=
      CellAwareScopeConditionalHead.preserves bridge context model named producer registry invocation faults
        administrative scope expected type booleans found nodeType typed generated leftTyped rightTyped
        budget children leftCorrect rightCorrect headWithin environments heaps locals agrees actualTyped runtime covers sameLedger
        initial admitted authority physical owner sameLocation ready (.branch testTrace branchTrace)
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

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeConditionalFlow
