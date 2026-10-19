import Solcore.SourceSemantics.CoreLowering.CellAwareScopeFlowBounds
import Solcore.SourceSemantics.CoreLowering.LoopRenaming
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedConditionalHeads

/-! An actual Boolean condition chooses exactly one mixed scoped branch.
Both phases retain their concrete descriptor effects and reached admission. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeConditionalHead
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
  (leftTyped : ProtectedStateImperativeTypedSourceSites.Statements (CallableIndexedNamedGeneration.source named) context left)
  (rightTyped : ProtectedStateImperativeTypedSourceSites.Statements (CallableIndexedNamedGeneration.source named) context (right.getD []))

include booleans found nodeType typed generated leftTyped rightTyped in
theorem reflects (budget : Nat)
    (children : CellAwareScopeExpressionBounds.ReflectsBelow bridge context model named registry invocation certificate faults budget)
    (leftCorrect : CellAwareScopeFlowBounds.ReflectsAtMost bridge context model named producer registry invocation faults
      administrative scope false left expected type leftCode budget)
    (rightCorrect : CellAwareScopeFlowBounds.ReflectsAtMost bridge context model named producer registry invocation faults
      administrative scope false (right.getD []) expected type rightCode budget)
    {size : Nat} (within : size ≤ budget)
    {mapping world actualContext environment canonical actual before store embedding}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree embedding canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (runtime : Dynamic.SourceRuntimeValid program context (CallableIndexedNamedGeneration.source named))
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
      named.signature.key [] mapping world before store environment)
    (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLocation : owner.key.frameLocation = physical.location)
    (ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native)
    {value finalStore}
    (completed : EvaluationSize size actual store ((LocalLoop.conditional type testCode leftCode rightCode).rename embedding) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Trace program registry invocation context environment before test left right sourceSize outcome after ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  rw [LoopRenaming.conditional] at completed
  obtain ⟨testSize, middleStore, input, smaller, testEval⟩ := completed.bind_computation
  obtain ⟨testSourceSize, testOutcome, middle, middleMap, middleWorld, testTrace, represented,
      middleHeaps, maps, worlds, preservation, metadata, firstEffect, middleState, expressionRelated, testPost⟩ :=
    children testSize (Nat.lt_of_lt_of_le smaller within) generated found typed
      environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation testEval
  cases represented with
  | fault matched =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalControl.choose_failure _ testEval.sound)
      exact ⟨_, _, middle, middleMap, middleWorld, .fault testTrace, .fault matched, middleHeaps,
        maps, worlds, preservation, metadata, firstEffect, middleState, expressionRelated, testPost.at_fault_type⟩
  | value payload =>
      rw [nodeType] at payload
      obtain ⟨truth, sourceEq, coreEq⟩ := booleans payload
      subst sourceEq
      subst coreEq
      have selected : CellAwareScopeFlowBounds.ReflectsAtMost bridge context model named producer registry invocation faults
              administrative scope false (if truth then left else right.getD []) expected type
              (if truth then leftCode else rightCode) budget := by
        cases truth <;> assumption
      have branch : ∃ branchSize, branchSize < size ∧ EvaluationSize branchSize (.bool truth :: actual)
          middleStore (((if truth then leftCode else rightCode).rename embedding).weakenAt 0) value finalStore := by
        cases truth with
        | false => exact completed.choose_false testEval.sound
        | true => exact completed.choose_true testEval.sound
      obtain ⟨branchSize, branchSmaller, branchEval⟩ := branch
      obtain ⟨branchSourceSize, finalContext, outcome, after, finalMap, finalWorld, branchTrace,
          represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, lastEffect, reached, branchRelated, post⟩ :=
        selected _ (Nat.le_trans (Nat.le_of_lt branchSmaller) within)
          (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (GenericExpressionMeaning.agree_prefix agrees (.bool truth))
          (.cons .bool (actualTyped.weaken worlds)) runtime covers sameLedger
          (by cases truth <;> assumption)
          middleState testPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect preservation)
          owner sameLocation ready
          (by simpa only [GenericExpressionMeaning.rename_prefix] using branchEval)
      exact ⟨_, outcome, after, finalMap, finalWorld, .branch testTrace branchTrace, represented, finalHeaps,
        maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame, metadata.trans lastMetadata, firstEffect.trans lastEffect,
        reached, protocol.trans expressionRelated branchRelated, post⟩

include booleans found nodeType typed generated leftTyped rightTyped in
theorem preserves (budget : Nat)
    (children : CellAwareScopeExpressionBounds.PreservesBelow bridge context model named registry invocation certificate faults budget)
    (leftCorrect : CellAwareScopeFlowBounds.PreservesAtMost bridge context model named producer registry invocation faults
      administrative scope false left expected type leftCode budget)
    (rightCorrect : CellAwareScopeFlowBounds.PreservesAtMost bridge context model named producer registry invocation faults
      administrative scope false (right.getD []) expected type rightCode budget)
    {size : Nat} (within : size ≤ budget)
    {mapping world actualContext environment canonical actual before store embedding}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree embedding canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (runtime : Dynamic.SourceRuntimeValid program context (CallableIndexedNamedGeneration.source named))
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
      named.signature.key [] mapping world before store environment)
    (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLocation : owner.key.frameLocation = physical.location)
    (ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native)
    {outcome after}
    (trace : Trace program registry invocation context environment before test left right size outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((LocalLoop.conditional type testCode leftCode rightCode).rename embedding) value finalStore ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  cases trace with
  | @fault testSize failure after testTrace =>
      have smaller : testSize < budget := Nat.lt_of_lt_of_le
        (Staging.Recursive.Size.child_lt_stepSize (by simp)) within
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
          maps, worlds, preservation, metadata, effect, reached, related, post⟩ :=
        children testSize smaller generated found typed environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation testTrace
      cases represented with
      | fault matched =>
          refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
            maps, worlds, preservation, metadata, effect, reached, related, post.at_fault_type⟩
          rw [LoopRenaming.conditional]
          exact LocalControl.choose_failure _ evaluated
  | @branch testSize branchSize truth middle innerContext outcome after testTrace branchTrace =>
      have smaller : testSize < budget := Nat.lt_of_lt_of_le
        (Staging.Recursive.Size.child_lt_stepSize (by simp)) within
      obtain ⟨value, middleStore, middleMap, middleWorld, testEval, represented, middleHeaps,
          maps, worlds, preservation, metadata, firstEffect, middleState, expressionRelated, testPost⟩ :=
        children testSize smaller generated found typed environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation testTrace
      cases represented with
      | value payload =>
          rw [nodeType] at payload
          obtain ⟨actualTruth, sourceEq, coreEq⟩ := booleans payload
          cases sourceEq
          subst coreEq
          have selected : CellAwareScopeFlowBounds.PreservesAtMost bridge context model named producer registry invocation faults
              administrative scope false (if truth then left else right.getD []) expected type
              (if truth then leftCode else rightCode) budget := by
            cases truth <;> assumption
          have branchWithin : branchSize ≤ budget := Nat.le_trans
            (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) within
          obtain ⟨value, finalStore, finalMap, finalWorld, branchEval, represented, finalHeaps,
              lastMaps, lastWorlds, lastFrame, lastMetadata, lastEffect, reached, branchRelated, post⟩ :=
            selected _ branchWithin (environments.extend maps worlds) middleHeaps (locals.mono metadata)
              (GenericExpressionMeaning.agree_prefix agrees (.bool truth))
              (.cons .bool (actualTyped.weaken worlds)) runtime covers sameLedger
              (by cases truth <;> assumption)
              middleState testPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect preservation)
              owner sameLocation ready branchTrace
          refine ⟨value, finalStore, finalMap, finalWorld, ?_, represented, finalHeaps,
            maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame, metadata.trans lastMetadata, firstEffect.trans lastEffect,
            reached, protocol.trans expressionRelated branchRelated, post⟩
          rw [LoopRenaming.conditional]
          rw [GenericExpressionMeaning.rename_prefix] at branchEval
          cases truth with
          | false => exact LocalControl.choose_false _ testEval branchEval
          | true => exact LocalControl.choose_true _ testEval branchEval

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeConditionalHead
