import Solcore.SourceSemantics.CoreLowering.CellAwareLoopProgress
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeFlowBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareLoopHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedWhileSequences
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedWhileSourceTyping
import Solcore.SourceSemantics.CoreLowering.CellAwareLoopEntry
import Solcore.SourceSemantics.CoreLowering.CoreHelperInversion

/-! The real while prelude and recursive execution compose with the same
mixed state. No Source cell or generalized descriptor is erased when installing
the native recursive closure or restoring its caller. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareLoopSequences
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds (PostAdmission)
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CellAwareLoopState (Progress)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    projects compiled.indexed.layouts.definitions)
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) callerProtocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)))
  {administrative actualContext : Core.Context} {context : SourceSemantics.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {location : Location} {type : Ty} {conditionCode code : Expr} {selfReason : Word}
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before after : Dynamic.Heap} {store : Store}
  {certificate : GenericExpressionMeaning.Certificate} {body : Expr}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}

variable (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {test : ExpressionId} {node : ExpressionNode} {statements : List StatementId}
  {expected : TypeSystem.Ty} {testCode loopCode : Expr}
  (booleans : ∀ {mapping world sourceValue nativeValue},
    model.Represents mapping world .bool sourceValue nativeValue .bool →
    ∃ truth, sourceValue = .bool truth ∧ nativeValue = .bool truth)

variable {mode : Bool} {id : StatementId} {statement : StatementNode} {rest : List StatementId}
  (sourceEq : invocation.source = CallableIndexedNamedGeneration.source named)

include bridge model producer transport booleans sourceEq in
theorem reflects {budget : Nat}
    (children : ∀ childSize, childSize < budget → CellAwareScopeExpressionBounds.ReflectsAt bridge context model named stages invocation certificate faults childSize)
    (found : invocation.source.lookupExpression? test = some node)
    (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context test node.type)
    (generated : certificate scope test ⟨.bool, testCode⟩)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type testCode loopCode selfReason) (LocalLoop.resultType type)
      compiled.indexed.layouts.definitions)
    (correct : CellAwareScopeFlowBounds.ReflectsAtMost bridge context model named producer stages invocation faults
      administrative scope false statements expected type loopCode budget)
    (statementFound : invocation.source.lookupStatement? id = some statement)
    (form : statement.form = .whileLoop test statements)
    (remaining : CellAwareScopeFlowBounds.ReflectsAtMost bridge context model named producer stages invocation faults
      administrative scope mode rest expected type body budget)
    {size : Nat} (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (runtime : Dynamic.SourceRuntimeValid program context (CallableIndexedNamedGeneration.source named))
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements)
    (sourceTyped : ProtectedStateImperativeTypedSourceSites.Statements (CallableIndexedNamedGeneration.source named) context (id :: rest))
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
      named.signature.key [] mapping world before store environment)
    (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLocation : owner.key.frameLocation = physical.location)
    (ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native)
    (completed : EvaluationSize size actual store ((LocalLoop.sequence type (LocalLoop.whileLoop type testCode loopCode selfReason) body).rename ξ) value finalStore) :
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      Staging.Recursive.Size.StatementsIn program stages mode sourceSize invocation context environment before
        (id :: rest) finalContext outcome after ∧
      Represents model finalMap finalWorld mode expected type faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  have unique : NodeOccurrencesUnique invocation.source := sourceEq.symm ▸ runtime.graph.nodeOccurrencesUnique
  have bodyTyped := (CallableIndexedOwnedPreparedStagedScopedWhileSourceTyping.children
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ statementFound) form).2
  have suffixTyped := CallableIndexedOwnedPreparedStagedScopedWhileSourceTyping.suffix
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ statementFound) form
  rw [LoopRenaming.sequence] at completed
  obtain ⟨headSize, middleStore, headValue, headSmaller, headEval⟩ := completed.bind_computation
  obtain ⟨headSourceSize, headOutcome, middle, middleMap, middleWorld, headTrace, represented,
      middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, headRelated, headPost⟩ :=
    CellAwareLoopHeads.reflects bridge model producer transport booleans children
      found nodeType typed generated nativeTyped correct (Nat.le_trans (Nat.le_of_lt headSmaller) within)
      environments heaps locals agrees actualTyped runtime covers sameLedger bodyTyped initial admitted authority physical owner sameLocation ready headEval
  cases represented with
  | breaking innerEnvironment => exact ((SelectedCompilationStageLoopOutcomes.while_closed headTrace).1 innerEnvironment rfl).elim
  | continuing innerEnvironment => exact ((SelectedCompilationStageLoopOutcomes.while_closed headTrace).2 innerEnvironment rfl).elim
  | returned payload =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_returned _ headEval.sound)
      exact ⟨_, context, _, middle, middleMap, middleWorld,
        .whileReturned (lookupStatement?_sound statementFound) form headTrace,
        .returned payload, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect,
        middleState, headRelated, headPost⟩
  | fault matched =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_failure _ headEval.sound)
      exact ⟨_, context, _, middle, middleMap, middleWorld,
        .whileFault (lookupStatement?_sound statementFound) form headTrace,
        .fault matched, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect,
        middleState, headRelated, headPost⟩
  | fallthrough innerEnvironment _ =>
      have same := SelectedCompilationStageLoopOutcomes.while_environment headTrace
      subst innerEnvironment
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
        .whileFallthrough (lookupStatement?_sound statementFound) form headTrace tailTrace,
        represented, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
        firstFrame.trans framePreserved, firstMetadata.trans metadata, firstEffect.trans effect, reached,
        callerProtocol.trans headRelated tailRelated, post⟩

include bridge model producer transport booleans sourceEq in
theorem preserves {budget : Nat}
    (children : ∀ childSize, childSize < budget → CellAwareScopeExpressionBounds.PreservesAt bridge context model named stages invocation certificate faults childSize)
    (found : invocation.source.lookupExpression? test = some node)
    (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context test node.type)
    (generated : certificate scope test ⟨.bool, testCode⟩)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type testCode loopCode selfReason) (LocalLoop.resultType type)
      compiled.indexed.layouts.definitions)
    (correct : CellAwareScopeFlowBounds.PreservesAtMost bridge context model named producer stages invocation faults
      administrative scope false statements expected type loopCode budget)
    (unique : NodeOccurrencesUnique invocation.source)
    (statementFound : invocation.source.lookupStatement? id = some statement)
    (form : statement.form = .whileLoop test statements)
    (remaining : CellAwareScopeFlowBounds.PreservesAtMost bridge context model named producer stages invocation faults
      administrative scope mode rest expected type body budget)
    {size : Nat} (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (runtime : Dynamic.SourceRuntimeValid program context (CallableIndexedNamedGeneration.source named))
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements)
    (sourceTyped : ProtectedStateImperativeTypedSourceSites.Statements (CallableIndexedNamedGeneration.source named) context (id :: rest))
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
      named.signature.key [] mapping world before store environment)
    (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLocation : owner.key.frameLocation = physical.location)
    (ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native)
    {finalContext : SourceSemantics.Context} {outcome : Staging.Recursive.BodyOutcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.StatementsIn program stages mode size invocation context environment before
      (id :: rest) finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((LocalLoop.sequence type (LocalLoop.whileLoop type testCode loopCode selfReason) body).rename ξ) value finalStore ∧
      Represents model finalMap finalWorld mode expected type faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  have bodyTyped := (CallableIndexedOwnedPreparedStagedScopedWhileSourceTyping.children
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ statementFound) form).2
  have suffixTyped := CallableIndexedOwnedPreparedStagedScopedWhileSourceTyping.suffix
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ statementFound) form
  have finish {headSize : Nat} {headOutcome : Staging.Recursive.BodyOutcome}
      (headTrace : Staging.Recursive.Size.While program stages headSize invocation context environment before test statements headOutcome after)
      (terminal : ∀ innerEnvironment, headOutcome ≠ .fallthrough innerEnvironment)
      (bounded : headSize ≤ budget) :
      ∃ value finalStore finalMap finalWorld,
        Evaluates actual store ((LocalLoop.sequence type (LocalLoop.whileLoop type testCode loopCode selfReason) body).rename ξ) value finalStore ∧
        Represents model finalMap finalWorld mode expected type faults headOutcome value ∧
        GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
        mapping world before store finalMap finalWorld after finalStore ∧
        ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
          callerProtocol.Relates initial reached ∧ Post bridge context expected headOutcome reached := by
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, preservation, metadata, effect, reached, related, post⟩ :=
      CellAwareLoopHeads.preserves bridge model producer transport booleans children
        found nodeType typed generated nativeTyped correct bounded environments heaps locals agrees actualTyped
        runtime covers sameLedger bodyTyped initial admitted authority physical owner sameLocation ready headTrace
    cases represented with
    | breaking innerEnvironment => exact ((SelectedCompilationStageLoopOutcomes.while_closed headTrace).1 innerEnvironment rfl).elim
    | continuing innerEnvironment => exact ((SelectedCompilationStageLoopOutcomes.while_closed headTrace).2 innerEnvironment rfl).elim
    | returned payload =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .returned payload, finalHeaps,
          maps, worlds, preservation, metadata, effect, reached, related, post⟩
        rw [LoopRenaming.sequence]
        exact LocalLoop.sequence_returned _ evaluated
    | fault matched =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
          maps, worlds, preservation, metadata, effect, reached, related, post⟩
        rw [LoopRenaming.sequence]
        exact LocalLoop.sequence_failure _ evaluated
    | fallthrough innerEnvironment _ => exact False.elim (terminal innerEnvironment rfl)
  rcases CallableIndexedOwnedPreparedStagedScopedWhileSourceInversion.loop_and_tail unique statementFound form trace with
    ⟨loopSize, sourceValue, sameSize, _contextEq, outcomeEq, loopTrace⟩ |
    ⟨loopSize, failure, sameSize, _contextEq, outcomeEq, loopTrace⟩ |
    ⟨loopSize, tailSize, middle, sameSize, loopTrace, tailTrace⟩
  · subst outcome
    exact finish loopTrace (by intros; intro impossible; cases impossible)
      (Nat.le_trans (Nat.le_of_lt (by rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
  · subst outcome
    exact finish loopTrace (by intros; intro impossible; cases impossible)
      (Nat.le_trans (Nat.le_of_lt (by rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
  · have headWithin : loopSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
    obtain ⟨value, middleStore, middleMap, middleWorld, headEval, represented, middleHeaps,
        maps, worlds, preservation, metadata, effect, middleState, headRelated, headPost⟩ :=
      CellAwareLoopHeads.preserves bridge model producer transport booleans children
        found nodeType typed generated nativeTyped correct headWithin environments heaps locals agrees actualTyped
        runtime covers sameLedger bodyTyped initial admitted authority physical owner sameLocation ready loopTrace
    cases represented with
    | fallthrough _ _ =>
        have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
          rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
        obtain ⟨value, finalStore, finalMap, finalWorld, tailEval, represented, finalHeaps,
            lastMaps, lastWorlds, lastFrame, lastMetadata, lastEffect, reached, tailRelated, post⟩ :=
          remaining _ tailWithin (environments.extend maps worlds) middleHeaps (locals.mono metadata)
            (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix
              (GenericExpressionMeaning.agree_prefix agrees (.inLeft LocalLoop.transferType (.inLeft type .unit))) (.inLeft type .unit)) .unit)
            (.cons .unit (.cons (.inLeft .unit) (.cons (.inLeft (.inLeft .unit)) (actualTyped.weaken worlds)))) runtime covers sameLedger suffixTyped
            middleState headPost (authority.transport effect) (physical.transport effect preservation)
            owner sameLocation ready tailTrace
        refine ⟨value, finalStore, finalMap, finalWorld, ?_, represented, finalHeaps,
          maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame,
          metadata.trans lastMetadata, effect.trans lastEffect, reached, callerProtocol.trans headRelated tailRelated, post⟩
        rw [LoopRenaming.sequence]
        simp only [GenericExpressionMeaning.rename_prefix] at tailEval
        exact LocalLoop.sequence_fallthrough _ headEval tailEval

end Solcore.SourceSemantics.CoreLowering.CellAwareLoopSequences
