import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.ScopeStatements
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.CatalogOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.ScopeAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.SourceFlowLifting
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.StageAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateForPost
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.StageWhileMatch
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.StageForLoops
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.Loops
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.ScopedSourceInversion
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.ScopeExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.NamedEntries
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.ForLoops
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.SelectedTerminalDispatch
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedFlows

/-!
# Lifting Source traces over cell-aware loops

Lifting of `for` and `while` loops, by the form of each initializer and item, and of projected assignments and their resolution.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareSourceProjectedResolutionLifting
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceProjectedResolutionLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleEquality CoreProof
open SourceCoreCompatibleDataPlaces
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareScopeSourceLiftBounds (LiftsAt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {receiving : SourceCoreRawMetadata.Registry}
  {named : SourceCoreGeneralFunctions.Function}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations compiled.compatible.checked.catalog functions identities)
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  {scope : SourceCoreLocalCell.Scope} {site : SourceCoreElaboration.ErrorSite}
  {place : PlaceResolution} {prepared : Prepared} {codes : List SourceCoreBasic.LoweredExpr}
  {rhsType : Core.Ty} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty} {administrative : Core.Context}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

include extension transport faithful observations in
/-- Ordinary key effects are lifted before the getter and before any RHS. -/
theorem lifts (budget : Nat)
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := compiled.indexed.layouts.definitions) (.initial compiled.compatible.checked) invocation.source
      certificate scope site place prepared codes sourceTypes leaf administrative rhsType)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (unique : NodeOccurrencesUnique invocation.source)
    {originalTypes : List TypeSystem.Ty}
    (keyTyped : ExpressionsHaveTypes invocation.source context (DataPlaceKeyOrder.sourceKeys place.projections) originalTypes)
    (children : ∀ size, size < budget → LiftsAt bridge context model named stages invocation certificate size)
    (preservation : ∀ size, CellAwareScopeExpressionBounds.PreservesAt
      bridge context model named stages invocation certificate faults size)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
    {canonical actual : Environment} {before after : Dynamic.Heap} {store : Store} {actualContext : Core.Context} {ξ : Renaming}
    {index : Nat} {target : Dynamic.ResolvedPlace} {size : Nat}
    (environments : DataHeap.EnvRepresents (definitions := compiled.indexed.layouts.definitions) (storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
      named.signature.key [] mapping world before store environment)
    (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (ownerFrame : owner.key.frameLocation = physical.location)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (writable : WritableLocal context place.root prepared.route.rootSourceType)
    (trace : SourceExecutionSize.SourcePlaceResolves program size context invocation.evidence invocation.source
      environment before place target after) (within : size ≤ budget) :
    (∃ origin call reason reached,
      Staging.Recursive.ProjectedTarget.RootReady environment before place ∧
      Staging.Recursive.Expressions program stages invocation context environment before
        (Staging.Recursive.ProjectedTarget.keys place.projections) (.fault (.stage origin call reason)) reached) ∨
    (∃ sources,
      Staging.Recursive.Expressions program stages invocation context environment before
        (Staging.Recursive.ProjectedTarget.keys place.projections) (.values sources) after ∧
      Staging.Recursive.ProjectedTarget.Snapshot environment before after place sources target ∧
      Dynamic.ValuesHaveTypes context after sources sourceTypes ∧
      ∃ resolution : CompatibleCellPlaceResolution.Execution compiled.compatible.checked receiving functions
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed))
        (GeneralizedLocalInstanceValues.model compiled.indexed) prepared
        (CompatibleRenamedPlace.renamedCodes codes ξ) sourceTypes place leaf target actual store mapping world before after,
        ∃ reached : callerProtocol.State ⟨scope, resolution.mapping, resolution.world, after, resolution.store, canonical⟩,
          callerProtocol.Relates initial reached ∧ Admission bridge context reached) := by
  obtain ⟨keySize, sources, keyBound, ordinaryKeys, snapshot⟩ := SelectedCompilationStageProjectedTargetInversion.resolved trace
  have rowTyped := CellAwareScopeProjectedAssignmentHeads.tree_typed layout.children unique keyTyped
  obtain ⟨outcome, reached, stagedKeys, adapted⟩ := CellAwareScopeSourceSequenceLifting.values bridge budget
    layout.children unique rowTyped children preservation environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame
    (by simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using ordinaryKeys)
    (Nat.le_trans (Nat.le_of_lt keyBound) within)
  have keyTrace : Staging.Recursive.Expressions program stages invocation context environment before
      (Staging.Recursive.ProjectedTarget.keys place.projections) outcome reached := by
    simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using stagedKeys
  cases adapted with
  | rejected origin call reason reached =>
      refine .inl ⟨origin, call, reason, reached, ?_, keyTrace⟩
      cases snapshot with
      | intro lookup read _ _ _ _ => exact .intro lookup read
  | completed =>
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expressions.of_trace keyTrace
      obtain ⟨resolution, _sameSources, keyValues, _keyHeap, _lookup, reached, related, admitted⟩ :=
        CellAwareScopeProjectedAssignmentHeads.preserves_resolution bridge stagedSize layout ordinary
          extension transport faithful observations environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame unique
          keyTyped (fun n _ => preservation n) slot writable measured (Nat.le_refl _) snapshot
      exact .inr ⟨sources, keyTrace, snapshot, keyValues, resolution, reached, related, admitted⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceProjectedResolutionLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowProjectedAssignmentLifting
/-! Independent projected assignment lifts the actual ordered keys, getter,
RHS and final write at their reached mixed states. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowProjectedAssignmentLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleEquality CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations compiled.compatible.checked.catalog functions identities)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  {receiving : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
      (GeneralizedLocalInstanceValues.model compiled.indexed)))
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep}

include transport extension faithful observations in
theorem lifts {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {mode : Bool} {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    (sourceEq : invocation.source = source named)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .assignValue assignment operator rhs)
    (head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) invocation.source context
      certificate scope administrative compiled.indexed.layouts.definitions assignment operator rhs)
    (projected : assignment.target.projections ≠ [])
    (children : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeSourceLiftBounds.LiftsAt bridge context
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
        named stages invocation certificate size)
    (preservation : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeExpressionBounds.PreservesAt bridge context
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
        named stages invocation certificate faults size)
    (remaining : CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := stages) (invocation := invocation) bridge producer context scope mode rest) :
    CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := stages) (invocation := invocation) bridge producer context scope mode (id :: rest) := by
  intro size mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner sameLocation ready
    finalContext outcome after trace
  have unique : NodeOccurrencesUnique invocation.source := sourceEq.symm ▸ runtime.graph.nodeOccurrencesUnique
  have assignmentTyped := ProtectedStateImperativeTypedSourceSites.assignment unique
    (sourceEq.symm ▸ ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
  have suffix := ProtectedStateImperativeStatementSuffixTyping.assignment
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ found) form
  let budget := size + 1
  have within : size ≤ budget := by omega
  have childLift : ∀ childSize, childSize < budget → CellAwareScopeSourceLiftBounds.LiftsAt bridge context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
      named stages invocation certificate childSize := fun childSize _ => children runtime covers sameLedger childSize
  have childMeaning : ∀ childSize, CellAwareScopeExpressionBounds.PreservesAt bridge context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
      named stages invocation certificate faults childSize := preservation runtime covers sameLedger
  have typed := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique head.found assignmentTyped
  obtain ⟨targetType, targetTyped⟩ := CallableIndexedOwnedPlaceAdmission.assignment_target_typed assignmentTyped
  obtain ⟨originalTypes, originalKeyTyped⟩ := CallableIndexedOwnedPlaceAdmission.place_keys_typed targetTyped
  rcases head with ⟨prepared, index, codes, leaf, lowered, rhsNode, invalid, shape, slot, writable, rhsFound, generated, rightView, rightType, profile⟩
  cases shape with
  | bare empty _ => exact (projected empty).elim
  | @projected codes leaf sourceTypes site layout ordinary =>
    let head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) invocation.source context
        certificate scope administrative compiled.indexed.layouts.definitions assignment operator rhs :=
      ⟨prepared, index, codes, leaf, lowered, rhsNode, invalid, .projected layout ordinary,
        slot, writable, rhsFound, generated, rightView, rightType, profile⟩
    have keyTyped := CellAwareScopeProjectedAssignmentHeads.tree_typed layout.children unique originalKeyTyped
    have liftResolved {resolvedTarget : Dynamic.ResolvedPlace} {resolvedHeap : Dynamic.Heap} {resolvedGrade : Nat}
        (resolved : SourceExecutionSize.SourcePlaceResolves program resolvedGrade context invocation.evidence invocation.source
          environment before assignment.target resolvedTarget resolvedHeap) (bounded : resolvedGrade ≤ budget) :=
      CellAwareSourceProjectedResolutionLifting.lifts
                (stages := stages) (faults := faults)
        bridge functions extension transport
        faithful observations budget layout ordinary unique originalKeyTyped childLift childMeaning
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation head.slot head.writable resolved bounded
    rcases SelectedCompilationStageProjectedAssignmentInversion.child_and_tail unique found form trace with
      ⟨assignedSize, reason, strict, rfl, rfl, failed⟩ |
      ⟨assignedSize, tailSize, updated, written, strict, tailStrict, assigned, tail⟩
    · cases failed with
      | target failed =>
        rcases SelectedCompilationStageProjectedTargetInversion.failed failed with
          ⟨rfl, rootFault⟩ | ⟨keySize, keyStrict, ready, keysFailed⟩ |
          ⟨keySize, values, keyStrict, ordinaryKeys, getterFault⟩
        · exact ⟨_, _, _, .assignProjectedRootFault (lookupStatement?_sound found) form projected rootFault, .completed (.fault reason)⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := CellAwareScopeSourceSequenceLifting.fault bridge budget
            layout.children unique keyTyped childLift childMeaning environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation
            (by simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using keysFailed)
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
          have keys := lifted
          rw [← Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] at keys
          cases adapted with
          | completed =>
              exact ⟨_, _, _, .assignProjectedKeysFault (lookupStatement?_sound found) form projected ready keys, .completed (.fault reason)⟩
          | rejected origin call reason reached =>
              exact ⟨_, _, _, .assignProjectedKeysFault (lookupStatement?_sound found) form projected ready keys, .rejected origin call reason _ reached⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := CellAwareScopeSourceSequenceLifting.values bridge budget
            layout.children unique keyTyped childLift childMeaning environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation
            (by simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using ordinaryKeys)
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
          have keys := lifted
          rw [← Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] at keys
          cases adapted with
          | completed =>
              exact ⟨_, _, _, .assignProjectedGetterFault (lookupStatement?_sound found) form projected keys getterFault, .completed (.fault reason)⟩
          | rejected origin call reason reached =>
              have ready : Staging.Recursive.ProjectedTarget.RootReady environment before assignment.target := by
                cases getterFault <;> exact .intro (by assumption) (by assumption)
              exact ⟨_, _, _, .assignProjectedKeysFault (lookupStatement?_sound found) form projected ready keys, .rejected origin call reason _ reached⟩
      | rhs resolved evaluated =>
        rcases liftResolved resolved
          (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega) with
          ⟨origin, call, reason, reached, ready, keys⟩ |
          ⟨sources, keys, snapshot, _keyValues, resolution, getterState, _getterRelated, getterAdmission⟩
        · exact ⟨_, _, _, .assignProjectedKeysFault (lookupStatement?_sound found) form projected ready keys, .rejected origin call reason _ reached⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := childLift _
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
            head.right head.found typed (environments.extend resolution.maps resolution.worlds)
            resolution.heaps (locals.mono resolution.metadata) agrees (actualTyped.weaken resolution.worlds)
            getterState getterAdmission (authority.transport resolution.effect)
              (physical.transport resolution.effect resolution.frame) owner sameLocation (.fault evaluated)
          cases adapted with
          | rejected origin call reason reached =>
              exact ⟨_, _, _, .assignProjectedRhsFault (lookupStatement?_sound found) form projected keys snapshot lifted, .rejected origin call reason _ reached⟩
          | completed =>
              exact ⟨_, _, _, .assignProjectedRhsFault (lookupStatement?_sound found) form projected keys snapshot lifted, .completed (.fault reason)⟩
      | operands resolved evaluated currentRead rootType initialValue pathRead invalid =>
        rcases liftResolved resolved
          (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega) with
          ⟨origin, call, reason, reached, ready, keys⟩ |
          ⟨sources, keys, snapshot, _keyValues, resolution, getterState, _getterRelated, getterAdmission⟩
        · exact ⟨_, _, _, .assignProjectedKeysFault (lookupStatement?_sound found) form projected ready keys, .rejected origin call reason _ reached⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := childLift _
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
            head.right head.found typed (environments.extend resolution.maps resolution.worlds)
            resolution.heaps (locals.mono resolution.metadata) agrees (actualTyped.weaken resolution.worlds)
            getterState getterAdmission (authority.transport resolution.effect)
              (physical.transport resolution.effect resolution.frame) owner sameLocation (.value evaluated)
          cases adapted with
          | rejected origin call reason reached =>
              exact ⟨_, _, _, .assignProjectedRhsFault (lookupStatement?_sound found) form projected keys snapshot lifted, .rejected origin call reason _ reached⟩
          | completed =>
              exact ⟨_, _, _, .assignProjectedWriteFault (lookupStatement?_sound found) form projected keys snapshot lifted (.operands currentRead rootType initialValue pathRead invalid), .completed (.fault (.invalidAssignmentOperands operator))⟩
      | structuralUpdate resolved evaluated currentRead rootType initialValue pathFault =>
        rcases liftResolved resolved
          (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega) with
          ⟨origin, call, reason, reached, ready, keys⟩ |
          ⟨sources, keys, snapshot, _keyValues, resolution, getterState, _getterRelated, getterAdmission⟩
        · exact ⟨_, _, _, .assignProjectedKeysFault (lookupStatement?_sound found) form projected ready keys, .rejected origin call reason _ reached⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := childLift _
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
            head.right head.found typed (environments.extend resolution.maps resolution.worlds)
            resolution.heaps (locals.mono resolution.metadata) agrees (actualTyped.weaken resolution.worlds)
            getterState getterAdmission (authority.transport resolution.effect)
              (physical.transport resolution.effect resolution.frame) owner sameLocation (.value evaluated)
          cases adapted with
          | rejected origin call reason reached =>
              exact ⟨_, _, _, .assignProjectedRhsFault (lookupStatement?_sound found) form projected keys snapshot lifted, .rejected origin call reason _ reached⟩
          | completed =>
              exact ⟨_, _, _, .assignProjectedWriteFault (lookupStatement?_sound found) form projected keys snapshot lifted (.structural currentRead rootType initialValue pathFault), .completed (.fault reason)⟩
    · cases assigned with
      | intro resolved evaluated write =>
        rcases liftResolved resolved
          (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega) with
          ⟨origin, call, reason, reached, ready, keys⟩ |
          ⟨sources, keys, snapshot, _keyValues, resolution, getterState, _getterRelated, getterAdmission⟩
        · exact ⟨_, _, _, .assignProjectedKeysFault (lookupStatement?_sound found) form projected ready keys, .rejected origin call reason _ reached⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := childLift _
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
            head.right head.found typed (environments.extend resolution.maps resolution.worlds)
            resolution.heaps (locals.mono resolution.metadata) agrees (actualTyped.weaken resolution.worlds)
            getterState getterAdmission (authority.transport resolution.effect)
              (physical.transport resolution.effect resolution.frame) owner sameLocation (.value evaluated)
          cases adapted with
          | rejected origin call reason reached =>
              exact ⟨_, _, _, .assignProjectedRhsFault (lookupStatement?_sound found) form projected keys snapshot lifted, .rejected origin call reason _ reached⟩
          | completed =>
            obtain ⟨keyStageSize, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
            obtain ⟨rhsStageSize, measuredRhs⟩ := Staging.Recursive.Size.Expression.of_trace lifted
            obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, framePreserved, metadata,
                effect, _count, nextTyped, ⟨middleState, _related, nextAdmitted⟩, _continuation⟩ :=
              CellAwareScopeProjectedAssignmentHeads.preserves_value
                                (stages := stages) (faults := faults)
                bridge functions extension transport
                faithful observations head projected environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
                (keyStageSize + rhsStageSize + 1) (fun n _ => childMeaning n)
                measuredKeys (by omega) snapshot measuredRhs (by omega) write
            obtain ⟨nextContext, result, finalHeap, restTrace, restAdapted⟩ := remaining
              (environments.extend maps worlds) middleHeaps
              (locals.mono metadata) (DataPlaceChildExpressions.prefix_agrees agrees slots) nextTyped runtime covers sameLedger suffix
              middleState nextAdmitted (authority.transport effect) (physical.transport effect framePreserved)
              owner sameLocation ready tail
            exact ⟨nextContext, result, finalHeap,
              .assignProjected (lookupStatement?_sound found) form projected keys snapshot lifted write restTrace, restAdapted⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowProjectedAssignmentLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareSourceWhileLifting
/-! Independent Source while execution follows the actual mixed continuation.
Repeated and continued iterations retain all descriptor bundles; a genuine
earlier stage rejection records its reached heap and stops the remaining loop. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceWhileLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)
open SelectedCompilationStageBodyLiftBounds

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)))
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
  {administrative : Core.Context} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}

open CellAwareSourceFlowReadiness (Ready body_prefix body_ready test_value)
open SelectedCompilationStageWhileLifting (PlainWhile WhileLift)
variable {certificate : GenericExpressionMeaning.Certificate}
  {test : ExpressionId} {node : ExpressionNode} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {testCode loopCode : Expr}
variable {environment : Dynamic.Environment} {canonical actual : Environment}
  {actualContext : Core.Context} {embedding : Renaming}

local notation "ReadyAt" => Ready (named := named) (administrative := administrative)
  (invocation := invocation) (context := context) (scope := scope)
  bridge producer environment canonical actual actualContext embedding

theorem body_continue_ready {before after : Dynamic.Heap} {finalContext : SourceSemantics.Context}
    {finalEnvironment : Dynamic.Environment} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (preservation : ∀ size, CellAwareScopeFlowBounds.PreservesAt bridge context model named producer registry invocation faults
      administrative scope false statements expected type code size)
    (sourceTyped : ProtectedStateImperativeTypedSourceSites.Statements (source named) context statements)
    (ready : ReadyAt before)
    (trace : Staging.Recursive.StatementsIn program registry false invocation context environment before statements
      finalContext (.continuing finalEnvironment) after) : ReadyAt after := by
  obtain ⟨mapping,world,store,environments,heaps,locals,agrees,actualTyped,runtime,covers,sameLedger,
    initial,admitted,authority,physical,owner,sameLocation,allocationReady⟩ := ready
  obtain ⟨size,measured⟩ := Staging.Recursive.Size.StatementsIn.of_trace trace
  obtain ⟨_,finalStore,finalMap,finalWorld,_,_,finalHeaps,maps,worlds,preserved,metadata,effect,
    last,_,post⟩ := preservation size environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation allocationReady measured
  exact ⟨finalMap,finalWorld,finalStore,environments.extend maps worlds,finalHeaps,
    locals.mono metadata,agrees,actualTyped.weaken worlds,runtime,covers,sameLedger,
    last,post,authority.transport effect,physical.transport effect preserved,owner,sameLocation,allocationReady⟩

theorem while_ready
    (children : ∀ childSize, CellAwareScopeSourceLiftBounds.LiftsAt bridge context model named registry invocation certificate childSize)
    (preservation : ∀ childSize, CellAwareScopeExpressionBounds.PreservesAt
      bridge context model named registry invocation certificate faults childSize)
    (booleans : ∀ {mapping world sourceValue nativeValue},
      model.Represents mapping world .bool sourceValue nativeValue .bool →
      ∃ truth, sourceValue = .bool truth ∧ nativeValue = .bool truth)
    (found : invocation.source.lookupExpression? test = some node)
    (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context test node.type)
    (generated : certificate scope test ⟨.bool, testCode⟩)
    (body : CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope false statements)
    (bodyPreservation : ∀ size, CellAwareScopeFlowBounds.PreservesAt bridge context model named producer registry invocation faults
      administrative scope false statements expected type loopCode size)
    (bodyTyped : ProtectedStateImperativeTypedSourceSites.Statements (source named) context statements)
    {size : Nat} {before after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome}
    (ready : ReadyAt before)
    (trace : PlainWhile program size invocation context environment before test statements outcome after) :
    WhileLift program registry invocation context environment before test statements outcome after := by
  induction size using Nat.strongRecOn generalizing before after outcome with
  | ind size ih =>
    cases trace with
    | control trace =>
      cases trace with
      | done testTrace =>
        rcases test_value bridge producer children preservation booleans found nodeType typed generated ready testTrace with
          stopped | ⟨lifted, _, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .conditionFault stopped, .rejected origin call reason context reached⟩
        · exact ⟨_, _, .done lifted, .completed (.fallthrough environment)⟩
      | nextFallthrough testTrace bodyTrace next =>
        rcases test_value bridge producer children preservation booleans found nodeType typed generated ready testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .conditionFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge producer body bodyTyped testReady
              (.control bodyTrace)
          cases adaptedBody with
          | rejected origin call reason finalContext reached =>
            exact ⟨_, _, .bodyFault liftedTest liftedBody, .rejected origin call reason context _⟩
          | completed matched =>
            cases matched
            have nextReady := body_ready bridge producer bodyPreservation bodyTyped testReady liftedBody
            obtain ⟨staged, reached, liftedNext, adaptedNext⟩ := ih _
              (SourceExecutionSize.child_lt_stepSize (by simp))
              nextReady (.control next)
            exact ⟨staged, reached, .next liftedTest liftedBody liftedNext, adaptedNext⟩
      | nextContinue testTrace bodyTrace next =>
        rcases test_value bridge producer children preservation booleans found nodeType typed generated ready testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .conditionFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge producer body bodyTyped testReady
              (.control bodyTrace)
          cases adaptedBody with
          | rejected origin call reason finalContext reached =>
            exact ⟨_, _, .bodyFault liftedTest liftedBody, .rejected origin call reason context _⟩
          | completed matched =>
            cases matched
            have nextReady := body_continue_ready bridge producer bodyPreservation bodyTyped testReady liftedBody
            obtain ⟨staged, reached, liftedNext, adaptedNext⟩ := ih _
              (SourceExecutionSize.child_lt_stepSize (by simp))
              nextReady (.control next)
            exact ⟨staged, reached, .continueNext liftedTest liftedBody liftedNext, adaptedNext⟩

      | breaks testTrace bodyTrace =>
        rcases test_value bridge producer children preservation booleans found nodeType typed generated ready testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .conditionFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge producer body bodyTyped testReady
              (.control bodyTrace)
          cases adaptedBody with
          | rejected origin call reason finalContext reached =>
            exact ⟨_, _, .bodyFault liftedTest liftedBody, .rejected origin call reason context _⟩
          | completed matched =>
            cases matched
            exact ⟨_, _, .breakFromBody liftedTest liftedBody, .completed (.fallthrough environment)⟩
      | returns testTrace bodyTrace =>
        rcases test_value bridge producer children preservation booleans found nodeType typed generated ready testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .conditionFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge producer body bodyTyped testReady
              (.control bodyTrace)
          cases adaptedBody with
          | rejected origin call reason finalContext reached =>
            exact ⟨_, _, .bodyFault liftedTest liftedBody, .rejected origin call reason context _⟩
          | completed matched =>
            cases matched
            exact ⟨_, _, .returned liftedTest liftedBody, .completed (.returned _)⟩
    | fault trace =>
      cases trace with
      | condition failed =>
        obtain ⟨mapping,world,store,environments,heaps,locals,agrees,actualTyped,_runtime,_covers,_sameLedger,
          initial,admitted,authority,physical,owner,sameLocation,_allocationReady⟩ := ready
        obtain ⟨staged, reached, lifted, adapted⟩ := children _ generated found typed
          environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation (.fault failed)
        cases adapted with
        | completed => exact ⟨_, _, .conditionFault lifted, .completed (.fault _)⟩
        | rejected origin call reason reached =>
          exact ⟨_, reached, .conditionFault lifted, .rejected origin call reason context reached⟩
      | conditionType testTrace notBoolean _ =>
        rcases test_value bridge producer children preservation booleans found nodeType typed generated ready testTrace with
          stopped | ⟨_, _, valueTyped⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .conditionFault stopped, .rejected origin call reason context reached⟩
        · exact False.elim (notBoolean valueTyped)
      | body testTrace bodyTrace =>
        rcases test_value bridge producer children preservation booleans found nodeType typed generated ready testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .conditionFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge producer body bodyTyped testReady
              (.fault bodyTrace)
          cases adaptedBody with
          | rejected origin call reason finalContext reached =>
            exact ⟨_, _, .bodyFault liftedTest liftedBody, .rejected origin call reason context _⟩
          | completed matched =>
            cases matched
            exact ⟨_, _, .bodyFault liftedTest liftedBody, .completed (.fault _)⟩
      | nextFallthrough testTrace bodyTrace next =>
        rcases test_value bridge producer children preservation booleans found nodeType typed generated ready testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .conditionFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge producer body bodyTyped testReady
              (.control bodyTrace)
          cases adaptedBody with
          | rejected origin call reason finalContext reached =>
            exact ⟨_, _, .bodyFault liftedTest liftedBody, .rejected origin call reason context _⟩
          | completed matched =>
            cases matched
            have nextReady := body_ready bridge producer bodyPreservation bodyTyped testReady liftedBody
            obtain ⟨staged, reached, liftedNext, adaptedNext⟩ := ih _
              (SourceExecutionSize.child_lt_stepSize (by simp))
              nextReady (.fault next)
            exact ⟨staged, reached, .next liftedTest liftedBody liftedNext, adaptedNext⟩
      | nextContinue testTrace bodyTrace next =>
        rcases test_value bridge producer children preservation booleans found nodeType typed generated ready testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .conditionFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge producer body bodyTyped testReady
              (.control bodyTrace)
          cases adaptedBody with
          | rejected origin call reason finalContext reached =>
            exact ⟨_, _, .bodyFault liftedTest liftedBody, .rejected origin call reason context _⟩
          | completed matched =>
            cases matched
            have nextReady := body_continue_ready bridge producer bodyPreservation bodyTyped testReady liftedBody
            obtain ⟨staged, reached, liftedNext, adaptedNext⟩ := ih _
              (SourceExecutionSize.child_lt_stepSize (by simp))
              nextReady (.fault next)
            exact ⟨staged, reached, .continueNext liftedTest liftedBody liftedNext, adaptedNext⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceWhileLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareSourceForInitialBounds
/-! Independent Source for-loop headers use the same reached mixed state as
ordinary statements. Source and native grades are independent. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceForInitialBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)
open SelectedCompilationStageBodyLiftBounds

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)))
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
  {administrative : Core.Context} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}

open CellAwareSourceFlowReadiness (Ready body_prefix body_ready test_value)
open SelectedCompilationStageForInitialBounds (PlainInitial InitialLift)
variable {certificate : GenericExpressionMeaning.Certificate}
  {test : ExpressionId} {node : ExpressionNode} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {testCode loopCode postCode : Expr} {post : List ForItemForm}
variable {environment : Dynamic.Environment} {canonical actual : Environment}
  {actualContext : Core.Context} {embedding : Renaming}

local notation "ReadyAt" => Ready (named := named) (administrative := administrative)
  (invocation := invocation) (context := context) (scope := scope)
  bridge producer environment canonical actual actualContext embedding

def InitializersLifts (items : List ForItemForm) (test : ExpressionId) (post : List ForItemForm) (statements : List StatementId) : Prop :=
  ∀ {size : Nat} {environment : Dynamic.Environment} {canonical actual : Environment}
    {actualContext : Core.Context} {embedding : Renaming} {before after : Dynamic.Heap},
    Ready (named := named) (administrative := administrative)
      (invocation := invocation) (context := context) (scope := scope)
      bridge producer environment canonical actual actualContext embedding before →
    ∀ {outcome : Dynamic.ControlOutcome},
      PlainInitial program invocation context environment before items test post statements size outcome after →
      InitialLift program registry invocation context environment before items test post statements outcome after

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceForInitialBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareSourceForSequenceLifting
/-! Actual Source initializer execution keeps its lexical bindings through the
loop and restores the original scope before the reached suffix. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceForSequenceLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageBodyLiftBounds SelectedCompilationStageScopedLiftBounds
open CallableIndexedNamedGeneration (source)
open CellAwareSourceFlowReadiness (Ready body_prefix body_ready test_value)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)))
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}

open SelectedCompilationStageForInitialBounds (PlainInitial InitialLift)

/-- Only normal for completion reaches the original statement suffix. -/
theorem lifts {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {mode : Bool} {id : StatementId} {rest statements : List StatementId}
    {statement : StatementNode} {test : ExpressionId} {items postItems : List ForItemForm}
    {expected : TypeSystem.Ty} {type : Ty} {initialCode : Expr}
    (sourceEq : invocation.source = source named)
    (initialLift : CellAwareSourceForInitialBounds.InitializersLifts
      (administrative := administrative) (named := named) (context := context) (scope := scope)
      (registry := registry) (invocation := invocation) bridge producer items test postItems statements)
    (initialPreservation : ∀ size, CellAwareScopeForInitialBounds.PreservesAt
      bridge context model named producer registry invocation faults administrative scope items test postItems statements expected type initialCode size)
    (statementFound : invocation.source.lookupStatement? id = some statement)
    (form : statement.form = .forLoop items test postItems statements)
    (remaining : CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope mode rest) :
    CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope mode (id :: rest) := by
  intro size mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation allocationReady finalContext outcome after trace
  have unique : NodeOccurrencesUnique invocation.source := sourceEq.symm ▸ runtime.graph.nodeOccurrencesUnique
  have ready : Ready (named := named) (administrative := administrative) (invocation := invocation)
      (context := context) (scope := scope) bridge producer environment canonical actual actualContext embedding before :=
    ⟨mapping,world,store,environments,heaps,locals,agrees,actualTyped,runtime,covers,sameLedger,
      initial,admitted,authority,physical,owner,sameLocation,allocationReady⟩
  have suffixTyped := CallableIndexedOwnedPreparedStagedScopedForSourceTyping.suffix
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ statementFound) form
  rcases SelectedCompilationStageScopedSourceInversion.head_and_tail unique statementFound
    (by intro expression equal; rw [form] at equal; cases equal) trace with
    ⟨headSize, reason, _headSmaller, rfl, rfl, failed⟩ |
    ⟨headSize, _headSmaller, terminal, executed⟩ |
    ⟨headSize, tailSize, middleContext, nextEnvironment, middle, _headSmaller, _tailSmaller, executed, tail⟩
  · have loop := SelectedCompilationStageForSourceInversion.fault unique statementFound form failed
    obtain ⟨stagedSize, staged, reached, lifted, adapted⟩ := initialLift ready loop
    cases adapted with
    | completed matched =>
      cases matched
      exact ⟨_, _, _, (CallableIndexedOwnedAdmittedStagedForSourceBridge.fault statementFound form lifted).sound, .completed (.fault reason)⟩
    | rejected origin call reason finalContext reached =>
      exact ⟨_, _, _, (CallableIndexedOwnedAdmittedStagedForSourceBridge.fault statementFound form lifted).sound,
        .rejected origin call reason _ _⟩
  · obtain ⟨rfl, loop⟩ := SelectedCompilationStageForSourceInversion.control unique statementFound form executed
    obtain ⟨stagedSize, staged, reached, lifted, adapted⟩ := initialLift ready loop
    cases adapted with
    | rejected origin call reason finalContext reached =>
      exact ⟨_, _, _, (CallableIndexedOwnedAdmittedStagedForSourceBridge.fault statementFound form lifted).sound,
        .rejected origin call reason _ _⟩
    | completed matched =>
      cases matched with
      | breaking innerEnvironment => exact ((CallableIndexedOwnedAdmittedStagedForSourceBridge.closed lifted).1 innerEnvironment rfl).elim
      | continuing innerEnvironment => exact ((CallableIndexedOwnedAdmittedStagedForSourceBridge.closed lifted).2 innerEnvironment rfl).elim
      | returned value =>
        exact ⟨_, _, _, (CallableIndexedOwnedAdmittedStagedForSourceBridge.returned statementFound form lifted).sound, .completed (.returned value)⟩
      | fault reason =>
        exact ⟨_, _, _, (CallableIndexedOwnedAdmittedStagedForSourceBridge.fault statementFound form lifted).sound, .completed (.fault reason)⟩
      | fallthrough innerEnvironment =>
        cases SelectedCompilationStageForSourceInversion.fallthrough_environment loop
        rcases terminal with terminal | rfl
        · cases terminal
        · exact ⟨_, _, _, (CallableIndexedOwnedAdmittedStagedForSourceBridge.fallthrough statementFound form lifted .nil).sound,
            .completed (.fallthrough environment)⟩
  · obtain ⟨rfl, loop⟩ := SelectedCompilationStageForSourceInversion.control unique statementFound form executed
    cases SelectedCompilationStageForSourceInversion.fallthrough_environment loop
    obtain ⟨stagedSize, staged, reached, lifted, adapted⟩ := initialLift ready loop
    cases adapted with
    | rejected origin call reason finalContext reached =>
      exact ⟨_, _, _, (CallableIndexedOwnedAdmittedStagedForSourceBridge.fault statementFound form lifted).sound,
        .rejected origin call reason _ _⟩
    | completed matched =>
      cases matched
      obtain ⟨_, finalStore, finalMap, finalWorld, _, _, finalHeaps, maps, worlds, preserved, metadata, effect,
        last, _, post⟩ := initialPreservation stagedSize environments heaps locals agrees actualTyped
          runtime covers sameLedger initial admitted authority physical owner sameLocation allocationReady lifted
      obtain ⟨tailContext, tailOutcome, tailHeap, liftedTail, adaptedTail⟩ := remaining
        (environments.extend maps worlds) finalHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
        runtime covers sameLedger suffixTyped last post (authority.transport effect) (physical.transport effect preserved)
        owner sameLocation allocationReady tail
      obtain ⟨tailGrade, tailMeasured⟩ := Staging.Recursive.Size.StatementsIn.of_trace liftedTail
      exact ⟨tailContext, tailOutcome, tailHeap,
        (CallableIndexedOwnedAdmittedStagedForSourceBridge.fallthrough statementFound form lifted tailMeasured).sound,
        adaptedTail⟩


end Solcore.SourceSemantics.CoreLowering.CellAwareSourceForSequenceLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareSourceForInitialProjectedAssignmentLifting
/-! Independent Source assignment first resolves the original root, then
lifts the real RHS. A completed write supplies the exact mixed state for the
remaining Source flow; an earlier stage rejection retains its reached heap. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceForInitialProjectedAssignmentLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleEquality CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)
open CellAwareSourceForInitialBounds (InitializersLifts)
open CallableIndexedOwnedAdmittedStagedForInitializerSource

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations compiled.compatible.checked.catalog functions identities)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  {receiving : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
      (GeneralizedLocalInstanceValues.model compiled.indexed)))
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep}

variable {test : ExpressionId} {postItems : List ForItemForm} {statements : List StatementId}

include transport extension faithful observations in
theorem lifts {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {rest : List ForItemForm}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    (sourceEq : invocation.source = source named)
    (head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) invocation.source context
      certificate scope administrative compiled.indexed.layouts.definitions assignment operator rhs)
    (projected : assignment.target.projections ≠ [])
    (assignmentTyped : SourceAssignmentHasType invocation.source context assignment operator rhs)
    (children : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeSourceLiftBounds.LiftsAt bridge context
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
        named stages invocation certificate size)
    (preservation : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeExpressionBounds.PreservesAt bridge context
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
        named stages invocation certificate faults size)
    (remaining : InitializersLifts (named := named) (administrative := administrative)
      (registry := stages) (invocation := invocation) (context := context) (scope := scope) bridge producer rest test postItems statements) :
    InitializersLifts (named := named) (administrative := administrative)
      (registry := stages) (invocation := invocation) (context := context) (scope := scope) bridge producer (.assignValue assignment operator rhs :: rest) test postItems statements := by
  intro size environment canonical actual actualContext embedding before after reachedReady outcome trace
  obtain ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, runtime, covers, sameLedger,
    initial, admitted, authority, physical, owner, sameLocation, ready⟩ := reachedReady
  have unique : NodeOccurrencesUnique invocation.source := sourceEq.symm ▸ runtime.graph.nodeOccurrencesUnique
  let budget := size + 1
  have within : size ≤ budget := by omega
  have childLift : ∀ childSize, childSize < budget → CellAwareScopeSourceLiftBounds.LiftsAt bridge context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
      named stages invocation certificate childSize := fun childSize _ => children runtime covers sameLedger childSize
  have childMeaning : ∀ childSize, CellAwareScopeExpressionBounds.PreservesAt bridge context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
      named stages invocation certificate faults childSize := preservation runtime covers sameLedger
  have typed := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique head.found assignmentTyped
  obtain ⟨targetType, targetTyped⟩ := CallableIndexedOwnedPlaceAdmission.assignment_target_typed assignmentTyped
  obtain ⟨originalTypes, originalKeyTyped⟩ := CallableIndexedOwnedPlaceAdmission.place_keys_typed targetTyped
  rcases head with ⟨prepared, index, codes, leaf, lowered, rhsNode, invalid, shape, slot, writable, rhsFound, generated, rightView, rightType, profile⟩
  cases shape with
  | bare empty _ => exact (projected empty).elim
  | @projected codes leaf sourceTypes site layout ordinary =>
    let head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) invocation.source context
        certificate scope administrative compiled.indexed.layouts.definitions assignment operator rhs :=
      ⟨prepared, index, codes, leaf, lowered, rhsNode, invalid, .projected layout ordinary,
        slot, writable, rhsFound, generated, rightView, rightType, profile⟩
    have keyTyped := CellAwareScopeProjectedAssignmentHeads.tree_typed layout.children unique originalKeyTyped
    have liftResolved {resolvedTarget : Dynamic.ResolvedPlace} {resolvedHeap : Dynamic.Heap} {resolvedGrade : Nat}
        (resolved : SourceExecutionSize.SourcePlaceResolves program resolvedGrade context invocation.evidence invocation.source
          environment before assignment.target resolvedTarget resolvedHeap) (bounded : resolvedGrade ≤ budget) :=
      CellAwareSourceProjectedResolutionLifting.lifts
                (stages := stages) (faults := faults)
        bridge functions extension transport
        faithful observations budget layout ordinary unique originalKeyTyped childLift childMeaning
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation head.slot head.writable resolved bounded
    rcases SelectedCompilationStageForInitialInversion.assignProjected trace with
      ⟨assignedSize, reason, strict, rfl, failed⟩ |
      ⟨assignedSize, tailSize, updated, written, strict, tailStrict, assigned, tail⟩
    · cases failed with
      | target failed =>
        rcases SelectedCompilationStageProjectedTargetInversion.failed failed with
          ⟨rfl, rootFault⟩ | ⟨keySize, keyStrict, ready, keysFailed⟩ |
          ⟨keySize, values, keyStrict, ordinaryKeys, getterFault⟩
        · exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_root_fault projected rootFault, .completed (.fault reason)⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := CellAwareScopeSourceSequenceLifting.fault bridge budget
            layout.children unique keyTyped childLift childMeaning environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation
            (by simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using keysFailed)
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
          have keys := lifted
          rw [← Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] at keys
          cases adapted with
          | completed =>
              obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
              exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_keys_fault projected ready measuredKeys, .completed (.fault reason)⟩
          | rejected origin call reason reached =>
              obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
              exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_keys_fault projected ready measuredKeys, .rejected origin call reason _ reached⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := CellAwareScopeSourceSequenceLifting.values bridge budget
            layout.children unique keyTyped childLift childMeaning environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation
            (by simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using ordinaryKeys)
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
          have keys := lifted
          rw [← Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] at keys
          cases adapted with
          | completed =>
              obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
              exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_getter_fault projected measuredKeys getterFault, .completed (.fault reason)⟩
          | rejected origin call reason reached =>
              have ready : Staging.Recursive.ProjectedTarget.RootReady environment before assignment.target := by
                cases getterFault <;> exact .intro (by assumption) (by assumption)
              obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
              exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_keys_fault projected ready measuredKeys, .rejected origin call reason _ reached⟩
      | rhs resolved evaluated =>
        rcases liftResolved resolved
          (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega) with
          ⟨origin, call, reason, reached, ready, keys⟩ |
          ⟨sources, keys, snapshot, _keyValues, resolution, getterState, _getterRelated, getterAdmission⟩
        · obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
          exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_keys_fault projected ready measuredKeys, .rejected origin call reason _ reached⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := childLift _
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
            head.right head.found typed (environments.extend resolution.maps resolution.worlds)
            resolution.heaps (locals.mono resolution.metadata) agrees (actualTyped.weaken resolution.worlds)
            getterState getterAdmission (authority.transport resolution.effect)
              (physical.transport resolution.effect resolution.frame) owner sameLocation (.fault evaluated)
          cases adapted with
          | rejected origin call reason reached =>
              obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
              obtain ⟨rhsGrade, measuredRhs⟩ := Staging.Recursive.Size.Expression.of_trace lifted
              exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_rhs_fault projected measuredKeys snapshot measuredRhs, .rejected origin call reason _ reached⟩
          | completed =>
              obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
              obtain ⟨rhsGrade, measuredRhs⟩ := Staging.Recursive.Size.Expression.of_trace lifted
              exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_rhs_fault projected measuredKeys snapshot measuredRhs, .completed (.fault reason)⟩
      | operands resolved evaluated currentRead rootType initialValue pathRead invalid =>
        rcases liftResolved resolved
          (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega) with
          ⟨origin, call, reason, reached, ready, keys⟩ |
          ⟨sources, keys, snapshot, _keyValues, resolution, getterState, _getterRelated, getterAdmission⟩
        · obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
          exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_keys_fault projected ready measuredKeys, .rejected origin call reason _ reached⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := childLift _
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
            head.right head.found typed (environments.extend resolution.maps resolution.worlds)
            resolution.heaps (locals.mono resolution.metadata) agrees (actualTyped.weaken resolution.worlds)
            getterState getterAdmission (authority.transport resolution.effect)
              (physical.transport resolution.effect resolution.frame) owner sameLocation (.value evaluated)
          cases adapted with
          | rejected origin call reason reached =>
              obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
              obtain ⟨rhsGrade, measuredRhs⟩ := Staging.Recursive.Size.Expression.of_trace lifted
              exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_rhs_fault projected measuredKeys snapshot measuredRhs, .rejected origin call reason _ reached⟩
          | completed =>
              obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
              obtain ⟨rhsGrade, measuredRhs⟩ := Staging.Recursive.Size.Expression.of_trace lifted
              exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_write_fault projected measuredKeys snapshot measuredRhs (.operands currentRead rootType initialValue pathRead invalid), .completed (.fault (.invalidAssignmentOperands operator))⟩
      | structuralUpdate resolved evaluated currentRead rootType initialValue pathFault =>
        rcases liftResolved resolved
          (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega) with
          ⟨origin, call, reason, reached, ready, keys⟩ |
          ⟨sources, keys, snapshot, _keyValues, resolution, getterState, _getterRelated, getterAdmission⟩
        · obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
          exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_keys_fault projected ready measuredKeys, .rejected origin call reason _ reached⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := childLift _
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
            head.right head.found typed (environments.extend resolution.maps resolution.worlds)
            resolution.heaps (locals.mono resolution.metadata) agrees (actualTyped.weaken resolution.worlds)
            getterState getterAdmission (authority.transport resolution.effect)
              (physical.transport resolution.effect resolution.frame) owner sameLocation (.value evaluated)
          cases adapted with
          | rejected origin call reason reached =>
              obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
              obtain ⟨rhsGrade, measuredRhs⟩ := Staging.Recursive.Size.Expression.of_trace lifted
              exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_rhs_fault projected measuredKeys snapshot measuredRhs, .rejected origin call reason _ reached⟩
          | completed =>
              obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
              obtain ⟨rhsGrade, measuredRhs⟩ := Staging.Recursive.Size.Expression.of_trace lifted
              exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_write_fault projected measuredKeys snapshot measuredRhs (.structural currentRead rootType initialValue pathFault), .completed (.fault reason)⟩
    · cases assigned with
      | intro resolved evaluated write =>
        rcases liftResolved resolved
          (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega) with
          ⟨origin, call, reason, reached, ready, keys⟩ |
          ⟨sources, keys, snapshot, _keyValues, resolution, getterState, _getterRelated, getterAdmission⟩
        · obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
          exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_keys_fault projected ready measuredKeys, .rejected origin call reason _ reached⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := childLift _
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
            head.right head.found typed (environments.extend resolution.maps resolution.worlds)
            resolution.heaps (locals.mono resolution.metadata) agrees (actualTyped.weaken resolution.worlds)
            getterState getterAdmission (authority.transport resolution.effect)
              (physical.transport resolution.effect resolution.frame) owner sameLocation (.value evaluated)
          cases adapted with
          | rejected origin call reason reached =>
              obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
              obtain ⟨rhsGrade, measuredRhs⟩ := Staging.Recursive.Size.Expression.of_trace lifted
              exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_rhs_fault projected measuredKeys snapshot measuredRhs, .rejected origin call reason _ reached⟩
          | completed =>
            obtain ⟨keyStageSize, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
            obtain ⟨rhsStageSize, measuredRhs⟩ := Staging.Recursive.Size.Expression.of_trace lifted
            obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, framePreserved, metadata,
                effect, _count, nextTyped, ⟨middleState, _related, nextAdmitted⟩, _continuation⟩ :=
              CellAwareScopeProjectedAssignmentHeads.preserves_value
                                (stages := stages) (faults := faults)
                bridge functions extension transport
                faithful observations head projected environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
                (keyStageSize + rhsStageSize + 1) (fun n _ => childMeaning n)
                measuredKeys (by omega) snapshot measuredRhs (by omega) write
            obtain ⟨nextSize, result, finalHeap, restTrace, restAdapted⟩ := remaining
              ⟨_, _, _, environments.extend maps worlds, middleHeaps,
                locals.mono metadata, DataPlaceChildExpressions.prefix_agrees agrees slots, nextTyped,
                runtime, covers, sameLedger, middleState, nextAdmitted,
                authority.transport effect, physical.transport effect framePreserved, owner, sameLocation, ready⟩ tail
            exact ⟨_, result, finalHeap,
              CallableIndexedOwnedAdmittedStagedForInitializerSource.prepend_projected_assignment
                projected measuredKeys snapshot measuredRhs write restTrace, restAdapted⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceForInitialProjectedAssignmentLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareSourceForInitialAbsentLifting
/-! An original uninitialized declaration lifts through its actual absent
cell allocation. The independently executed suffix starts at that exact heap,
with every earlier generalized descriptor still retained. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceForInitialAbsentLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)
open CellAwareSourceForInitialBounds (InitializersLifts)
open CallableIndexedOwnedAdmittedStagedForInitializerSource
open TypedLexicalControl (absentRequest)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)))
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep}


private theorem restore_adapted {outer inner : SourceSemantics.Context}
    (environment : Dynamic.Environment) {plain : Dynamic.ControlOutcome} {staged : Staging.Recursive.BodyOutcome}
    {after reached : Dynamic.Heap}
    (adapted : SelectedCompilationStageBodyLiftBounds.BodyAdapted inner plain after inner staged reached) :
    SelectedCompilationStageBodyLiftBounds.BodyAdapted outer (Dynamic.restoreControl environment plain) after
      outer (staged.restore environment) reached := by
  cases adapted with
  | completed matched => cases matched <;> exact .completed (by constructor)
  | rejected origin call reason finalContext reached => exact .rejected origin call reason _ _

variable {test : ExpressionId} {postItems : List ForItemForm} {statements : List StatementId}

include registered in
theorem absent {context nextContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {binder : TypedBinder} {rest : List ForItemForm}
    {payload : Ty} {body : Expr} {administrative : Core.Context}
    (member : binder ∈ SourceCoreDataPlaces.declaredBinders (source named))
    (mono : binder.scheme.quantified = [])
    (extended : BinderExtends (source named).owner context binder nextContext)
    (ordinary : (source named).inputs.any (fun input => decide (input.id = binder.id)) = false)
    (projection : projects binder.scheme.body payload)
    (allocation : SourceCoreAllocationLayouts.Allocation whole.indexed.layouts named.signature.key []
      (absentRequest (source named) scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated whole.indexed.ancestry.layout.frame
      whole.indexed.base.globals.length
      (whole.indexed.layouts.allocatorAt named.signature.key [] (fun error => .sourceAllocation (reprStr error)))
      (absentRequest (source named) scope binder payload))
    (same : annotation.original = allocation.expression)
    (sourceEq : invocation.source = source named)
    (remaining : InitializersLifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) (context := nextContext) (scope := ((binder.id, payload) :: scope)) bridge producer rest test postItems statements) :
    InitializersLifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) (context := context) (scope := scope) bridge producer (.letDecl binder none :: rest) test postItems statements := by
  intro size environment canonical actual actualContext embedding before after reachedReady outcome trace
  obtain ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, runtime, covers, sameLedger,
    current, admitted, authority, physical, owner, sameLocation, ready⟩ := reachedReady
  obtain ⟨tailSize, location, bound, nextOutcome, _smaller, sameOutcome, allocated, tail⟩ :=
    SelectedCompilationStageForInitialInversion.absent mono
      (by simpa only [sourceEq] using extended) trace
  subst outcome
  obtain ⟨marker, _agreement, _smaller, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
      _preserved, _allocationEffect, nextAuthority, reachedState, _related, nextAdmitted, nextPhysical, locationEq, nativeEq⟩ :=
    CellAwareNamedAbsentPrefix.complete bridge mono member extended ordinary allocation annotation same producer registered
      projection environments heaps locals agrees actualTyped current admitted authority physical
      (ready current physical.read) allocated body
  have nextReady : ProtectedStateTransition.CellAllocation.ReadyAt producer nextPhysical.location nextPhysical.native := by
    intro index current stored
    have previous := ready current (by simpa only [locationEq, nativeEq] using stored)
    simpa only [locationEq, nativeEq] using previous
  obtain ⟨resultContext, resultOutcome, resultHeap, stagedTail, tailAdapted⟩ :=
    remaining ⟨_, _, _, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
      runtime.transport (.ofBinderExtends extended),
      (Dynamic.RuntimeContextFields.ofBinderExtends extended).covers covers,
      (Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans sameLedger,
      reachedState, nextAdmitted, nextAuthority, nextPhysical, owner, sameLocation.trans locationEq.symm, nextReady⟩ tail
  exact ⟨_, _, resultHeap,
    prepend_absent mono (by simpa only [sourceEq] using extended) allocated stagedTail, restore_adapted environment tailAdapted⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceForInitialAbsentLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareSourceForInitialOrdinaryLifting
/-! A real ordinary Source initializer is lifted before allocation. A failed
or rejected child keeps its reached heap, and successful allocation retains
all earlier generalized descriptors for the actual Source suffix. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceForInitialOrdinaryLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)
open CellAwareSourceForInitialBounds (InitializersLifts)
open CallableIndexedOwnedAdmittedStagedForInitializerSource
open TypedLexicalWhile (initializedRequest sequence)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)))
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep}


private theorem restore_adapted {outer inner : SourceSemantics.Context}
    (environment : Dynamic.Environment) {plain : Dynamic.ControlOutcome} {staged : Staging.Recursive.BodyOutcome}
    {after reached : Dynamic.Heap}
    (adapted : SelectedCompilationStageBodyLiftBounds.BodyAdapted inner plain after inner staged reached) :
    SelectedCompilationStageBodyLiftBounds.BodyAdapted outer (Dynamic.restoreControl environment plain) after
      outer (staged.restore environment) reached := by
  cases adapted with
  | completed matched => cases matched <;> exact .completed (by constructor)
  | rejected origin call reason finalContext reached => exact .rejected origin call reason _ _

variable {test : ExpressionId} {postItems : List ForItemForm} {statements : List StatementId}

include registered in
theorem initialized {context nextContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {binder : TypedBinder} {initializer : ExpressionId}
    {initializerNode : ExpressionNode} {rest : List ForItemForm} {type : Ty}
    {lowered : SourceCoreBasic.LoweredExpr} {body : Expr} {administrative : Core.Context}
      (member : binder ∈ SourceCoreDataPlaces.declaredBinders (source named))
      (mono : binder.scheme.quantified = [])
      (extended : BinderExtends (source named).owner context binder nextContext)
      (ordinary : (source named).inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : (source named).lookupExpression? initializer = some initializerNode)
      (valueType : initializerNode.type = binder.scheme.body)
      (typed : ExpressionHasType (source named) context initializer initializerNode.type)
      (value : certificates context scope initializer lowered)
      (allocation : SourceCoreAllocationLayouts.Allocation whole.indexed.layouts named.signature.key []
        (initializedRequest (source named) scope binder lowered.type))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated whole.indexed.ancestry.layout.frame
        whole.indexed.base.globals.length
        (whole.indexed.layouts.allocatorAt named.signature.key [] (fun error => .sourceAllocation (reprStr error)))
        (initializedRequest (source named) scope binder lowered.type))
      (same : annotation.original = allocation.expression)
    (sourceEq : invocation.source = source named)
    (childLift : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeSourceLiftBounds.LiftsAt bridge context model named registry invocation (certificates context) size)
    (preservation : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeExpressionBounds.PreservesAt bridge context model named registry invocation (certificates context) faults size)
    (remaining : InitializersLifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) (context := nextContext) (scope := ((binder.id, lowered.type) :: scope)) bridge producer rest test postItems statements) :
    InitializersLifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) (context := context) (scope := scope) bridge producer (.letDecl binder (some initializer) :: rest) test postItems statements := by
  intro size environment canonical actual actualContext embedding before after reachedReady outcome trace
  obtain ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, runtime, covers, sameLedger,
    current, admitted, authority, physical, owner, sameLocation, ready⟩ := reachedReady
  rcases SelectedCompilationStageForInitialInversion.initialized mono
      (by simpa only [sourceEq] using extended) trace with
    ⟨childSize, reason, _strict, outcomeEq, child⟩ |
    ⟨childSize, tailSize, sourceValue, middle, location, bound, nextOutcome, _childStrict, _tailStrict, sameOutcome, child, allocated, tail⟩
  · subst outcome
    obtain ⟨staged, reached, lifted, adapted⟩ := childLift runtime covers sameLedger childSize value
      (by simpa only [sourceEq] using initializerFound) (by simpa only [sourceEq] using typed)
      environments heaps locals agrees actualTyped current admitted authority physical owner sameLocation child
    obtain ⟨measuredSize, measuredChild⟩ := Staging.Recursive.Size.Expression.of_trace lifted
    cases adapted with
    | completed => exact ⟨_, _, _, initializer_fault mono measuredChild, .completed (.fault reason)⟩
    | rejected origin call reason reached => exact ⟨_, _, _, initializer_fault mono measuredChild, .rejected origin call reason _ reached⟩
  · subst outcome
    obtain ⟨staged, reached, lifted, adapted⟩ := childLift runtime covers sameLedger childSize value
      (by simpa only [sourceEq] using initializerFound) (by simpa only [sourceEq] using typed)
      environments heaps locals agrees actualTyped current admitted authority physical owner sameLocation child
    obtain ⟨measuredSize, measuredChild⟩ := Staging.Recursive.Size.Expression.of_trace lifted
    cases adapted with
    | rejected origin call reason reached => exact ⟨_, _, _, initializer_fault mono measuredChild, .rejected origin call reason _ reached⟩
    | completed =>
      obtain ⟨stageSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      obtain ⟨native, middleStore, middleMap, middleWorld, evaluated, represented, middleHeaps,
          maps, worlds, frame, metadata, effect, middleState, _expressionRelated, post⟩ :=
        preservation runtime covers sameLedger stageSize value
          (by simpa only [sourceEq] using initializerFound) (by simpa only [sourceEq] using typed)
          environments heaps locals agrees actualTyped current admitted authority physical owner sameLocation measured
      cases represented with
      | value payload =>
        let middlePhysical := physical.transport effect frame
        obtain ⟨marker, _agreement, _smaller, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
            _preserved, _allocationEffect, nextAuthority, reachedState, _related, nextAdmitted, nextPhysical, locationEq, nativeEq⟩ :=
          CellAwareNamedOrdinaryPrefix.complete bridge mono member extended ordinary allocation annotation same producer registered
            evaluated (valueType ▸ payload) (valueType ▸ post.at_value.1)
            (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
            middleState post.at_value.2 (authority.transport effect) middlePhysical
            (ready middleState middlePhysical.read) allocated type body
        have nextReady : ProtectedStateTransition.CellAllocation.ReadyAt producer nextPhysical.location nextPhysical.native := by
          intro index current stored
          have previous := ready current (by simpa only [locationEq, nativeEq, middlePhysical,
            CellAwareScopePhysical.Physical.transport_location, CellAwareScopePhysical.Physical.transport_native] using stored)
          simpa only [locationEq, nativeEq, middlePhysical, CellAwareScopePhysical.Physical.transport_location,
            CellAwareScopePhysical.Physical.transport_native] using previous
        obtain ⟨resultContext, resultOutcome, resultHeap, stagedTail, tailAdapted⟩ :=
          remaining ⟨_, _, _, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
      runtime.transport (.ofBinderExtends extended),
      (Dynamic.RuntimeContextFields.ofBinderExtends extended).covers covers,
      (Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans sameLedger,
      reachedState, nextAdmitted, nextAuthority, nextPhysical, owner, sameLocation.trans locationEq.symm, nextReady⟩ tail
        exact ⟨_, _, resultHeap,
          prepend_initialized mono (by simpa only [sourceEq] using extended) measuredChild allocated stagedTail, restore_adapted environment tailAdapted⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceForInitialOrdinaryLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareSourceForInitialDiscardLifting
/-! A real return or tail expression preserves the ordinary Source outcome,
or propagates its actual earlier stage rejection. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceForInitialDiscardLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)
open CellAwareSourceForInitialBounds (InitializersLifts)
open CallableIndexedOwnedAdmittedStagedForInitializerSource
open CallableIndexedOwnedAdmittedStagedScopedTerminalStatements (Head)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)))
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {context : SourceSemantics.Context} {certificates : GenericExpressionMeaning.Certificate}

variable {faults : RecursiveStageMeaning.FaultRep}

variable {test : ExpressionId} {postItems : List ForItemForm} {statements : List StatementId}

theorem lifts {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {rest : List ForItemForm}
    {expression : ExpressionId} {expressionNode : ExpressionNode}
    {lowered : SourceCoreBasic.LoweredExpr}
    (expressionFound : invocation.source.lookupExpression? expression = some expressionNode)
    (typed : ExpressionHasType invocation.source context expression expressionNode.type)
    (generated : certificates scope expression lowered)
    (children : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeSourceLiftBounds.LiftsAt bridge context model named registry invocation certificates size)
    (preservation : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeExpressionBounds.PreservesAt bridge context model named registry invocation certificates faults size)
    (remaining : InitializersLifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) (context := context) (scope := scope) bridge producer rest test postItems statements) :
    InitializersLifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) (context := context) (scope := scope) bridge producer (.expression expression :: rest) test postItems statements := by
  intro size environment canonical actual actualContext embedding before after reachedReady outcome trace
  obtain ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, runtime, covers, sameLedger,
    initial, admitted, authority, physical, owner, sameLocation, ready⟩ := reachedReady
  rcases SelectedCompilationStageForInitialInversion.discard trace with
    ⟨childSize, reason, _strict, rfl, evaluated⟩ |
    ⟨childSize, tailSize, sourceValue, middle, _strict, _tailStrict, evaluated, tail⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children runtime covers sameLedger childSize generated expressionFound typed
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation evaluated
    obtain ⟨measuredSize, measuredChild⟩ := Staging.Recursive.Size.Expression.of_trace lifted
    cases adapted with
    | completed => exact ⟨_, _, _, expression_fault measuredChild,
        .completed (.fault reason)⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, _, expression_fault measuredChild,
        .rejected origin call reason _ reached⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children runtime covers sameLedger childSize generated expressionFound typed
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation evaluated
    obtain ⟨measuredSize, measuredChild⟩ := Staging.Recursive.Size.Expression.of_trace lifted
    cases adapted with
    | rejected origin call reason reached =>
      exact ⟨_, _, _, expression_fault measuredChild,
        .rejected origin call reason _ reached⟩
    | completed =>
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      obtain ⟨_value, middleStore, middleMap, middleWorld, _evaluated, _represented, middleHeaps,
          maps, worlds, framePreserved, metadata, effect, middleState, _related, post⟩ :=
        preservation runtime covers sameLedger stagedSize generated expressionFound typed environments heaps locals agrees actualTyped
          initial admitted authority physical owner sameLocation measured
      obtain ⟨nextContext, result, finalHeap, restTrace, restAdapted⟩ := remaining
        ⟨_, _, _, environments.extend maps worlds, middleHeaps, locals.mono metadata, agrees, actualTyped.weaken worlds,
          runtime, covers, sameLedger, middleState, post.at_value.2,
          authority.transport effect, physical.transport effect framePreserved, owner, sameLocation, ready⟩ tail
      exact ⟨_, _, finalHeap, prepend_expression measuredChild restTrace, restAdapted⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceForInitialDiscardLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareSourceForInitialAssignmentLifting
/-! Independent Source assignment first resolves the original root, then
lifts the real RHS. A completed write supplies the exact mixed state for the
remaining Source flow; an earlier stage rejection retains its reached heap. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceForInitialAssignmentLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)
open CellAwareSourceForInitialBounds (InitializersLifts)
open CallableIndexedOwnedAdmittedStagedForInitializerSource

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  {receiving : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
      (GeneralizedLocalInstanceValues.model compiled.indexed)))
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep}

variable {test : ExpressionId} {postItems : List ForItemForm} {statements : List StatementId}

include transport extension in
theorem lifts {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {rest : List ForItemForm}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    (sourceEq : invocation.source = source named)
    (head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) invocation.source context
      certificate scope administrative compiled.indexed.layouts.definitions assignment operator rhs)
    (bare : assignment.target.projections = [])
    (assignmentTyped : SourceAssignmentHasType invocation.source context assignment operator rhs)
    (children : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeSourceLiftBounds.LiftsAt bridge context
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
        named stages invocation certificate size)
    (preservation : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeExpressionBounds.PreservesAt bridge context
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
        named stages invocation certificate faults size)
    (remaining : InitializersLifts (named := named) (administrative := administrative)
      (registry := stages) (invocation := invocation) (context := context) (scope := scope) bridge producer rest test postItems statements) :
    InitializersLifts (named := named) (administrative := administrative)
      (registry := stages) (invocation := invocation) (context := context) (scope := scope) bridge producer (.assignValue assignment operator rhs :: rest) test postItems statements := by
  intro size environment canonical actual actualContext embedding before after reachedReady outcome trace
  obtain ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, runtime, covers, sameLedger,
    initial, admitted, authority, physical, owner, sameLocation, ready⟩ := reachedReady
  have unique : NodeOccurrencesUnique invocation.source := sourceEq.symm ▸ runtime.graph.nodeOccurrencesUnique
  have typed := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique head.found assignmentTyped
  obtain ⟨target, snapshot⟩ := CellAwareScopeBareAssignmentHeads.target_snapshot
    (invocation := invocation) bridge functions extension head bare environments heaps locals agrees initial admitted
  rcases SelectedCompilationStageForInitialInversion.assign snapshot trace with
    ⟨childSize, reason, _strict, rfl, evaluated⟩ |
    ⟨childSize, sourceValue, currentCell, initialValue, currentSelected, _strict, rfl, evaluated,
      currentRead, rootType, rootInitial, pathRead, invalid⟩ |
    ⟨childSize, tailSize, sourceValue, middle, updated, written, _strict, _tailStrict, evaluated, write, tail⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children runtime covers sameLedger childSize head.right head.found typed
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation evaluated
    obtain ⟨measuredSize, measuredChild⟩ := Staging.Recursive.Size.Expression.of_trace lifted
    cases adapted with
    | completed => exact ⟨_, _, _, assignment_fault snapshot measuredChild,
        .completed (.fault reason)⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, _, assignment_fault snapshot measuredChild,
        .rejected origin call reason _ reached⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children runtime covers sameLedger childSize head.right head.found typed
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation evaluated
    obtain ⟨measuredSize, measuredChild⟩ := Staging.Recursive.Size.Expression.of_trace lifted
    cases adapted with
    | completed => exact ⟨_, _, _, assignment_operands snapshot measuredChild
        currentRead rootType rootInitial pathRead invalid, .completed (.fault (.invalidAssignmentOperands operator))⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, _, assignment_fault snapshot measuredChild, .rejected origin call reason _ reached⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children runtime covers sameLedger childSize head.right head.found typed
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation evaluated
    obtain ⟨measuredSize, measuredChild⟩ := Staging.Recursive.Size.Expression.of_trace lifted
    cases adapted with
    | rejected origin call reason reached =>
      exact ⟨_, _, _, assignment_fault snapshot measuredChild,
        .rejected origin call reason _ reached⟩
    | completed =>
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, framePreserved, metadata,
          effect, _count, nextTyped, ⟨middleState, _related, nextAdmitted⟩, _continuation⟩ :=
        CellAwareScopeBareAssignmentHeads.preserves_value bridge functions extension transport head bare
          environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
          (preservation runtime covers sameLedger stagedSize) snapshot measured write
      obtain ⟨nextContext, result, finalHeap, restTrace, restAdapted⟩ := remaining
        ⟨_, _, _, environments.extend maps worlds, middleHeaps, locals.mono metadata,
          DataPlaceChildExpressions.prefix_agrees agrees slots, nextTyped, runtime, covers, sameLedger,
          middleState, nextAdmitted, authority.transport effect, physical.transport effect framePreserved,
          owner, sameLocation, ready⟩ tail
      exact ⟨_, _, finalHeap,
        prepend_assignment snapshot measuredChild write restTrace, restAdapted⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceForInitialAssignmentLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareSourceForInitialTreeLifting
/-! Post-header declarations, expression effects and actual ordinary writes
retain the mixed heap. Every branch restores the outer lexical observations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceForInitialTreeLifting
open Core Frontend SourceInference CompatibleEquality GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post restore_post)
open CallableIndexedOwnedAdmittedStagedForPostContracts (restoredOutcome)
open CallableIndexedNamedGeneration (source)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (bindings : ProtectedStateTransition.Bindings protocol)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  (functions : FunctionModel whole.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions whole.indexed))
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations whole.compatible.checked.catalog functions identities)
  {receiving : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial whole.compatible.checked).registry receiving)
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  (compiled : CallableIndexedNamedGeneration.Compilation whole.indexed named diagnostics namedCode)
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) (GeneralizedLocalInstanceValues.model whole.indexed)))
  {faults : RecursiveStageMeaning.FaultRep}
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
  (operandIncluded : ∀ reason token,
    GenericAssignmentDiagnostics.OperandRep compiled.own.assignments reason token → faults (.semantic reason) token)
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}

private theorem member_of_root {source : TypedSource} {binder : TypedBinder}
    (declared : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder) :
    binder ∈ SourceCoreDataPlaces.declaredBinders source := by
  have member : binder ∈ (SourceCoreDataPlaces.declaredBinders source).filter
      (fun actual => decide (actual.id = binder.id)) := by
    rw [CompatibleMatchArmScopes.rootBinder_filter declared]
    exact List.mem_cons_self
  exact (List.mem_filter.mp member).1

variable {test : ExpressionId} {postItems : List ForItemForm} {statements : List StatementId}

include transport extension registered faithful observations in
theorem lifts
    (children : ∀ context, Dynamic.SourceRuntimeValid program context (source named) →
      invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeSourceLiftBounds.LiftsAt bridge context
        (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named registry invocation
        (certificates context) size)
    (preservation : ∀ context, Dynamic.SourceRuntimeValid program context (source named) →
      invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeExpressionBounds.PreservesAt bridge context
        (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named registry invocation
        (certificates context) faults size)
    (sourceEq : invocation.source = source named)
    {administrative : Core.Context} {context finishContext : SourceSemantics.Context}
    {scope finishScope : SourceCoreLocalCell.Scope} {items : List ForItemForm}
    {type : Ty} {code terminal : Expr}
    (tree : CellAwareForHeaderTree.Tree whole.indexed named compiled certificates administrative type
      finishContext finishScope terminal context scope items code)
    (last : CellAwareSourceForInitialBounds.InitializersLifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) (context := finishContext) (scope := finishScope) bridge producer [] test postItems statements) :
    CellAwareSourceForInitialBounds.InitializersLifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) (context := context) (scope := scope) bridge producer items test postItems statements := by
  induction tree with
  | nil => exact last
  | @absent context nextContext scope binder rest body payload
      declaration mono extended ordinary projected allocation annotation same remaining ih =>
    exact CellAwareSourceForInitialAbsentLifting.absent bridge producer registered (body := body)
      (member_of_root declaration) mono extended ordinary projected allocation annotation same sourceEq ih
  | @initialized context nextContext scope binder initializer initializerNode rest lowered body
      declaration mono extended ordinary initializerFound valueType typed certified allocation annotation same remaining ih =>
    exact CellAwareSourceForInitialOrdinaryLifting.initialized bridge producer registered (type := type) (body := body)
      (member_of_root declaration) mono extended ordinary initializerFound valueType typed certified
      allocation annotation same sourceEq (children context) (preservation context) ih
  | @discard context scope expression node rest lowered body found typed certified remaining ih =>
    exact CellAwareSourceForInitialDiscardLifting.lifts bridge producer
      (by simpa only [sourceEq] using found) (by simpa only [sourceEq] using typed) certified
      (children context) (preservation context) ih
  | @assign context scope assignment operator rhs rest body head bare typed operands remaining ih =>
    cases invocation with
    | mk origin actualSource owned stageContext evidence guards =>
      cases sourceEq
      exact CellAwareSourceForInitialAssignmentLifting.lifts bridge functions transport extension producer
        rfl head bare typed (children context) (preservation context) ih

  | @assignProjected context scope assignment operator rhs rest body head projected typed _site remaining ih =>
    cases invocation with
    | mk origin actualSource owned stageContext evidence guards =>
      cases sourceEq
      exact CellAwareSourceForInitialProjectedAssignmentLifting.lifts bridge functions faithful observations transport extension producer
        rfl head projected typed (children context) (preservation context) ih

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceForInitialTreeLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareSourceForLiftBounds
/-! Independent Source for-loop headers use the same reached mixed state as
ordinary statements. Source and native grades are independent. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceForLiftBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)
open SelectedCompilationStageBodyLiftBounds

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)))
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
  {administrative : Core.Context} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}

open CellAwareSourceFlowReadiness (Ready body_prefix body_ready test_value)
open SelectedCompilationStageForLiftBounds (PlainItems ItemsLift PlainFor ForLift)
variable {certificate : GenericExpressionMeaning.Certificate}
  {test : ExpressionId} {node : ExpressionNode} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {testCode loopCode postCode : Expr} {post : List ForItemForm}
variable {environment : Dynamic.Environment} {canonical actual : Environment}
  {actualContext : Core.Context} {embedding : Renaming}

local notation "ReadyAt" => Ready (named := named) (administrative := administrative)
  (invocation := invocation) (context := context) (scope := scope)
  bridge producer environment canonical actual actualContext embedding

def ItemsLifts (items : List ForItemForm) : Prop :=
  ∀ {size : Nat} {environment : Dynamic.Environment} {canonical actual : Environment}
    {actualContext : Core.Context} {embedding : Renaming} {before after : Dynamic.Heap},
    Ready (named := named) (administrative := administrative)
      (invocation := invocation) (context := context) (scope := scope)
      bridge producer environment canonical actual actualContext embedding before →
    ∀ {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome},
      PlainItems program size invocation context environment before items finalContext outcome after →
      ItemsLift program registry invocation context environment before items finalContext outcome after

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceForLiftBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareSourceForLifting
/-! Independent Source for-loop headers use the same reached mixed state as
ordinary statements. Source and native grades are independent. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceForLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)
open SelectedCompilationStageBodyLiftBounds

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)))
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
  {administrative : Core.Context} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}

open CellAwareSourceFlowReadiness (Ready body_prefix body_ready test_value)
open SelectedCompilationStageForLiftBounds (PlainItems ItemsLift PlainFor ForLift)
variable {certificate : GenericExpressionMeaning.Certificate}
  {test : ExpressionId} {node : ExpressionNode} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {testCode loopCode postCode : Expr} {post : List ForItemForm}
variable {environment : Dynamic.Environment} {canonical actual : Environment}
  {actualContext : Core.Context} {embedding : Renaming}

open CellAwareSourceForLiftBounds (ItemsLifts)
open CellAwareSourceWhileLifting (body_continue_ready)

local notation "ReadyAt" => Ready (named := named) (administrative := administrative)
  (invocation := invocation) (context := context) (scope := scope)
  bridge producer environment canonical actual actualContext embedding

theorem post_ready {before after : Dynamic.Heap} {finalContext : SourceSemantics.Context}
    {finalEnvironment : Dynamic.Environment}
    (preservation : ∀ size, CellAwareScopeForPostBounds.PreservesAt bridge context model named producer
      registry invocation faults administrative scope post expected type postCode size)
    (postTyped : ∃ control final, ForItemsHaveType (source named) control context post final)
    (ready : ReadyAt before)
    (trace : Staging.Recursive.ForItems program registry invocation context environment before post
      finalContext (.done finalEnvironment) after) : ReadyAt after := by
  obtain ⟨mapping,world,store,environments,heaps,locals,agrees,actualTyped,runtime,covers,sameLedger,
    initial,admitted,authority,physical,owner,sameLocation,allocationReady⟩ := ready
  obtain ⟨size,measured⟩ := Staging.Recursive.Size.ForItems.of_trace trace
  obtain ⟨_,finalStore,finalMap,finalWorld,_,_,finalHeaps,maps,worlds,preserved,metadata,effect,
    last,_,post⟩ := preservation size environments heaps locals agrees actualTyped runtime covers sameLedger postTyped
      initial admitted authority physical owner sameLocation allocationReady measured
  exact ⟨finalMap,finalWorld,finalStore,environments.extend maps worlds,finalHeaps,
    locals.mono metadata,agrees,actualTyped.weaken worlds,runtime,covers,sameLedger,
    last,post,authority.transport effect,physical.transport effect preserved,owner,sameLocation,allocationReady⟩

theorem post_value {size : Nat} {before after : Dynamic.Heap}
    {finalContext : SourceSemantics.Context} {finalEnvironment : Dynamic.Environment}
    (postLift : ItemsLifts (named := named) (administrative := administrative) (context := context)
      (scope := scope) (registry := registry) (invocation := invocation) bridge producer post)
    (postPreservation : ∀ size, CellAwareScopeForPostBounds.PreservesAt bridge context model named producer
      registry invocation faults administrative scope post expected type postCode size)
    (postTyped : ∃ control final, ForItemsHaveType (source named) control context post final)
    (ready : ReadyAt before)
    (trace : SourceExecutionSize.ForItemsExecute program size context invocation.evidence invocation.source
      environment before post finalContext finalEnvironment after) :
    (∃ failedContext origin call reason reached,
      Staging.Recursive.ForItems program registry invocation context environment before post
        failedContext (.fault (.stage origin call reason)) reached) ∨
    (Staging.Recursive.ForItems program registry invocation context environment before post
      finalContext (.done finalEnvironment) after ∧ ReadyAt after) := by
  obtain ⟨last,staged,reached,lifted,adapted⟩ := postLift ready (.done trace)
  cases staged with
  | done env =>
    cases adapted with
    | completed matched =>
      cases matched
      exact .inr ⟨lifted,post_ready bridge producer postPreservation postTyped ready lifted⟩
  | fault reason =>
    cases adapted with
    | completed matched => cases matched
    | rejected origin call reason finalContext reached =>
      exact .inl ⟨_,origin,call,reason,reached,lifted⟩

theorem for_ready
    (children : ∀ childSize, CellAwareScopeSourceLiftBounds.LiftsAt bridge context model named registry invocation certificate childSize)
    (preservation : ∀ childSize, CellAwareScopeExpressionBounds.PreservesAt
      bridge context model named registry invocation certificate faults childSize)
    (booleans : ∀ {mapping world sourceValue nativeValue},
      model.Represents mapping world .bool sourceValue nativeValue .bool →
      ∃ truth, sourceValue = .bool truth ∧ nativeValue = .bool truth)
    (found : invocation.source.lookupExpression? test = some node)
    (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context test node.type)
    (generated : certificate scope test ⟨.bool, testCode⟩)
    (body : CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope false statements)
    (bodyPreservation : ∀ size, CellAwareScopeFlowBounds.PreservesAt bridge context model named producer registry invocation faults
      administrative scope false statements expected type loopCode size)
    (bodyTyped : ProtectedStateImperativeTypedSourceSites.Statements (source named) context statements)
    (postLift : ItemsLifts (named := named) (administrative := administrative) (context := context)
      (scope := scope) (registry := registry) (invocation := invocation) bridge producer post)
    (postPreservation : ∀ size, CellAwareScopeForPostBounds.PreservesAt bridge context model named producer
      registry invocation faults administrative scope post expected type postCode size)
    (postTyped : ∃ control final, ForItemsHaveType (source named) control context post final)
    {size : Nat} {before after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome}
    (ready : ReadyAt before)
    (trace : PlainFor program size invocation context environment before test post statements outcome after) :
    ForLift program registry invocation context environment before test post statements outcome after := by
  induction size using Nat.strongRecOn generalizing before after outcome with
  | ind size ih =>
    cases trace with
    | control trace =>
      cases trace with
      | done testTrace =>
        rcases test_value bridge producer children preservation booleans found nodeType typed generated ready testTrace with
          stopped | ⟨lifted, _, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .testFault stopped, .rejected origin call reason context reached⟩
        · exact ⟨_, _, .finished lifted, .completed (.fallthrough environment)⟩
      | nextFallthrough testTrace bodyTrace postTrace next =>
        rcases test_value bridge producer children preservation booleans found nodeType typed generated ready testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .testFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge producer body bodyTyped testReady
              (.control bodyTrace)
          cases adaptedBody with
          | rejected origin call reason finalContext reached =>
            exact ⟨_, _, .bodyFailure liftedTest liftedBody, .rejected origin call reason context _⟩
          | completed matched =>
            cases matched
            have bodyReady := body_ready bridge producer bodyPreservation bodyTyped testReady liftedBody
            rcases post_value bridge producer postLift postPreservation postTyped bodyReady postTrace with
              stopped | ⟨liftedPost, nextReady⟩
            · obtain ⟨failedContext, origin, call, reason, reached, stopped⟩ := stopped
              exact ⟨_, reached, .postFailure liftedTest liftedBody stopped,
                .rejected origin call reason context reached⟩
            · obtain ⟨staged, reached, liftedNext, adaptedNext⟩ := ih _
                (SourceExecutionSize.child_lt_stepSize (by simp))
                nextReady (.control next)
              exact ⟨staged, reached, .iterate liftedTest liftedBody liftedPost liftedNext, adaptedNext⟩
      | nextContinue testTrace bodyTrace postTrace next =>
        rcases test_value bridge producer children preservation booleans found nodeType typed generated ready testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .testFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge producer body bodyTyped testReady
              (.control bodyTrace)
          cases adaptedBody with
          | rejected origin call reason finalContext reached =>
            exact ⟨_, _, .bodyFailure liftedTest liftedBody, .rejected origin call reason context _⟩
          | completed matched =>
            cases matched
            have bodyReady := body_continue_ready bridge producer bodyPreservation bodyTyped testReady liftedBody
            rcases post_value bridge producer postLift postPreservation postTyped bodyReady postTrace with
              stopped | ⟨liftedPost, nextReady⟩
            · obtain ⟨failedContext, origin, call, reason, reached, stopped⟩ := stopped
              exact ⟨_, reached, .continuePostFailure liftedTest liftedBody stopped,
                .rejected origin call reason context reached⟩
            · obtain ⟨staged, reached, liftedNext, adaptedNext⟩ := ih _
                (SourceExecutionSize.child_lt_stepSize (by simp))
                nextReady (.control next)
              exact ⟨staged, reached, .continueIterate liftedTest liftedBody liftedPost liftedNext, adaptedNext⟩

      | breaks testTrace bodyTrace =>
        rcases test_value bridge producer children preservation booleans found nodeType typed generated ready testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .testFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge producer body bodyTyped testReady
              (.control bodyTrace)
          cases adaptedBody with
          | rejected origin call reason finalContext reached =>
            exact ⟨_, _, .bodyFailure liftedTest liftedBody, .rejected origin call reason context _⟩
          | completed matched =>
            cases matched
            exact ⟨_, _, .forBreakFromBody liftedTest liftedBody, .completed (.fallthrough environment)⟩
      | returns testTrace bodyTrace =>
        rcases test_value bridge producer children preservation booleans found nodeType typed generated ready testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .testFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge producer body bodyTyped testReady
              (.control bodyTrace)
          cases adaptedBody with
          | rejected origin call reason finalContext reached =>
            exact ⟨_, _, .bodyFailure liftedTest liftedBody, .rejected origin call reason context _⟩
          | completed matched =>
            cases matched
            exact ⟨_, _, .returnedFromBody liftedTest liftedBody, .completed (.returned _)⟩
    | fault trace =>
      cases trace with
      | condition failed =>
        obtain ⟨mapping,world,store,environments,heaps,locals,agrees,actualTyped,_runtime,_covers,_sameLedger,
          initial,admitted,authority,physical,owner,sameLocation,_allocationReady⟩ := ready
        obtain ⟨staged, reached, lifted, adapted⟩ := children _ generated found typed
          environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation (.fault failed)
        cases adapted with
        | completed => exact ⟨_, _, .testFault lifted, .completed (.fault _)⟩
        | rejected origin call reason reached =>
          exact ⟨_, reached, .testFault lifted, .rejected origin call reason context reached⟩
      | conditionType testTrace notBoolean _ =>
        rcases test_value bridge producer children preservation booleans found nodeType typed generated ready testTrace with
          stopped | ⟨_, _, valueTyped⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .testFault stopped, .rejected origin call reason context reached⟩
        · exact False.elim (notBoolean valueTyped)
      | body testTrace bodyTrace =>
        rcases test_value bridge producer children preservation booleans found nodeType typed generated ready testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .testFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge producer body bodyTyped testReady
              (.fault bodyTrace)
          cases adaptedBody with
          | rejected origin call reason finalContext reached =>
            exact ⟨_, _, .bodyFailure liftedTest liftedBody, .rejected origin call reason context _⟩
          | completed matched =>
            cases matched
            exact ⟨_, _, .bodyFailure liftedTest liftedBody, .completed (.fault _)⟩
      | postFallthrough testTrace bodyTrace failed =>
        rcases test_value bridge producer children preservation booleans found nodeType typed generated ready testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .testFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge producer body bodyTyped testReady
              (.control bodyTrace)
          cases adaptedBody with
          | rejected origin call reason finalContext reached =>
            exact ⟨_, _, .bodyFailure liftedTest liftedBody, .rejected origin call reason context _⟩
          | completed matched =>
            cases matched
            have bodyReady := body_ready bridge producer bodyPreservation bodyTyped testReady liftedBody
            obtain ⟨last, stagedPost, reached, liftedPost, adaptedPost⟩ := postLift
              bodyReady (.fault failed)
            cases stagedPost with
            | done env => cases adaptedPost with | completed matched => cases matched
            | fault reason =>
              cases adaptedPost with
              | completed matched =>
                cases matched
                exact ⟨_, _, .postFailure liftedTest liftedBody liftedPost, .completed (.fault _)⟩
              | rejected origin call reason finalContext reached =>
                exact ⟨_, reached, .postFailure liftedTest liftedBody liftedPost,
                  .rejected origin call reason context reached⟩
      | postContinue testTrace bodyTrace failed =>
        rcases test_value bridge producer children preservation booleans found nodeType typed generated ready testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .testFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge producer body bodyTyped testReady
              (.control bodyTrace)
          cases adaptedBody with
          | rejected origin call reason finalContext reached =>
            exact ⟨_, _, .bodyFailure liftedTest liftedBody, .rejected origin call reason context _⟩
          | completed matched =>
            cases matched
            have bodyReady := body_continue_ready bridge producer bodyPreservation bodyTyped testReady liftedBody
            obtain ⟨last, stagedPost, reached, liftedPost, adaptedPost⟩ := postLift
              bodyReady (.fault failed)
            cases stagedPost with
            | done env => cases adaptedPost with | completed matched => cases matched
            | fault reason =>
              cases adaptedPost with
              | completed matched =>
                cases matched
                exact ⟨_, _, .continuePostFailure liftedTest liftedBody liftedPost, .completed (.fault _)⟩
              | rejected origin call reason finalContext reached =>
                exact ⟨_, reached, .continuePostFailure liftedTest liftedBody liftedPost,
                  .rejected origin call reason context reached⟩
      | nextFallthrough testTrace bodyTrace postTrace next =>
        rcases test_value bridge producer children preservation booleans found nodeType typed generated ready testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .testFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge producer body bodyTyped testReady
              (.control bodyTrace)
          cases adaptedBody with
          | rejected origin call reason finalContext reached =>
            exact ⟨_, _, .bodyFailure liftedTest liftedBody, .rejected origin call reason context _⟩
          | completed matched =>
            cases matched
            have bodyReady := body_ready bridge producer bodyPreservation bodyTyped testReady liftedBody
            rcases post_value bridge producer postLift postPreservation postTyped bodyReady postTrace with
              stopped | ⟨liftedPost, nextReady⟩
            · obtain ⟨failedContext, origin, call, reason, reached, stopped⟩ := stopped
              exact ⟨_, reached, .postFailure liftedTest liftedBody stopped,
                .rejected origin call reason context reached⟩
            · obtain ⟨staged, reached, liftedNext, adaptedNext⟩ := ih _
                (SourceExecutionSize.child_lt_stepSize (by simp))
                nextReady (.fault next)
              exact ⟨staged, reached, .iterate liftedTest liftedBody liftedPost liftedNext, adaptedNext⟩
      | nextContinue testTrace bodyTrace postTrace next =>
        rcases test_value bridge producer children preservation booleans found nodeType typed generated ready testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .testFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge producer body bodyTyped testReady
              (.control bodyTrace)
          cases adaptedBody with
          | rejected origin call reason finalContext reached =>
            exact ⟨_, _, .bodyFailure liftedTest liftedBody, .rejected origin call reason context _⟩
          | completed matched =>
            cases matched
            have bodyReady := body_continue_ready bridge producer bodyPreservation bodyTyped testReady liftedBody
            rcases post_value bridge producer postLift postPreservation postTyped bodyReady postTrace with
              stopped | ⟨liftedPost, nextReady⟩
            · obtain ⟨failedContext, origin, call, reason, reached, stopped⟩ := stopped
              exact ⟨_, reached, .continuePostFailure liftedTest liftedBody stopped,
                .rejected origin call reason context reached⟩
            · obtain ⟨staged, reached, liftedNext, adaptedNext⟩ := ih _
                (SourceExecutionSize.child_lt_stepSize (by simp))
                nextReady (.fault next)
              exact ⟨staged, reached, .continueIterate liftedTest liftedBody liftedPost liftedNext, adaptedNext⟩


end Solcore.SourceSemantics.CoreLowering.CellAwareSourceForLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareSourceForInitialTerminal
/-! Independent Source for-loop headers use the same reached mixed state as
ordinary statements. Source and native grades are independent. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceForInitialTerminal
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)
open SelectedCompilationStageBodyLiftBounds

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)))
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
  {administrative : Core.Context} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}

open CellAwareSourceFlowReadiness (Ready body_prefix body_ready test_value)
open SelectedCompilationStageForLiftBounds (PlainItems ItemsLift PlainFor ForLift)
variable {certificate : GenericExpressionMeaning.Certificate}
  {test : ExpressionId} {node : ExpressionNode} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {testCode loopCode postCode : Expr} {post : List ForItemForm}
variable {environment : Dynamic.Environment} {canonical actual : Environment}
  {actualContext : Core.Context} {embedding : Renaming}

open CellAwareSourceForLiftBounds (ItemsLifts)
open CellAwareSourceWhileLifting (body_continue_ready)

local notation "ReadyAt" => Ready (named := named) (administrative := administrative)
  (invocation := invocation) (context := context) (scope := scope)
  bridge producer environment canonical actual actualContext embedding

theorem lifts
    (children : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ childSize, CellAwareScopeSourceLiftBounds.LiftsAt bridge context model named registry invocation certificate childSize)
    (preservation : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ childSize, CellAwareScopeExpressionBounds.PreservesAt
      bridge context model named registry invocation certificate faults childSize)
    (booleans : ∀ {mapping world sourceValue nativeValue},
      model.Represents mapping world .bool sourceValue nativeValue .bool →
      ∃ truth, sourceValue = .bool truth ∧ nativeValue = .bool truth)
    (found : invocation.source.lookupExpression? test = some node)
    (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context test node.type)
    (generated : certificate scope test ⟨.bool, testCode⟩)
    (body : CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope false statements)
    (bodyPreservation : ∀ size, CellAwareScopeFlowBounds.PreservesAt bridge context model named producer registry invocation faults
      administrative scope false statements expected type loopCode size)
    (bodyTyped : ProtectedStateImperativeTypedSourceSites.Statements (source named) context statements)
    (postLift : ItemsLifts (named := named) (administrative := administrative) (context := context)
      (scope := scope) (registry := registry) (invocation := invocation) bridge producer post)
    (postPreservation : ∀ size, CellAwareScopeForPostBounds.PreservesAt bridge context model named producer
      registry invocation faults administrative scope post expected type postCode size)
    (postTyped : ∃ control final, ForItemsHaveType (source named) control context post final)
 : CellAwareSourceForInitialBounds.InitializersLifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) (context := context) (scope := scope)
      bridge producer [] test post statements := by
  intro size environment canonical actual actualContext embedding before after ready outcome trace
  have current := ready
  obtain ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, runtime, covers, sameLedger,
    initial, admitted, authority, physical, owner, sameLocation, allocationReady⟩ := current
  cases trace with
  | initializerFault failed => cases failed
  | loop initial loop =>
    cases initial
    obtain ⟨staged, reached, lifted, adapted⟩ := CellAwareSourceForLifting.for_ready bridge producer
      (children runtime covers sameLedger) (preservation runtime covers sameLedger)
      booleans found nodeType typed generated body bodyPreservation bodyTyped postLift postPreservation postTyped ready loop
    obtain ⟨grade, measured⟩ := Staging.Recursive.Size.ForLoop.of_trace lifted
    refine ⟨_, _, reached, CallableIndexedOwnedAdmittedStagedForHeadContracts.Trace.loop .empty measured, ?_⟩
    cases adapted with
    | completed matched => cases matched <;> exact .completed (by constructor)
    | rejected origin call reason finalContext reached => exact .rejected origin call reason _ _

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceForInitialTerminal
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareSourceForItemsProjectedAssignmentLifting
/-! Independent Source assignment first resolves the original root, then
lifts the real RHS. A completed write supplies the exact mixed state for the
remaining Source flow; an earlier stage rejection retains its reached heap. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceForItemsProjectedAssignmentLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleEquality CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)
open CellAwareSourceForLiftBounds (ItemsLifts)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations compiled.compatible.checked.catalog functions identities)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  {receiving : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
      (GeneralizedLocalInstanceValues.model compiled.indexed)))
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep}

include transport extension faithful observations in
theorem lifts {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {rest : List ForItemForm}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    (sourceEq : invocation.source = source named)
    (head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) invocation.source context
      certificate scope administrative compiled.indexed.layouts.definitions assignment operator rhs)
    (projected : assignment.target.projections ≠ [])
    (assignmentTyped : SourceAssignmentHasType invocation.source context assignment operator rhs)
    (children : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeSourceLiftBounds.LiftsAt bridge context
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
        named stages invocation certificate size)
    (preservation : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeExpressionBounds.PreservesAt bridge context
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
        named stages invocation certificate faults size)
    (remaining : ItemsLifts (named := named) (administrative := administrative)
      (registry := stages) (invocation := invocation) (context := context) (scope := scope) bridge producer rest) :
    ItemsLifts (named := named) (administrative := administrative)
      (registry := stages) (invocation := invocation) (context := context) (scope := scope) bridge producer (.assignValue assignment operator rhs :: rest) := by
  intro size environment canonical actual actualContext embedding before after reachedReady finalContext outcome trace
  obtain ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, runtime, covers, sameLedger,
    initial, admitted, authority, physical, owner, sameLocation, ready⟩ := reachedReady
  have unique : NodeOccurrencesUnique invocation.source := sourceEq.symm ▸ runtime.graph.nodeOccurrencesUnique
  let budget := size + 1
  have within : size ≤ budget := by omega
  have childLift : ∀ childSize, childSize < budget → CellAwareScopeSourceLiftBounds.LiftsAt bridge context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
      named stages invocation certificate childSize := fun childSize _ => children runtime covers sameLedger childSize
  have childMeaning : ∀ childSize, CellAwareScopeExpressionBounds.PreservesAt bridge context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
      named stages invocation certificate faults childSize := preservation runtime covers sameLedger
  have typed := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique head.found assignmentTyped
  obtain ⟨targetType, targetTyped⟩ := CallableIndexedOwnedPlaceAdmission.assignment_target_typed assignmentTyped
  obtain ⟨originalTypes, originalKeyTyped⟩ := CallableIndexedOwnedPlaceAdmission.place_keys_typed targetTyped
  rcases head with ⟨prepared, index, codes, leaf, lowered, rhsNode, invalid, shape, slot, writable, rhsFound, generated, rightView, rightType, profile⟩
  cases shape with
  | bare empty _ => exact (projected empty).elim
  | @projected codes leaf sourceTypes site layout ordinary =>
    let head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) invocation.source context
        certificate scope administrative compiled.indexed.layouts.definitions assignment operator rhs :=
      ⟨prepared, index, codes, leaf, lowered, rhsNode, invalid, .projected layout ordinary,
        slot, writable, rhsFound, generated, rightView, rightType, profile⟩
    have keyTyped := CellAwareScopeProjectedAssignmentHeads.tree_typed layout.children unique originalKeyTyped
    have liftResolved {resolvedTarget : Dynamic.ResolvedPlace} {resolvedHeap : Dynamic.Heap} {resolvedGrade : Nat}
        (resolved : SourceExecutionSize.SourcePlaceResolves program resolvedGrade context invocation.evidence invocation.source
          environment before assignment.target resolvedTarget resolvedHeap) (bounded : resolvedGrade ≤ budget) :=
      CellAwareSourceProjectedResolutionLifting.lifts
                (stages := stages) (faults := faults)
        bridge functions extension transport
        faithful observations budget layout ordinary unique originalKeyTyped childLift childMeaning
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation head.slot head.writable resolved bounded
    rcases SelectedCompilationStageProjectedAssignmentInversion.item_and_tail trace with
      ⟨assignedSize, reason, strict, rfl, rfl, failed⟩ |
      ⟨assignedSize, tailSize, updated, written, strict, tailStrict, assigned, tail⟩
    · cases failed with
      | target failed =>
        rcases SelectedCompilationStageProjectedTargetInversion.failed failed with
          ⟨rfl, rootFault⟩ | ⟨keySize, keyStrict, ready, keysFailed⟩ |
          ⟨keySize, values, keyStrict, ordinaryKeys, getterFault⟩
        · exact ⟨_, _, _, .projectedAssignmentRootFault projected rootFault, .completed (.fault reason)⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := CellAwareScopeSourceSequenceLifting.fault bridge budget
            layout.children unique keyTyped childLift childMeaning environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation
            (by simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using keysFailed)
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
          have keys := lifted
          rw [← Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] at keys
          cases adapted with
          | completed =>
              exact ⟨_, _, _, .projectedAssignmentKeysFault projected ready keys, .completed (.fault reason)⟩
          | rejected origin call reason reached =>
              exact ⟨_, _, _, .projectedAssignmentKeysFault projected ready keys, .rejected origin call reason _ reached⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := CellAwareScopeSourceSequenceLifting.values bridge budget
            layout.children unique keyTyped childLift childMeaning environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation
            (by simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using ordinaryKeys)
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
          have keys := lifted
          rw [← Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] at keys
          cases adapted with
          | completed =>
              exact ⟨_, _, _, .projectedAssignmentGetterFault projected keys getterFault, .completed (.fault reason)⟩
          | rejected origin call reason reached =>
              have ready : Staging.Recursive.ProjectedTarget.RootReady environment before assignment.target := by
                cases getterFault <;> exact .intro (by assumption) (by assumption)
              exact ⟨_, _, _, .projectedAssignmentKeysFault projected ready keys, .rejected origin call reason _ reached⟩
      | rhs resolved evaluated =>
        rcases liftResolved resolved
          (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega) with
          ⟨origin, call, reason, reached, ready, keys⟩ |
          ⟨sources, keys, snapshot, _keyValues, resolution, getterState, _getterRelated, getterAdmission⟩
        · exact ⟨_, _, _, .projectedAssignmentKeysFault projected ready keys, .rejected origin call reason _ reached⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := childLift _
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
            head.right head.found typed (environments.extend resolution.maps resolution.worlds)
            resolution.heaps (locals.mono resolution.metadata) agrees (actualTyped.weaken resolution.worlds)
            getterState getterAdmission (authority.transport resolution.effect)
              (physical.transport resolution.effect resolution.frame) owner sameLocation (.fault evaluated)
          cases adapted with
          | rejected origin call reason reached =>
              exact ⟨_, _, _, .projectedAssignmentRhsFault projected keys snapshot lifted, .rejected origin call reason _ reached⟩
          | completed =>
              exact ⟨_, _, _, .projectedAssignmentRhsFault projected keys snapshot lifted, .completed (.fault reason)⟩
      | operands resolved evaluated currentRead rootType initialValue pathRead invalid =>
        rcases liftResolved resolved
          (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega) with
          ⟨origin, call, reason, reached, ready, keys⟩ |
          ⟨sources, keys, snapshot, _keyValues, resolution, getterState, _getterRelated, getterAdmission⟩
        · exact ⟨_, _, _, .projectedAssignmentKeysFault projected ready keys, .rejected origin call reason _ reached⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := childLift _
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
            head.right head.found typed (environments.extend resolution.maps resolution.worlds)
            resolution.heaps (locals.mono resolution.metadata) agrees (actualTyped.weaken resolution.worlds)
            getterState getterAdmission (authority.transport resolution.effect)
              (physical.transport resolution.effect resolution.frame) owner sameLocation (.value evaluated)
          cases adapted with
          | rejected origin call reason reached =>
              exact ⟨_, _, _, .projectedAssignmentRhsFault projected keys snapshot lifted, .rejected origin call reason _ reached⟩
          | completed =>
              exact ⟨_, _, _, .projectedAssignmentWriteFault projected keys snapshot lifted (.operands currentRead rootType initialValue pathRead invalid), .completed (.fault (.invalidAssignmentOperands operator))⟩
      | structuralUpdate resolved evaluated currentRead rootType initialValue pathFault =>
        rcases liftResolved resolved
          (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega) with
          ⟨origin, call, reason, reached, ready, keys⟩ |
          ⟨sources, keys, snapshot, _keyValues, resolution, getterState, _getterRelated, getterAdmission⟩
        · exact ⟨_, _, _, .projectedAssignmentKeysFault projected ready keys, .rejected origin call reason _ reached⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := childLift _
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
            head.right head.found typed (environments.extend resolution.maps resolution.worlds)
            resolution.heaps (locals.mono resolution.metadata) agrees (actualTyped.weaken resolution.worlds)
            getterState getterAdmission (authority.transport resolution.effect)
              (physical.transport resolution.effect resolution.frame) owner sameLocation (.value evaluated)
          cases adapted with
          | rejected origin call reason reached =>
              exact ⟨_, _, _, .projectedAssignmentRhsFault projected keys snapshot lifted, .rejected origin call reason _ reached⟩
          | completed =>
              exact ⟨_, _, _, .projectedAssignmentWriteFault projected keys snapshot lifted (.structural currentRead rootType initialValue pathFault), .completed (.fault reason)⟩
    · cases assigned with
      | intro resolved evaluated write =>
        rcases liftResolved resolved
          (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega) with
          ⟨origin, call, reason, reached, ready, keys⟩ |
          ⟨sources, keys, snapshot, _keyValues, resolution, getterState, _getterRelated, getterAdmission⟩
        · exact ⟨_, _, _, .projectedAssignmentKeysFault projected ready keys, .rejected origin call reason _ reached⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := childLift _
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
            head.right head.found typed (environments.extend resolution.maps resolution.worlds)
            resolution.heaps (locals.mono resolution.metadata) agrees (actualTyped.weaken resolution.worlds)
            getterState getterAdmission (authority.transport resolution.effect)
              (physical.transport resolution.effect resolution.frame) owner sameLocation (.value evaluated)
          cases adapted with
          | rejected origin call reason reached =>
              exact ⟨_, _, _, .projectedAssignmentRhsFault projected keys snapshot lifted, .rejected origin call reason _ reached⟩
          | completed =>
            obtain ⟨keyStageSize, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
            obtain ⟨rhsStageSize, measuredRhs⟩ := Staging.Recursive.Size.Expression.of_trace lifted
            obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, framePreserved, metadata,
                effect, _count, nextTyped, ⟨middleState, _related, nextAdmitted⟩, _continuation⟩ :=
              CellAwareScopeProjectedAssignmentHeads.preserves_value
                                (stages := stages) (faults := faults)
                bridge functions extension transport
                faithful observations head projected environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
                (keyStageSize + rhsStageSize + 1) (fun n _ => childMeaning n)
                measuredKeys (by omega) snapshot measuredRhs (by omega) write
            obtain ⟨nextContext, result, finalHeap, restTrace, restAdapted⟩ := remaining
              ⟨_, _, _, environments.extend maps worlds, middleHeaps,
                locals.mono metadata, DataPlaceChildExpressions.prefix_agrees agrees slots, nextTyped,
                runtime, covers, sameLedger, middleState, nextAdmitted,
                authority.transport effect, physical.transport effect framePreserved, owner, sameLocation, ready⟩ tail
            exact ⟨nextContext, result, finalHeap,
              .projectedAssignment projected keys snapshot lifted write restTrace, restAdapted⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceForItemsProjectedAssignmentLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareSourceForItemsAbsentLifting
/-! An original uninitialized declaration lifts through its actual absent
cell allocation. The independently executed suffix starts at that exact heap,
with every earlier generalized descriptor still retained. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceForItemsAbsentLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)
open CellAwareSourceForLiftBounds (ItemsLifts)
open TypedLexicalControl (absentRequest)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)))
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep}


include registered in
theorem absent {context nextContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {binder : TypedBinder} {rest : List ForItemForm}
    {payload : Ty} {body : Expr} {administrative : Core.Context}
    (member : binder ∈ SourceCoreDataPlaces.declaredBinders (source named))
    (mono : binder.scheme.quantified = [])
    (extended : BinderExtends (source named).owner context binder nextContext)
    (ordinary : (source named).inputs.any (fun input => decide (input.id = binder.id)) = false)
    (projection : projects binder.scheme.body payload)
    (allocation : SourceCoreAllocationLayouts.Allocation whole.indexed.layouts named.signature.key []
      (absentRequest (source named) scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated whole.indexed.ancestry.layout.frame
      whole.indexed.base.globals.length
      (whole.indexed.layouts.allocatorAt named.signature.key [] (fun error => .sourceAllocation (reprStr error)))
      (absentRequest (source named) scope binder payload))
    (same : annotation.original = allocation.expression)
    (sourceEq : invocation.source = source named)
    (remaining : ItemsLifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) (context := nextContext) (scope := ((binder.id, payload) :: scope)) bridge producer rest) :
    ItemsLifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) (context := context) (scope := scope) bridge producer (.letDecl binder none :: rest) := by
  intro size environment canonical actual actualContext embedding before after reachedReady finalContext outcome trace
  obtain ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, runtime, covers, sameLedger,
    current, admitted, authority, physical, owner, sameLocation, ready⟩ := reachedReady
  obtain ⟨tailSize, location, bound, _smaller, allocated, tail⟩ :=
    SelectedCompilationStageForItemsSourceInversion.absent mono
      (by simpa only [sourceEq] using extended) trace
  obtain ⟨marker, _agreement, _smaller, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
      _preserved, _allocationEffect, nextAuthority, reachedState, _related, nextAdmitted, nextPhysical, locationEq, nativeEq⟩ :=
    CellAwareNamedAbsentPrefix.complete bridge mono member extended ordinary allocation annotation same producer registered
      projection environments heaps locals agrees actualTyped current admitted authority physical
      (ready current physical.read) allocated body
  have nextReady : ProtectedStateTransition.CellAllocation.ReadyAt producer nextPhysical.location nextPhysical.native := by
    intro index current stored
    have previous := ready current (by simpa only [locationEq, nativeEq] using stored)
    simpa only [locationEq, nativeEq] using previous
  obtain ⟨resultContext, resultOutcome, resultHeap, stagedTail, tailAdapted⟩ :=
    remaining ⟨_, _, _, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
      runtime.transport (.ofBinderExtends extended),
      (Dynamic.RuntimeContextFields.ofBinderExtends extended).covers covers,
      (Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans sameLedger,
      reachedState, nextAdmitted, nextAuthority, nextPhysical, owner, sameLocation.trans locationEq.symm, nextReady⟩ tail
  exact ⟨resultContext, resultOutcome, resultHeap,
    .absent mono (by simpa only [sourceEq] using extended) allocated stagedTail, tailAdapted⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceForItemsAbsentLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareSourceForItemsOrdinaryLifting
/-! A real ordinary Source initializer is lifted before allocation. A failed
or rejected child keeps its reached heap, and successful allocation retains
all earlier generalized descriptors for the actual Source suffix. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceForItemsOrdinaryLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)
open CellAwareSourceForLiftBounds (ItemsLifts)
open TypedLexicalWhile (initializedRequest sequence)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)))
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep}


include registered in
theorem initialized {context nextContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {binder : TypedBinder} {initializer : ExpressionId}
    {initializerNode : ExpressionNode} {rest : List ForItemForm} {type : Ty}
    {lowered : SourceCoreBasic.LoweredExpr} {body : Expr} {administrative : Core.Context}
      (member : binder ∈ SourceCoreDataPlaces.declaredBinders (source named))
      (mono : binder.scheme.quantified = [])
      (extended : BinderExtends (source named).owner context binder nextContext)
      (ordinary : (source named).inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : (source named).lookupExpression? initializer = some initializerNode)
      (valueType : initializerNode.type = binder.scheme.body)
      (typed : ExpressionHasType (source named) context initializer initializerNode.type)
      (value : certificates context scope initializer lowered)
      (allocation : SourceCoreAllocationLayouts.Allocation whole.indexed.layouts named.signature.key []
        (initializedRequest (source named) scope binder lowered.type))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated whole.indexed.ancestry.layout.frame
        whole.indexed.base.globals.length
        (whole.indexed.layouts.allocatorAt named.signature.key [] (fun error => .sourceAllocation (reprStr error)))
        (initializedRequest (source named) scope binder lowered.type))
      (same : annotation.original = allocation.expression)
    (sourceEq : invocation.source = source named)
    (childLift : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeSourceLiftBounds.LiftsAt bridge context model named registry invocation (certificates context) size)
    (preservation : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeExpressionBounds.PreservesAt bridge context model named registry invocation (certificates context) faults size)
    (remaining : ItemsLifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) (context := nextContext) (scope := ((binder.id, lowered.type) :: scope)) bridge producer rest) :
    ItemsLifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) (context := context) (scope := scope) bridge producer (.letDecl binder (some initializer) :: rest) := by
  intro size environment canonical actual actualContext embedding before after reachedReady finalContext outcome trace
  obtain ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, runtime, covers, sameLedger,
    current, admitted, authority, physical, owner, sameLocation, ready⟩ := reachedReady
  rcases SelectedCompilationStageForItemsSourceInversion.initialized mono
      (by simpa only [sourceEq] using extended) trace with
    ⟨childSize, reason, _strict, contextEq, outcomeEq, child⟩ |
    ⟨childSize, tailSize, sourceValue, middle, location, bound, _childStrict, _tailStrict, child, allocated, tail⟩
  · subst finalContext
    subst outcome
    obtain ⟨staged, reached, lifted, adapted⟩ := childLift runtime covers sameLedger childSize value
      (by simpa only [sourceEq] using initializerFound) (by simpa only [sourceEq] using typed)
      environments heaps locals agrees actualTyped current admitted authority physical owner sameLocation child
    cases adapted with
    | completed => exact ⟨_, _, _, .initializerFault mono lifted, .completed (.fault reason)⟩
    | rejected origin call reason reached => exact ⟨_, _, _, .initializerFault mono lifted, .rejected origin call reason _ reached⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ := childLift runtime covers sameLedger childSize value
      (by simpa only [sourceEq] using initializerFound) (by simpa only [sourceEq] using typed)
      environments heaps locals agrees actualTyped current admitted authority physical owner sameLocation child
    cases adapted with
    | rejected origin call reason reached => exact ⟨_, _, _, .initializerFault mono lifted, .rejected origin call reason _ reached⟩
    | completed =>
      obtain ⟨stageSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      obtain ⟨native, middleStore, middleMap, middleWorld, evaluated, represented, middleHeaps,
          maps, worlds, frame, metadata, effect, middleState, _expressionRelated, post⟩ :=
        preservation runtime covers sameLedger stageSize value
          (by simpa only [sourceEq] using initializerFound) (by simpa only [sourceEq] using typed)
          environments heaps locals agrees actualTyped current admitted authority physical owner sameLocation measured
      cases represented with
      | value payload =>
        let middlePhysical := physical.transport effect frame
        obtain ⟨marker, _agreement, _smaller, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
            _preserved, _allocationEffect, nextAuthority, reachedState, _related, nextAdmitted, nextPhysical, locationEq, nativeEq⟩ :=
          CellAwareNamedOrdinaryPrefix.complete bridge mono member extended ordinary allocation annotation same producer registered
            evaluated (valueType ▸ payload) (valueType ▸ post.at_value.1)
            (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
            middleState post.at_value.2 (authority.transport effect) middlePhysical
            (ready middleState middlePhysical.read) allocated type body
        have nextReady : ProtectedStateTransition.CellAllocation.ReadyAt producer nextPhysical.location nextPhysical.native := by
          intro index current stored
          have previous := ready current (by simpa only [locationEq, nativeEq, middlePhysical,
            CellAwareScopePhysical.Physical.transport_location, CellAwareScopePhysical.Physical.transport_native] using stored)
          simpa only [locationEq, nativeEq, middlePhysical, CellAwareScopePhysical.Physical.transport_location,
            CellAwareScopePhysical.Physical.transport_native] using previous
        obtain ⟨resultContext, resultOutcome, resultHeap, stagedTail, tailAdapted⟩ :=
          remaining ⟨_, _, _, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
      runtime.transport (.ofBinderExtends extended),
      (Dynamic.RuntimeContextFields.ofBinderExtends extended).covers covers,
      (Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans sameLedger,
      reachedState, nextAdmitted, nextAuthority, nextPhysical, owner, sameLocation.trans locationEq.symm, nextReady⟩ tail
        exact ⟨resultContext, resultOutcome, resultHeap,
          .initialized mono (by simpa only [sourceEq] using extended) lifted allocated stagedTail, tailAdapted⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceForItemsOrdinaryLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareSourceForItemsDiscardLifting
/-! A real return or tail expression preserves the ordinary Source outcome,
or propagates its actual earlier stage rejection. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceForItemsDiscardLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)
open CellAwareSourceForLiftBounds (ItemsLifts)
open CallableIndexedOwnedAdmittedStagedScopedTerminalStatements (Head)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)))
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {context : SourceSemantics.Context} {certificates : GenericExpressionMeaning.Certificate}

variable {faults : RecursiveStageMeaning.FaultRep}

theorem lifts {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {rest : List ForItemForm}
    {expression : ExpressionId} {expressionNode : ExpressionNode}
    {lowered : SourceCoreBasic.LoweredExpr}
    (expressionFound : invocation.source.lookupExpression? expression = some expressionNode)
    (typed : ExpressionHasType invocation.source context expression expressionNode.type)
    (generated : certificates scope expression lowered)
    (children : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeSourceLiftBounds.LiftsAt bridge context model named registry invocation certificates size)
    (preservation : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeExpressionBounds.PreservesAt bridge context model named registry invocation certificates faults size)
    (remaining : ItemsLifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) (context := context) (scope := scope) bridge producer rest) :
    ItemsLifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) (context := context) (scope := scope) bridge producer (.expression expression :: rest) := by
  intro size environment canonical actual actualContext embedding before after reachedReady finalContext outcome trace
  obtain ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, runtime, covers, sameLedger,
    initial, admitted, authority, physical, owner, sameLocation, ready⟩ := reachedReady
  rcases SelectedCompilationStageForItemsSourceInversion.discard trace with
    ⟨childSize, reason, _strict, rfl, rfl, evaluated⟩ |
    ⟨childSize, tailSize, sourceValue, middle, _strict, _tailStrict, evaluated, tail⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children runtime covers sameLedger childSize generated expressionFound typed
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation evaluated
    cases adapted with
    | completed => exact ⟨_, _, _, .expressionFailure lifted,
        .completed (.fault reason)⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, _, .expressionFailure lifted,
        .rejected origin call reason _ reached⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children runtime covers sameLedger childSize generated expressionFound typed
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation evaluated
    cases adapted with
    | rejected origin call reason reached =>
      exact ⟨_, _, _, .expressionFailure lifted,
        .rejected origin call reason _ reached⟩
    | completed =>
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      obtain ⟨_value, middleStore, middleMap, middleWorld, _evaluated, _represented, middleHeaps,
          maps, worlds, framePreserved, metadata, effect, middleState, _related, post⟩ :=
        preservation runtime covers sameLedger stagedSize generated expressionFound typed environments heaps locals agrees actualTyped
          initial admitted authority physical owner sameLocation measured
      obtain ⟨nextContext, result, finalHeap, restTrace, restAdapted⟩ := remaining
        ⟨_, _, _, environments.extend maps worlds, middleHeaps, locals.mono metadata, agrees, actualTyped.weaken worlds,
          runtime, covers, sameLedger, middleState, post.at_value.2,
          authority.transport effect, physical.transport effect framePreserved, owner, sameLocation, ready⟩ tail
      exact ⟨nextContext, result, finalHeap, .expression lifted restTrace, restAdapted⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceForItemsDiscardLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareSourceForItemsAssignmentLifting
/-! Independent Source assignment first resolves the original root, then
lifts the real RHS. A completed write supplies the exact mixed state for the
remaining Source flow; an earlier stage rejection retains its reached heap. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceForItemsAssignmentLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)
open CellAwareSourceForLiftBounds (ItemsLifts)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  {receiving : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
      (GeneralizedLocalInstanceValues.model compiled.indexed)))
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep}

include transport extension in
theorem lifts {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {rest : List ForItemForm}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    (sourceEq : invocation.source = source named)
    (head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) invocation.source context
      certificate scope administrative compiled.indexed.layouts.definitions assignment operator rhs)
    (bare : assignment.target.projections = [])
    (assignmentTyped : SourceAssignmentHasType invocation.source context assignment operator rhs)
    (children : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeSourceLiftBounds.LiftsAt bridge context
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
        named stages invocation certificate size)
    (preservation : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeExpressionBounds.PreservesAt bridge context
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
        named stages invocation certificate faults size)
    (remaining : ItemsLifts (named := named) (administrative := administrative)
      (registry := stages) (invocation := invocation) (context := context) (scope := scope) bridge producer rest) :
    ItemsLifts (named := named) (administrative := administrative)
      (registry := stages) (invocation := invocation) (context := context) (scope := scope) bridge producer (.assignValue assignment operator rhs :: rest) := by
  intro size environment canonical actual actualContext embedding before after reachedReady finalContext outcome trace
  obtain ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, runtime, covers, sameLedger,
    initial, admitted, authority, physical, owner, sameLocation, ready⟩ := reachedReady
  have unique : NodeOccurrencesUnique invocation.source := sourceEq.symm ▸ runtime.graph.nodeOccurrencesUnique
  have typed := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique head.found assignmentTyped
  obtain ⟨target, snapshot⟩ := CellAwareScopeBareAssignmentHeads.target_snapshot
    (invocation := invocation) bridge functions extension head bare environments heaps locals agrees initial admitted
  rcases SelectedCompilationStageForItemsAssignmentInversion.child_and_tail snapshot trace with
    ⟨childSize, reason, _strict, rfl, rfl, evaluated⟩ |
    ⟨childSize, sourceValue, currentCell, initialValue, currentSelected, _strict, rfl, rfl, evaluated,
      currentRead, rootType, rootInitial, pathRead, invalid⟩ |
    ⟨childSize, tailSize, sourceValue, middle, updated, written, _strict, _tailStrict, evaluated, write, tail⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children runtime covers sameLedger childSize head.right head.found typed
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation evaluated
    cases adapted with
    | completed => exact ⟨_, _, _, .assignmentFailure snapshot lifted,
        .completed (.fault reason)⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, _, .assignmentFailure snapshot lifted,
        .rejected origin call reason _ reached⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children runtime covers sameLedger childSize head.right head.found typed
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation evaluated
    cases adapted with
    | completed => exact ⟨_, _, _, .assignmentOperands snapshot lifted
        currentRead rootType rootInitial pathRead invalid, .completed (.fault (.invalidAssignmentOperands operator))⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, _, .assignmentFailure snapshot lifted, .rejected origin call reason _ reached⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children runtime covers sameLedger childSize head.right head.found typed
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation evaluated
    cases adapted with
    | rejected origin call reason reached =>
      exact ⟨_, _, _, .assignmentFailure snapshot lifted,
        .rejected origin call reason _ reached⟩
    | completed =>
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, framePreserved, metadata,
          effect, _count, nextTyped, ⟨middleState, _related, nextAdmitted⟩, _continuation⟩ :=
        CellAwareScopeBareAssignmentHeads.preserves_value bridge functions extension transport head bare
          environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
          (preservation runtime covers sameLedger stagedSize) snapshot measured write
      obtain ⟨nextContext, result, finalHeap, restTrace, restAdapted⟩ := remaining
        ⟨_, _, _, environments.extend maps worlds, middleHeaps, locals.mono metadata,
          DataPlaceChildExpressions.prefix_agrees agrees slots, nextTyped, runtime, covers, sameLedger,
          middleState, nextAdmitted, authority.transport effect, physical.transport effect framePreserved,
          owner, sameLocation, ready⟩ tail
      exact ⟨nextContext, result, finalHeap,
        .assignment snapshot lifted write restTrace, restAdapted⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceForItemsAssignmentLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareSourceForHeaderLifting
/-! Post-header declarations, expression effects and actual ordinary writes
retain the mixed heap. Every branch restores the outer lexical observations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceForHeaderLifting
open Core Frontend SourceInference CompatibleEquality GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post restore_post)
open CallableIndexedOwnedAdmittedStagedForPostContracts (restoredOutcome)
open CallableIndexedNamedGeneration (source)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (bindings : ProtectedStateTransition.Bindings protocol)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  (functions : FunctionModel whole.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions whole.indexed))
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations whole.compatible.checked.catalog functions identities)
  {receiving : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial whole.compatible.checked).registry receiving)
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  (compiled : CallableIndexedNamedGeneration.Compilation whole.indexed named diagnostics namedCode)
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) (GeneralizedLocalInstanceValues.model whole.indexed)))
  {faults : RecursiveStageMeaning.FaultRep}
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
  (operandIncluded : ∀ reason token,
    GenericAssignmentDiagnostics.OperandRep compiled.own.assignments reason token → faults (.semantic reason) token)
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}

private theorem member_of_root {source : TypedSource} {binder : TypedBinder}
    (declared : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder) :
    binder ∈ SourceCoreDataPlaces.declaredBinders source := by
  have member : binder ∈ (SourceCoreDataPlaces.declaredBinders source).filter
      (fun actual => decide (actual.id = binder.id)) := by
    rw [CompatibleMatchArmScopes.rootBinder_filter declared]
    exact List.mem_cons_self
  exact (List.mem_filter.mp member).1

include transport extension registered faithful observations in
theorem lifts
    (children : ∀ context, Dynamic.SourceRuntimeValid program context (source named) →
      invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeSourceLiftBounds.LiftsAt bridge context
        (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named registry invocation
        (certificates context) size)
    (preservation : ∀ context, Dynamic.SourceRuntimeValid program context (source named) →
      invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeExpressionBounds.PreservesAt bridge context
        (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named registry invocation
        (certificates context) faults size)
    (sourceEq : invocation.source = source named)
    {administrative : Core.Context} {context finishContext : SourceSemantics.Context}
    {scope finishScope : SourceCoreLocalCell.Scope} {items : List ForItemForm}
    {type : Ty} {code terminal : Expr}
    (tree : CellAwareForHeaderTree.Tree whole.indexed named compiled certificates administrative type
      finishContext finishScope terminal context scope items code) :
    CellAwareSourceForLiftBounds.ItemsLifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) (context := context) (scope := scope) bridge producer items := by
  induction tree with
  | nil =>
    intro size environment canonical actual actualContext embedding before after _ready finalContext outcome trace
    cases trace with
    | done trace => cases trace; exact ⟨_, _, _, .empty, .completed (.fallthrough environment)⟩
    | fault trace => cases trace
  | @absent context nextContext scope binder rest body payload
      declaration mono extended ordinary projected allocation annotation same remaining ih =>
    exact CellAwareSourceForItemsAbsentLifting.absent bridge producer registered (body := body)
      (member_of_root declaration) mono extended ordinary projected allocation annotation same sourceEq ih
  | @initialized context nextContext scope binder initializer initializerNode rest lowered body
      declaration mono extended ordinary initializerFound valueType typed certified allocation annotation same remaining ih =>
    exact CellAwareSourceForItemsOrdinaryLifting.initialized bridge producer registered (type := type) (body := body)
      (member_of_root declaration) mono extended ordinary initializerFound valueType typed certified
      allocation annotation same sourceEq (children context) (preservation context) ih
  | @discard context scope expression node rest lowered body found typed certified remaining ih =>
    exact CellAwareSourceForItemsDiscardLifting.lifts bridge producer
      (by simpa only [sourceEq] using found) (by simpa only [sourceEq] using typed) certified
      (children context) (preservation context) ih
  | @assign context scope assignment operator rhs rest body head bare typed operands remaining ih =>
    cases invocation with
    | mk origin actualSource owned stageContext evidence guards =>
      cases sourceEq
      exact CellAwareSourceForItemsAssignmentLifting.lifts bridge functions transport extension producer
        rfl head bare typed (children context) (preservation context) ih

  | @assignProjected context scope assignment operator rhs rest body head projected typed _site remaining ih =>
    cases invocation with
    | mk origin actualSource owned stageContext evidence guards =>
      cases sourceEq
      exact CellAwareSourceForItemsProjectedAssignmentLifting.lifts bridge functions faithful observations transport extension producer
        rfl head projected typed (children context) (preservation context) ih

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceForHeaderLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareSourceWhileSequenceLifting
/-! Ordinary Source conditions and exactly the selected branch reach the same
mixed physical continuation. Genuine earlier stage rejection retains its
actual heap and bypasses the remaining branch and suffix. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceWhileSequenceLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageBodyLiftBounds SelectedCompilationStageScopedLiftBounds
open CallableIndexedNamedGeneration (source)
open CellAwareSourceFlowReadiness (Ready body_prefix body_ready test_value)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)))
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}

open SelectedCompilationStageWhileLifting (PlainWhile WhileLift)
variable (transport : ProtectedStateTransition.AdministrativeTransport protocol)

include transport in
/-- The actual while head and the reached suffix share one mixed caller state. -/
theorem lifts {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {mode : Bool} {id : StatementId} {rest statements : List StatementId}
    {statement : StatementNode} {test : ExpressionId} {node : ExpressionNode}
    {testCode loopCode : Expr} {certificate : GenericExpressionMeaning.Certificate}
    {expected : TypeSystem.Ty} {type : Ty} {selfReason : Word}
    (sourceEq : invocation.source = source named)
    (booleans : ∀ {mapping world sourceValue nativeValue},
      model.Represents mapping world .bool sourceValue nativeValue .bool →
      ∃ truth, sourceValue = .bool truth ∧ nativeValue = .bool truth)
    (statementFound : invocation.source.lookupStatement? id = some statement)
    (form : statement.form = .whileLoop test statements)
    (found : invocation.source.lookupExpression? test = some node) (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context test node.type)
    (generated : certificate scope test ⟨.bool,testCode⟩)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type testCode loopCode selfReason) (LocalLoop.resultType type) whole.indexed.layouts.definitions)
    (children : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeSourceLiftBounds.LiftsAt bridge context model named registry invocation certificate size)
    (preservation : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeExpressionBounds.PreservesAt bridge context model named registry invocation certificate faults size)
    (body : CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope false statements)
    (bodyPreservation : ∀ size, CellAwareScopeFlowBounds.PreservesAt bridge context model named producer registry invocation faults
      administrative scope false statements expected type loopCode size)
    (remaining : CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope mode rest) :
    CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope mode (id :: rest) := by
  intro size mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation allocationReady finalContext outcome after trace
  have unique : NodeOccurrencesUnique invocation.source := sourceEq.symm ▸ runtime.graph.nodeOccurrencesUnique
  have ready : Ready (named := named) (administrative := administrative) (invocation := invocation)
      (context := context) (scope := scope) bridge producer environment canonical actual actualContext embedding before :=
    ⟨mapping,world,store,environments,heaps,locals,agrees,actualTyped,runtime,covers,sameLedger,
      initial,admitted,authority,physical,owner,sameLocation,allocationReady⟩
  have bodyTyped := (CallableIndexedOwnedPreparedStagedScopedWhileSourceTyping.children
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ statementFound) form).2
  have suffixTyped := CallableIndexedOwnedPreparedStagedScopedWhileSourceTyping.suffix
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ statementFound) form
  have children := children runtime covers sameLedger
  have preservation := preservation runtime covers sameLedger
  have lift {n : Nat} {plain : Dynamic.ControlOutcome} {reached : Dynamic.Heap}
      (loop : PlainWhile program n invocation context environment before test statements plain reached) :
      WhileLift program registry invocation context environment before test statements plain reached :=
    CellAwareSourceWhileLifting.while_ready bridge producer children preservation booleans found nodeType typed generated
      body bodyPreservation bodyTyped ready loop
  rcases SelectedCompilationStageScopedSourceInversion.head_and_tail unique statementFound
    (by intro expression equal; rw [form] at equal; cases equal) trace with
    ⟨headSize, reason, _headSmaller, rfl, rfl, failed⟩ |
    ⟨headSize, _headSmaller, terminal, executed⟩ |
    ⟨headSize, tailSize, middleContext, nextEnvironment, middle, _headSmaller, _tailSmaller, executed, tail⟩
  · obtain ⟨loopSize, _loopSmaller, loop⟩ := SelectedCompilationStageWhileSourceInversion.fault unique statementFound form failed
    obtain ⟨staged, reached, lifted, adapted⟩ := lift loop
    cases adapted with
    | completed matched =>
      cases matched
      exact ⟨_, _, _, .whileFault (lookupStatement?_sound statementFound) form lifted, .completed (.fault reason)⟩
    | rejected origin call reason finalContext reached =>
      exact ⟨_, _, _, .whileFault (lookupStatement?_sound statementFound) form lifted,
        .rejected origin call reason _ _⟩
  · obtain ⟨loopSize, _loopSmaller, rfl, loop⟩ := SelectedCompilationStageWhileSourceInversion.control unique statementFound form executed
    obtain ⟨staged, reached, lifted, adapted⟩ := lift loop
    cases adapted with
    | rejected origin call reason finalContext reached =>
      exact ⟨_, _, _, .whileFault (lookupStatement?_sound statementFound) form lifted,
        .rejected origin call reason _ _⟩
    | completed matched =>
      cases matched with
      | breaking innerEnvironment => exact ((SelectedCompilationStageLoopOutcomes.while_closed_of_trace lifted).1 innerEnvironment rfl).elim
      | continuing innerEnvironment => exact ((SelectedCompilationStageLoopOutcomes.while_closed_of_trace lifted).2 innerEnvironment rfl).elim
      | returned value =>
        exact ⟨_, _, _, .whileReturned (lookupStatement?_sound statementFound) form lifted, .completed (.returned value)⟩
      | fault reason =>
        exact ⟨_, _, _, .whileFault (lookupStatement?_sound statementFound) form lifted, .completed (.fault reason)⟩
      | fallthrough innerEnvironment =>
        cases SelectedCompilationStageWhileSourceInversion.fallthrough_environment loop
        rcases terminal with terminal | rfl
        · cases terminal
        · exact ⟨_, _, _, .whileFallthrough (lookupStatement?_sound statementFound) form lifted .nil,
            .completed (.fallthrough environment)⟩
  · obtain ⟨loopSize, _loopSmaller, rfl, loop⟩ := SelectedCompilationStageWhileSourceInversion.control unique statementFound form executed
    cases SelectedCompilationStageWhileSourceInversion.fallthrough_environment loop
    obtain ⟨staged, reached, lifted, adapted⟩ := lift loop
    cases adapted with
    | rejected origin call reason finalContext reached =>
      exact ⟨_, _, _, .whileFault (lookupStatement?_sound statementFound) form lifted,
        .rejected origin call reason _ _⟩
    | completed matched =>
      cases matched
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.While.of_trace lifted
      obtain ⟨_, finalStore, finalMap, finalWorld, _, _, finalHeaps, maps, worlds, preserved, metadata, effect,
        last, _, post⟩ := CellAwareLoopHeads.preserves bridge model producer transport booleans
          (fun n _ => preservation n) found nodeType typed generated nativeTyped (fun n _ => bodyPreservation n)
          (Nat.le_refl stagedSize) environments heaps locals agrees actualTyped runtime covers sameLedger bodyTyped
          initial admitted authority physical owner sameLocation allocationReady measured
      obtain ⟨tailContext, tailOutcome, tailHeap, liftedTail, adaptedTail⟩ := remaining
        (environments.extend maps worlds) finalHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
        runtime covers sameLedger suffixTyped last post (authority.transport effect) (physical.transport effect preserved)
        owner sameLocation allocationReady tail
      exact ⟨tailContext, tailOutcome, tailHeap,
        .whileFallthrough (lookupStatement?_sound statementFound) form lifted liftedTail, adaptedTail⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceWhileSequenceLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowAssignmentLifting
/-! Independent Source assignment first resolves the original root, then
lifts the real RHS. A completed write supplies the exact mixed state for the
remaining Source flow; an earlier stage rejection retains its reached heap. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowAssignmentLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  {receiving : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
      (GeneralizedLocalInstanceValues.model compiled.indexed)))
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep}

include transport extension in
theorem lifts {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {mode : Bool} {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    (sourceEq : invocation.source = source named)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .assignValue assignment operator rhs)
    (head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) invocation.source context
      certificate scope administrative compiled.indexed.layouts.definitions assignment operator rhs)
    (bare : assignment.target.projections = [])
    (children : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeSourceLiftBounds.LiftsAt bridge context
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
        named stages invocation certificate size)
    (preservation : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeExpressionBounds.PreservesAt bridge context
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
        named stages invocation certificate faults size)
    (remaining : CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := stages) (invocation := invocation) bridge producer context scope mode rest) :
    CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := stages) (invocation := invocation) bridge producer context scope mode (id :: rest) := by
  intro size mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner sameLocation ready
    finalContext outcome after trace
  have unique : NodeOccurrencesUnique invocation.source := sourceEq.symm ▸ runtime.graph.nodeOccurrencesUnique
  have assignmentTyped := ProtectedStateImperativeTypedSourceSites.assignment unique
    (sourceEq.symm ▸ ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
  have suffix := ProtectedStateImperativeStatementSuffixTyping.assignment
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ found) form
  have typed := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique head.found assignmentTyped
  obtain ⟨target, snapshot⟩ := CellAwareScopeBareAssignmentHeads.target_snapshot
    (invocation := invocation) bridge functions extension head bare environments heaps locals agrees initial admitted
  rcases SelectedCompilationStageAssignmentInversion.child_and_tail unique found form snapshot trace with
    ⟨childSize, reason, _strict, rfl, rfl, evaluated⟩ |
    ⟨childSize, sourceValue, currentCell, initialValue, currentSelected, _strict, rfl, rfl, evaluated,
      currentRead, rootType, rootInitial, pathRead, invalid⟩ |
    ⟨childSize, tailSize, sourceValue, middle, updated, written, _strict, _tailStrict, evaluated, write, tail⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children runtime covers sameLedger childSize head.right head.found typed
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation evaluated
    cases adapted with
    | completed => exact ⟨_, _, _, .assignBareFault (lookupStatement?_sound found) form snapshot lifted,
        .completed (.fault reason)⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, _, .assignBareFault (lookupStatement?_sound found) form snapshot lifted,
        .rejected origin call reason _ reached⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children runtime covers sameLedger childSize head.right head.found typed
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation evaluated
    cases adapted with
    | completed => exact ⟨_, _, _, .assignBareOperands (lookupStatement?_sound found) form snapshot lifted
        currentRead rootType rootInitial pathRead invalid, .completed (.fault (.invalidAssignmentOperands operator))⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, _, .assignBareFault (lookupStatement?_sound found) form snapshot lifted, .rejected origin call reason _ reached⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children runtime covers sameLedger childSize head.right head.found typed
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation evaluated
    cases adapted with
    | rejected origin call reason reached =>
      exact ⟨_, _, _, .assignBareFault (lookupStatement?_sound found) form snapshot lifted,
        .rejected origin call reason _ reached⟩
    | completed =>
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, framePreserved, metadata,
          effect, _count, nextTyped, ⟨middleState, _related, nextAdmitted⟩, _continuation⟩ :=
        CellAwareScopeBareAssignmentHeads.preserves_value bridge functions extension transport head bare
          environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
          (preservation runtime covers sameLedger stagedSize) snapshot measured write
      obtain ⟨nextContext, result, finalHeap, restTrace, restAdapted⟩ := remaining
        (environments.extend maps worlds) middleHeaps (locals.mono metadata)
        (DataPlaceChildExpressions.prefix_agrees agrees slots) nextTyped runtime covers sameLedger suffix
        middleState nextAdmitted (authority.transport effect) (physical.transport effect framePreserved) owner sameLocation ready tail
      exact ⟨nextContext, result, finalHeap,
        .assignBare (lookupStatement?_sound found) form snapshot lifted write restTrace, restAdapted⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowAssignmentLifting
end
