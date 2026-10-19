import Solcore.SourceSemantics.CoreLowering.CellAwareScopeTransferFlow
import Solcore.SourceSemantics.CoreLowering.CellAwareLoopSequences
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeBareAssignmentFlow
import Solcore.SourceSemantics.CoreLowering.CellAwareImperativeTree
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeEmptyFlow
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeDiscardFlow
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeBlockFlow
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeConditionalFlow
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeTerminalFlow
import Solcore.SourceSemantics.CoreLowering.CellAwareFaultingNativeBodyTree
import Solcore.SourceSemantics.CoreLowering.CellAwareLexicalNamedBodyTreeBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedAbsentPrefix
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedOrdinaryPrefix
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedLexicalSourceInversion
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedGeneralizedPrefix
import Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedSourceInversion
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeTerminalStatements
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalSourceBodyInversion
import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeStatementSuffixTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedFlowOutcomes

/-! Ordinary and generalized declarations compose in the actual compiled
lexical body. Successful children retain descriptor authority before allocation;
failed children retain the reached heap without allocating a new cell. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareImperativeTreeBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post restore_post)
open CallableIndexedOwnedAdmittedStagedTerminalStatements (Head control)
open CallableIndexedNamedGeneration (source)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (bindings : ProtectedStateTransition.Bindings protocol)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  (functions : FunctionModel whole.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions whole.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial whole.compatible.checked).registry receiving)
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  (compiled : CallableIndexedNamedGeneration.Compilation whole.indexed named diagnostics namedCode)
  (record : SourceCompilationPlan.exactSpecialization whole.indexed.base.plan named.signature.key = .ok named.specialized)
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

private theorem head_typed {context : SourceSemantics.Context} {id : StatementId} {rest : List StatementId}
    (typed : ProtectedStateImperativeTypedSourceSites.Statements (source named) context (id :: rest)) :
    ∃ control final facts, StatementHasType (source named) control context id final facts := by
  obtain ⟨control, final, facts, typed⟩ := typed
  cases typed with
  | singleton head => exact ⟨control, _, _, head⟩
  | cons head _ => exact ⟨control, _, _, head⟩

variable
  (booleans : ∀ {mapping world sourceValue nativeValue},
    (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions).Represents mapping world .bool sourceValue nativeValue .bool →
    ∃ truth, sourceValue = .bool truth ∧ nativeValue = .bool truth)
  (unitValue : ∀ mapping world, (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions).Represents mapping world .unit .unit .unit .unit)

include record bindings transport extension registered operandIncluded booleans unitValue in
theorem preserves {budget : Nat}
    (children : ∀ context, Dynamic.SourceRuntimeValid program context (source named) →
      invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      CellAwareScopeExpressionBounds.PreservesBelow bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named registry invocation
      (certificates context) faults budget)
    (sourceEq : invocation.source = source named)
    {administrative : Core.Context} {reasonAt : ExpressionId → Word}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : CellAwareImperativeTree.Tree whole.indexed named compiled certificates administrative reasonAt
      context scope mode statements expected type code)
    (issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed named reasonAt) :
    CellAwareScopeFlowBounds.PreservesAtMost bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named producer registry invocation faults
      administrative scope mode statements expected type code budget := by
  induction tree with
  | @generalizedInitialized context nextContext scope mode id node binder initializer initializerNode parameters result lambdaBody rest expected type lowered body childFuel
      found form declaration polymorphic extended ordinary _initializerFound _initializerForm _valueType _requirements _coercions site initialReceipt nativeTyped allocation annotation same remaining ih =>
    intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner sameLocation ready
      finalContext outcome after trace
    have unique := runtime.graph.nodeOccurrencesUnique
    obtain ⟨tailSize, function, location, bound, sameSize, captures, allocated, remainingTrace⟩ :=
      CellAwareGeneralizedSourceInversion.generalized (by simpa only [sourceEq] using unique)
        (by simpa only [sourceEq] using found) form polymorphic
        (by simpa only [sourceEq] using extended) trace
    have capturesNamed : Dynamic.GeneralizedClosureCaptures context (source named) environment binder initializer function := by
      simpa only [sourceEq] using captures
    obtain ⟨control, next, facts, headTyped⟩ := head_typed sourceTyped
    have functionTyped := CellAwareGeneralizedSourceInversion.captured_wellTyped runtime locals headTyped
      found form polymorphic capturesNamed
    have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
    obtain ⟨values, marker, agreement, _smaller, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
        preserved, effect, nextAuthority, reached, related, nextAdmitted, nextPhysical, locationEq, nativeEq⟩ :=
      CellAwareNamedGeneralizedPrefix.complete bridge compiled record site initialReceipt issuer declaration polymorphic extended
        ordinary nativeTyped allocation annotation same producer registered environments heaps locals agrees actualTyped
        initial admitted authority physical (ready initial physical.read) capturesNamed functionTyped allocated type body
    have nextReady : ProtectedStateTransition.CellAllocation.ReadyAt producer nextPhysical.location nextPhysical.native := by
      intro index current stored
      have previous := ready current (by simpa only [locationEq, nativeEq] using stored)
      simpa only [locationEq, nativeEq] using previous
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, finalFrame, metadata, finalEffect, tailState, tailRelated, post⟩ :=
      ih _ tailWithin nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
        (runtime.transport (.ofBinderExtends extended))
        ((Dynamic.RuntimeContextFields.ofBinderExtends extended).covers covers)
        ((Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans sameLedger)
        (ProtectedStateImperativeStatementSuffixTyping.let_decl unique sourceTyped found form extended)
        reached nextAdmitted nextAuthority nextPhysical owner (sameLocation.trans locationEq.symm) nextReady remainingTrace
    let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (id := binder.id) (type := lowered.type)
      (value := .cellRef (OptionalCell.cellType lowered.type) (store.length + 2)) tailState
    refine ⟨value, finalStore, finalMap, finalWorld, agreement.wrap evaluated, represented, finalHeaps,
      effect.maps.trans maps, effect.worlds.trans worlds, preserved.trans finalFrame,
      effect.metadata.trans metadata, effect.trans finalEffect, finalState,
      protocol.trans related (protocol.trans tailRelated (bindings.restore_related
        (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (id := binder.id) (type := lowered.type)
        (value := .cellRef (OptionalCell.cellType lowered.type) (store.length + 2)) tailState)), ?_⟩
    exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (store.length + 2)) tailState post

  | @uninitialized context nextContext scope mode id node binder rest expected type body payload
      found form member mono extended ordinary projected allocation annotation same remaining ih =>
    intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner sameLocation ready
      finalContext outcome after trace
    have unique := runtime.graph.nodeOccurrencesUnique
    obtain ⟨tailSize, location, bound, sameSize, allocated, remainingTrace⟩ :=
      CallableIndexedOwnedPreparedStagedScopedLexicalSourceInversion.absent
        (by simpa only [sourceEq] using unique) (by simpa only [sourceEq] using found) form
        (by simpa only [sourceEq] using extended) trace
    have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
    obtain ⟨marker, agreement, _smaller, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
        preserved, effect, nextAuthority, reached, related, nextAdmitted, nextPhysical, locationEq, nativeEq⟩ :=
      CellAwareNamedAbsentPrefix.complete bridge mono member extended ordinary allocation annotation same producer registered
        projected environments heaps locals agrees actualTyped initial admitted authority physical
        (ready initial physical.read) allocated body
    have nextReady : ProtectedStateTransition.CellAllocation.ReadyAt producer nextPhysical.location nextPhysical.native := by
      intro index current stored
      have previous := ready current (by simpa only [locationEq, nativeEq] using stored)
      simpa only [locationEq, nativeEq] using previous
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, finalFrame, metadata, finalEffect, tailState, tailRelated, post⟩ :=
      ih _ tailWithin nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
        (runtime.transport (.ofBinderExtends extended))
        ((Dynamic.RuntimeContextFields.ofBinderExtends extended).covers covers)
        ((Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans sameLedger)
        (ProtectedStateImperativeStatementSuffixTyping.let_decl unique sourceTyped found form extended)
        reached nextAdmitted nextAuthority nextPhysical owner (sameLocation.trans locationEq.symm) nextReady remainingTrace
    let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (id := binder.id) (type := payload)
      (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState
    refine ⟨value, finalStore, finalMap, finalWorld, agreement.wrap evaluated, represented, finalHeaps,
      effect.maps.trans maps, effect.worlds.trans worlds, preserved.trans finalFrame,
      effect.metadata.trans metadata, effect.trans finalEffect, finalState,
      protocol.trans related (protocol.trans tailRelated (bindings.restore_related
        (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (id := binder.id) (type := payload)
        (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState)), ?_⟩
    exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState post

  | @initialized context nextContext scope mode id node binder initializer initializerNode rest expected type lowered body
      found form member mono extended ordinary initializerFound valueType typed certified allocation annotation same remaining ih =>
    intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner sameLocation ready
      finalContext outcome after trace
    have unique := runtime.graph.nodeOccurrencesUnique
    rcases CallableIndexedOwnedPreparedStagedScopedLexicalSourceInversion.initialized
        (by simpa only [sourceEq] using unique) (by simpa only [sourceEq] using found) form mono
        (by simpa only [sourceEq] using extended) trace with
      ⟨childSize, failure, sameSize, contextEq, outcomeEq, child⟩ |
      ⟨childSize, tailSize, sourceValue, location, middle, bound, sameSize, child, allocated, remainingTrace⟩
    · subst finalContext
      subst outcome
      have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
        rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
          maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
        children context runtime covers sameLedger childSize childStrict certified
          (by simpa only [sourceEq] using initializerFound) (by simpa only [sourceEq] using typed)
          environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation child
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, CellAwareOrdinaryContinuation.failure evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, metadata, effect, reached, related, post.at_fault_type⟩
    · have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
        rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
      have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
        rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
      obtain ⟨value, middleStore, middleMap, middleWorld, evaluated, represented, middleHeaps,
          maps, worlds, frame, metadata, effect, middleState, expressionRelated, post⟩ :=
        children context runtime covers sameLedger childSize childStrict certified
          (by simpa only [sourceEq] using initializerFound) (by simpa only [sourceEq] using typed)
          environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation child
      cases represented with
      | @value _ coreValue payload =>
        let middlePhysical := physical.transport effect frame
        obtain ⟨marker, agreement, _smaller, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
            preserved, allocationEffect, nextAuthority, reached, related, nextAdmitted, nextPhysical, locationEq, nativeEq⟩ :=
          CellAwareNamedOrdinaryPrefix.complete bridge mono member extended ordinary allocation annotation same producer registered
            evaluated (valueType ▸ payload) (valueType ▸ post.at_value.1)
            (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
            middleState post.at_value.2 (authority.transport effect) middlePhysical
            (ready middleState middlePhysical.read) allocated type body
        have nextReady : ProtectedStateTransition.CellAllocation.ReadyAt producer nextPhysical.location nextPhysical.native := by
          intro index current stored
          have previous := ready current (by simpa only [locationEq, nativeEq, middlePhysical, CellAwareScopePhysical.Physical.transport_location, CellAwareScopePhysical.Physical.transport_native] using stored)
          simpa only [locationEq, nativeEq, middlePhysical, CellAwareScopePhysical.Physical.transport_location, CellAwareScopePhysical.Physical.transport_native] using previous
        obtain ⟨value, finalStore, finalMap, finalWorld, tailEvaluated, represented, finalHeaps,
            tailMaps, tailWorlds, finalFrame, finalMetadata, finalEffect, tailState, tailRelated, tailPost⟩ :=
          ih _ tailWithin nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
            (runtime.transport (.ofBinderExtends extended))
            ((Dynamic.RuntimeContextFields.ofBinderExtends extended).covers covers)
            ((Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans sameLedger)
            (ProtectedStateImperativeStatementSuffixTyping.let_decl unique sourceTyped found form extended)
            reached nextAdmitted nextAuthority nextPhysical owner (sameLocation.trans locationEq.symm) nextReady remainingTrace
        let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
          (id := binder.id) (type := lowered.type)
          (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState
        refine ⟨value, finalStore, finalMap, finalWorld, agreement.wrap tailEvaluated, represented, finalHeaps,
          maps.trans (allocationEffect.maps.trans tailMaps), worlds.trans (allocationEffect.worlds.trans tailWorlds),
          frame.trans (preserved.trans finalFrame), metadata.trans (allocationEffect.metadata.trans finalMetadata),
          effect.trans (allocationEffect.trans finalEffect), finalState,
          protocol.trans expressionRelated (protocol.trans related (protocol.trans tailRelated (bindings.restore_related
            (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
            (id := binder.id) (type := lowered.type)
            (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState))), ?_⟩
        exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
          (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState tailPost
  | @nil context scope mode expected type allowed =>
    intro size _within
    exact CellAwareScopeEmptyFlow.preserves bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named producer registry invocation faults
      administrative scope mode expected type allowed size
  | @returnUnit context scope mode id node rest found form =>
    intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready finalContext outcome after trace
    exact CellAwareScopeTerminalFlow.unit_preserves bridge producer unitValue
      (by simpa only [sourceEq] using found) form
      (by simpa only [sourceEq] using runtime.graph.nodeOccurrencesUnique) size
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready trace
  | @returning context scope mode id node expression expressionNode expected lowered rest found form expressionFound valueType typed certified =>
    intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready finalContext outcome after trace
    have head : CallableIndexedOwnedAdmittedStagedScopedTerminalStatements.Head invocation expression mode (id :: rest) :=
      .returning rest (by simpa only [sourceEq] using lookupStatement?_sound found) form
    have childTyped : ExpressionHasType invocation.source context expression expressionNode.type := by simpa only [sourceEq] using typed
    have meaning := CellAwareScopeTerminalFlow.preserves (administrative := administrative) bridge producer
      (by simpa only [sourceEq] using runtime.graph.nodeOccurrencesUnique)
      head (by simpa only [sourceEq] using expressionFound) childTyped certified budget
      (children context runtime covers sameLedger)
    rw [valueType] at meaning
    exact meaning size within environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready trace
  | @tail context scope id node expression expressionNode expected lowered found form expressionFound valueType typed certified =>
    intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready finalContext outcome after trace
    have head : CallableIndexedOwnedAdmittedStagedScopedTerminalStatements.Head invocation expression true [id] :=
      .tail (by simpa only [sourceEq] using lookupStatement?_sound found) form
    have childTyped : ExpressionHasType invocation.source context expression expressionNode.type := by simpa only [sourceEq] using typed
    have meaning := CellAwareScopeTerminalFlow.preserves (administrative := administrative) bridge producer
      (by simpa only [sourceEq] using runtime.graph.nodeOccurrencesUnique)
      head (by simpa only [sourceEq] using expressionFound) childTyped certified budget
      (children context runtime covers sameLedger)
    rw [valueType] at meaning
    exact meaning size within environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready trace
  | @discard context scope mode id node expression expressionNode semicolon rest expected lowered type body found form _notTail continuing expressionFound typed certified remaining ih =>
    intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready finalContext outcome after trace
    exact CellAwareScopeDiscardFlow.preserves bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named producer registry invocation faults
      administrative scope mode expected type sourceEq
      (by simpa only [sourceEq] using runtime.graph.nodeOccurrencesUnique)
      (by simpa only [sourceEq] using found) form continuing
      (by simpa only [sourceEq] using expressionFound) (by simpa only [sourceEq] using typed) certified
      budget (children context runtime covers sameLedger) ih size within
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready trace
  | @block context scope mode id node statements rest expected type innerCode body found form inner remaining innerIH remainingIH =>
    intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready finalContext outcome after trace
    exact CellAwareScopeBlockFlow.preserves bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named producer registry invocation faults
      administrative scope mode expected type sourceEq
      (by simpa only [sourceEq] using runtime.graph.nodeOccurrencesUnique)
      (by simpa only [sourceEq] using found) form budget innerIH remainingIH size within
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready trace
  | @ifThen context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body
      found form conditionFound conditionType conditionTyped conditionCertificate thenTree elseTree remaining thenIH elseIH remainingIH =>
    intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready finalContext outcome after trace
    exact CellAwareScopeConditionalFlow.preserves bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named producer registry invocation faults
      administrative scope expected type booleans
      (by simpa only [sourceEq] using conditionFound) conditionType
      (by simpa only [sourceEq] using conditionTyped) conditionCertificate sourceEq
      (by simpa only [sourceEq] using runtime.graph.nodeOccurrencesUnique)
      (by simpa only [sourceEq] using found) form budget (children context runtime covers sameLedger)
      thenIH elseIH remainingIH size within
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready trace
  | @whileLoop context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body escaped
      found form conditionFound conditionType conditionTyped conditionCertificate loopTree nativeTyped remaining loopIH remainingIH =>
    intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready finalContext outcome after trace
    exact CellAwareLoopSequences.preserves bridge (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) producer transport booleans sourceEq
      (children context runtime covers sameLedger)
      (by simpa only [sourceEq] using conditionFound) conditionType
      (by simpa only [sourceEq] using conditionTyped) conditionCertificate nativeTyped loopIH
      (by simpa only [sourceEq] using runtime.graph.nodeOccurrencesUnique)
      (by simpa only [sourceEq] using found) form remainingIH within
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready trace
  | @assign context scope mode id node assignment operator rhs rest expected type body
      found form head bare _rightTyped operands remaining remainingIH =>
    intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready finalContext outcome after trace
    cases invocation with
    | mk origin actualSource owned stageContext evidence guards =>
      cases sourceEq
      exact CellAwareScopeBareAssignmentFlow.preserves bridge transport functions producer rfl
        runtime.graph.nodeOccurrencesUnique found form head bare extension
        (fun previous right invalid => operandIncluded _ _ (operands previous right invalid))
        budget (children context runtime covers sameLedger) remainingIH size within
        environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
        initial admitted authority physical owner sameLocation ready trace

  | @breaking context scope mode id node expected type rest found form =>
    intro size _within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready finalContext outcome after trace
    exact CellAwareScopeTransferFlow.breaking_preserves bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named producer registry invocation faults
      administrative scope mode expected type
      (by simpa only [sourceEq] using runtime.graph.nodeOccurrencesUnique)
      (by simpa only [sourceEq] using found) form size
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready trace
  | @continuing context scope mode id node expected type rest found form =>
    intro size _within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready finalContext outcome after trace
    exact CellAwareScopeTransferFlow.continuing_preserves bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named producer registry invocation faults
      administrative scope mode expected type
      (by simpa only [sourceEq] using runtime.graph.nodeOccurrencesUnique)
      (by simpa only [sourceEq] using found) form size
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready trace

include record bindings transport extension registered operandIncluded booleans unitValue in
theorem reflects {budget : Nat}
    (children : ∀ context, Dynamic.SourceRuntimeValid program context (source named) →
      invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      CellAwareScopeExpressionBounds.ReflectsBelow bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named registry invocation
      (certificates context) faults budget)
    (sourceEq : invocation.source = source named)
    {administrative : Core.Context} {reasonAt : ExpressionId → Word}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : CellAwareImperativeTree.Tree whole.indexed named compiled certificates administrative reasonAt
      context scope mode statements expected type code)
    (issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed named reasonAt) :
    CellAwareScopeFlowBounds.ReflectsAtMost bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named producer registry invocation faults
      administrative scope mode statements expected type code budget := by
  induction tree with
  | @generalizedInitialized context nextContext scope mode id node binder initializer initializerNode parameters result lambdaBody
      rest expected type lowered body childFuel found form declaration polymorphic extended ordinary
      initializerFound initializerForm valueType requirements coercions site initialReceipt nativeTyped allocation annotation same remaining ih =>
    intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner sameLocation ready
      completed
    let function := Dynamic.GeneralizedClosure.ofDirectLambda context (source named) environment binder initializer
      parameters result lambdaBody
    have captures : Dynamic.GeneralizedClosureCaptures context (source named) environment binder initializer function :=
      .directLambda (lookupExpression?_sound initializerFound) initializerForm
        (by simpa only [ExpressionNode.rawType, coercions] using valueType) valueType requirements coercions
    let location : Dynamic.Location := ⟨before.cells.length⟩
    let bound : Dynamic.Heap := ⟨before.cells ++ [⟨function.binder.scheme.body, none, some function⟩]⟩
    have allocated : Dynamic.Heap.AllocatesGeneralized before function location bound := .append
    have unique := runtime.graph.nodeOccurrencesUnique
    obtain ⟨control, next, facts, headTyped⟩ := head_typed sourceTyped
    have functionTyped := CellAwareGeneralizedSourceInversion.captured_wellTyped runtime locals headTyped
      found form polymorphic captures
    obtain ⟨values, marker, _agreement, smaller, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
        preserved, effect, nextAuthority, reached, related, nextAdmitted, nextPhysical, locationEq, nativeEq⟩ :=
      CellAwareNamedGeneralizedPrefix.complete bridge compiled record site initialReceipt issuer declaration polymorphic extended
        ordinary nativeTyped allocation annotation same producer registered environments heaps locals agrees actualTyped
        initial admitted authority physical (ready initial physical.read) captures functionTyped allocated type body
    obtain ⟨tailSize, strict, tailCompleted⟩ := smaller completed
    have nextReady : ProtectedStateTransition.CellAllocation.ReadyAt producer nextPhysical.location nextPhysical.native := by
      intro index current stored
      have previous := ready current (by simpa only [locationEq, nativeEq] using stored)
      simpa only [locationEq, nativeEq] using previous
    obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
        maps, worlds, finalFrame, metadata, finalEffect, tailState, tailRelated, post⟩ :=
      ih _ (Nat.le_trans (Nat.le_of_lt strict) within) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
        (runtime.transport (.ofBinderExtends extended))
        ((Dynamic.RuntimeContextFields.ofBinderExtends extended).covers covers)
        ((Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans sameLedger)
        (ProtectedStateImperativeStatementSuffixTyping.let_decl unique sourceTyped found form extended)
        reached nextAdmitted nextAuthority nextPhysical owner (sameLocation.trans locationEq.symm) nextReady tailCompleted
    let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (id := binder.id) (type := lowered.type)
      (value := .cellRef (OptionalCell.cellType lowered.type) (store.length + 2)) tailState
    refine ⟨Staging.Recursive.Size.stepSize [sourceSize], finalContext, outcome, after, finalMap, finalWorld,
      .letGeneralized (by simpa only [sourceEq] using lookupStatement?_sound found) form
        (by simpa only [sourceEq] using captures) polymorphic (by simpa only [sourceEq] using extended) allocated trace,
      represented, finalHeaps, effect.maps.trans maps, effect.worlds.trans worlds, preserved.trans finalFrame,
      effect.metadata.trans metadata, effect.trans finalEffect, finalState,
      protocol.trans related (protocol.trans tailRelated (bindings.restore_related
        (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (id := binder.id) (type := lowered.type)
        (value := .cellRef (OptionalCell.cellType lowered.type) (store.length + 2)) tailState)), ?_⟩
    exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (store.length + 2)) tailState post

  | @uninitialized context nextContext scope mode id node binder rest expected type body payload
      found form member mono extended ordinary projected allocation annotation same remaining ih =>
    intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner sameLocation ready
      completed
    let location : Dynamic.Location := ⟨before.cells.length⟩
    let bound : Dynamic.Heap := ⟨before.cells ++ [⟨binder.scheme.body, none, none⟩]⟩
    have allocated : Dynamic.Heap.Allocates before binder.scheme.body none location bound := .append
    have unique := runtime.graph.nodeOccurrencesUnique
    obtain ⟨marker, _agreement, smaller, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
        preserved, effect, nextAuthority, reached, related, nextAdmitted, nextPhysical, locationEq, nativeEq⟩ :=
      CellAwareNamedAbsentPrefix.complete bridge mono member extended ordinary allocation annotation same producer registered
        projected environments heaps locals agrees actualTyped initial admitted authority physical
        (ready initial physical.read) allocated body
    obtain ⟨tailSize, strict, tailCompleted⟩ := smaller completed
    have nextReady : ProtectedStateTransition.CellAllocation.ReadyAt producer nextPhysical.location nextPhysical.native := by
      intro index current stored
      have previous := ready current (by simpa only [locationEq, nativeEq] using stored)
      simpa only [locationEq, nativeEq] using previous
    obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
        maps, worlds, finalFrame, metadata, finalEffect, tailState, tailRelated, post⟩ :=
      ih _ (Nat.le_trans (Nat.le_of_lt strict) within) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
        (runtime.transport (.ofBinderExtends extended))
        ((Dynamic.RuntimeContextFields.ofBinderExtends extended).covers covers)
        ((Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans sameLedger)
        (ProtectedStateImperativeStatementSuffixTyping.let_decl unique sourceTyped found form extended)
        reached nextAdmitted nextAuthority nextPhysical owner (sameLocation.trans locationEq.symm) nextReady tailCompleted
    let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (id := binder.id) (type := payload)
      (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState
    refine ⟨Staging.Recursive.Size.stepSize [sourceSize], finalContext, outcome, after, finalMap, finalWorld,
      .letUninitialized (by simpa only [sourceEq] using lookupStatement?_sound found) form
        mono (by simpa only [sourceEq] using extended) allocated trace,
      represented, finalHeaps, effect.maps.trans maps, effect.worlds.trans worlds, preserved.trans finalFrame,
      effect.metadata.trans metadata, effect.trans finalEffect, finalState,
      protocol.trans related (protocol.trans tailRelated (bindings.restore_related
        (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (id := binder.id) (type := payload)
        (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState)), ?_⟩
    exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState post

  | @initialized context nextContext scope mode id node binder initializer initializerNode rest expected type lowered body
      found form member mono extended ordinary initializerFound valueType typed certified allocation annotation same remaining ih =>
    intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner sameLocation ready
      completed
    have original := completed
    rw [TypedLexicalControl.sequence_rename] at original
    obtain ⟨childSize, middleStore, input, childSmaller, childEvaluation⟩ := original.bind_computation
    obtain ⟨childSourceSize, sourceOutcome, middle, middleMap, middleWorld, child, represented, middleHeaps,
        maps, worlds, frame, metadata, effect, middleState, expressionRelated, post⟩ :=
      children context runtime covers sameLedger childSize (Nat.lt_of_lt_of_le childSmaller within) certified
        (by simpa only [sourceEq] using initializerFound) (by simpa only [sourceEq] using typed)
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation childEvaluation
    cases represented with
    | fault matched =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound
        (CellAwareOrdinaryContinuation.failure childEvaluation.sound)
      exact ⟨Staging.Recursive.Size.stepSize [childSourceSize], context, _, middle, middleMap, middleWorld,
        .letFault (by simpa only [sourceEq] using lookupStatement?_sound found) form mono child,
        .fault matched, middleHeaps, maps, worlds, frame, metadata, effect, middleState, expressionRelated, post.at_fault_type⟩
    | @value sourceValue coreValue payload =>
      let location : Dynamic.Location := ⟨middle.cells.length⟩
      let bound : Dynamic.Heap := ⟨middle.cells ++ [⟨binder.scheme.body, some sourceValue, none⟩]⟩
      have allocated : Dynamic.Heap.Allocates middle binder.scheme.body (some sourceValue) location bound := .append
      let middlePhysical := physical.transport effect frame
      obtain ⟨marker, _agreement, smaller, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
          preserved, allocationEffect, nextAuthority, reached, related, nextAdmitted, nextPhysical, locationEq, nativeEq⟩ :=
        CellAwareNamedOrdinaryPrefix.complete bridge mono member extended ordinary allocation annotation same producer registered
          childEvaluation.sound (valueType ▸ payload) (valueType ▸ post.at_value.1)
          (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
          middleState post.at_value.2 (authority.transport effect) middlePhysical
          (ready middleState middlePhysical.read) allocated type body
      obtain ⟨tailSize, tailStrict, tailEvaluation⟩ := smaller completed
      have nextReady : ProtectedStateTransition.CellAllocation.ReadyAt producer nextPhysical.location nextPhysical.native := by
        intro index current stored
        have previous := ready current (by simpa only [locationEq, nativeEq, middlePhysical, CellAwareScopePhysical.Physical.transport_location, CellAwareScopePhysical.Physical.transport_native] using stored)
        simpa only [locationEq, nativeEq, middlePhysical, CellAwareScopePhysical.Physical.transport_location, CellAwareScopePhysical.Physical.transport_native] using previous
      obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
          tailMaps, tailWorlds, finalFrame, finalMetadata, finalEffect, tailState, tailRelated, tailPost⟩ :=
        ih _ (Nat.le_trans (Nat.le_of_lt tailStrict) within) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
          (runtime.transport (.ofBinderExtends extended))
          ((Dynamic.RuntimeContextFields.ofBinderExtends extended).covers covers)
          ((Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans sameLedger)
          (ProtectedStateImperativeStatementSuffixTyping.let_decl runtime.graph.nodeOccurrencesUnique sourceTyped found form extended)
          reached nextAdmitted nextAuthority nextPhysical owner (sameLocation.trans locationEq.symm) nextReady tailEvaluation
      let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (id := binder.id) (type := lowered.type)
        (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState
      refine ⟨Staging.Recursive.Size.stepSize [childSourceSize, sourceSize], finalContext, outcome, after, finalMap, finalWorld,
        .letInitialized (by simpa only [sourceEq] using lookupStatement?_sound found) form child mono
          (by simpa only [sourceEq] using extended) allocated trace,
        represented, finalHeaps, maps.trans (allocationEffect.maps.trans tailMaps), worlds.trans (allocationEffect.worlds.trans tailWorlds),
        frame.trans (preserved.trans finalFrame), metadata.trans (allocationEffect.metadata.trans finalMetadata),
        effect.trans (allocationEffect.trans finalEffect), finalState,
        protocol.trans expressionRelated (protocol.trans related (protocol.trans tailRelated (bindings.restore_related
          (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
          (id := binder.id) (type := lowered.type)
          (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState))), ?_⟩
      exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState tailPost
  | @nil context scope mode expected type allowed =>
    intro size _within
    exact CellAwareScopeEmptyFlow.reflects bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named producer registry invocation faults
      administrative scope mode expected type allowed size
  | @returnUnit context scope mode id node rest found form =>
    intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed
    exact CellAwareScopeTerminalFlow.unit_reflects bridge producer unitValue
      (by simpa only [sourceEq] using found) form size
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed
  | @returning context scope mode id node expression expressionNode expected lowered rest found form expressionFound valueType typed certified =>
    intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed
    have head : CallableIndexedOwnedAdmittedStagedScopedTerminalStatements.Head invocation expression mode (id :: rest) :=
      .returning rest (by simpa only [sourceEq] using lookupStatement?_sound found) form
    have childTyped : ExpressionHasType invocation.source context expression expressionNode.type := by simpa only [sourceEq] using typed
    have meaning := CellAwareScopeTerminalFlow.reflects (administrative := administrative) bridge producer
      head (by simpa only [sourceEq] using expressionFound) childTyped certified budget
      (children context runtime covers sameLedger)
    rw [valueType] at meaning
    exact meaning size within environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed
  | @tail context scope id node expression expressionNode expected lowered found form expressionFound valueType typed certified =>
    intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed
    have head : CallableIndexedOwnedAdmittedStagedScopedTerminalStatements.Head invocation expression true [id] :=
      .tail (by simpa only [sourceEq] using lookupStatement?_sound found) form
    have childTyped : ExpressionHasType invocation.source context expression expressionNode.type := by simpa only [sourceEq] using typed
    have meaning := CellAwareScopeTerminalFlow.reflects (administrative := administrative) bridge producer
      head (by simpa only [sourceEq] using expressionFound) childTyped certified budget
      (children context runtime covers sameLedger)
    rw [valueType] at meaning
    exact meaning size within environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed
  | @discard context scope mode id node expression expressionNode semicolon rest expected lowered type body found form _notTail continuing expressionFound typed certified remaining ih =>
    intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed
    exact CellAwareScopeDiscardFlow.reflects bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named producer registry invocation faults
      administrative scope mode expected type sourceEq
      (by simpa only [sourceEq] using runtime.graph.nodeOccurrencesUnique)
      (by simpa only [sourceEq] using found) form continuing
      (by simpa only [sourceEq] using expressionFound) (by simpa only [sourceEq] using typed) certified
      budget (children context runtime covers sameLedger) ih size within
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed
  | @block context scope mode id node statements rest expected type innerCode body found form inner remaining innerIH remainingIH =>
    intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed
    exact CellAwareScopeBlockFlow.reflects bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named producer registry invocation faults
      administrative scope mode expected type sourceEq
      (by simpa only [sourceEq] using runtime.graph.nodeOccurrencesUnique)
      (by simpa only [sourceEq] using found) form budget innerIH remainingIH size within
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed
  | @ifThen context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body
      found form conditionFound conditionType conditionTyped conditionCertificate thenTree elseTree remaining thenIH elseIH remainingIH =>
    intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed
    exact CellAwareScopeConditionalFlow.reflects bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named producer registry invocation faults
      administrative scope expected type booleans
      (by simpa only [sourceEq] using conditionFound) conditionType
      (by simpa only [sourceEq] using conditionTyped) conditionCertificate sourceEq
      (by simpa only [sourceEq] using runtime.graph.nodeOccurrencesUnique)
      (by simpa only [sourceEq] using found) form budget (children context runtime covers sameLedger)
      thenIH elseIH remainingIH size within
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed

  | @whileLoop context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body escaped
      found form conditionFound conditionType conditionTyped conditionCertificate loopTree nativeTyped remaining loopIH remainingIH =>
    intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed
    exact CellAwareLoopSequences.reflects bridge (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) producer transport booleans sourceEq
      (children context runtime covers sameLedger)
      (by simpa only [sourceEq] using conditionFound) conditionType
      (by simpa only [sourceEq] using conditionTyped) conditionCertificate nativeTyped loopIH
      (by simpa only [sourceEq] using found) form remainingIH within
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed
  | @assign context scope mode id node assignment operator rhs rest expected type body
      found form head bare _rightTyped operands remaining remainingIH =>
    intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed
    cases invocation with
    | mk origin actualSource owned stageContext evidence guards =>
      cases sourceEq
      exact CellAwareScopeBareAssignmentFlow.reflects bridge transport functions producer rfl
        runtime.graph.nodeOccurrencesUnique found form head bare extension
        (fun previous right invalid => operandIncluded _ _ (operands previous right invalid))
        budget (children context runtime covers sameLedger) remainingIH size within
        environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
        initial admitted authority physical owner sameLocation ready completed

  | @breaking context scope mode id node expected type rest found form =>
    intro size _within mapping world actualContext environment canonical actual before store embedding value finalStore
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed
    exact CellAwareScopeTransferFlow.breaking_reflects bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named producer registry invocation faults
      administrative scope mode expected type
      (by simpa only [sourceEq] using found) form size
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed
  | @continuing context scope mode id node expected type rest found form =>
    intro size _within mapping world actualContext environment canonical actual before store embedding value finalStore
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed
    exact CellAwareScopeTransferFlow.continuing_reflects bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named producer registry invocation faults
      administrative scope mode expected type
      (by simpa only [sourceEq] using found) form size
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed

end Solcore.SourceSemantics.CoreLowering.CellAwareImperativeTreeBounds
