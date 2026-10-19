import Solcore.SourceSemantics.CoreLowering.CellAwareLexicalNativeBodyTree
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedBodyTreeBounds
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
namespace Solcore.SourceSemantics.CoreLowering.CellAwareLexicalNamedBodyTreeBounds
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
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  (compiled : CallableIndexedNamedGeneration.Compilation whole.indexed named diagnostics namedCode)
  (record : SourceCompilationPlan.exactSpecialization whole.indexed.base.plan named.signature.key = .ok named.specialized)
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)))
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep}

private theorem head_typed {context : SourceSemantics.Context} {id : StatementId} {rest : List StatementId}
    (typed : ProtectedStateImperativeTypedSourceSites.Statements (source named) context (id :: rest)) :
    ∃ control final facts, StatementHasType (source named) control context id final facts := by
  obtain ⟨control, final, facts, typed⟩ := typed
  cases typed with
  | singleton head => exact ⟨control, _, _, head⟩
  | cons head _ => exact ⟨control, _, _, head⟩

include record bindings registered in
/-- Every generalized prefix is an actual compiler initializer and allocation.
The final statement uses the strict expression child, then restores lexical
observations while retaining its complete heap and concrete descriptor effect. -/
theorem preserves {budget : Nat}
    (children : ∀ context, Dynamic.SourceRuntimeValid program context (source named) →
      invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      CellAwareScopeExpressionBounds.PreservesBelow bridge context model named registry invocation
      (certificates context) faults budget)
    (sourceEq : invocation.source = source named)
    {administrative : Core.Context} {reasonAt : ExpressionId → Word}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : CellAwareLexicalNativeBodyTree.Tree whole.indexed named compiled certificates administrative reasonAt
      context scope true statements expected type code)
    (issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed named reasonAt) :
    ∀ {size}, size ≤ budget →
    ∀ {mapping world actualContext environment canonical actual before store embedding},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
      mapping world administrative scope environment canonical whole.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree embedding canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions →
    Dynamic.SourceRuntimeValid program context (source named) →
    invocation.evidence.Covers context →
    context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
    ProtectedStateImperativeTypedSourceSites.Statements (source named) context statements →
    ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model whole.indexed)
      named.signature.key [] mapping world before store environment →
    ∀ physical : CellAwareScopePhysical.Physical whole named context scope canonical mapping world before store environment,
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
    owner.key.frameLocation = physical.location →
    ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native →
    ∀ {finalContext outcome after},
    Staging.Recursive.Size.Statements program registry size invocation context environment before
      statements finalContext outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename embedding) value finalStore ∧
      Represents model finalMap finalWorld true expected type faults outcome value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed))
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model whole.indexed)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  generalize modeEq : true = mode at tree
  induction tree with
  | existing tree =>
    cases modeEq
    exact CellAwareNamedBodyTreeBounds.preserves bridge bindings compiled record producer registered
      children sourceEq tree issuer
  | @generalizedInitialized context nextContext scope mode id node binder initializer initializerNode parameters result lambdaBody rest expected type lowered body childFuel
      found form declaration polymorphic extended ordinary _initializerFound _initializerForm _valueType _requirements _coercions site initialReceipt nativeTyped allocation annotation same remaining ih =>
    cases modeEq
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
      ih rfl tailWithin nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
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

  | @initialized context nextContext scope mode id node binder initializer initializerNode rest expected type lowered body
      found form member mono extended ordinary initializerFound valueType typed certified allocation annotation same remaining ih =>
    cases modeEq
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
          ih rfl tailWithin nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
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

include record bindings registered in
/-- Actual native completion reconstructs descriptor allocation and the original
terminal Source run, preserving the exact reached heap and lexical scope. -/
theorem reflects {budget : Nat}
    (children : ∀ context, Dynamic.SourceRuntimeValid program context (source named) →
      invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      CellAwareScopeExpressionBounds.ReflectsBelow bridge context model named registry invocation
      (certificates context) faults budget)
    (sourceEq : invocation.source = source named)
    {administrative : Core.Context} {reasonAt : ExpressionId → Word}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : CellAwareLexicalNativeBodyTree.Tree whole.indexed named compiled certificates administrative reasonAt
      context scope true statements expected type code)
    (issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed named reasonAt) :
    ∀ {size}, size ≤ budget →
    ∀ {mapping world actualContext environment canonical actual before store embedding},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
      mapping world administrative scope environment canonical whole.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree embedding canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions →
    Dynamic.SourceRuntimeValid program context (source named) →
    invocation.evidence.Covers context →
    context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
    ProtectedStateImperativeTypedSourceSites.Statements (source named) context statements →
    ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model whole.indexed)
      named.signature.key [] mapping world before store environment →
    ∀ physical : CellAwareScopePhysical.Physical whole named context scope canonical mapping world before store environment,
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
    owner.key.frameLocation = physical.location →
    ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native →
    ∀ {value finalStore}, EvaluationSize size actual store (code.rename embedding) value finalStore →
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      Staging.Recursive.Size.Statements program registry sourceSize invocation context environment before
        statements finalContext outcome after ∧
      Represents model finalMap finalWorld true expected type faults outcome value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed))
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model whole.indexed)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  generalize modeEq : true = mode at tree
  induction tree with
  | existing tree =>
    cases modeEq
    exact CellAwareNamedBodyTreeBounds.reflects bridge bindings compiled record producer registered
      children sourceEq tree issuer
  | @generalizedInitialized context nextContext scope mode id node binder initializer initializerNode parameters result lambdaBody
      rest expected type lowered body childFuel found form declaration polymorphic extended ordinary
      initializerFound initializerForm valueType requirements coercions site initialReceipt nativeTyped allocation annotation same remaining ih =>
    cases modeEq
    intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner sameLocation ready
      value finalStore completed
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
      ih rfl (Nat.le_trans (Nat.le_of_lt strict) within) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
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

  | @initialized context nextContext scope mode id node binder initializer initializerNode rest expected type lowered body
      found form member mono extended ordinary initializerFound valueType typed certified allocation annotation same remaining ih =>
    cases modeEq
    intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner sameLocation ready
      value finalStore completed
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
        ih rfl (Nat.le_trans (Nat.le_of_lt tailStrict) within) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
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

/-- The bounded compiler tree always reaches a return or a real fault. This
follows the original statements rather than a native result tag. -/
theorem terminal_outcome {administrative : Core.Context} {reasonAt : ExpressionId → Word}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : CellAwareLexicalNativeBodyTree.Tree whole.indexed named compiled certificates administrative reasonAt
      context scope true statements expected type code)
    (sourceEq : invocation.source = source named)
    (unique : NodeOccurrencesUnique invocation.source) :
    ∀ {size environment before finalContext outcome after},
      Staging.Recursive.Size.Statements program registry size invocation context environment before
        statements finalContext outcome after →
      ∃ result, outcome = CallableIndexedOwnedAdmittedStagedTerminalStatements.control result := by
  generalize modeEq : true = mode at tree
  induction tree with
  | existing tree =>
    cases modeEq
    exact CellAwareNamedBodyTreeBounds.terminal_outcome compiled tree sourceEq unique
  | generalizedInitialized found form _ polymorphic extended _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    cases modeEq
    intro size environment before finalContext outcome after trace
    obtain ⟨_, _, _, _, _, _, _, remaining⟩ :=
      CellAwareGeneralizedSourceInversion.generalized unique
        (by simpa only [sourceEq] using found) form polymorphic
        (by simpa only [sourceEq] using extended) trace
    exact ih rfl remaining
  | initialized found form _ mono extended _ _ _ _ _ _ _ _ _ ih =>
    cases modeEq
    intro size environment before finalContext outcome after trace
    rcases CallableIndexedOwnedPreparedStagedScopedLexicalSourceInversion.initialized unique
        (by simpa only [sourceEq] using found) form mono (by simpa only [sourceEq] using extended) trace with
      ⟨_, failure, _, _, same, _⟩ | ⟨_, _, _, _, _, _, _, _, _, remaining⟩
    · exact ⟨.fault failure, same⟩
    · exact ih rfl remaining

end Solcore.SourceSemantics.CoreLowering.CellAwareLexicalNamedBodyTreeBounds
