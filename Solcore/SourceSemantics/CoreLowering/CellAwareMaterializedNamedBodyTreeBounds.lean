import Solcore.SourceSemantics.CoreLowering.CellAwareNamedGeneralizedPrefix
import Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedSourceInversion
import Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedTerminalStatements
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalSourceBodyInversion
import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeStatementSuffixTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedFlowOutcomes

/-! The finite actual named body follows its original generalized declarations
and terminal expression. Allocation and lexical exit retain exact authority;
expression bounds are internal induction hypotheses from the compiler tree. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedNamedBodyTreeBounds
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

private theorem terminal_preserves {budget size : Nat}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {expression : ExpressionId} {statements : List StatementId} {node : ExpressionNode}
    {expected : TypeSystem.Ty} {lowered : SourceCoreBasic.LoweredExpr}
    (children : CellAwareMaterializedScopeBounds.PreservesBelow bridge context model named registry invocation
      (certificates context) faults budget)
    (unique : NodeOccurrencesUnique invocation.source)
    (head : Head invocation expression statements)
    (certified : certificates context scope expression lowered)
    (found : invocation.source.lookupExpression? expression = some node)
    (typed : ExpressionHasType invocation.source context expression node.type)
    (valueType : node.type = expected)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {embedding : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
      mapping world administrative scope environment canonical whole.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree embedding canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model whole.indexed)
      named.signature.key [] mapping world before store environment)
    (physical : CellAwareScopePhysical.Physical whole named context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLocation : owner.key.frameLocation = physical.location)
    {finalContext : SourceSemantics.Context} {outcome : Staging.Recursive.BodyOutcome}
    (trace : Staging.Recursive.Size.Statements program registry size invocation context environment before
      statements finalContext outcome after) (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((LocalLoop.returnValue lowered.type lowered.expression).rename embedding) value finalStore ∧
      Represents model finalMap finalWorld true expected lowered.type faults outcome value ∧
      CellAwareMaterializedFlowOutput.FlowAt whole finalMap finalWorld owner.key.frameLocation outcome value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed))
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model whole.indexed)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  obtain ⟨childSize, childOutcome, sameSize, _sameContext, sameOutcome, child⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalSourceBodyInversion.child_of_body unique head trace
  subst outcome
  obtain ⟨_trace, value, finalStore, finalMap, finalWorld, evaluated, represented, output,
      finalHeaps, maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
    CellAwareMaterializedTerminalStatements.preserves bridge head certified found typed environments heaps locals agrees actualTyped
      initial admitted authority physical owner sameLocation budget children child (sameSize ▸ within)
  refine ⟨value, finalStore, finalMap, finalWorld, evaluated, ?_, output, finalHeaps, maps, worlds,
    frame, metadata, effect, reached, related, ?_⟩
  · cases represented with
    | returned payload => exact .returned (valueType ▸ payload)
    | fault matched => exact .fault matched
  · cases childOutcome <;> simpa only [Post, CallableIndexedOwnedAdmittedStagedTerminalStatements.control, ← valueType] using post

include record bindings registered in
/-- Every generalized prefix is an actual compiler initializer and allocation.
The final statement uses the strict expression child, then restores lexical
observations while retaining its complete heap and concrete descriptor effect. -/
theorem preserves {budget : Nat}
    (children : ∀ context, Dynamic.SourceRuntimeValid program context (source named) →
      invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      CellAwareMaterializedScopeBounds.PreservesBelow bridge context model named registry invocation
      (certificates context) faults budget)
    (sourceEq : invocation.source = source named)
    {administrative : Core.Context} {reasonAt : ExpressionId → Word}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : CellAwareNativeBodyTree.Tree whole.indexed named compiled certificates administrative reasonAt
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
      CellAwareMaterializedFlowOutput.FlowAt whole finalMap finalWorld owner.key.frameLocation outcome value ∧
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
  | returning rest found form expressionFound valueType typed certified =>
    cases modeEq
    intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger _sourceTyped initial admitted authority physical owner sameLocation _ready
      finalContext outcome after trace
    exact terminal_preserves bridge (children _ runtime covers sameLedger) (by simpa only [sourceEq] using runtime.graph.nodeOccurrencesUnique)
      (.returning rest (by simpa only [sourceEq] using lookupStatement?_sound found) form) certified
      (by simpa only [sourceEq] using expressionFound) (by simpa only [sourceEq] using typed) valueType
      environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation trace within
  | tail found form expressionFound valueType typed certified =>
    intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger _sourceTyped initial admitted authority physical owner sameLocation _ready
      finalContext outcome after trace
    exact terminal_preserves bridge (children _ runtime covers sameLedger) (by simpa only [sourceEq] using runtime.graph.nodeOccurrencesUnique)
      (.tail (by simpa only [sourceEq] using lookupStatement?_sound found) form) certified
      (by simpa only [sourceEq] using expressionFound) (by simpa only [sourceEq] using typed) valueType
      environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation trace within
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
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, output, finalHeaps,
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
    refine ⟨value, finalStore, finalMap, finalWorld, agreement.wrap evaluated, represented, output, finalHeaps,
      effect.maps.trans maps, effect.worlds.trans worlds, preserved.trans finalFrame,
      effect.metadata.trans metadata, effect.trans finalEffect, finalState,
      protocol.trans related (protocol.trans tailRelated (bindings.restore_related
        (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (id := binder.id) (type := lowered.type)
        (value := .cellRef (OptionalCell.cellType lowered.type) (store.length + 2)) tailState)), ?_⟩
    exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (store.length + 2)) tailState post

end Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedNamedBodyTreeBounds
