import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.NamedEntries
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.StagedProjected
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.ScopeStatements
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateForPost
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedFlows
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedImperative
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.NamedAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.ProgramAdmission
import Solcore.SourceSemantics.CoreLowering.PublicSupport
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.ReadEffects
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.PublicHistories
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.FunctionValuesAndState
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogAndSpecialization
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.NamedExpressionCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.CanonicalCallerState
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.SourceFlowLifting

/-!
# Cell-aware bodies: the named family

Named bodies with a finite profile: tree bounds, body meaning, program profiles, and the lifting of Source traces up to the named invocation.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareNamedBodyTreeBounds
/-! The finite actual named body follows its original generalized declarations
and terminal expression. Allocation and lexical exit retain exact authority;
expression bounds are internal induction hypotheses from the compiler tree. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedBodyTreeBounds
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
    (children : CellAwareScopeExpressionBounds.PreservesBelow bridge context model named registry invocation
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
  obtain ⟨_trace, value, finalStore, finalMap, finalWorld, evaluated, represented,
      finalHeaps, maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
    CellAwareScopeTerminalStatements.preserves bridge head certified found typed environments heaps locals agrees actualTyped
      initial admitted authority physical owner sameLocation budget children child (sameSize ▸ within)
  refine ⟨value, finalStore, finalMap, finalWorld, evaluated, ?_, finalHeaps, maps, worlds,
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
      CellAwareScopeExpressionBounds.PreservesBelow bridge context model named registry invocation
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
      found form declaration polymorphic extended ordinary _initializerFound _initializerForm _valueType _requirements _coercions site initialReceipt nativeTyped allocation annotation same captured copied remaining ih =>
    cases modeEq
    intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner sameLocation ready
      finalContext outcome after trace
    have unique := runtime.graph.nodeOccurrencesUnique
    obtain ⟨tailSize, copies, snapshotHeap, function, location, bound, sameSize, snapshot, captures, allocated,
        remainingTrace⟩ :=
      CellAwareGeneralizedSourceInversion.generalized (by simpa only [sourceEq] using unique)
        (by simpa only [sourceEq] using found) form polymorphic
        (by simpa only [sourceEq] using extended) trace
    have snapshotNamed : Dynamic.EnvironmentCopies (source named) environment before copies snapshotHeap := by
      simpa only [sourceEq] using snapshot
    have capturesNamed : Dynamic.GeneralizedClosureCaptures context (source named) copies binder initializer function := by
      simpa only [sourceEq] using captures
    obtain ⟨control, next, facts, headTyped⟩ := head_typed sourceTyped
    have functionTyped := CellAwareGeneralizedSourceInversion.captured_wellTyped runtime (snapshotNamed.agrees locals)
      headTyped found form polymorphic capturesNamed
    have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
    obtain ⟨values, marker, copiedStore, copiedMap, copiedWorld, agreement, _smaller, nextEnvironments, nextHeaps,
        nextLocals, nextAgrees, nextTyped, preserved, effect, nextAuthority, reached, related, nextAdmitted, nextPhysical,
        locationEq, nativeEq⟩ :=
      CellAwareNamedGeneralizedPrefix.complete bridge compiled record site initialReceipt issuer declaration polymorphic extended
        ordinary nativeTyped allocation annotation same copied producer bindings registered environments heaps locals agrees
        actualTyped initial admitted authority physical ready snapshotNamed capturesNamed functionTyped allocated type body
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
      (value := .cellRef (OptionalCell.cellType lowered.type) (copiedStore.length + 2)) tailState
    refine ⟨value, finalStore, finalMap, finalWorld, agreement.wrap evaluated, represented, finalHeaps,
      effect.maps.trans maps, effect.worlds.trans worlds, preserved.trans finalFrame,
      effect.metadata.trans metadata, effect.trans finalEffect, finalState,
      protocol.trans related (protocol.trans tailRelated (bindings.restore_related
        (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (id := binder.id) (type := lowered.type)
        (value := .cellRef (OptionalCell.cellType lowered.type) (copiedStore.length + 2)) tailState)), ?_⟩
    exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (copiedStore.length + 2))
      tailState post

private theorem terminal_reflects {budget size : Nat}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {expression : ExpressionId} {statements : List StatementId} {node : ExpressionNode}
    {expected : TypeSystem.Ty} {lowered : SourceCoreBasic.LoweredExpr}
    (children : CellAwareScopeExpressionBounds.ReflectsBelow bridge context model named registry invocation
      (certificates context) faults budget)
    (head : Head invocation expression statements)
    (certified : certificates context scope expression lowered)
    (found : invocation.source.lookupExpression? expression = some node)
    (typed : ExpressionHasType invocation.source context expression node.type)
    (valueType : node.type = expected)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
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
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store
      ((LocalLoop.returnValue lowered.type lowered.expression).rename embedding) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Statements program registry sourceSize invocation context environment before
        statements context outcome after ∧
      Represents model finalMap finalWorld true expected lowered.type faults outcome value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed))
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model whole.indexed)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented,
      finalHeaps, maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
    CellAwareScopeTerminalStatements.reflects bridge head certified found typed environments heaps locals agrees actualTyped
      initial admitted authority physical owner sameLocation budget children completed within
  refine ⟨sourceSize, _, after, finalMap, finalWorld, trace, ?_, finalHeaps, maps, worlds,
    frame, metadata, effect, reached, related, ?_⟩
  · cases represented with
    | returned payload => exact .returned (valueType ▸ payload)
    | fault matched => exact .fault matched
  · cases outcome <;> simpa only [Post, CallableIndexedOwnedAdmittedStagedTerminalStatements.control, ← valueType] using post

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
  | returning rest found form expressionFound valueType typed certified =>
    cases modeEq
    intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger _sourceTyped initial admitted authority physical owner sameLocation _ready
      value finalStore completed
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, rest⟩ :=
      terminal_reflects bridge (children _ runtime covers sameLedger)
        (.returning rest (by simpa only [sourceEq] using lookupStatement?_sound found) form) certified
        (by simpa only [sourceEq] using expressionFound) (by simpa only [sourceEq] using typed) valueType
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation completed within
    exact ⟨sourceSize, _, outcome, after, finalMap, finalWorld, trace, rest⟩
  | tail found form expressionFound valueType typed certified =>
    intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger _sourceTyped initial admitted authority physical owner sameLocation _ready
      value finalStore completed
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, rest⟩ :=
      terminal_reflects bridge (children _ runtime covers sameLedger)
        (.tail (by simpa only [sourceEq] using lookupStatement?_sound found) form) certified
        (by simpa only [sourceEq] using expressionFound) (by simpa only [sourceEq] using typed) valueType
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation completed within
    exact ⟨sourceSize, _, outcome, after, finalMap, finalWorld, trace, rest⟩
  | @generalizedInitialized context nextContext scope mode id node binder initializer initializerNode parameters result lambdaBody
      rest expected type lowered body childFuel found form declaration polymorphic extended ordinary
      initializerFound initializerForm valueType requirements coercions site initialReceipt nativeTyped allocation annotation same
      captured copied remaining ih =>
    cases modeEq
    intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner sameLocation ready
      value finalStore completed
    obtain ⟨copies, snapshotHeap, snapshot⟩ := CellAwareGeneralizedSourceInversion.copies_exist (source named) locals
    let function := Dynamic.GeneralizedClosure.ofDirectLambda context (source named) copies binder initializer
      parameters result lambdaBody
    have captures : Dynamic.GeneralizedClosureCaptures context (source named) copies binder initializer function :=
      .directLambda (lookupExpression?_sound initializerFound) initializerForm
        (by simpa only [ExpressionNode.rawType, coercions] using valueType) valueType requirements coercions
    let location : Dynamic.Location := ⟨snapshotHeap.cells.length⟩
    let bound : Dynamic.Heap := ⟨snapshotHeap.cells ++ [⟨function.binder.scheme.body, none, some function⟩]⟩
    have allocated : Dynamic.Heap.AllocatesGeneralized snapshotHeap function location bound := .append
    have unique := runtime.graph.nodeOccurrencesUnique
    obtain ⟨control, next, facts, headTyped⟩ := head_typed sourceTyped
    have functionTyped := CellAwareGeneralizedSourceInversion.captured_wellTyped runtime (snapshot.agrees locals)
      headTyped found form polymorphic captures
    obtain ⟨values, marker, copiedStore, copiedMap, copiedWorld, _agreement, smaller, nextEnvironments, nextHeaps,
        nextLocals, nextAgrees, nextTyped, preserved, effect, nextAuthority, reached, related, nextAdmitted, nextPhysical,
        locationEq, nativeEq⟩ :=
      CellAwareNamedGeneralizedPrefix.complete bridge compiled record site initialReceipt issuer declaration polymorphic extended
        ordinary nativeTyped allocation annotation same copied producer bindings registered environments heaps locals agrees
        actualTyped initial admitted authority physical ready snapshot captures functionTyped allocated type body
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
      (value := .cellRef (OptionalCell.cellType lowered.type) (copiedStore.length + 2)) tailState
    refine ⟨Staging.Recursive.Size.stepSize [sourceSize], finalContext, outcome, after, finalMap, finalWorld,
      .letGeneralized (by simpa only [sourceEq] using lookupStatement?_sound found) form
        (by simpa only [sourceEq] using snapshot) (by simpa only [sourceEq] using captures) polymorphic
        (by simpa only [sourceEq] using extended) allocated trace,
      represented, finalHeaps, effect.maps.trans maps, effect.worlds.trans worlds, preserved.trans finalFrame,
      effect.metadata.trans metadata, effect.trans finalEffect, finalState,
      protocol.trans related (protocol.trans tailRelated (bindings.restore_related
        (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (id := binder.id) (type := lowered.type)
        (value := .cellRef (OptionalCell.cellType lowered.type) (copiedStore.length + 2)) tailState)), ?_⟩
    exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (copiedStore.length + 2))
      tailState post

/-- The bounded compiler tree always reaches a return or a real fault. This
follows the original statements rather than a native result tag. -/
theorem terminal_outcome {administrative : Core.Context} {reasonAt : ExpressionId → Word}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : CellAwareNativeBodyTree.Tree whole.indexed named compiled certificates administrative reasonAt
      context scope true statements expected type code)
    (sourceEq : invocation.source = source named)
    (unique : NodeOccurrencesUnique invocation.source) :
    ∀ {size environment before finalContext outcome after},
      Staging.Recursive.Size.Statements program registry size invocation context environment before
        statements finalContext outcome after →
      ∃ result, outcome = CallableIndexedOwnedAdmittedStagedTerminalStatements.control result := by
  generalize modeEq : true = mode at tree
  induction tree with
  | returning rest found form _ _ _ _ =>
    cases modeEq
    intro size environment before finalContext outcome after trace
    obtain ⟨_, childOutcome, _, _, same, _⟩ :=
      CallableIndexedOwnedPreparedStagedTerminalSourceBodyInversion.child_of_body unique
        (.returning rest (by simpa only [sourceEq] using lookupStatement?_sound found) form) trace
    exact ⟨childOutcome, same⟩
  | tail found form _ _ _ _ =>
    intro size environment before finalContext outcome after trace
    obtain ⟨_, childOutcome, _, _, same, _⟩ :=
      CallableIndexedOwnedPreparedStagedTerminalSourceBodyInversion.child_of_body unique
        (.tail (by simpa only [sourceEq] using lookupStatement?_sound found) form) trace
    exact ⟨childOutcome, same⟩
  | generalizedInitialized found form _ polymorphic extended _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    cases modeEq
    intro size environment before finalContext outcome after trace
    obtain ⟨_, _, _, _, _, _, _, _, _, _, remaining⟩ :=
      CellAwareGeneralizedSourceInversion.generalized unique
        (by simpa only [sourceEq] using found) form polymorphic
        (by simpa only [sourceEq] using extended) trace
    exact ih rfl remaining

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedBodyTreeBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareNamedBodyFinish
/-! The actual named compiler footer consumes the bounded body’s original
returned value or fault. It leaves the reached mixed heap and frame unchanged. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedBodyFinish
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

private theorem finished {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {mapping : LocationMap} {world : StoreTyping} {raw : TypeSystem.Ty} {type : Ty}
    {faults : RecursiveStageMeaning.FaultRep} {outcome : Staging.Recursive.BodyOutcome}
    {value : Value} {actual : Environment} {before after : Store} {flow : Expr}
    (represented : Represents model mapping world true raw type faults outcome value)
    (terminal : ∃ result, outcome = CallableIndexedOwnedAdmittedStagedTerminalStatements.control result)
    (evaluated : Evaluates actual before flow value after) (escaped : Word) (fallback : Expr) :
    ∃ native, Evaluates actual before
      (CallableIndexedOwnedAdmittedStagedTerminalBody.code type flow escaped fallback) native after ∧
      RecursiveStageMeaning.ResultRepresentsFor model mapping world raw type faults
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) native := by
  obtain ⟨result, rfl⟩ := terminal
  cases result with
  | value source =>
    cases represented with
    | returned payload =>
      exact CallableIndexedOwnedAdmittedStagedTerminalBody.terminal_evaluates (.returned payload) evaluated escaped
  | fault failure =>
    cases represented with
    | fault matched =>
      exact CallableIndexedOwnedAdmittedStagedTerminalBody.terminal_evaluates (.fault matched) evaluated escaped

include record bindings registered in
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
    (tree : CellAwareNativeBodyTree.Tree whole.indexed named compiled certificates administrative reasonAt
      context scope true statements expected type code)
    (issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed named reasonAt) (fellThrough escaped : Word) :
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
      Evaluates actual store ((CompatibleStatements.finish type code fellThrough escaped).rename embedding) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld expected type faults
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed))
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model whole.indexed)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context expected
          (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) reached := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger typed initial admitted authority physical owner sameLocation ready
    finalContext outcome after trace
  obtain ⟨flowValue, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
    CellAwareNamedBodyTreeBounds.preserves bridge bindings compiled record producer registered children sourceEq tree issuer within
      environments heaps locals agrees actualTyped runtime covers sameLedger typed initial admitted authority physical owner sameLocation ready trace
  have terminal := CellAwareNamedBodyTreeBounds.terminal_outcome compiled tree sourceEq
    (by simpa only [sourceEq] using runtime.graph.nodeOccurrencesUnique) trace
  obtain ⟨value, complete, result⟩ := finished represented terminal evaluated escaped
    ((CallableIndexedOwnedPreparedStagedTerminalBodyMeaning.fallback type fellThrough).rename embedding)
  exact ⟨value, finalStore, finalMap, finalWorld,
    by rwa [CallableIndexedOwnedAdmittedStagedLexicalFooter.finish_rename], result,
    finalHeaps, maps, worlds, frame, metadata, effect, reached, related,
    CallableIndexedOwnedAdmittedStagedFlowOutcomes.Post.to_function represented post⟩

include record bindings registered in
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
    (tree : CellAwareNativeBodyTree.Tree whole.indexed named compiled certificates administrative reasonAt
      context scope true statements expected type code)
    (issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed named reasonAt) (fellThrough escaped : Word) :
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
    ∀ {value finalStore}, EvaluationSize size actual store ((CompatibleStatements.finish type code fellThrough escaped).rename embedding) value finalStore →
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      Staging.Recursive.Size.Statements program registry sourceSize invocation context environment before
        statements finalContext outcome after ∧
      Staging.Recursive.BodyResult expected outcome (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld expected type faults
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed))
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model whole.indexed)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context expected
          (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) reached := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger typed initial admitted authority physical owner sameLocation ready
    value finalStore completed
  have original := completed
  rw [CallableIndexedOwnedAdmittedStagedLexicalFooter.finish_rename] at original
  obtain ⟨flowSize, flowValue, flowStore, flow, strict⟩ :=
    CallableIndexedOwnedAdmittedStagedTerminalBody.flow_prefix original within
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
    CellAwareNamedBodyTreeBounds.reflects bridge bindings compiled record producer registered children sourceEq tree issuer
      (Nat.le_of_lt strict) environments heaps locals agrees actualTyped runtime covers sameLedger typed initial admitted authority
      physical owner sameLocation ready flow
  have terminal := CellAwareNamedBodyTreeBounds.terminal_outcome compiled tree sourceEq
    (by simpa only [sourceEq] using runtime.graph.nodeOccurrencesUnique) trace
  obtain ⟨native, complete, result⟩ := finished represented terminal flow.sound escaped
    ((CallableIndexedOwnedPreparedStagedTerminalBodyMeaning.fallback type fellThrough).rename embedding)
  obtain ⟨same, stores⟩ := evaluation_deterministic original.sound complete
  cases same
  subst stores
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented.body_result,
    result, finalHeaps, maps, worlds, frame, metadata, effect, reached, related,
    CallableIndexedOwnedAdmittedStagedFlowOutcomes.Post.to_function represented post⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedBodyFinish
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareNamedBodyMeaning
/-! The complete bounded named body uses only its authentic compiler tree.
All expression and call behavior is derived from actual receipts; the caller
supplies the real parameter state and original Source typing. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedBodyMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole (Program.ofChecked whole.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole (Program.ofChecked whole.sourceProgram))}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (bindings : ProtectedStateTransition.Bindings protocol)
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  (compiled : CallableIndexedNamedGeneration.Compilation whole.indexed named diagnostics namedCode)
  (record : SourceCompilationPlan.exactSpecialization whole.indexed.base.plan named.signature.key = .ok named.specialized)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : whole.compatible.checked.catalog.callableContracts = true)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver whole.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt whole.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial whole.compatible.checked).registry
    completion.result.context.registry)
  {invocation : Staging.Recursive.Scope}
  (authority : CellAwareNamedCallPorts.Authority (compiled := whole) named invocation)
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies (Program.ofChecked whole.sourceProgram) (SelectedCompilationPhysicalProgramSupport.stages whole))
  (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))

local notation "functions" => CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel whole.compatible.checked completion.result.context.registry functions
local notation "registry" => SelectedCompilationPhysicalProgramSupport.stages whole
local notation "faults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics
local notation "program" => Program.ofChecked whole.sourceProgram

variable
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel
      (CompatibleAmbientHeap.payloadModel whole.compatible.checked completion.result.context.registry
        (CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults profile))
      (GeneralizedLocalInstanceValues.model whole.indexed)))
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)

include bindings record receiver extension authority selectedBodies registered in
theorem preserves_selected {budget : Nat}
    (sourceEq : invocation.source = source named)
    {administrative : Core.Context}
    {context : SourceSemantics.Context}
    {expected : TypeSystem.Ty}
    (body : CellAwareNamedBodySupport.Body compiled (CellAwareNamedBodyProducer.Certificate compiled)
      administrative context expected)
    (issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed named (diagnostics.reasonAt named.signature.key)) :
    ∀ {size}, size ≤ budget →
    ∀ {mapping world actualContext environment canonical actual before store embedding},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
      mapping world administrative (CellAwareNamedBodySupport.scope named) environment canonical whole.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree embedding canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions →
    Dynamic.SourceRuntimeValid program context (source named) →
    invocation.evidence.Covers context →
    context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
    ProtectedStateImperativeTypedSourceSites.Statements (source named) context compiled.statements →
    ∀ initial : protocol.State ⟨CellAwareNamedBodySupport.scope named, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model whole.indexed)
      named.signature.key [] mapping world before store environment →
    ∀ physical : CellAwareScopePhysical.Physical whole named context (CellAwareNamedBodySupport.scope named) canonical mapping world before store environment,
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
    owner.key.frameLocation = physical.location →
    ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native →
    ∀ {finalContext outcome after},
    Staging.Recursive.Size.Statements program registry size invocation context environment before
      compiled.statements finalContext outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (compiled.body.rename embedding) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld expected named.signature.resultType faults
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed))
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model whole.indexed)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨CellAwareNamedBodySupport.scope named, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context expected
          (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) reached := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger typed initial admitted lexical physical owner sameLocation ready
    finalContext outcome after trace
  rw [body.emitted]
  exact CellAwareNamedBodyFinish.preserves bridge bindings compiled record producer registered
    (fun childContext childRuntime childCovers childLedger childSize _ =>
      CellAwareNamedExpressionMeaning.preserves_selected compiled bridge profile receiver extension authority sourceEq issuer record
        childLedger (by simpa only [sourceEq] using childRuntime) selectedBodies childCovers childSize)
    sourceEq body.tree issuer _ _ within environments heaps locals agrees actualTyped runtime covers sameLedger typed
    initial admitted lexical physical owner sameLocation ready trace

include bindings record receiver extension authority selectedBodies registered in
theorem reflects_selected {budget : Nat}
    (sourceEq : invocation.source = source named)
    {administrative : Core.Context}
    {context : SourceSemantics.Context}
    {expected : TypeSystem.Ty}
    (body : CellAwareNamedBodySupport.Body compiled (CellAwareNamedBodyProducer.Certificate compiled)
      administrative context expected)
    (issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed named (diagnostics.reasonAt named.signature.key)) :
    ∀ {size}, size ≤ budget →
    ∀ {mapping world actualContext environment canonical actual before store embedding},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
      mapping world administrative (CellAwareNamedBodySupport.scope named) environment canonical whole.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree embedding canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions →
    Dynamic.SourceRuntimeValid program context (source named) →
    invocation.evidence.Covers context →
    context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
    ProtectedStateImperativeTypedSourceSites.Statements (source named) context compiled.statements →
    ∀ initial : protocol.State ⟨CellAwareNamedBodySupport.scope named, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model whole.indexed)
      named.signature.key [] mapping world before store environment →
    ∀ physical : CellAwareScopePhysical.Physical whole named context (CellAwareNamedBodySupport.scope named) canonical mapping world before store environment,
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
    owner.key.frameLocation = physical.location →
    ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native →
    ∀ {value finalStore}, EvaluationSize size actual store (compiled.body.rename embedding) value finalStore →
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      Staging.Recursive.Size.Statements program registry sourceSize invocation context environment before
        compiled.statements finalContext outcome after ∧
      Staging.Recursive.BodyResult expected outcome (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld expected named.signature.resultType faults
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed))
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model whole.indexed)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨CellAwareNamedBodySupport.scope named, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context expected
          (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) reached := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger typed initial admitted lexical physical owner sameLocation ready
    value finalStore completed
  rw [body.emitted] at completed
  exact CellAwareNamedBodyFinish.reflects bridge bindings compiled record producer registered
    (fun childContext childRuntime childCovers childLedger childSize _ =>
      CellAwareNamedExpressionMeaning.reflects_selected compiled bridge profile receiver extension authority sourceEq issuer record
        childLedger (by simpa only [sourceEq] using childRuntime) selectedBodies childCovers childSize)
    sourceEq body.tree issuer _ _ within environments heaps locals agrees actualTyped runtime covers sameLedger typed
    initial admitted lexical physical owner sameLocation ready completed

/- Compatibility adapters for callers with a whole-program receipt. -/
include bindings record receiver extension authority wellFormed registered in
theorem preserves {budget : Nat}
    (sourceEq : invocation.source = source named)
    {administrative : Core.Context}
    {context : SourceSemantics.Context}
    {expected : TypeSystem.Ty}
    (body : CellAwareNamedBodySupport.Body compiled (CellAwareNamedBodyProducer.Certificate compiled)
      administrative context expected)
    (issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed named (diagnostics.reasonAt named.signature.key)) :
    ∀ {size}, size ≤ budget →
    ∀ {mapping world actualContext environment canonical actual before store embedding},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
      mapping world administrative (CellAwareNamedBodySupport.scope named) environment canonical whole.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree embedding canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions →
    Dynamic.SourceRuntimeValid program context (source named) →
    invocation.evidence.Covers context →
    context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
    ProtectedStateImperativeTypedSourceSites.Statements (source named) context compiled.statements →
    ∀ initial : protocol.State ⟨CellAwareNamedBodySupport.scope named, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model whole.indexed)
      named.signature.key [] mapping world before store environment →
    ∀ physical : CellAwareScopePhysical.Physical whole named context (CellAwareNamedBodySupport.scope named) canonical mapping world before store environment,
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
    owner.key.frameLocation = physical.location →
    ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native →
    ∀ {finalContext outcome after},
    Staging.Recursive.Size.Statements program registry size invocation context environment before
      compiled.statements finalContext outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (compiled.body.rename embedding) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld expected named.signature.resultType faults
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed))
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model whole.indexed)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨CellAwareNamedBodySupport.scope named, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context expected
          (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) reached := by
  apply preserves_selected (selectedBodies := Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed) (bindings := bindings) (record := record) (receiver := receiver) (extension := extension) (authority := authority) (registered := registered) <;> assumption

include bindings record receiver extension authority wellFormed registered in
theorem reflects {budget : Nat}
    (sourceEq : invocation.source = source named)
    {administrative : Core.Context}
    {context : SourceSemantics.Context}
    {expected : TypeSystem.Ty}
    (body : CellAwareNamedBodySupport.Body compiled (CellAwareNamedBodyProducer.Certificate compiled)
      administrative context expected)
    (issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed named (diagnostics.reasonAt named.signature.key)) :
    ∀ {size}, size ≤ budget →
    ∀ {mapping world actualContext environment canonical actual before store embedding},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
      mapping world administrative (CellAwareNamedBodySupport.scope named) environment canonical whole.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree embedding canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions →
    Dynamic.SourceRuntimeValid program context (source named) →
    invocation.evidence.Covers context →
    context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
    ProtectedStateImperativeTypedSourceSites.Statements (source named) context compiled.statements →
    ∀ initial : protocol.State ⟨CellAwareNamedBodySupport.scope named, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model whole.indexed)
      named.signature.key [] mapping world before store environment →
    ∀ physical : CellAwareScopePhysical.Physical whole named context (CellAwareNamedBodySupport.scope named) canonical mapping world before store environment,
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
    owner.key.frameLocation = physical.location →
    ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native →
    ∀ {value finalStore}, EvaluationSize size actual store (compiled.body.rename embedding) value finalStore →
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      Staging.Recursive.Size.Statements program registry sourceSize invocation context environment before
        compiled.statements finalContext outcome after ∧
      Staging.Recursive.BodyResult expected outcome (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld expected named.signature.resultType faults
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed))
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model whole.indexed)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨CellAwareNamedBodySupport.scope named, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context expected
          (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) reached := by
  apply reflects_selected (selectedBodies := Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed) (bindings := bindings) (record := record) (receiver := receiver) (extension := extension) (authority := authority) (registered := registered) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedBodyMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareNamedInvocation
/-! One genuine named invocation joins marked parameters, the actual bounded
compiler body and restoration of the saved physical caller. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedInvocation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedFunctionValues (Header NamedCapture OwnedKey)

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header whole (Program.ofChecked whole.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole (Program.ofChecked whole.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : whole.compatible.checked.catalog.callableContracts = true)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver whole.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt whole.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial whole.compatible.checked).registry
    completion.result.context.registry)
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {canonical : Environment}
  (owner : OwnedKey keys)
  (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (header : Header whole (Program.ofChecked whole.sourceProgram))
  (capture : NamedCapture headers owner.key header mapping world)
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (generation : CallableIndexedNamedGeneration.Compilation whole.indexed header.named diagnostics code)
  (record : SourceCompilationPlan.exactSpecialization whole.indexed.base.plan header.named.signature.key = .ok header.named.specialized)
  (sameLayouts : header.layouts = whole.indexed.layouts)
  (sameGlobals : header.globals = whole.indexed.base.globals.length)
  (sameBindings : header.bindings = header.named.inputs)
  (sameBody : header.body = generation.body)
  (sameSolved : header.solved = header.named.specialized.function.solvedRequirements)
  {invocation : Staging.Recursive.Scope}
  (selected : (SelectedCompilationPhysicalProgramSupport.stages whole).Closure header.function invocation)
  (authority : CellAwareNamedCallPorts.Authority (compiled := whole) header.named invocation)
  (issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed header.named (diagnostics.reasonAt header.named.signature.key))
  (body : CellAwareNamedBodySupport.Body generation (CellAwareNamedBodyProducer.Certificate generation)
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: capture.administrative)
    header.context header.function.resultType)
  (support : SelectedCompilationNamedSupport.Support whole)
  (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))
  {arguments : List Dynamic.Value} {payloads : List Value}

local notation "functions" => CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel whole.compatible.checked completion.result.context.registry functions
local notation "instances" => GeneralizedLocalInstanceValues.model whole.indexed
local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel model instances
local notation "stages" => SelectedCompilationPhysicalProgramSupport.stages whole
local notation "faults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics
local notation "bridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)

private theorem reindex_physical
    {named : SourceCoreGeneralFunctions.Function} {context : SourceSemantics.Context}
    {first second : SourceCoreLocalCell.Scope} {environment : Dynamic.Environment}
    (physical : CellAwareScopePhysical.Physical whole named context first canonical mapping world before store environment)
    (same : first = second) :
    ∃ next : CellAwareScopePhysical.Physical whole named context second canonical mapping world before store environment,
      next.location = physical.location ∧ next.native = physical.native := by
  cases same
  exact ⟨physical, rfl, rfl⟩

private theorem statements : generation.statements = header.function.body := by
  have same := (RecursiveNamedPreparedSourceFrames.compiled_roots_eq generation).symm.trans
    (header.agreement.source ▸ header.agreement.roots)
  exact (List.map_inj_right (fun _ _ same => NodeId.statement.inj same)).mp same

include body record receiver extension sameLayouts sameGlobals sameBindings sameBody sameSolved selected authority issuer support in
/-- The Source allocation and body trace are independent inputs. Every native
entry, body step and saved-caller restoration is constructed from the compiler. -/
theorem preserves_selected
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world header.bindings arguments payloads)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {outcome : Staging.Recursive.BodyOutcome}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : Staging.Recursive.Size.Statements (Program.ofChecked whole.sourceProgram) stages size invocation
      header.context environment bound header.function.body finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        functions cells owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) after value finalStore finalMap finalWorld faults ∧
      CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after finalStore := by
  obtain ⟨entryEnvironment, entryHeap, entryCanonical, entryActual, entryContext, entryStore, entryMap, entryWorld,
      entryEmbedding, entryAllocated, environments, entryHeaps, sourceReceipt, agrees, actualTyped,
      prefixFrame, prefixEffect, lexical, reached, related, rows, physical, frameEq, wrap, _unwrap⟩ :=
    CellAwareNamedEntry.prepare_selected owner caller header capture sameLayouts sameGlobals record (support.certified header)
      heapTyped argumentsTyped represented heaps stable
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entryAllocated allocated
  rw [← sameEnvironment, ← sameHeap] at trace
  have sourceEq : invocation.source = CallableIndexedNamedGeneration.source header.named :=
    ((SelectedCompilationPhysicalProgramSupport.stages whole).source selected).trans header.agreement.source
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked whole.sourceProgram) header.context
      (CallableIndexedNamedGeneration.source header.named) := by
    simpa only [CallableIndexedNamedGeneration.source, header.agreement.source] using sourceReceipt.runtime
  have covers : invocation.evidence.Covers header.context := by
    simpa only [(SelectedCompilationPhysicalProgramSupport.stages whole).evidence selected] using sourceReceipt.covers
  have sameLedger : header.context.solvedRequirements =
      (CallableIndexedNamedGeneration.context whole.indexed header.named).solvedRequirements := by
    exact header.valid.ledger.trans sameSolved
  have typed : ProtectedStateImperativeTypedSourceSites.Statements
      (CallableIndexedNamedGeneration.source header.named) header.context generation.statements := by
    obtain ⟨final, facts, typed, _completes⟩ := sourceReceipt.bodyTyped
    exact ⟨_, final, facts, by simpa only [statements header generation, CallableIndexedNamedGeneration.source, header.agreement.source] using typed⟩
  let producer := CallableIndexedOwnedCellAllocationProducer.producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) headers keys cells
  have ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native := by
    intro index reached read
    have result := CallableIndexedOwnedAllocationProducer.ready_of_stable_read reached owner.position
      (by simpa only [frameEq, OwnedKey.key] using read) physical.carried
    simpa only [producer, CallableIndexedOwnedCellAllocationProducer.producer, frameEq, OwnedKey.key] using result
  rw [← statements header generation] at trace
  obtain ⟨bodyPhysical, sameLocation, sameNative⟩ := reindex_physical physical
    (show header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)) =
      CellAwareNamedBodySupport.scope header.named by rw [sameBindings]; rfl)
  have bodyReady : ProtectedStateTransition.CellAllocation.ReadyAt producer bodyPhysical.location bodyPhysical.native := by
    intro index state read
    rw [sameLocation, sameNative] at read ⊢
    exact ready state read
  have meaning := CellAwareNamedBodyMeaning.preserves_selected bridge (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
    generation record profile receiver extension authority support.registryBodies producer
    (CallableIndexedAmbient.frame_registered whole.indexed) sourceEq body issuer (Nat.le_refl size)
    (mapping := entryMap) (world := entryWorld) (actualContext := entryContext)
    (environment := entryEnvironment) (canonical := entryCanonical) (actual := entryActual)
    (before := entryHeap) (store := entryStore) (embedding := entryEmbedding)
  simp only [CellAwareNamedBodySupport.scope, ← sameBindings] at meaning
  obtain ⟨value, bodyStore, finalMap, finalWorld, evaluated, result, bodyHeaps, bodyMaps, bodyWorlds,
      bodyFrame, bodyMetadata, bodyEffect, bodyState, bodyRelated, bodyPost⟩ :=
    meaning environments entryHeaps sourceReceipt.locals agrees actualTyped runtime covers sameLedger typed reached ⟨sourceReceipt.heapTyped, rows⟩
      lexical bodyPhysical owner (sameLocation.trans frameEq).symm bodyReady trace
  have evaluatedHeader : Evaluates entryActual entryStore (header.body.rename entryEmbedding) value bodyStore := by
    simpa only [sameBody] using evaluated
  have fullEffect := prefixEffect.trans bodyEffect
  have bodyCaller : Relates caller bodyState := related.trans bodyRelated
  obtain ⟨restoredHeaps, restoredFrame, _cell, restoredRelated⟩ :=
    CellAwareOwnedBodyRestoration.restore_return caller bodyState owner.position bodyHeaps fullEffect.worlds
      (prefixFrame.trans bodyFrame) bodyCaller
  have restoredEffect := CellAwareOwnedBodyRestoration.restored_effect caller bodyState owner.position instances fullEffect
  let returned := CallableIndexedOwnedBodyRestoration.returned caller bodyState owner.position
  have supports := Dynamic.TypeContextSupports.ofClosed rfl sourceReceipt.runtime.closed sourceReceipt.runtime.closed
    sourceReceipt.runtime.variables_closed sourceReceipt.runtime.residual_variables_open
  have post := CallableIndexedOwnedPreparedStagedBodyRestorationAdmission.restore_post
    caller bodyState owner.position stable bodyPost supports restoredFrame
  refine ⟨value, _, finalMap, finalWorld, ⟨wrap evaluatedHeader, ?_⟩, restoredEffect⟩
  exact ⟨by simpa only [header.resultType] using result, restoredHeaps, fullEffect.maps, fullEffect.worlds,
    restoredFrame, fullEffect.metadata, returned, restoredRelated, post⟩

include body record receiver extension sameLayouts sameGlobals sameBindings sameBody sameSolved selected authority issuer support in
/-- Actual native completion is unwrapped through the same named entry. Its
independent Source grade and concrete saved-caller post are returned together. -/
theorem reflects_selected
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world header.bindings arguments payloads)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    {value : Value} {finalStore : Store}
    (completed : Evaluates (DataPatternValues.packValues payloads :: capture.captured) store
      (header.code.rename capture.embedding.lift) value finalStore) :
    ∃ size environment bound finalContext outcome after finalMap finalWorld,
      Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound ∧
      Staging.Recursive.Size.Statements (Program.ofChecked whole.sourceProgram) stages size invocation
        header.context environment bound header.function.body finalContext outcome after ∧
      Staging.Recursive.BodyResult header.function.resultType outcome
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) ∧
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        functions cells owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) after value finalStore finalMap finalWorld faults ∧
      CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after finalStore := by
  obtain ⟨entryEnvironment, entryHeap, entryCanonical, entryActual, entryContext, entryStore, entryMap, entryWorld,
      entryEmbedding, entryAllocated, environments, entryHeaps, sourceReceipt, agrees, actualTyped,
      prefixFrame, prefixEffect, lexical, reached, related, rows, physical, frameEq, _wrap, unwrap⟩ :=
    CellAwareNamedEntry.prepare_selected owner caller header capture sameLayouts sameGlobals record (support.certified header)
      heapTyped argumentsTyped represented heaps stable
  obtain ⟨bodyStore, bodyEvaluation, finalEq⟩ := unwrap completed
  have compiledEvaluation : Evaluates entryActual entryStore (generation.body.rename entryEmbedding) value bodyStore := by
    simpa only [sameBody] using bodyEvaluation
  obtain ⟨nativeSize, nativeTrace⟩ := evaluation_has_size compiledEvaluation
  have sourceEq : invocation.source = CallableIndexedNamedGeneration.source header.named :=
    ((SelectedCompilationPhysicalProgramSupport.stages whole).source selected).trans header.agreement.source
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked whole.sourceProgram) header.context
      (CallableIndexedNamedGeneration.source header.named) := by
    simpa only [CallableIndexedNamedGeneration.source, header.agreement.source] using sourceReceipt.runtime
  have covers : invocation.evidence.Covers header.context := by
    simpa only [(SelectedCompilationPhysicalProgramSupport.stages whole).evidence selected] using sourceReceipt.covers
  have sameLedger : header.context.solvedRequirements =
      (CallableIndexedNamedGeneration.context whole.indexed header.named).solvedRequirements := by
    exact header.valid.ledger.trans sameSolved
  have typed : ProtectedStateImperativeTypedSourceSites.Statements
      (CallableIndexedNamedGeneration.source header.named) header.context generation.statements := by
    obtain ⟨final, facts, typed, _completes⟩ := sourceReceipt.bodyTyped
    exact ⟨_, final, facts, by simpa only [statements header generation, CallableIndexedNamedGeneration.source, header.agreement.source] using typed⟩
  let producer := CallableIndexedOwnedCellAllocationProducer.producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) headers keys cells
  have ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native := by
    intro index reached read
    have result := CallableIndexedOwnedAllocationProducer.ready_of_stable_read reached owner.position
      (by simpa only [frameEq, OwnedKey.key] using read) physical.carried
    simpa only [producer, CallableIndexedOwnedCellAllocationProducer.producer, frameEq, OwnedKey.key] using result
  obtain ⟨bodyPhysical, sameLocation, sameNative⟩ := reindex_physical physical
    (show header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)) =
      CellAwareNamedBodySupport.scope header.named by rw [sameBindings]; rfl)
  have bodyReady : ProtectedStateTransition.CellAllocation.ReadyAt producer bodyPhysical.location bodyPhysical.native := by
    intro index state read
    rw [sameLocation, sameNative] at read ⊢
    exact ready state read
  have meaning := CellAwareNamedBodyMeaning.reflects_selected bridge (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
    generation record profile receiver extension authority support.registryBodies producer
    (CallableIndexedAmbient.frame_registered whole.indexed) sourceEq body issuer (Nat.le_refl nativeSize)
    (mapping := entryMap) (world := entryWorld) (actualContext := entryContext)
    (environment := entryEnvironment) (canonical := entryCanonical) (actual := entryActual)
    (before := entryHeap) (store := entryStore) (embedding := entryEmbedding)
  simp only [CellAwareNamedBodySupport.scope, ← sameBindings] at meaning
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, matched, result, bodyHeaps,
      bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, bodyEffect, bodyState, bodyRelated, bodyPost⟩ :=
    meaning environments entryHeaps sourceReceipt.locals agrees actualTyped runtime covers sameLedger typed reached ⟨sourceReceipt.heapTyped, rows⟩
      lexical bodyPhysical owner (sameLocation.trans frameEq).symm bodyReady nativeTrace
  have fullEffect := prefixEffect.trans bodyEffect
  have bodyCaller : Relates caller bodyState := related.trans bodyRelated
  obtain ⟨restoredHeaps, restoredFrame, _cell, restoredRelated⟩ :=
    CellAwareOwnedBodyRestoration.restore_return caller bodyState owner.position bodyHeaps fullEffect.worlds
      (prefixFrame.trans bodyFrame) bodyCaller
  have restoredEffect := CellAwareOwnedBodyRestoration.restored_effect caller bodyState owner.position instances fullEffect
  let returned := CallableIndexedOwnedBodyRestoration.returned caller bodyState owner.position
  have supports := Dynamic.TypeContextSupports.ofClosed rfl sourceReceipt.runtime.closed sourceReceipt.runtime.closed
    sourceReceipt.runtime.variables_closed sourceReceipt.runtime.residual_variables_open
  have post := CallableIndexedOwnedPreparedStagedBodyRestorationAdmission.restore_post
    caller bodyState owner.position stable bodyPost supports restoredFrame
  refine ⟨sourceSize, entryEnvironment, entryHeap, finalContext, outcome, after, finalMap, finalWorld,
    entryAllocated, ?_, matched, ?_, ?_⟩
  · simpa only [statements header generation] using trace
  · refine ⟨completed, ?_⟩
    rw [finalEq]
    exact ⟨by simpa only [header.resultType] using result, restoredHeaps, fullEffect.maps, fullEffect.worlds,
      restoredFrame, fullEffect.metadata, returned, restoredRelated, post⟩
  · rw [finalEq]
    exact restoredEffect

/- Compatibility adapters for callers with a whole-program receipt. -/
include body record receiver extension sameLayouts sameGlobals sameBindings sameBody sameSolved selected authority issuer wellFormed in
theorem preserves
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world header.bindings arguments payloads)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {outcome : Staging.Recursive.BodyOutcome}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : Staging.Recursive.Size.Statements (Program.ofChecked whole.sourceProgram) stages size invocation
      header.context environment bound header.function.body finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        functions cells owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) after value finalStore finalMap finalWorld faults ∧
      CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after finalStore := by
  apply preserves_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (body := body) (record := record) (receiver := receiver) (extension := extension) (sameLayouts := sameLayouts) (sameGlobals := sameGlobals) (sameBindings := sameBindings) (sameBody := sameBody) (sameSolved := sameSolved) (selected := selected) (authority := authority) (issuer := issuer) <;> assumption

include body record receiver extension sameLayouts sameGlobals sameBindings sameBody sameSolved selected authority issuer wellFormed in
theorem reflects
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world header.bindings arguments payloads)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    {value : Value} {finalStore : Store}
    (completed : Evaluates (DataPatternValues.packValues payloads :: capture.captured) store
      (header.code.rename capture.embedding.lift) value finalStore) :
    ∃ size environment bound finalContext outcome after finalMap finalWorld,
      Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound ∧
      Staging.Recursive.Size.Statements (Program.ofChecked whole.sourceProgram) stages size invocation
        header.context environment bound header.function.body finalContext outcome after ∧
      Staging.Recursive.BodyResult header.function.resultType outcome
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) ∧
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        functions cells owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) after value finalStore finalMap finalWorld faults ∧
      CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after finalStore := by
  apply reflects_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (body := body) (record := record) (receiver := receiver) (extension := extension) (sameLayouts := sameLayouts) (sameGlobals := sameGlobals) (sameBindings := sameBindings) (sameBody := sameBody) (sameSolved := sameSolved) (selected := selected) (authority := authority) (issuer := issuer) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedInvocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareNamedPreparedReceipt
/-! The actual selected row and installed physical capture fix every static
input used by the mixed named invocation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedPreparedReceipt
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header NamedCapture)

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header whole (Program.ofChecked whole.sourceProgram))}
  {key : CallableIndexedOwnedFunctionValues.Key whole (Program.ofChecked whole.sourceProgram)}
  {mapping : LocationMap} {world : StoreTyping} {store : Store}
  {header : Header whole (Program.ofChecked whole.sourceProgram)}

private theorem globals_types (globals : List SourceCoreCalls.Signature) (base : Nat) :
    (SourceCoreLambdaTemplates.freshGlobals globals base).map Value.type = globals.map (·.referenceType) := by
  simp only [SourceCoreLambdaTemplates.freshGlobals, List.map_map]
  change globals.zipIdx.map (fun pair => pair.1.referenceType) = _
  change globals.zipIdx.map ((fun signature => signature.referenceType) ∘ Prod.fst) = _
  rw [← List.map_map, List.zipIdx_map_fst]

/-- Runtime tags fix the types of the actual canonical physical references.
No unused administrative suffix is invented. -/
theorem administrative
    (capture : CallableIndexedOwnedNamedPhysicalCaptures.Capture headers key header mapping world store) :
    capture.named.administrative = whole.indexed.base.globals.map (·.referenceType) ++
      [.cell whole.indexed.ancestry.layout.frame.type] := by
  have tags := capture.named.environments.runtime_hasTypes.type_tags
  change capture.named.canonical.map Value.type = capture.named.administrative at tags
  rw [capture.canonical_eq] at tags
  have eq : (CallableIndexedOwnedPhysicalGlobals.environment whole).map Value.type =
      whole.indexed.base.globals.map (·.referenceType) ++ [.cell whole.indexed.ancestry.layout.frame.type] := by
    simp only [CallableIndexedOwnedPhysicalGlobals.environment, SourceCoreCallableIndexedTemplates.globalEnvironment,
      List.map_append, globals_types, List.map_cons, List.map_nil, Value.type]
  exact tags.symm.trans eq

def cast_generation {first second : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
    {code : Expr} (same : first = second)
    (generation : CallableIndexedNamedGeneration.Compilation whole.indexed first diagnostics code) :
    CallableIndexedNamedGeneration.Compilation whole.indexed second diagnostics code := same ▸ generation

@[simp] theorem cast_generation_body {first second : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
    {code : Expr} (same : first = second)
    (generation : CallableIndexedNamedGeneration.Compilation whole.indexed first diagnostics code) :
    (cast_generation same generation).body = generation.body := by cases same; rfl

def cast_body {first second : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
    {code : Expr} (same : first = second)
    (generation : CallableIndexedNamedGeneration.Compilation whole.indexed first diagnostics code)
    {administrative : Core.Context} {context : SourceSemantics.Context} {expected : TypeSystem.Ty}
    (body : CellAwareNamedBodySupport.Body generation (CellAwareNamedBodyProducer.Certificate generation)
      administrative context expected) :
    CellAwareNamedBodySupport.Body (cast_generation same generation)
      (CellAwareNamedBodyProducer.Certificate (cast_generation same generation)) administrative context expected := by
  cases same
  exact body

variable {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared whole row)
  {instantiation : DeclarationInstantiation}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
  (capture : CallableIndexedOwnedNamedPhysicalCaptures.Capture headers key header mapping world store)

structure Receipt where
  generation : CallableIndexedNamedGeneration.Compilation whole.indexed header.named prepared.diagnostics prepared.code
  emitted : header.body = generation.body
  body : CellAwareNamedBodySupport.Body generation (CellAwareNamedBodyProducer.Certificate generation)
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: capture.named.administrative)
    header.context header.function.resultType
  issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed header.named
    (prepared.diagnostics.reasonAt header.named.signature.key)

include aligned in
theorem of_header_selected {recipe : SourceCoreIndexedSession.Recipe}
    (ready : SourceCoreIndexedSession.Recipe.prepare whole = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    (bodyTyping : SelectedCompilationBodyTyping.Bodies whole)
    {entry : SourceCoreCallableIndexedPrograms.Entry whole.indexed.layouts}
    (member : entry ∈ whole.indexed.entries)
    (profile : CellAwareNamedBodyProducer.Profile whole.indexed prepared.named prepared.compilation.statements
      prepared.named.specialized.function.inferredBodyType) :
    Nonempty (Receipt prepared capture) := by
  obtain ⟨body⟩ := CellAwareNamedBodyReceipt.of_header_selected prepared aligned ready bodyTyping member profile
  let generation := cast_generation aligned.named.symm prepared.compilation
  have actual := cast_body aligned.named.symm prepared.compilation body
  have prefixEq : RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial whole.compatible.checked) header =
      SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: capture.named.administrative := by
    simp only [RecursiveNamedLambdaFormationHeads.nativePrefix, administrative capture, header.parameterType, List.cons_append]
  have issuer := CellAwareNamedDiagnosticIssuer.of_prepared prepared diagnostic aligned
  rw [aligned.reasonAt] at issuer
  have issuerAt : CellAwareNamedDiagnosticIssuer.Named whole.indexed header.named
      (prepared.diagnostics.reasonAt header.named.signature.key) := by
    simpa only [aligned.named] using issuer
  exact ⟨⟨generation, aligned.body.trans (cast_generation_body aligned.named.symm prepared.compilation).symm,
    prefixEq ▸ actual, issuerAt⟩⟩

/- Compatibility adapters for callers with a whole-program receipt. -/
include aligned in
theorem of_header {recipe : SourceCoreIndexedSession.Recipe}
    (ready : SourceCoreIndexedSession.Recipe.prepare whole = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))
    {entry : SourceCoreCallableIndexedPrograms.Entry whole.indexed.layouts}
    (member : entry ∈ whole.indexed.entries)
    (profile : CellAwareNamedBodyProducer.Profile whole.indexed prepared.named prepared.compilation.statements
      prepared.named.specialized.function.inferredBodyType) :
    Nonempty (Receipt prepared capture) := by
  apply of_header_selected (bodyTyping := SelectedCompilationBodyTyping.Bodies.of_program wellFormed) (aligned := aligned) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedPreparedReceipt
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareNamedSourceTreeLifting
/-! Independent ordinary Source bodies follow the actual compiler tree.
Generalized declarations construct their real physical state before recursion. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedSourceTreeLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
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


include bindings record registered in
theorem lifts
    (children : ∀ context, Dynamic.SourceRuntimeValid program context (source named) →
      invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeSourceLiftBounds.LiftsAt bridge context model named registry invocation (certificates context) size)
    (sourceEq : invocation.source = source named)
    {administrative : Core.Context} {reasonAt : ExpressionId → Word}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : CellAwareNativeBodyTree.Tree whole.indexed named compiled certificates administrative reasonAt
      context scope true statements expected type code)
    (issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed named reasonAt) :
    CellAwareSourceBodyLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope statements := by
  generalize modeEq : true = mode at tree
  induction tree with
  | returning rest found form expressionFound valueType typed certified =>
    cases modeEq
    exact CellAwareSourceTerminalLifting.terminal bridge producer sourceEq
      (.returning rest (by simpa only [sourceEq] using lookupStatement?_sound found) form)
      (by simpa only [sourceEq] using expressionFound) (by simpa only [sourceEq] using typed)
      certified (children _)
  | tail found form expressionFound valueType typed certified =>
    exact CellAwareSourceTerminalLifting.terminal bridge producer sourceEq
      (.tail (by simpa only [sourceEq] using lookupStatement?_sound found) form)
      (by simpa only [sourceEq] using expressionFound) (by simpa only [sourceEq] using typed)
      certified (children _)
  | @generalizedInitialized context nextContext scope mode id node binder initializer initializerNode parameters result lambdaBody rest expected type lowered body childFuel
      found form declaration polymorphic extended ordinary initializerFound initializerForm valueType requirements coercions site initial nativeTyped allocation annotation same captured copied remaining ih =>
    cases modeEq
    exact CellAwareSourceGeneralizedPrefixLifting.generalized bridge bindings compiled record producer registered
      (type := type) (body := body) found form declaration polymorphic extended ordinary initializerFound initializerForm
      valueType requirements coercions site initial nativeTyped allocation annotation same copied sourceEq issuer (ih rfl)

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedSourceTreeLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareNamedProgramProfiles
/-! The complete ordered named cache receives finite compiler profiles.
Root extraction accepts only the actual statement-root action, and a selected
slot recovers its original profile without dropping any other cached row. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedProgramProfiles
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation source)

def statements (named : SourceCoreGeneralFunctions.Function) :
    Except SourceCoreGeneralFunctions.Error (List StatementId) :=
  (source named).roots.mapM (fun
    | .statement id => pure id
    | .expression id => throw (.expectedStatementRoot id))

structure Entry {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (named : SourceCoreGeneralFunctions.Function) where
  roots : List StatementId
  extracted : statements named = .ok roots
  profile : CellAwareNamedBodyProducer.Profile prepared named roots
    named.specialized.function.inferredBodyType

def entry? {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (named : SourceCoreGeneralFunctions.Function) : Option (Entry prepared named) :=
  match extracted : statements named with
  | .error _ => none
  | .ok roots => do
    let profile ← CellAwareNamedBodyProducer.profile? prepared named roots
      named.specialized.function.inferredBodyType
    pure ⟨roots, extracted, profile⟩

inductive Rows {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked) :
    List SourceCoreGeneralFunctions.Function → Type where
  | nil : Rows prepared []
  | cons {named rest} (entry : Entry prepared named) (tail : Rows prepared rest) :
      Rows prepared (named :: rest)

def rows? {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked) :
    (named : List SourceCoreGeneralFunctions.Function) → Option (Rows prepared named)
  | [] => some .nil
  | named :: rest => do
    let entry ← entry? prepared named
    let tail ← rows? prepared rest
    pure (.cons entry tail)

abbrev Profile {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked) :=
  Rows prepared prepared.base.functions

def profile? {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked) :
    Option (Profile prepared) := rows? prepared prepared.base.functions

theorem Rows.at_slot {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {named : List SourceCoreGeneralFunctions.Function} (rows : Rows prepared named)
    {index : Nat} {function : SourceCoreGeneralFunctions.Function}
    (selected : named[index]? = some function) : Nonempty (Entry prepared function) := by
  induction rows generalizing index with
  | nil => simp only [List.getElem?_nil] at selected; cases selected
  | cons entry tail ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero] at selected
      cases selected
      exact ⟨entry⟩
    | succ index => exact ih selected

def Entry.for_compilation {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {named : SourceCoreGeneralFunctions.Function} (entry : Entry prepared named)
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (compiled : Compilation prepared named diagnostics code) :
    CellAwareNamedBodyProducer.Profile prepared named compiled.statements
      named.specialized.function.inferredBodyType := by
  have same : entry.roots = compiled.statements := Except.ok.inj (entry.extracted.symm.trans compiled.roots)
  exact same ▸ entry.profile

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedProgramProfiles
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareNamedSourceBodyLifting
/-! The accepted body supplies all lifting evidence internally. Ordinary Source
execution may stop at an actual selected-stage rejection at its reached heap. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedSourceBodyLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole (Program.ofChecked whole.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole (Program.ofChecked whole.sourceProgram))}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (bindings : ProtectedStateTransition.Bindings protocol)
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  (compiled : CallableIndexedNamedGeneration.Compilation whole.indexed named diagnostics namedCode)
  (record : SourceCompilationPlan.exactSpecialization whole.indexed.base.plan named.signature.key = .ok named.specialized)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : whole.compatible.checked.catalog.callableContracts = true)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver whole.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt whole.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial whole.compatible.checked).registry
    completion.result.context.registry)
  {invocation : Staging.Recursive.Scope}
  (authority : CellAwareNamedCallPorts.Authority (compiled := whole) named invocation)
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies (Program.ofChecked whole.sourceProgram) (SelectedCompilationPhysicalProgramSupport.stages whole))
  (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))

local notation "functions" => CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel whole.compatible.checked completion.result.context.registry functions
local notation "stages" => SelectedCompilationPhysicalProgramSupport.stages whole
local notation "faults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics
local notation "program" => Program.ofChecked whole.sourceProgram

variable
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel
      (CompatibleAmbientHeap.payloadModel whole.compatible.checked completion.result.context.registry
        (CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults profile))
      (GeneralizedLocalInstanceValues.model whole.indexed)))
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)


include bindings record receiver extension authority selectedBodies registered in
theorem lifts_selected
    (sourceEq : invocation.source = source named)
    {administrative : Core.Context} {context : SourceSemantics.Context} {expected : TypeSystem.Ty}
    (body : CellAwareNamedBodySupport.Body compiled (CellAwareNamedBodyProducer.Certificate compiled)
      administrative context expected)
    (issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed named (diagnostics.reasonAt named.signature.key)) :
    CellAwareSourceBodyLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := stages) (invocation := invocation) bridge producer context
      (CellAwareNamedBodySupport.scope named) compiled.statements := by
  exact CellAwareNamedSourceTreeLifting.lifts bridge bindings compiled record producer registered
    (fun childContext childRuntime childCovers childLedger size =>
      CellAwareNamedExpressionSourceLifting.lifts_selected compiled bridge profile receiver extension authority sourceEq issuer
        record childLedger (by simpa only [sourceEq] using childRuntime) selectedBodies childCovers size)
    sourceEq body.tree issuer

/- Compatibility adapters for callers with a whole-program receipt. -/
include bindings record receiver extension authority wellFormed registered in
theorem lifts
    (sourceEq : invocation.source = source named)
    {administrative : Core.Context} {context : SourceSemantics.Context} {expected : TypeSystem.Ty}
    (body : CellAwareNamedBodySupport.Body compiled (CellAwareNamedBodyProducer.Certificate compiled)
      administrative context expected)
    (issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed named (diagnostics.reasonAt named.signature.key)) :
    CellAwareSourceBodyLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := stages) (invocation := invocation) bridge producer context
      (CellAwareNamedBodySupport.scope named) compiled.statements := by
  apply lifts_selected (selectedBodies := Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed) (bindings := bindings) (record := record) (receiver := receiver) (extension := extension) (authority := authority) (registered := registered) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedSourceBodyLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareNamedSourceInvocation
/-! Original Source bodies are lifted from the actual marked parameter entry.
The resulting public invocation includes the real earlier stage stop when a
guard rejects, retaining its reached heap and the saved caller restoration. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedSourceInvocation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedFunctionValues (Header NamedCapture OwnedKey)

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header whole (Program.ofChecked whole.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole (Program.ofChecked whole.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : whole.compatible.checked.catalog.callableContracts = true)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver whole.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt whole.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial whole.compatible.checked).registry
    completion.result.context.registry)
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {canonical : Environment}
  (owner : OwnedKey keys)
  (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (header : Header whole (Program.ofChecked whole.sourceProgram))
  (capture : NamedCapture headers owner.key header mapping world)
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (generation : CallableIndexedNamedGeneration.Compilation whole.indexed header.named diagnostics code)
  (record : SourceCompilationPlan.exactSpecialization whole.indexed.base.plan header.named.signature.key = .ok header.named.specialized)
  (sameLayouts : header.layouts = whole.indexed.layouts)
  (sameGlobals : header.globals = whole.indexed.base.globals.length)
  (sameBindings : header.bindings = header.named.inputs)
  (sameBody : header.body = generation.body)
  (sameSolved : header.solved = header.named.specialized.function.solvedRequirements)
  {invocation : Staging.Recursive.Scope}
  (selected : (SelectedCompilationPhysicalProgramSupport.stages whole).Closure header.function invocation)
  (authority : CellAwareNamedCallPorts.Authority (compiled := whole) header.named invocation)
  (issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed header.named (diagnostics.reasonAt header.named.signature.key))
  (body : CellAwareNamedBodySupport.Body generation (CellAwareNamedBodyProducer.Certificate generation)
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: capture.administrative)
    header.context header.function.resultType)
  (support : SelectedCompilationNamedSupport.Support whole)
  (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))
  {arguments : List Dynamic.Value} {payloads : List Value}

local notation "functions" => CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel whole.compatible.checked completion.result.context.registry functions
local notation "instances" => GeneralizedLocalInstanceValues.model whole.indexed
local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel model instances
local notation "stages" => SelectedCompilationPhysicalProgramSupport.stages whole
local notation "faults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics
local notation "bridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)

private theorem reindex_physical
    {named : SourceCoreGeneralFunctions.Function} {context : SourceSemantics.Context}
    {first second : SourceCoreLocalCell.Scope} {environment : Dynamic.Environment}
    (physical : CellAwareScopePhysical.Physical whole named context first canonical mapping world before store environment)
    (same : first = second) :
    ∃ next : CellAwareScopePhysical.Physical whole named context second canonical mapping world before store environment,
      next.location = physical.location ∧ next.native = physical.native := by
  cases same
  exact ⟨physical, rfl, rfl⟩

private theorem statements : generation.statements = header.function.body := by
  have same := (RecursiveNamedPreparedSourceFrames.compiled_roots_eq generation).symm.trans
    (header.agreement.source ▸ header.agreement.roots)
  exact (List.map_inj_right (fun _ _ same => NodeId.statement.inj same)).mp same


include body record receiver extension sameLayouts sameGlobals sameBindings sameSolved selected authority issuer support in
theorem lift_selected
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world header.bindings arguments payloads)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.FunctionOutcome (Program.ofChecked whole.sourceProgram) size
      header.context invocation.evidence invocation.source environment bound header.function.body finalContext outcome after) :
    ∃ stagedSize stagedContext stagedOutcome reached,
      Staging.Recursive.Size.Statements (Program.ofChecked whole.sourceProgram) stages stagedSize invocation
        header.context environment bound header.function.body stagedContext stagedOutcome reached ∧
      SelectedCompilationStageBodyLiftBounds.BodyAdapted finalContext outcome after stagedContext stagedOutcome reached := by
  obtain ⟨entryEnvironment, entryHeap, entryCanonical, entryActual, entryContext, entryStore, entryMap, entryWorld,
      entryEmbedding, entryAllocated, environments, entryHeaps, sourceReceipt, agrees, actualTyped,
      _prefixFrame, _prefixEffect, lexical, reached, _related, rows, physical, frameEq, _wrap, _unwrap⟩ :=
    CellAwareNamedEntry.prepare_selected owner caller header capture sameLayouts sameGlobals record (support.certified header)
      heapTyped argumentsTyped represented heaps stable
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entryAllocated allocated
  rw [← sameEnvironment, ← sameHeap] at trace
  have sourceEq : invocation.source = CallableIndexedNamedGeneration.source header.named :=
    ((SelectedCompilationPhysicalProgramSupport.stages whole).source selected).trans header.agreement.source
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked whole.sourceProgram) header.context
      (CallableIndexedNamedGeneration.source header.named) := by
    simpa only [CallableIndexedNamedGeneration.source, header.agreement.source] using sourceReceipt.runtime
  have covers : invocation.evidence.Covers header.context := by
    simpa only [(SelectedCompilationPhysicalProgramSupport.stages whole).evidence selected] using sourceReceipt.covers
  have sameLedger : header.context.solvedRequirements =
      (CallableIndexedNamedGeneration.context whole.indexed header.named).solvedRequirements := by
    exact header.valid.ledger.trans sameSolved
  have typed : ProtectedStateImperativeTypedSourceSites.Statements
      (CallableIndexedNamedGeneration.source header.named) header.context generation.statements := by
    obtain ⟨final, facts, typed, _completes⟩ := sourceReceipt.bodyTyped
    exact ⟨_, final, facts, by simpa only [statements header generation, CallableIndexedNamedGeneration.source, header.agreement.source] using typed⟩
  let producer := CallableIndexedOwnedCellAllocationProducer.producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) headers keys cells
  have ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native := by
    intro index reached read
    have result := CallableIndexedOwnedAllocationProducer.ready_of_stable_read reached owner.position
      (by simpa only [frameEq, OwnedKey.key] using read) physical.carried
    simpa only [producer, CallableIndexedOwnedCellAllocationProducer.producer, frameEq, OwnedKey.key] using result
  rw [← statements header generation] at trace
  obtain ⟨bodyPhysical, sameLocation, sameNative⟩ := reindex_physical physical
    (show header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)) =
      CellAwareNamedBodySupport.scope header.named by rw [sameBindings]; rfl)
  have bodyReady : ProtectedStateTransition.CellAllocation.ReadyAt producer bodyPhysical.location bodyPhysical.native := by
    intro index state read
    rw [sameLocation, sameNative] at read ⊢
    exact ready state read
  have meaning := CellAwareNamedSourceBodyLifting.lifts_selected bridge (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys) generation record profile receiver extension authority
    support.registryBodies producer (CallableIndexedAmbient.frame_registered whole.indexed) sourceEq body issuer
    (size := size) (mapping := entryMap) (world := entryWorld) (actualContext := entryContext)
    (environment := entryEnvironment) (canonical := entryCanonical) (actual := entryActual)
    (before := entryHeap) (store := entryStore) (embedding := entryEmbedding)
  simp only [CellAwareNamedBodySupport.scope, ← sameBindings] at meaning
  obtain ⟨stagedContext, stagedOutcome, reachedHeap, lifted, adapted⟩ :=
    meaning environments entryHeaps sourceReceipt.locals agrees actualTyped runtime covers sameLedger typed
      reached ⟨sourceReceipt.heapTyped, rows⟩ lexical bodyPhysical owner (sameLocation.trans frameEq).symm bodyReady trace
  have actual : Staging.Recursive.Statements (Program.ofChecked whole.sourceProgram) stages invocation
      header.context environment bound header.function.body stagedContext stagedOutcome reachedHeap := by
    simpa only [sameEnvironment, sameHeap, statements header generation] using lifted
  obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Statements.of_trace actual
  exact ⟨stagedSize, stagedContext, stagedOutcome, reachedHeap, measured, adapted⟩

include body record receiver extension sameLayouts sameGlobals sameBindings sameBody sameSolved selected authority issuer support in
theorem preserves_selected
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world header.bindings arguments payloads)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.FunctionOutcome (Program.ofChecked whole.sourceProgram) size
      header.context invocation.evidence invocation.source environment bound header.function.body finalContext outcome after) :
    ∃ stagedContext stagedOutcome reached value finalStore finalMap finalWorld,
      SelectedCompilationStageBodyLiftBounds.BodyAdapted finalContext outcome after stagedContext stagedOutcome reached ∧
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        functions cells owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result stagedOutcome) reached value finalStore finalMap finalWorld faults ∧
      CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld reached finalStore := by
  obtain ⟨stageSize, stagedContext, stagedOutcome, reached, measured, adapted⟩ :=
    lift_selected profile receiver extension owner caller header capture generation record sameLayouts sameGlobals sameBindings
      sameSolved selected authority issuer body support stable heapTyped argumentsTyped represented heaps allocated trace
  obtain ⟨value, finalStore, finalMap, finalWorld, result, effect⟩ :=
    CellAwareNamedInvocation.preserves_selected profile receiver extension owner caller header capture generation record sameLayouts
      sameGlobals sameBindings sameBody sameSolved selected authority issuer body support stable heapTyped argumentsTyped
      represented heaps allocated measured
  exact ⟨stagedContext, stagedOutcome, reached, value, finalStore, finalMap, finalWorld, adapted, result, effect⟩

/- Compatibility adapters for callers with a whole-program receipt. -/
include body record receiver extension sameLayouts sameGlobals sameBindings sameSolved selected authority issuer wellFormed in
theorem lift
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world header.bindings arguments payloads)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.FunctionOutcome (Program.ofChecked whole.sourceProgram) size
      header.context invocation.evidence invocation.source environment bound header.function.body finalContext outcome after) :
    ∃ stagedSize stagedContext stagedOutcome reached,
      Staging.Recursive.Size.Statements (Program.ofChecked whole.sourceProgram) stages stagedSize invocation
        header.context environment bound header.function.body stagedContext stagedOutcome reached ∧
      SelectedCompilationStageBodyLiftBounds.BodyAdapted finalContext outcome after stagedContext stagedOutcome reached := by
  apply lift_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (body := body) (record := record) (receiver := receiver) (extension := extension) (sameLayouts := sameLayouts) (sameGlobals := sameGlobals) (sameBindings := sameBindings) (sameSolved := sameSolved) (selected := selected) (authority := authority) (issuer := issuer) <;> assumption

include body record receiver extension sameLayouts sameGlobals sameBindings sameBody sameSolved selected authority issuer wellFormed in
theorem preserves
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world header.bindings arguments payloads)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.FunctionOutcome (Program.ofChecked whole.sourceProgram) size
      header.context invocation.evidence invocation.source environment bound header.function.body finalContext outcome after) :
    ∃ stagedContext stagedOutcome reached value finalStore finalMap finalWorld,
      SelectedCompilationStageBodyLiftBounds.BodyAdapted finalContext outcome after stagedContext stagedOutcome reached ∧
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        functions cells owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result stagedOutcome) reached value finalStore finalMap finalWorld faults ∧
      CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld reached finalStore := by
  apply preserves_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (body := body) (record := record) (receiver := receiver) (extension := extension) (sameLayouts := sameLayouts) (sameGlobals := sameGlobals) (sameBindings := sameBindings) (sameBody := sameBody) (sameSolved := sameSolved) (selected := selected) (authority := authority) (issuer := issuer) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedSourceInvocation
end
