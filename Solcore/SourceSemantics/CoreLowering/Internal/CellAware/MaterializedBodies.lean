import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.BodyMeaning
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.BodyEntries
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.PublicHistories
import Solcore.SourceSemantics.CoreLowering.PublicSupport
import Solcore.SourceSemantics.CoreLowering.RecursivePublicPackedArguments
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectClosureApplicationBounds
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.NamedEntries
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.StagedProjected
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.MaterializedExpressions
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalSourceBodyInversion
import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeStatementSuffixTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedFlowOutcomes
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedLexicalFooter
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.NamedBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.NamedAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.ProgramAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedLexicalCollectors
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderSourceTyping
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderScopeDeclarations
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.ReadEffects
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryAllocation
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedSourceFrames
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedPhysicalCaptures
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.ForLoops

/-!
# Cell-aware bodies: the materialized family

Named bodies that materialize generalized local functions: packed application, tree bounds, body meaning and receipts, profiles and the named invocation.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedPackedApplication
/-! A retained materialized handle uses its authentic owned frame at the current
public caller. Actual packed input typing supplies its Source argument row;
zero, singleton and multiple arguments keep the original packing convention. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedPackedApplication
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open GeneralizedLocalMaterializedAssociation
open CellAwarePublicApplicationResult (ResultAt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry
    completion.result.context.registry)
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {canonical : Environment}
  (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (stable : StableRows caller)
  {context : SourceSemantics.Context} {callerSource : TypedSource}
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context callerSource)
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies (Program.ofChecked compiled.sourceProgram)
      (SelectedCompilationPhysicalProgramSupport.stages compiled))
  (heapTyped : Dynamic.HeapWellTyped context before)
  {function : Dynamic.Closure} {native : Value} {bindings : List CallableIndexedParameterCertificates.Binding}
  {parameter result : TypeSystem.Ty} {parameterCore resultCore : Core.Ty}
  (member : Association compiled mapping world function native bindings parameterCore resultCore)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (atFrame : member.AtFrame owner.key.frameLocation)
  (calleeTyped : Dynamic.ValueHasType context before (.closure function) (.function parameter result))
  {packedSource : Dynamic.Value} {packedNative : Value}
  (packedTyped : Dynamic.ValueHasType context before packedSource parameter)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions
local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)
local notation "callStages" => SelectedCompilationPhysicalProgramSupport.stages compiled
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

variable (packedRelated : ValueRep compiled.compatible.checked completion.result.context.registry functions
    mapping world parameter packedSource packedNative parameterCore)
  (heaps : GenericHeap.CellHeapRepresents
    (GeneralizedLocalDescriptorHeap.cellModel
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
      (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store)

include profile runtime heapTyped member calleeTyped packedTyped packedRelated in
private theorem arguments :
    ∃ sources values,
      Dynamic.ValuesPack sources packedSource ∧ sources.length = function.parameters.length ∧
      packedNative = DataPatternValues.packValues values ∧
      CallableIndexedParameterMeaning.Arguments model mapping world bindings sources values ∧
      CallableIndexedOwnedStoredClosureSourceArguments.SourceArguments function before sources ∧
      Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function := by
  obtain ⟨parameterEq, _resultEq, signatures, code, covers, _captures⟩ := calleeTyped.closure_function_inv
  have frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function :=
    ⟨signatures.trans runtime.signatures, code.owner, code, code.requirement_ledger.idsUnique, covers⟩
  have sourceBundle : parameter = TypeSystem.Ty.productMany (bindings.map (fun binding => binding.1.scheme.body)) := by
    rw [member.source_binders]
    exact parameterEq
  have packed := packedRelated
  rw [sourceBundle, GeneralizedLocalMaterializedArgumentRows.parameter_core member frame profile] at packed
  obtain ⟨sources, values, packing, nativeEq, represented⟩ := RecursivePublicPackedArguments.arguments bindings
    (GeneralizedLocalMaterializedArgumentRows.projected_bindings member frame) packed
  have length : bindings.length = function.parameters.length := by
    simpa only [List.length_map] using congrArg List.length member.source_binders
  have arity := represented.length.1.symm.trans length
  have sourceTyped := packing.unpackTypes (parameterEq ▸ packedTyped) (by simpa only [List.length_map] using arity)
  have raw := CallableIndexedOwnedStoredClosureSourceArguments.at_arguments runtime calleeTyped heapTyped
    sourceTyped packing parameterEq.symm arity
  exact ⟨sources, values, packing, arity, nativeEq, represented, raw, frame⟩

include profile receiver extension stable runtime selectedBodies heapTyped atFrame calleeTyped packedTyped packedRelated heaps in
/-- The original packed Source call constructs the actual handle payload
execution and returns the same mixed heap and restored caller pool. -/
theorem preserves {invocation : Staging.Recursive.Scope} {tail : Environment}
    {sources : List Dynamic.Value} (packing : Dynamic.ValuesPack sources packedSource)
    (arity : sources.length = function.parameters.length)
    {size : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) callStages size invocation context
      before (.closure function) sources outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (native :: packedNative :: tail) store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      ResultAt (registry := completion.result.context.registry) functions cells caller context result resultCore
        outcome after value finalStore finalMap finalWorld callFaults := by
  obtain ⟨decoded, values, decodedPacking, decodedArity, nativeEq, represented, raw, frame⟩ :=
    arguments functions profile runtime heapTyped member calleeTyped packedTyped packedRelated
  have same : decoded = sources := decodedPacking.injective_of_length_eq packing (decodedArity.trans arity.symm)
  subst decoded
  have resultEq := calleeTyped.closure_function_inv.2.1
  subst result
  cases member with
  | viewed material view _typed =>
    obtain ⟨inputs⟩ := GeneralizedLocalBodyCompiler.entry_context material frame material.ownership
    obtain ⟨value, finalStore, evaluated, finalMap, finalWorld, representedResult, finalHeaps,
        maps, worlds, preserved, metadata, _effect, returned, related, post⟩ :=
      GeneralizedLocalApplicationMeaning.preserves (faults := callFaults) material view inputs functions extension owner caller
        atFrame frame raw stable runtime selectedBodies (material.body_uninitialized receiver) (fun _ _ proof => proof)
        represented heaps trace
    obtain ⟨nativeSize, measured⟩ := evaluation_has_size evaluated
    have padded : EvaluationSize nativeSize (view.native :: packedNative :: tail) store
        CallableIndexedLambdaCalls.applyPayload value finalStore := by
      rw [nativeEq]
      exact RecursiveNamedPublicDirectClosureApplicationBounds.application_tail measured
    exact ⟨value, finalStore, finalMap, finalWorld, padded.sound, representedResult, finalHeaps,
      maps, worlds, preserved, metadata, returned, related, post⟩

include profile receiver extension stable runtime selectedBodies heapTyped atFrame calleeTyped packedTyped packedRelated heaps in
/-- Completion of the actual handle payload reconstructs its ordered Source
arguments and call, even when its lexical frame belongs to a different owner. -/
theorem reflects {invocation : Staging.Recursive.Scope} {tail : Environment}
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (native :: packedNative :: tail) store CallableIndexedLambdaCalls.applyPayload value finalStore) :
    ∃ sources,
      Dynamic.ValuesPack sources packedSource ∧ sources.length = function.parameters.length ∧
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) callStages sourceSize invocation context
          before (.closure function) sources outcome after ∧
        ResultAt (registry := completion.result.context.registry) functions cells caller context result resultCore
          outcome after value finalStore finalMap finalWorld callFaults := by
  obtain ⟨sources, values, packing, arity, nativeEq, represented, raw, frame⟩ :=
    arguments functions profile runtime heapTyped member calleeTyped packedTyped packedRelated
  have resultEq := calleeTyped.closure_function_inv.2.1
  subst result
  cases member with
  | viewed material view _typed =>
    obtain ⟨inputs⟩ := GeneralizedLocalBodyCompiler.entry_context material frame material.ownership
    obtain ⟨sidecar, _accepted, selected⟩ := material.scope_at
    have evaluation : EvaluationSize size [view.native, DataPatternValues.packValues values] store
        CallableIndexedLambdaCalls.applyPayload value finalStore := by
      rw [← nativeEq]
      exact RecursiveNamedPublicDirectClosureApplicationBounds.application_tail completed
    obtain ⟨sourceSize, outcome, after, trace, finalMap, finalWorld, representedResult, finalHeaps,
        maps, worlds, preserved, metadata, _effect, returned, related, post⟩ :=
      GeneralizedLocalApplicationMeaning.reflects (faults := callFaults) (registry := callStages)
        material view inputs functions extension owner caller atFrame frame raw stable runtime selectedBodies
        (material.body_uninitialized receiver) (fun _ _ proof => proof) represented heaps (.anonymous selected) evaluation.sound
    exact ⟨sources, packing, arity, sourceSize, outcome, after, finalMap, finalWorld, trace,
      representedResult, finalHeaps, maps, worlds, preserved, metadata, returned, related, post⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedPackedApplication
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedNamedBodyTreeBounds
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
      headTyped
      found form polymorphic capturesNamed
    have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
    obtain ⟨values, marker, copiedStore, copiedMap, copiedWorld, agreement, _smaller, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
        preserved, effect, nextAuthority, reached, related, nextAdmitted, nextPhysical, locationEq, nativeEq⟩ :=
      CellAwareNamedGeneralizedPrefix.complete bridge compiled record site initialReceipt issuer declaration polymorphic extended
        ordinary nativeTyped allocation annotation same copied producer bindings registered environments heaps locals agrees
        actualTyped initial admitted authority physical ready snapshotNamed capturesNamed functionTyped allocated type body
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
      (value := .cellRef (OptionalCell.cellType lowered.type) (copiedStore.length + 2)) tailState
    refine ⟨value, finalStore, finalMap, finalWorld, agreement.wrap evaluated, represented, output, finalHeaps,
      effect.maps.trans maps, effect.worlds.trans worlds, preserved.trans finalFrame,
      effect.metadata.trans metadata, effect.trans finalEffect, finalState,
      protocol.trans related (protocol.trans tailRelated (bindings.restore_related
        (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (id := binder.id) (type := lowered.type)
        (value := .cellRef (OptionalCell.cellType lowered.type) (copiedStore.length + 2)) tailState)), ?_⟩
    exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (copiedStore.length + 2)) tailState post

end Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedNamedBodyTreeBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedNamedBodyFinish
/-! The actual named compiler footer consumes the bounded body’s original
returned value or fault. It leaves the reached mixed heap and frame unchanged. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedNamedBodyFinish
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
    {compiled : SourceCoreUnifiedCompilation.Compiled} {location : Core.Location}
    (represented : Represents model mapping world true raw type faults outcome value)
    (output : CellAwareMaterializedFlowOutput.FlowAt compiled mapping world location outcome value)
    (terminal : ∃ result, outcome = CallableIndexedOwnedAdmittedStagedTerminalStatements.control result)
    (evaluated : Evaluates actual before flow value after) (escaped : Word) (fallback : Expr) :
    ∃ native, Evaluates actual before
      (CallableIndexedOwnedAdmittedStagedTerminalBody.code type flow escaped fallback) native after ∧
      RecursiveStageMeaning.ResultRepresentsFor model mapping world raw type faults
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) native ∧
      CellAwareMaterializedOutput.OutcomeAt compiled mapping world location
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) native := by
  obtain ⟨result, rfl⟩ := terminal
  cases result with
  | value source =>
    cases represented with
    | returned payload =>
      obtain ⟨rawValue, same, positive⟩ := output source rfl
      cases same
      refine ⟨_, LocalControl.finish_returned type (LocalLoop.toControl_normal type escaped evaluated),
        .value payload, ?_⟩
      intro other sameSource
      cases sameSource
      exact ⟨_, rfl, positive⟩
  | fault failure =>
    cases represented with
    | fault matched =>
      exact ⟨_, LocalControl.finish_failure type (LocalLoop.toControl_failure type escaped evaluated),
        .fault matched, CellAwareMaterializedOutput.OutcomeAt.fault⟩

include record bindings registered in
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
      CellAwareMaterializedOutput.OutcomeAt whole finalMap finalWorld owner.key.frameLocation
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
  obtain ⟨flowValue, finalStore, finalMap, finalWorld, evaluated, represented, output, finalHeaps,
      maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
    CellAwareMaterializedNamedBodyTreeBounds.preserves bridge bindings compiled record producer registered children sourceEq tree issuer within
      environments heaps locals agrees actualTyped runtime covers sameLedger typed initial admitted authority physical owner sameLocation ready trace
  have terminal := CellAwareNamedBodyTreeBounds.terminal_outcome compiled tree sourceEq
    (by simpa only [sourceEq] using runtime.graph.nodeOccurrencesUnique) trace
  obtain ⟨value, complete, result, positive⟩ := finished represented output terminal evaluated escaped
    ((CallableIndexedOwnedPreparedStagedTerminalBodyMeaning.fallback type fellThrough).rename embedding)
  exact ⟨value, finalStore, finalMap, finalWorld,
    by rwa [CallableIndexedOwnedAdmittedStagedLexicalFooter.finish_rename], result, positive,
    finalHeaps, maps, worlds, frame, metadata, effect, reached, related,
    CallableIndexedOwnedAdmittedStagedFlowOutcomes.Post.to_function represented post⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedNamedBodyFinish
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedNamedBodyMeaning
/-! The complete bounded named body uses only its authentic compiler tree.
All expression and call behavior is derived from actual receipts; the caller
supplies the real parameter state and original Source typing. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedNamedBodyMeaning
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
  {invocation : Staging.Recursive.Scope}
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

include bindings record selectedBodies registered in
theorem preserves_selected {budget : Nat}
    (sourceEq : invocation.source = source named)
    {administrative : Core.Context}
    {context : SourceSemantics.Context}
    {expected : TypeSystem.Ty}
    (body : CellAwareNamedBodySupport.Body compiled (CellAwareMaterializedBodyProducer.Certificate compiled)
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
      CellAwareMaterializedOutput.OutcomeAt whole finalMap finalWorld owner.key.frameLocation
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
  exact CellAwareMaterializedNamedBodyFinish.preserves bridge bindings compiled record producer registered
    (fun childContext childRuntime childCovers _childLedger childSize _ =>
      CellAwareMaterializedExpressionMeaning.preserves_selected compiled bridge profile sourceEq
        (by simpa only [sourceEq] using childRuntime) selectedBodies childCovers childSize)
    sourceEq body.tree issuer _ _ within environments heaps locals agrees actualTyped runtime covers sameLedger typed
    initial admitted lexical physical owner sameLocation ready trace

/- Compatibility adapters for callers with a whole-program receipt. -/
include bindings record wellFormed registered in
theorem preserves {budget : Nat}
    (sourceEq : invocation.source = source named)
    {administrative : Core.Context}
    {context : SourceSemantics.Context}
    {expected : TypeSystem.Ty}
    (body : CellAwareNamedBodySupport.Body compiled (CellAwareMaterializedBodyProducer.Certificate compiled)
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
      CellAwareMaterializedOutput.OutcomeAt whole finalMap finalWorld owner.key.frameLocation
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
  apply preserves_selected (selectedBodies := Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed) (bindings := bindings) (record := record) (registered := registered) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedNamedBodyMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedNamedBodyReceipt
/-! The actual public preparation and named header produce the bounded mixed
body certificate. Source typing, parameter declarations and native body typing
are recovered from their original receipts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedNamedBodyReceipt
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (source)

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {recipe : SourceCoreIndexedSession.Recipe}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared whole row)
  {instantiation : DeclarationInstantiation}
  {header : CallableIndexedOwnedFunctionValues.Header whole (Program.ofChecked whole.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)

include aligned in
theorem of_header_selected
    (ready : SourceCoreIndexedSession.Recipe.prepare whole = .ok recipe)
    (bodyTyping : SelectedCompilationBodyTyping.Bodies whole)
    {entry : SourceCoreCallableIndexedPrograms.Entry whole.indexed.layouts}
    (member : entry ∈ whole.indexed.entries)
    (profile : CellAwareMaterializedBodyProducer.Profile whole.indexed prepared.named
      prepared.compilation.statements prepared.named.specialized.function.inferredBodyType) :
    Nonempty (CellAwareNamedBodySupport.Body prepared.compilation
      (CellAwareMaterializedBodyProducer.Certificate prepared.compilation)
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial whole.compatible.checked) header)
      header.context header.function.resultType) := by
  have sourceEq : header.function.source = source prepared.named := by
    rw [header.agreement.source, aligned.named]
    rfl
  have statementsEq : header.function.body = prepared.compilation.statements := by
    rw [aligned.function]
    rfl
  have resultEq : header.function.resultType = prepared.named.specialized.function.inferredBodyType := by
    rw [header.agreement.result, aligned.named]
  have record : SourceCompilationPlan.exactSpecialization whole.indexed.base.plan
      prepared.named.signature.key = .ok prepared.named.specialized := by
    simpa only [aligned.named] using CallableIndexedActualNamedSourceReceipts.header_record whole header
  have native := CallableIndexedOwnedPreparedNamedLexicalCollectors.body_typed prepared aligned ready member
  have declarations := RecursiveNamedHeaderScopeDeclarations.header_scope
    (ambient := CallableIndexedAmbient.ambientDefinitions whole.indexed)
    (values := SourceCoreCompatibleValues.Context.initial whole.compatible.checked)
    (prepared := whole.indexed.ancestry) (program := Program.ofChecked whole.sourceProgram) header
  obtain ⟨final, facts, typed, _⟩ := (SelectedCompilationHeaderCertificates.certified bodyTyping header).statements
  rw [sourceEq, statementsEq] at typed
  apply CellAwareMaterializedBodyProducer.of_compilation prepared.compilation record
    (by simpa only [resultEq] using profile) (sourceEq ▸ header.unique) rfl typed
  · simpa only [sourceEq, RecursiveNamedCatalogNativeContexts.bodyScope, aligned.bindings,
      CellAwareNamedBodySupport.scope] using declarations
  · simpa only [CallableIndexedOwnedPreparedStagedNamedLexicalReceipts.parameterScope,
      aligned.bindings, aligned.body, CellAwareNamedBodySupport.scope] using native

/- Compatibility adapters for callers with a whole-program receipt. -/
include aligned in
theorem of_header
    (ready : SourceCoreIndexedSession.Recipe.prepare whole = .ok recipe)
    (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))
    {entry : SourceCoreCallableIndexedPrograms.Entry whole.indexed.layouts}
    (member : entry ∈ whole.indexed.entries)
    (profile : CellAwareMaterializedBodyProducer.Profile whole.indexed prepared.named
      prepared.compilation.statements prepared.named.specialized.function.inferredBodyType) :
    Nonempty (CellAwareNamedBodySupport.Body prepared.compilation
      (CellAwareMaterializedBodyProducer.Certificate prepared.compilation)
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial whole.compatible.checked) header)
      header.context header.function.resultType) := by
  apply of_header_selected (bodyTyping := SelectedCompilationBodyTyping.Bodies.of_program wellFormed) (aligned := aligned) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedNamedBodyReceipt
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedNamedInvocation
/-! One genuine named invocation joins marked parameters, the actual bounded
compiler body and restoration of the saved physical caller. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedNamedInvocation
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
  (issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed header.named (diagnostics.reasonAt header.named.signature.key))
  (body : CellAwareNamedBodySupport.Body generation (CellAwareMaterializedBodyProducer.Certificate generation)
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

include body record sameLayouts sameGlobals sameBindings sameBody sameSolved selected issuer support in
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
      CellAwareMaterializedOutput.OutcomeAt whole finalMap finalWorld owner.key.frameLocation
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) value ∧
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
  have meaning := CellAwareMaterializedNamedBodyMeaning.preserves_selected bridge (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
    generation record profile support.registryBodies producer
    (CallableIndexedAmbient.frame_registered whole.indexed) sourceEq body issuer (Nat.le_refl size)
    (mapping := entryMap) (world := entryWorld) (actualContext := entryContext)
    (environment := entryEnvironment) (canonical := entryCanonical) (actual := entryActual)
    (before := entryHeap) (store := entryStore) (embedding := entryEmbedding)
  simp only [CellAwareNamedBodySupport.scope, ← sameBindings] at meaning
  obtain ⟨value, bodyStore, finalMap, finalWorld, evaluated, result, output, bodyHeaps, bodyMaps, bodyWorlds,
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
  refine ⟨value, _, finalMap, finalWorld, ⟨wrap evaluatedHeader, ?_⟩, output, restoredEffect⟩
  exact ⟨by simpa only [header.resultType] using result, restoredHeaps, fullEffect.maps, fullEffect.worlds,
    restoredFrame, fullEffect.metadata, returned, restoredRelated, post⟩

/- Compatibility adapters for callers with a whole-program receipt. -/
include body record sameLayouts sameGlobals sameBindings sameBody sameSolved selected issuer wellFormed in
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
      CellAwareMaterializedOutput.OutcomeAt whole finalMap finalWorld owner.key.frameLocation
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) value ∧
      CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after finalStore := by
  apply preserves_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (body := body) (record := record) (sameLayouts := sameLayouts) (sameGlobals := sameGlobals) (sameBindings := sameBindings) (sameBody := sameBody) (sameSolved := sameSolved) (selected := selected) (issuer := issuer) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedNamedInvocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedNamedPreparedReceipt
/-! The actual selected row and installed physical capture fix every static
input used by the mixed named invocation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedNamedPreparedReceipt
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header NamedCapture)
open CellAwareNamedPreparedReceipt (administrative cast_generation cast_generation_body)

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header whole (Program.ofChecked whole.sourceProgram))}
  {key : CallableIndexedOwnedFunctionValues.Key whole (Program.ofChecked whole.sourceProgram)}
  {mapping : LocationMap} {world : StoreTyping} {store : Store}
  {header : Header whole (Program.ofChecked whole.sourceProgram)}

def cast_body {first second : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
    {code : Expr} (same : first = second)
    (generation : CallableIndexedNamedGeneration.Compilation whole.indexed first diagnostics code)
    {administrative : Core.Context} {context : SourceSemantics.Context} {expected : TypeSystem.Ty}
    (body : CellAwareNamedBodySupport.Body generation (CellAwareMaterializedBodyProducer.Certificate generation)
      administrative context expected) :
    CellAwareNamedBodySupport.Body (cast_generation same generation)
      (CellAwareMaterializedBodyProducer.Certificate (cast_generation same generation)) administrative context expected := by
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
  body : CellAwareNamedBodySupport.Body generation (CellAwareMaterializedBodyProducer.Certificate generation)
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
    (profile : CellAwareMaterializedBodyProducer.Profile whole.indexed prepared.named prepared.compilation.statements
      prepared.named.specialized.function.inferredBodyType) :
    Nonempty (Receipt prepared capture) := by
  obtain ⟨body⟩ := CellAwareMaterializedNamedBodyReceipt.of_header_selected prepared aligned ready bodyTyping member profile
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
    (profile : CellAwareMaterializedBodyProducer.Profile whole.indexed prepared.named prepared.compilation.statements
      prepared.named.specialized.function.inferredBodyType) :
    Nonempty (Receipt prepared capture) := by
  apply of_header_selected (bodyTyping := SelectedCompilationBodyTyping.Bodies.of_program wellFormed) (aligned := aligned) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedNamedPreparedReceipt
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedNamedProfiles
/-! A stronger output profile is retained at its actual named compiler row.
Its roots come from the same statement-root action as the accepted compilation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedNamedProfiles
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation)

structure Entry {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (named : SourceCoreGeneralFunctions.Function) where
  roots : List StatementId
  extracted : CellAwareNamedProgramProfiles.statements named = .ok roots
  profile : CellAwareMaterializedBodyProducer.Profile prepared named roots
    named.specialized.function.inferredBodyType

def entry? {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (named : SourceCoreGeneralFunctions.Function) : Option (Entry prepared named) :=
  match extracted : CellAwareNamedProgramProfiles.statements named with
  | .error _ => none
  | .ok roots => do
    let profile ← CellAwareMaterializedBodyProducer.profile? prepared named roots
      named.specialized.function.inferredBodyType
    pure ⟨roots, extracted, profile⟩

def Entry.for_compilation {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {named : SourceCoreGeneralFunctions.Function} (entry : Entry prepared named)
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (compiled : Compilation prepared named diagnostics code) :
    CellAwareMaterializedBodyProducer.Profile prepared named compiled.statements
      named.specialized.function.inferredBodyType := by
  have same : entry.roots = compiled.statements := Except.ok.inj (entry.extracted.symm.trans compiled.roots)
  exact same ▸ entry.profile

end Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedNamedProfiles
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedNamedSourceInvocation
/-! Original Source bodies are lifted from the actual marked parameter entry.
The resulting public invocation includes the real earlier stage stop when a
guard rejects, retaining its reached heap and the saved caller restoration. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedNamedSourceInvocation
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
  (body : CellAwareNamedBodySupport.Body generation (CellAwareMaterializedBodyProducer.Certificate generation)
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
      CellAwareMaterializedOutput.OutcomeAt whole finalMap finalWorld owner.key.frameLocation
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result stagedOutcome) value ∧
      CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld reached finalStore := by
  let original := CellAwareNativeBodyCertificateMap.map_body
    (fun _ _ _ _ receipt => CellAwareMaterializedBodyProducer.Certificate.ordinary receipt) body
  obtain ⟨stageSize, stagedContext, stagedOutcome, reached, measured, adapted⟩ :=
    CellAwareNamedSourceInvocation.lift_selected profile receiver extension owner caller header capture generation record sameLayouts sameGlobals sameBindings
      sameSolved selected authority issuer original support stable heapTyped argumentsTyped represented heaps allocated trace
  obtain ⟨value, finalStore, finalMap, finalWorld, result, output, effect⟩ :=
    CellAwareMaterializedNamedInvocation.preserves_selected profile owner caller header capture generation record sameLayouts
      sameGlobals sameBindings sameBody sameSolved selected issuer body support stable heapTyped argumentsTyped
      represented heaps allocated measured
  exact ⟨stagedContext, stagedOutcome, reached, value, finalStore, finalMap, finalWorld, adapted, result, output, effect⟩

/- Compatibility adapters for callers with a whole-program receipt. -/
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
      CellAwareMaterializedOutput.OutcomeAt whole finalMap finalWorld owner.key.frameLocation
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result stagedOutcome) value ∧
      CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld reached finalStore := by
  apply preserves_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (body := body) (record := record) (receiver := receiver) (extension := extension) (sameLayouts := sameLayouts) (sameGlobals := sameGlobals) (sameBindings := sameBindings) (sameBody := sameBody) (sameSolved := sameSolved) (selected := selected) (authority := authority) (issuer := issuer) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedNamedSourceInvocation
end
