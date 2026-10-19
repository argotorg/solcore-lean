import Solcore.SourceSemantics.CoreLowering.CellAwareNamedAssignmentDiagnostics
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIssuedAssignmentRecipes
import Solcore.SourceSemantics.CoreLowering.CellAwareImperativeBodyProducer
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeFlowFinish
import Solcore.SourceSemantics.CoreLowering.CellAwareImperativeTreeBounds
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitiveValues
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionMeaning

/-! The complete bounded named body uses only its authentic compiler tree.
All expression and call behavior is derived from actual receipts; the caller
supplies the real parameter state and original Source typing. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareImperativeNamedBodyMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole (Program.ofChecked whole.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole (Program.ofChecked whole.sourceProgram))}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (bindings : ProtectedStateTransition.Bindings protocol)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
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

include bindings transport record receiver extension authority wellFormed registered in
theorem preserves {budget : Nat}
    (sourceEq : invocation.source = source named)
    {administrative : Core.Context}
    {context : SourceSemantics.Context}
    {expected : TypeSystem.Ty}
    (body : CellAwareImperativeBodyProducer.Body compiled (CellAwareImperativeBodyProducer.Certificate compiled)
      administrative context expected)
    {control : ControlContext} {staticFinal : SourceSemantics.Context} {facts : BodyFacts}
    (sourceTyped : StatementsHaveType (source named) control context compiled.statements staticFinal facts)
    (depth : control.loopDepth = 0)
    (projection : whole.compatible.checked.catalog.project expected = .ok named.signature.resultType)
    (issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed named (diagnostics.reasonAt named.signature.key))
    (issued : CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt whole.indexed diagnostics) :
    ∀ {size}, size ≤ budget →
    ∀ {mapping world actualContext environment canonical actual before store embedding},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
      mapping world administrative (CellAwareImperativeBodyProducer.scope named) environment canonical whole.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree embedding canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions →
    Dynamic.SourceRuntimeValid program context (source named) →
    invocation.evidence.Covers context →
    context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
    ProtectedStateImperativeTypedSourceSites.Statements (source named) context compiled.statements →
    ∀ initial : protocol.State ⟨CellAwareImperativeBodyProducer.scope named, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model whole.indexed)
      named.signature.key [] mapping world before store environment →
    ∀ physical : CellAwareScopePhysical.Physical whole named context (CellAwareImperativeBodyProducer.scope named) canonical mapping world before store environment,
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
      ∃ reached : protocol.State ⟨CellAwareImperativeBodyProducer.scope named, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context expected
          (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) reached := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger typed initial admitted lexical physical owner sameLocation ready
    finalContext outcome after trace
  rw [body.emitted]
  apply CellAwareScopeFlowFinish.preserves bridge producer
    (CellAwareImperativeTreeBounds.preserves bridge bindings transport functions extension compiled record producer registered
      (fun _ _ represented => CallableIndexedOwnedIssuedAssignmentRecipes.operands compiled issued receiver represented)
      (CallableIndexedLambdaValues.identity_faithful whole.indexed) (CellAwarePhysicalFunctionOrigins.observations profile)
      (CellAwareNamedAssignmentDiagnostics.ready record runtime.graph.nodeOccurrencesUnique issued receiver functions protocol)
      (fun represented => CompatibleExpressionPrimitives.bool_fields represented)
      (fun _ _ => CompatiblePayload.ValueRep.unit)
      (fun childContext childRuntime childCovers childLedger childSize _ =>
        CellAwareNamedExpressionMeaning.preserves compiled bridge profile receiver extension authority sourceEq issuer record
          childLedger (by simpa only [sourceEq] using childRuntime) wellFormed childCovers childSize)
      sourceEq body.tree issuer)
    sourceEq sourceTyped depth projection _ _ within environments heaps locals agrees actualTyped runtime covers sameLedger typed
    initial admitted lexical physical owner sameLocation ready trace

include bindings transport record receiver extension authority wellFormed registered in
theorem reflects {budget : Nat}
    (sourceEq : invocation.source = source named)
    {administrative : Core.Context}
    {context : SourceSemantics.Context}
    {expected : TypeSystem.Ty}
    (body : CellAwareImperativeBodyProducer.Body compiled (CellAwareImperativeBodyProducer.Certificate compiled)
      administrative context expected)
    {control : ControlContext} {staticFinal : SourceSemantics.Context} {facts : BodyFacts}
    (sourceTyped : StatementsHaveType (source named) control context compiled.statements staticFinal facts)
    (depth : control.loopDepth = 0)
    (projection : whole.compatible.checked.catalog.project expected = .ok named.signature.resultType)
    (issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed named (diagnostics.reasonAt named.signature.key))
    (issued : CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt whole.indexed diagnostics) :
    ∀ {size}, size ≤ budget →
    ∀ {mapping world actualContext environment canonical actual before store embedding},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
      mapping world administrative (CellAwareImperativeBodyProducer.scope named) environment canonical whole.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree embedding canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions →
    Dynamic.SourceRuntimeValid program context (source named) →
    invocation.evidence.Covers context →
    context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
    ProtectedStateImperativeTypedSourceSites.Statements (source named) context compiled.statements →
    ∀ initial : protocol.State ⟨CellAwareImperativeBodyProducer.scope named, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model whole.indexed)
      named.signature.key [] mapping world before store environment →
    ∀ physical : CellAwareScopePhysical.Physical whole named context (CellAwareImperativeBodyProducer.scope named) canonical mapping world before store environment,
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
      ∃ reached : protocol.State ⟨CellAwareImperativeBodyProducer.scope named, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context expected
          (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) reached := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger typed initial admitted lexical physical owner sameLocation ready
    value finalStore completed
  rw [body.emitted] at completed
  apply CellAwareScopeFlowFinish.reflects bridge producer
    (CellAwareImperativeTreeBounds.reflects bridge bindings transport functions extension compiled record producer registered
      (fun _ _ represented => CallableIndexedOwnedIssuedAssignmentRecipes.operands compiled issued receiver represented)
      (CallableIndexedLambdaValues.identity_faithful whole.indexed) (CellAwarePhysicalFunctionOrigins.observations profile)
      (CellAwareNamedAssignmentDiagnostics.ready record runtime.graph.nodeOccurrencesUnique issued receiver functions protocol)
      (fun represented => CompatibleExpressionPrimitives.bool_fields represented)
      (fun _ _ => CompatiblePayload.ValueRep.unit)
      (CellAwarePhysicalFunctionOrigins.runtime_views profile)
      (fun childContext childRuntime childCovers childLedger childSize _ =>
        CellAwareNamedExpressionMeaning.reflects compiled bridge profile receiver extension authority sourceEq issuer record
          childLedger (by simpa only [sourceEq] using childRuntime) wellFormed childCovers childSize)
      sourceEq body.tree issuer)
    sourceEq sourceTyped depth projection _ _ within environments heaps locals agrees actualTyped runtime covers sameLedger typed
    initial admitted lexical physical owner sameLocation ready completed

end Solcore.SourceSemantics.CoreLowering.CellAwareImperativeNamedBodyMeaning
