import Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowProjectedAssignmentLifting
import Solcore.SourceSemantics.CoreLowering.CellAwareSourceForSequenceLifting
import Solcore.SourceSemantics.CoreLowering.CellAwareSourceForInitialTreeLifting
import Solcore.SourceSemantics.CoreLowering.CellAwareSourceForInitialTerminal
import Solcore.SourceSemantics.CoreLowering.CellAwareSourceForHeaderLifting
import Solcore.SourceSemantics.CoreLowering.CellAwareSourceTransferLifting
import Solcore.SourceSemantics.CoreLowering.CellAwareSourceWhileSequenceLifting
import Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowAssignmentLifting
import Solcore.SourceSemantics.CoreLowering.CellAwareImperativeTreeBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowGeneralizedLifting
import Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowOrdinaryLifting
import Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowAbsentLifting
import Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowTerminalLifting
import Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowDiscardLifting
import Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowBlockLifting
import Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowConditionalLifting
import Solcore.SourceSemantics.CoreLowering.CellAwareLexicalSourceTreeLifting
import Solcore.SourceSemantics.CoreLowering.CellAwareSourceAbsentPrefixLifting
import Solcore.SourceSemantics.CoreLowering.CellAwareSourceOrdinaryPrefixLifting
import Solcore.SourceSemantics.CoreLowering.CellAwareFaultingNativeBodyTree
import Solcore.SourceSemantics.CoreLowering.CellAwareSourceTerminalLifting

/-! Independent ordinary Source bodies follow the actual compiler tree.
Generalized declarations construct their real physical state before recursion. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CellAwareImperativeSourceTreeLifting
open Core Frontend SourceInference CompatibleEquality GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
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
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations whole.compatible.checked.catalog functions identities)
  (assignmentDiagnostics : PreparedAssignmentReachedDiagnostics.Ready (values := .initial whole.compatible.checked)
    functions protocol (source named)
    (fun site root => diagnostics.placeReason named.signature.key site root none)
    (fun site root raw => diagnostics.placeReason named.signature.key site root (some raw))
    receiving (fun reason token => faults (.semantic reason) token))
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}


variable
  (booleans : ∀ {mapping world sourceValue nativeValue},
    (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions).Represents mapping world .bool sourceValue nativeValue .bool →
    ∃ truth, sourceValue = .bool truth ∧ nativeValue = .bool truth)
  (unitValue : ∀ mapping world, (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions).Represents mapping world .unit .unit .unit .unit)

include record registered bindings transport extension operandIncluded faithful observations assignmentDiagnostics booleans unitValue in
theorem lifts
    (children : ∀ context, Dynamic.SourceRuntimeValid program context (source named) →
      invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeSourceLiftBounds.LiftsAt bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named registry invocation (certificates context) size)
    (preservation : ∀ context, Dynamic.SourceRuntimeValid program context (source named) →
      invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeExpressionBounds.PreservesAt bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named registry invocation
        (certificates context) faults size)
    (sourceEq : invocation.source = source named)
    {administrative : Core.Context} {reasonAt : ExpressionId → Word}
    {mode : Bool} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : CellAwareImperativeTree.Tree whole.indexed named compiled certificates administrative reasonAt
      context scope mode statements expected type code)
    (issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed named reasonAt) :
    CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope mode statements := by
  induction tree with
  | @generalizedInitialized context nextContext scope mode id node binder initializer initializerNode parameters result lambdaBody rest expected type lowered body childFuel
      found form declaration polymorphic extended ordinary initializerFound initializerForm valueType requirements coercions site initial nativeTyped allocation annotation same remaining ih =>
    exact CellAwareSourceFlowGeneralizedLifting.generalized bridge compiled record producer registered
      (type := type) (body := body) found form declaration polymorphic extended ordinary initializerFound initializerForm
      valueType requirements coercions site initial nativeTyped allocation annotation same sourceEq issuer ih
  | @initialized context nextContext scope mode id node binder initializer initializerNode rest expected type lowered body
      found form member mono extended ordinary initializerFound valueType typed certified allocation annotation same remaining ih =>
    exact CellAwareSourceFlowOrdinaryLifting.initialized bridge producer registered (type := type) (body := body)
      found form member mono extended ordinary initializerFound valueType typed certified allocation annotation same
      sourceEq (children _) (preservation _) ih

  | @uninitialized context nextContext scope mode id node binder rest expected type body payload
      found form member mono extended ordinary projected allocation annotation same remaining ih =>
    exact CellAwareSourceFlowAbsentLifting.absent bridge producer registered (body := body)
      found form member mono extended ordinary projected allocation annotation same sourceEq ih

  | nil _allowed => exact CellAwareSourceFlowTerminalLifting.nil bridge producer
  | returnUnit rest found form =>
    exact CellAwareSourceFlowTerminalLifting.return_unit bridge producer sourceEq
      (by simpa only [sourceEq] using found) form
  | @returning context scope mode id node expression expressionNode expected lowered rest found form expressionFound _valueType typed certified =>
    exact CellAwareSourceFlowTerminalLifting.terminal bridge producer sourceEq
      (.returning rest (by simpa only [sourceEq] using lookupStatement?_sound found) form)
      (by simpa only [sourceEq] using expressionFound) (by simpa only [sourceEq] using typed)
      certified (children context)
  | @tail context scope id node expression expressionNode expected lowered found form expressionFound _valueType typed certified =>
    exact CellAwareSourceFlowTerminalLifting.terminal bridge producer sourceEq
      (.tail (by simpa only [sourceEq] using lookupStatement?_sound found) form)
      (by simpa only [sourceEq] using expressionFound) (by simpa only [sourceEq] using typed)
      certified (children context)
  | @discard context scope mode id node expression expressionNode semicolon rest expected lowered type body
      found form _notTail continuing expressionFound typed certified remaining ih =>
    exact CellAwareSourceFlowDiscardLifting.lifts bridge producer sourceEq
      (by simpa only [sourceEq] using found) form continuing
      (by simpa only [sourceEq] using expressionFound) (by simpa only [sourceEq] using typed)
      certified (children context) (preservation context) ih
  | @block context scope mode id node statements rest expected type innerCode body
      found form inner remaining innerIH remainingIH =>
    exact CellAwareSourceFlowBlockLifting.lifts bridge producer sourceEq
      (by simpa only [sourceEq] using found) form innerIH
      (fun size => CellAwareImperativeTreeBounds.preserves bridge bindings transport functions extension compiled record producer registered operandIncluded faithful observations assignmentDiagnostics
        booleans unitValue (fun context runtime covers sameLedger childSize _ =>
          preservation context runtime covers sameLedger childSize) sourceEq inner issuer size (Nat.le_refl _)) remainingIH
  | @ifThen context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body
      found form conditionFound conditionType conditionTyped conditionCertificate thenTree elseTree remaining thenIH elseIH remainingIH =>
    exact CellAwareSourceFlowConditionalLifting.lifts
      (expected := expected) (type := type) (branchCode := fun truth => if truth then thenCode else elseCode)
      bridge producer sourceEq booleans
      (by simpa only [sourceEq] using found) form
      (by simpa only [sourceEq] using conditionFound) conditionType
      (by simpa only [sourceEq] using conditionTyped) conditionCertificate
      (children context) (preservation context)
      (fun truth => by cases truth <;> assumption)
      (fun truth size => by
        cases truth
        · exact CellAwareImperativeTreeBounds.preserves bridge bindings transport functions extension compiled record producer registered operandIncluded faithful observations assignmentDiagnostics
            booleans unitValue (fun context runtime covers sameLedger childSize _ =>
              preservation context runtime covers sameLedger childSize) sourceEq elseTree issuer size (Nat.le_refl _)
        · exact CellAwareImperativeTreeBounds.preserves bridge bindings transport functions extension compiled record producer registered operandIncluded faithful observations assignmentDiagnostics
            booleans unitValue (fun context runtime covers sameLedger childSize _ =>
              preservation context runtime covers sameLedger childSize) sourceEq thenTree issuer size (Nat.le_refl _)) remainingIH

  | @whileLoop context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body escaped
      found form conditionFound conditionType conditionTyped conditionCertificate loopTree nativeTyped remaining loopIH remainingIH =>
    exact CellAwareSourceWhileSequenceLifting.lifts bridge producer transport sourceEq booleans
      (by simpa only [sourceEq] using found) form
      (by simpa only [sourceEq] using conditionFound) conditionType
      (by simpa only [sourceEq] using conditionTyped) conditionCertificate nativeTyped
      (children context) (preservation context) loopIH
      (fun size => CellAwareImperativeTreeBounds.preserves bridge bindings transport functions extension compiled record producer registered operandIncluded faithful observations assignmentDiagnostics
        booleans unitValue (fun context runtime covers sameLedger childSize _ =>
          preservation context runtime covers sameLedger childSize) sourceEq loopTree issuer size (Nat.le_refl _)) remainingIH
  | @forLoop context loopContext postContext scope loopScope postScope mode id node initialItems condition conditionNode postItems statements rest expected type conditionCode loopCode postCode initialCode body escaped
      found form initialTree conditionFound conditionType conditionTyped conditionCertificate loopTree postTree loopSourceTyped postSourceTyped nativeTyped remaining loopIH remainingIH =>
    have loopMeaning : ∀ size, CellAwareScopeFlowBounds.PreservesAt bridge loopContext
        (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named producer registry invocation faults
        administrative loopScope false statements expected type loopCode size :=
      fun size => CellAwareImperativeTreeBounds.preserves bridge bindings transport functions extension compiled record producer registered operandIncluded faithful observations assignmentDiagnostics
        booleans unitValue (fun context runtime covers sameLedger childSize _ =>
          preservation context runtime covers sameLedger childSize) sourceEq loopTree issuer size (Nat.le_refl _)
    have postMeaning : ∀ size, CellAwareScopeForPostBounds.PreservesAt bridge loopContext
        (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named producer registry invocation faults
        administrative loopScope postItems expected type postCode size :=
      fun size => CellAwareForPostTreeBounds.preserves bridge bindings transport functions extension compiled producer registered operandIncluded faithful observations assignmentDiagnostics
        (fun context runtime covers sameLedger childSize _ => preservation context runtime covers sameLedger childSize)
        sourceEq postTree size (Nat.le_refl _)
    have terminalMeaning : ∀ size, CellAwareScopeForInitialBounds.PreservesAt bridge loopContext
        (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named producer registry invocation faults
        administrative loopScope [] condition postItems statements expected type
        (LocalLoop.iterate type conditionCode loopCode postCode escaped) size := by
      intro terminalSize mapping world actualContext environment canonical actual before store embedding
        environments heaps locals agrees actualTyped runtime covers sameLedger initial admitted authority physical owner sameLocation ready outcome after trace
      exact CellAwareForInitialTerminal.preserves bridge (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions)
        producer transport booleans (fun n _ => preservation loopContext runtime covers sameLedger n)
        (by simpa only [sourceEq] using conditionFound) conditionType
        (by simpa only [sourceEq] using conditionTyped) conditionCertificate nativeTyped
        (fun n _ => loopMeaning n) (fun n _ => postMeaning n)
        loopSourceTyped postSourceTyped terminalSize (Nat.le_refl _)
        environments heaps locals agrees actualTyped runtime covers sameLedger initial admitted authority physical owner sameLocation ready trace
    have initialMeaning : ∀ size, CellAwareScopeForInitialBounds.PreservesAt bridge context
        (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named producer registry invocation faults
        administrative scope initialItems condition postItems statements expected type initialCode size :=
      fun size => CellAwareForInitialTreeBounds.preserves bridge bindings transport functions extension compiled producer registered operandIncluded faithful observations assignmentDiagnostics
        (fun context runtime covers sameLedger childSize _ => preservation context runtime covers sameLedger childSize)
        sourceEq initialTree (fun n _ => terminalMeaning n) size (Nat.le_refl _)
    have postLift : CellAwareSourceForLiftBounds.ItemsLifts (named := named) (administrative := administrative)
        (context := loopContext) (scope := loopScope) (registry := registry) (invocation := invocation) bridge producer postItems := CellAwareSourceForHeaderLifting.lifts bridge transport functions faithful observations extension compiled producer registered
      children preservation sourceEq postTree
    have terminalLift : CellAwareSourceForInitialBounds.InitializersLifts (named := named) (administrative := administrative)
        (context := loopContext) (scope := loopScope) (registry := registry) (invocation := invocation) bridge producer [] condition postItems statements := CellAwareSourceForInitialTerminal.lifts bridge producer
      (children loopContext) (preservation loopContext) booleans
      (by simpa only [sourceEq] using conditionFound) conditionType
      (by simpa only [sourceEq] using conditionTyped) conditionCertificate loopIH loopMeaning loopSourceTyped
      postLift postMeaning postSourceTyped
    have initialLift : CellAwareSourceForInitialBounds.InitializersLifts (named := named) (administrative := administrative)
        (context := context) (scope := scope) (registry := registry) (invocation := invocation) bridge producer initialItems condition postItems statements := CellAwareSourceForInitialTreeLifting.lifts bridge transport functions faithful observations extension compiled producer registered
      children preservation sourceEq initialTree terminalLift
    intro size mapping world actualContext environment canonical actual before store embedding
    exact CellAwareSourceForSequenceLifting.lifts bridge producer sourceEq initialLift initialMeaning
      (by simpa only [sourceEq] using found) form remainingIH
  | @assign context scope mode id node assignment operator rhs rest expected type body
      found form head bare _rightTyped _operands remaining remainingIH =>
    cases invocation with
    | mk origin actualSource owned stageContext evidence guards =>
      cases sourceEq
      exact CellAwareSourceFlowAssignmentLifting.lifts bridge functions transport extension producer rfl
        found form head bare (children context) (preservation context) remainingIH

  | @assignProjected context scope mode id node assignment operator rhs rest expected type body
      found form head projected _rightTyped _site remaining remainingIH =>
    cases invocation with
    | mk origin actualSource owned stageContext evidence guards =>
      cases sourceEq
      exact CellAwareSourceFlowProjectedAssignmentLifting.lifts bridge functions faithful observations transport extension producer rfl
        found form head projected (children context) (preservation context) remainingIH

  | breaking rest found form =>
    exact CellAwareSourceTransferLifting.breaking bridge producer sourceEq
      (by simpa only [sourceEq] using found) form
  | continuing rest found form =>
    exact CellAwareSourceTransferLifting.continuing bridge producer sourceEq
      (by simpa only [sourceEq] using found) form

end Solcore.SourceSemantics.CoreLowering.CellAwareImperativeSourceTreeLifting
