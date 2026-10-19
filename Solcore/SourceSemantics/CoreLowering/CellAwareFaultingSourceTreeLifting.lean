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
namespace Solcore.SourceSemantics.CoreLowering.CellAwareFaultingSourceTreeLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    (CompatibleHeap.projects whole.compatible.checked.catalog) whole.indexed.layouts.definitions}
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


include record registered in
theorem lifts
    (children : ∀ context, Dynamic.SourceRuntimeValid program context (source named) →
      invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeSourceLiftBounds.LiftsAt bridge context model named registry invocation (certificates context) size)
    (preservation : ∀ context, Dynamic.SourceRuntimeValid program context (source named) →
      invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeExpressionBounds.PreservesAt bridge context model named registry invocation
        (certificates context) faults size)
    (sourceEq : invocation.source = source named)
    {administrative : Core.Context} {reasonAt : ExpressionId → Word}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : CellAwareFaultingNativeBodyTree.Tree whole.indexed named compiled certificates administrative reasonAt
      context scope true statements expected type code)
    (issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed named reasonAt) :
    CellAwareSourceBodyLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope statements := by
  generalize modeEq : true = mode at tree
  induction tree with
  | existing old =>
    cases modeEq
    exact CellAwareLexicalSourceTreeLifting.lifts bridge compiled record producer registered children preservation sourceEq old issuer
  | @generalizedInitialized context nextContext scope mode id node binder initializer initializerNode parameters result lambdaBody rest expected type lowered body childFuel
      found form declaration polymorphic extended ordinary initializerFound initializerForm valueType requirements coercions site initial nativeTyped allocation annotation same remaining ih =>
    cases modeEq
    exact CellAwareSourceGeneralizedPrefixLifting.generalized bridge compiled record producer registered
      (type := type) (body := body) found form declaration polymorphic extended ordinary initializerFound initializerForm
      valueType requirements coercions site initial nativeTyped allocation annotation same sourceEq issuer (ih rfl)
  | @initialized context nextContext scope mode id node binder initializer initializerNode rest expected type lowered body
      found form member mono extended ordinary initializerFound valueType typed certified allocation annotation same remaining ih =>
    cases modeEq
    exact CellAwareSourceOrdinaryPrefixLifting.initialized bridge producer registered (type := type) (body := body)
      found form member mono extended ordinary initializerFound valueType typed certified allocation annotation same
      sourceEq (children _) (preservation _) (ih rfl)

  | @uninitialized context nextContext scope mode id node binder rest expected type body payload
      found form member mono extended ordinary projected allocation annotation same remaining ih =>
    cases modeEq
    exact CellAwareSourceAbsentPrefixLifting.absent bridge producer registered (body := body)
      found form member mono extended ordinary projected allocation annotation same sourceEq (ih rfl)

end Solcore.SourceSemantics.CoreLowering.CellAwareFaultingSourceTreeLifting
