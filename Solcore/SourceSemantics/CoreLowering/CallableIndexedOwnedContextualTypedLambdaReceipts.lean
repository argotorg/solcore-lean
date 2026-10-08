import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaProvenance
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaPackReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedTypedLambdaStaticBody

/-! Contextual receipts keep the exact selected Code and independent body
Syntax. These static projections construct a typed finish receipt in a proof
goal and retain the original ordered binder projections. No execution or
classification of legacy function alternatives is supplied. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualTypedLambdaReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedOwnedContextualLambdaProvenance

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}

/-- The explicit same-Code support supplies all data; only its independent
Syntax proof is obtained from the retained contextual packet. -/
theorem ordinary_typed_body
    {support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults}
    (provenance : OrdinaryAt code support) :
    ∃ body : CallableIndexedOwnedTypedLambdaStaticBody.Body code
        (Program.ofChecked compiled.sourceProgram) support.expressionSyntax support.certificates,
      body.toContext = support.body.toContext ∧ body.readFuel = support.body.readFuel ∧
      body.flow = support.body.flow ∧ HEq body.tree support.body.tree := by
  exact ⟨CallableIndexedOwnedTypedLambdaStaticBody.Body.of_body_with
    support.body provenance.syntax, rfl, rfl, rfl, HEq.rfl⟩

/-- The principal keeps its own complete support and dictionary at the same
Code. No ordinary Header is introduced. -/
theorem principal_typed_body
    {support : CallableIndexedOwnedMethodLambdaSupport.Support code registry faults}
    (provenance : PrincipalAt code support) :
    ∃ body : CallableIndexedOwnedTypedLambdaStaticBody.Body code
        (Program.ofChecked compiled.sourceProgram) support.expressionSyntax support.certificates,
      body.toContext = support.body.toContext ∧ body.readFuel = support.body.readFuel ∧
      body.flow = support.body.flow ∧ HEq body.tree support.body.tree := by
  exact ⟨CallableIndexedOwnedTypedLambdaStaticBody.Body.of_body_with
    support.body provenance.syntax, rfl, rfl, rfl, HEq.rfl⟩

/-- Genuine seed metadata and the actual producer's binder equation fix the
same ordered binder projection row after recapture. -/
theorem ordinary_projected_bindings
    {support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults}
    (provenance : OrdinaryAt code support) :
    ∀ binding ∈ code.receipt.loweredParameters,
      compiled.compatible.checked.catalog.project binding.1.scheme.body = .ok binding.2 := by
  cases provenance with
  | recaptured caller site expressionSyntax certificates body binderPolicy syntaxTree environment =>
    exact CallableIndexedOwnedLambdaBinderProjections.Site.projected_bindings
      site binderPolicy body.extended

/-- The principal binder row belongs to its actual Source context and seed. -/
theorem principal_projected_bindings
    {support : CallableIndexedOwnedMethodLambdaSupport.Support code registry faults}
    (provenance : PrincipalAt code support) :
    ∀ binding ∈ code.receipt.loweredParameters,
      compiled.compatible.checked.catalog.project binding.1.scheme.body = .ok binding.2 := by
  cases provenance with
  | recaptured principal site expressionSyntax certificates body binderPolicy syntaxTree environment =>
    exact CallableIndexedOwnedLambdaBinderProjections.Site.projected_bindings
      site binderPolicy body.extended

/-- Native packing is determined by the genuine binder and result
projections. Raw Source argument counts remain independent. -/
theorem ordinary_binding_pack
    {support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults}
    (provenance : OrdinaryAt code support)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    code.receipt.parameterCore =
      SourceCoreCompatibleCatalog.packTypes (code.receipt.loweredParameters.map Prod.snd) :=
  CallableIndexedOwnedStoredNativePackReceipts.code_binding_pack code profile
    (ordinary_projected_bindings provenance) support.body.projection

/-- The same principal Code determines its native binder pack. -/
theorem principal_binding_pack
    {support : CallableIndexedOwnedMethodLambdaSupport.Support code registry faults}
    (provenance : PrincipalAt code support)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    code.receipt.parameterCore =
      SourceCoreCompatibleCatalog.packTypes (code.receipt.loweredParameters.map Prod.snd) :=
  CallableIndexedOwnedStoredNativePackReceipts.code_binding_pack code profile
    (principal_projected_bindings provenance) support.body.projection

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualTypedLambdaReceipts
