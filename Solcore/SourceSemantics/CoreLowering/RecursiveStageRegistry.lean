import Solcore.SourceSemantics.Staging.RecursiveScope
import Solcore.SourceSemantics.CoreLowering.LambdaMetadataViews

/-! Authentic invocation scopes for anonymous closures. The actual original
sidecar supplies the caller marker/stage table; complete declaration and local
substitutions remain attached. Codebook origins, canonical-source receipts and
actual lambda metadata establish selection. No body evaluation is part of the
registry, and arbitrary Core-typed functions cannot enter it. Named/global
scope selection and traversal-wide receipt extraction remain separate work. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveStageRegistry
open Frontend Frontend.SourceInference SourceCoreStageContracts AuthenticatedCallableLedger

/-- The runtime lexical context/evidence belong to the closure. Its guard
frame comes from the original sidecar, including the original return marker. -/
def scope (sidecar : Sidecar) (active : TypeSystem.Substitution) (function : Dynamic.Closure) : Staging.Recursive.Scope := {
  origin := ⟨function.source.owner, sidecar.caller.parameterSubstitution, active⟩
  source := function.source, owned := rfl, context := function.context, evidence := function.evidence
  guards := CallableLedger.frame sidecar }

inductive Selected (checkedProgram : CheckedProgram) (plan : Plan) (table : SourceCoreStageCodebook.Table) :
    Dynamic.Closure → Staging.Recursive.Scope → Prop where
  | lambda {sidecar : Sidecar} {id : ExpressionId} {active : TypeSystem.Substitution}
      {descriptor : Core.Word} {function : Dynamic.Closure}
      (prepared : prepareSidecar plan sidecar.caller.key = .ok sidecar)
      (site : LambdaSite plan table sidecar.caller.key id active descriptor)
      (source : LambdaSourceAlignment.SourceReceipt checkedProgram plan sidecar.caller.key active function.source)
      (owner : function.source.owner = sidecar.caller.key.declaration)
      (origin : CallableLedger.LambdaOrigin plan sidecar.caller.key id active function site.contract) :
      Selected checkedProgram plan table function (scope sidecar active function)

def registry (checkedProgram : CheckedProgram) (plan : Plan) (table : SourceCoreStageCodebook.Table) :
    Staging.Recursive.Registry where
  Closure := Selected checkedProgram plan table
  source := by intro function selected related; cases related; rfl
  context := by intro function selected related; cases related; rfl
  evidence := by intro function selected related; cases related; rfl

/-- Actual sidecar/table preparation and the emitted lambda's static receipt
select a recursive body scope, even when compilation used a raw metadata view.
The caller passes static source/code provenance, never a child execution. -/
theorem selected_of_prepare {checkedProgram : CheckedProgram} {plan : Plan}
    {checked : SourceCoreDataCatalog.Checked} {limits : SourceCoreStageCodebook.Limits} {firstId : Nat}
    {table : SourceCoreStageCodebook.Table} {active : TypeSystem.Substitution}
    {sidecar : Sidecar} {bodyCertificate : FunctionCode.BodyCertificate} {policy : SourceCoreFunctions.Policy}
    {compilation : SourceCoreFunctions.Context} {view : TypedSource} {lexical : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {node : ExpressionNode} {function : Dynamic.Closure}
    {reportedType : Core.Ty} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreStageCodebook.prepare checkedProgram plan checked limits firstId = .ok table)
    (prepared : prepareSidecar plan compilation.owner = .ok sidecar)
    (descriptor : SourceCoreCallableContracts.Descriptor table (.lambda compilation.owner id active))
    (source : LambdaSourceAlignment.SourceReceipt checkedProgram plan compilation.owner active function.source)
    (owner : function.source.owner = compilation.owner.declaration)
    (metadata : LambdaMetadataViews.MetadataView function.source view)
    (unique : NodeOccurrencesUnique function.source)
    (artifact : DecoratedFunctionCode.LambdaCertificate bodyCertificate policy compilation view lexical id node
      function.parameters function.resultType function.body reportedType lowered) :
    (registry checkedProgram plan table).Closure function (scope sidecar active function) := by
  obtain ⟨site⟩ := lambda_site_of_descriptor accepted descriptor
  have same := (CallContractCertificates.sidecar_of_accepted prepared).2
  let alignedSite : LambdaSite plan table sidecar.caller.key id active descriptor.id := by
    simpa only [same] using site
  have alignedSource : LambdaSourceAlignment.SourceReceipt checkedProgram plan sidecar.caller.key active function.source := by
    simpa only [same] using source
  exact Selected.lambda (by simpa only [same] using prepared) alignedSite alignedSource
    (by simpa only [same] using owner)
    (LambdaMetadataViews.lambda_origin alignedSource alignedSite.original metadata unique artifact.raw.found artifact.raw.form)

@[simp] theorem scope_localSubstitution (sidecar : Sidecar) (active : TypeSystem.Substitution) (function : Dynamic.Closure) :
    (scope sidecar active function).origin.localSubstitution = active := rfl

@[simp] theorem scope_declarationSubstitution (sidecar : Sidecar) (active : TypeSystem.Substitution) (function : Dynamic.Closure) :
    (scope sidecar active function).origin.declarationSubstitution = sidecar.caller.parameterSubstitution := rfl

@[simp] theorem scope_returnMarker (sidecar : Sidecar) (active : TypeSystem.Substitution) (function : Dynamic.Closure) :
    (scope sidecar active function).guards.stages.callerReturnComptime = sidecar.caller.function.returnComptime := rfl

/-- A selected scope always keeps the original static sidecar. In particular,
its return marker is not recomputed from the source/Core function result type. -/
theorem Selected.original {checkedProgram : CheckedProgram} {plan : Plan} {table : SourceCoreStageCodebook.Table}
    {function : Dynamic.Closure} {selected : Staging.Recursive.Scope}
    (related : Selected checkedProgram plan table function selected) :
    ∃ sidecar active, prepareSidecar plan sidecar.caller.key = .ok sidecar ∧
      selected = scope sidecar active function ∧ selected.origin.declaration = sidecar.caller.key.declaration := by
  cases related with
  | lambda prepared _ _ owner _ => exact ⟨_, _, prepared, rfl, owner⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveStageRegistry
