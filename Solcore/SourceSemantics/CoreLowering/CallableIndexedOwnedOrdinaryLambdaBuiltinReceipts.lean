import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaFormationHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaRuntimeBody

/-! Accepted ordinary sites with genuine same-Code builtin body receipts yield
rank-one formation certificates. The supported bodies retain the original
imperative/control/assignment/match grammar with builtin expression children;
no named, indirect or method body child is added by this conversion.
Only the existing static Tree transport changes certificate and syntax facets. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaBuiltinReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedLambdaNestedRuntimeCertificates
open CallableIndexedLambdaNestedRuntimeBodyMeaning RecursiveNamedLambdaFormationHeads
open CallableLambdaViewEdits CallableLambdaBodyReachability

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))

/-- Finite syntax projection follows only the fixed fragment wrappers. It
keeps the actual parent lookup and does not traverse expression children. -/
private theorem builtin_nodes {source : TypedSource} {id : ExpressionId}
    (syntaxTree : CompatibleExpressionBuiltins.Syntax source id) : Nodes source id := by
  cases syntaxTree with
  | fragment general =>
    cases general with
    | fragment recursive =>
      cases recursive with
      | fragment members =>
        cases members with
        | fragment constructors =>
          cases constructors with
          | fragment conditionals =>
            cases conditionals with
            | primitive primitives =>
              cases primitives with
              | product products => cases products <;> exact ⟨_, by assumption⟩
              | _ => exact ⟨_, by assumption⟩
            | _ => exact ⟨_, by assumption⟩
          | _ => exact ⟨_, by assumption⟩
        | _ => exact ⟨_, by assumption⟩
      | _ => exact ⟨_, by assumption⟩
    | _ => exact ⟨_, by assumption⟩
  | _ => exact ⟨_, by assumption⟩

private theorem lift_builtin {rank fuel : Nat} {source : TypedSource}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {compilation : SourceCoreFunctions.Context} {reasonAt : ExpressionId → Word}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : CompatibleExpressionBuiltinRuntime.Certificate fuel (.initial compiled.compatible.checked)
      source context compilation.solvedRequirements reasonAt scope id lowered) :
    Certificates (indexed := compiled.indexed) (values := .initial compiled.compatible.checked)
      (program := Program.ofChecked compiled.sourceProgram)
      (LowerSupport (indexed := compiled.indexed) (values := .initial compiled.compatible.checked)
      (program := Program.ofChecked compiled.sourceProgram) headers caller registry faults rank)
      rank caller headers compilation fuel
      source context evidence compilation.solvedRequirements reasonAt scope id lowered := by
  obtain ⟨tree, sites⟩ := receipt
  exact ⟨.fragment tree, .fragment tree sites⟩

private theorem lift_sites {source : TypedSource} {compilation : SourceCoreFunctions.Context}
    {active : TypeSystem.Substitution} {administrative : Core.Context} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {flow : Expr}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {fuel rank : Nat} {evidence : Dynamic.EvidenceEnvironment} {reasonAt : ExpressionId → Word}
    (unique : NodeOccurrencesUnique source)
    {tree : GenericImperativeMatch.Tree compiled.indexed.layouts compilation.owner active
      compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length onError
      (.initial compiled.compatible.checked) source (CompatibleExpressionBuiltins.Syntax source)
      (fun context => CompatibleExpressionBuiltinRuntime.Certificate fuel (.initial compiled.compatible.checked)
        source context compilation.solvedRequirements reasonAt)
      compiled.indexed.layouts.definitions administrative context scope (.statements true statements) expected type flow}
    (sites : tree.CatalogSites .reachable registry faults) :
    ∃ next : GenericImperativeMatch.Tree compiled.indexed.layouts compilation.owner active
      compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length onError
      (.initial compiled.compatible.checked) source (Nodes source)
      (fun context => Certificates (indexed := compiled.indexed) (values := .initial compiled.compatible.checked)
      (program := Program.ofChecked compiled.sourceProgram)
      (LowerSupport (indexed := compiled.indexed) (values := .initial compiled.compatible.checked)
      (program := Program.ofChecked compiled.sourceProgram) headers caller registry faults rank)
      rank caller headers compilation fuel
        source context evidence compilation.solvedRequirements reasonAt)
      compiled.indexed.layouts.definitions administrative context scope (.statements true statements) expected type flow,
      next.CatalogSites .reachable registry faults := by
  have avoids : Avoids source (statements.map NodeId.statement) [] := by intro id member; cases member
  exact CallableLambdaViewMatchRuntimeCertificates.transport_sites_with
    (LocalView.refl source) avoids unique
    (fun _ _ syntaxTree => builtin_nodes syntaxTree)
    (fun _ _ _ _ _ receipt => lift_builtin caller receipt) sites
    (fun id member => .root (List.mem_map.mpr ⟨id, member, rfl⟩))

variable {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {scope : SourceCoreLocalCell.Scope}
  (site : CallableIndexedLambdaGeneration.Site compiled.indexed caller.named parameters result statements
    context evidence [] scope (nativePrefix (values := .initial compiled.compatible.checked) caller))
  (body : CallableIndexedLambdaRuntimeBody.Body (values := .initial compiled.compatible.checked) site.code
    (Program.ofChecked compiled.sourceProgram) registry faults)

include body in
/-- Both real Trees and their diagnostic ledgers are lifted at the same flow.
The accepted callback, original ClosureFrame and full body context are copied
from the authentic same-Code receipt, without a ranked-support premise. -/
theorem body_at_zero : Nonempty
    (BodyAt (indexed := compiled.indexed) (values := .initial compiled.compatible.checked)
      (program := Program.ofChecked compiled.sourceProgram) headers caller registry faults 0 site.code) := by
  have viewUnique := site.code.viewOfSource.unique body.unique
  obtain ⟨actualTree, actualSites⟩ := lift_sites (rank := 0) (evidence := evidence)
    caller viewUnique body.actualSites
  obtain ⟨tree, sites⟩ := lift_sites (rank := 0) (evidence := evidence)
    caller body.unique body.sites
  have original : CallableIndexedLambdaStaticBodySupport.BodyWith (values := .initial compiled.compatible.checked) Nodes
      (fun fuel source context => Certificates (indexed := compiled.indexed) (values := .initial compiled.compatible.checked)
      (program := Program.ofChecked compiled.sourceProgram)
      (LowerSupport (indexed := compiled.indexed) (values := .initial compiled.compatible.checked)
      (program := Program.ofChecked compiled.sourceProgram) headers caller registry faults 0)
        0 caller headers
        site.code.compilation fuel source context evidence site.code.compilation.solvedRequirements site.code.reasonAt)
      site.code (Program.ofChecked compiled.sourceProgram) registry faults := {
    toContext := body.toContext, frame := body.frame, readFuel := body.readFuel, policy := body.policy,
    callback := body.callback, flow := body.flow, generated := body.generated, projection := body.projection,
    emitted := body.emitted, actualTree := actualTree, actualSites := actualSites,
    tree := tree, sites := sites, valid := body.valid, unique := body.unique }
  have receipt : CallableIndexedLambdaNestedRuntimeCertificates.BodyReceipt

      (LowerSupport (indexed := compiled.indexed) (values := .initial compiled.compatible.checked)
        (program := Program.ofChecked compiled.sourceProgram) headers caller registry faults 0)
      0 caller headers site.code registry faults :=
    ⟨rfl, site.compilation, site.active, rfl, original⟩
  have equation := CallableIndexedLambdaNestedRuntimeCertificates.BodyAt.eq_1
    (indexed := compiled.indexed) (values := .initial compiled.compatible.checked)
    (program := Program.ofChecked compiled.sourceProgram) headers caller registry faults 0 site.code
  exact ⟨equation.symm ▸ receipt⟩

include body in
/-- Actual accepted Site emission and original raw Source metadata supply the
rank-one ordinary formation certificate consumed by the generic admitted leaf. -/
theorem certificate_of_site
    (sourceType : site.code.sourceNode.type = FunctionValues.sourceType
      (CallableIndexedLambdaGeneration.closure caller.named parameters result statements context evidence []))
    (requirements : site.code.sourceNode.requirements = []) (coercions : site.code.sourceNode.coercions = []) :
    CallableIndexedOwnedOrdinaryLambdaFormationHeads.Certificate (headers := headers)
      (registry := registry) (faults := faults) (source := CallableIndexedNamedGeneration.source caller.named)

    (context := context) (evidence := evidence) caller scope site.code.id site.code.lowered := by
  obtain ⟨ranked⟩ := body_at_zero caller site body
  have supported : LowerSupport (indexed := compiled.indexed) (values := .initial compiled.compatible.checked)
      (program := Program.ofChecked compiled.sourceProgram) headers caller registry faults 1 0 site.code := by
    simpa only [LowerSupport, dif_pos (show 0 < 1 by decide)] using ranked
  exact ⟨1, CallableIndexedLambdaNestedRuntimeCertificates.Lambda.of_site
     (indexed := compiled.indexed) (values := .initial compiled.compatible.checked)
      (program := Program.ofChecked compiled.sourceProgram)
    (support := LowerSupport (indexed := compiled.indexed) (values := .initial compiled.compatible.checked)
      (program := Program.ofChecked compiled.sourceProgram) headers caller registry faults 1)
    (source := CallableIndexedNamedGeneration.source caller.named)
    (context := context) (evidence := evidence) (caller := caller) site (show 0 < 1 by decide) supported
    (by simpa only [CallableIndexedLambdaGeneration.closure] using site.code.sourceFound)
    sourceType requirements coercions⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaBuiltinReceipts
