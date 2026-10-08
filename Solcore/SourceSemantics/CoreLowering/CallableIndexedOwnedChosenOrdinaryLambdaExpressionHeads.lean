import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryLambdaValues
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryLambdaFormationHeads

/-! Actual chosen formation certificates register their literal closure in the
full chosen model. The shared formation heads retain every returned receipt. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryLambdaExpressionHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : CallableIndexedNamedGeneration.Compilation compiled.indexed caller.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt (compiled := compiled)
    caller.named diagnostics namedCode compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)

local notation "functions" => CallableIndexedOwnedChosenOrdinaryLambdaValues.model
  root expressionSyntax headers keys registry faults profile

/-- Only the actual positive constructor supplies local formation membership. -/
theorem members : CallableIndexedOwnedChosenOrdinaryLambdaFormationHeads.Members
    (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    caller root expressionSyntax functions := by
  intro i history member
  exact .chosen_ordinary i history member

variable
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (globals : caller.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (prefixZero : owner.key.capturePrefix = 0)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {source : TypedSource}
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  (sameSource : source = CallableIndexedNamedGeneration.source caller.named)

include profile complete globals slots prefixZero wellFormed runtime covers sameSource in
/-- The actual formation head preserves its complete tuple in the chosen model. -/
theorem preserves_head_at (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedChosenOrdinaryLambdaFormationHeads.bridge (headers := headers) caller owner)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source
      (CallableIndexedOwnedChosenOrdinaryLambdaFormationHeads.Certificate caller context evidence root expressionSyntax)
      faults size :=
  CallableIndexedOwnedChosenOrdinaryLambdaFormationHeads.preserves_head_at
    caller context evidence root expressionSyntax owner profile functions (members caller root expressionSyntax profile)
    complete globals slots prefixZero wellFormed runtime covers sameSource size

include profile complete globals slots prefixZero wellFormed runtime covers sameSource in
/-- Native formation reflects the same Source leaf with its independent grade. -/
theorem reflects_head_at (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedChosenOrdinaryLambdaFormationHeads.bridge (headers := headers) caller owner)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source
      (CallableIndexedOwnedChosenOrdinaryLambdaFormationHeads.Certificate caller context evidence root expressionSyntax)
      faults size :=
  CallableIndexedOwnedChosenOrdinaryLambdaFormationHeads.reflects_head_at
    caller context evidence root expressionSyntax owner profile functions (members caller root expressionSyntax profile)
    complete globals slots prefixZero wellFormed runtime covers sameSource size

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryLambdaExpressionHeads
