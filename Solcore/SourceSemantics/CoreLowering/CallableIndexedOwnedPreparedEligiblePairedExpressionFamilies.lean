import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedEligibleSelectedNativeFamilyFlowStep

/-! The central E family keeps the actual body administrative context separate
from the genuine fixed compiler prefix. Closure F specializes to prefix/prefix;
named F uses the actual BodyState context. Neither direction rebases raw typing
or recovers Source authority by inverting a weaker heap model. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedEligiblePairedExpressionFamilies
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration CallableIndexedLambdaValues
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedSelectedDiagnosticIssuerReceipts (SelectedReceipt lowered)
open CallableIndexedOwnedPreparedCanonicalCaptureReceipts («prefix»)
open CallableIndexedOwnedPreparedCanonicalFlowBounds (Origin)
open RecursiveNamedCatalogInvocationBounds (Below)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))

section Expressions
variable {named : Named} {index : Nat} (selected : SelectedReceipt compiled named index)
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) named (lowered compiled selected.diagnostics)
    selected.code selected.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  (callerEvidence : Option Dynamic.EvidenceEnvironment) (readFuel : Nat)
  (administrative : Core.Context) (origin : Origin compiled) (owner : OwnedKey keys)
  (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)

/-- E is measured at the actual selected-root RuntimeTree. Its meaning is an
induction hypothesis, separate from every static receipt. -/
def ExpressionPreserves (size : Nat) : Prop :=
  ∀ compilerScope, CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
    (Origin.bridge (headers := headers) origin owner)
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    context evidence (source named)
    (CallableIndexedOwnedPreparedPairedReachedNativeExpressionTreeBounds.RuntimeTree
      (sourceContext := context) (compilerScope := compilerScope) (fuel := readFuel)
      (solved := (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements)
      root expressionSyntax callerEvidence headers administrative
      («prefix» (compiled := compiled) named)) faults size

def ExpressionReflects (size : Nat) : Prop :=
  ∀ compilerScope, CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
    (Origin.bridge (headers := headers) origin owner)
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    context evidence (source named)
    (CallableIndexedOwnedPreparedPairedReachedNativeExpressionTreeBounds.RuntimeTree
      (sourceContext := context) (compilerScope := compilerScope) (fuel := readFuel)
      (solved := (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements)
      root expressionSyntax callerEvidence headers administrative
      («prefix» (compiled := compiled) named)) faults size
end Expressions

/-- The numeric E hypothesis retains actual administrative typing and the
independent fixed-prefix witness at one literal occurrence. Static compiler
packets carry neither this hypothesis nor a completed execution law. -/
def ExpressionsPreserves (budget : Nat) : Prop :=
  ∀ {named : Named} {index : Nat} (selected : SelectedReceipt compiled named index)
    {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
    {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
    (root : RootPolicyReceipt (compiled := compiled) named (lowered compiled selected.diagnostics)
      selected.code selected.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    (callerEvidence : Option Dynamic.EvidenceEnvironment) (readFuel : Nat)
    (administrative : Core.Context) (origin : Origin compiled) (owner : OwnedKey keys)
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment),
    CallableIndexedOwnedPreparedEligibleSelectedNativeFamilyFlowStep.Eligible (headers := headers) selected origin callerEvidence evidence →
    CompatibleRuntimeContextValidity.Valid (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements
      context evidence → Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context (source named) →
    RecursiveNamedHeaderContracts.AtMost budget (ExpressionPreserves (headers := headers) (registry := registry) (faults := faults)
      functions selected root expressionSyntax callerEvidence readFuel administrative origin owner context evidence)

def ExpressionsReflects (budget : Nat) : Prop :=
  ∀ {named : Named} {index : Nat} (selected : SelectedReceipt compiled named index)
    {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
    {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
    (root : RootPolicyReceipt (compiled := compiled) named (lowered compiled selected.diagnostics)
      selected.code selected.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    (callerEvidence : Option Dynamic.EvidenceEnvironment) (readFuel : Nat)
    (administrative : Core.Context) (origin : Origin compiled) (owner : OwnedKey keys)
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment),
    CallableIndexedOwnedPreparedEligibleSelectedNativeFamilyFlowStep.Eligible (headers := headers) selected origin callerEvidence evidence →
    CompatibleRuntimeContextValidity.Valid (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements
      context evidence → Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context (source named) →
    Below budget (ExpressionReflects (headers := headers) (registry := registry) (faults := faults)
      functions selected root expressionSyntax callerEvidence readFuel administrative origin owner context evidence)

/-- The original closure F receives this specialization of the shared E IH.
The actual and fixed contexts are literally equal at this port. -/
theorem preserves_at_prefix {budget : Nat}
    (expressions : ExpressionsPreserves (headers := headers) (keys := keys)
      (registry := registry) (faults := faults) functions budget) :
    CallableIndexedOwnedPreparedEligibleSelectedNativeFamilyFlowStep.ExpressionsPreserves
      (headers := headers) (keys := keys) (registry := registry) (faults := faults) functions budget := by
  intro named index selected rootFuel rootSource rootScope rootId rootReasonAt rootLowered
    root expressionSyntax callerEvidence readFuel origin owner context evidence eligible valid runtime
  exact expressions selected root expressionSyntax callerEvidence readFuel («prefix» (compiled := compiled) named)
    origin owner context evidence eligible valid runtime

/-- The same literal specialization preserves reflection's independent Source grade. -/
theorem reflects_at_prefix {budget : Nat}
    (expressions : ExpressionsReflects (headers := headers) (keys := keys)
      (registry := registry) (faults := faults) functions budget) :
    CallableIndexedOwnedPreparedEligibleSelectedNativeFamilyFlowStep.ExpressionsReflects
      (headers := headers) (keys := keys) (registry := registry) (faults := faults) functions budget := by
  intro named index selected rootFuel rootSource rootScope rootId rootReasonAt rootLowered
    root expressionSyntax callerEvidence readFuel origin owner context evidence eligible valid runtime
  exact expressions selected root expressionSyntax callerEvidence readFuel («prefix» (compiled := compiled) named)
    origin owner context evidence eligible valid runtime

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedEligiblePairedExpressionFamilies
