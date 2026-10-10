import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeFamilyStaticQualification
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCanonicalFlowBounds

/-! The F step uses the literal retained AcceptedAt and one finite RuntimeTree
construction. Its E inputs are the mutually graded induction hypotheses at
that same Tree. The original JointBody prepared producer runs once per
direction. No static field stores an expression or body execution law.

This is the intermediate step of the mixed family. The final induction must
manufacture E call branches and the static Domain packets, and supply the
actual selected receiving diagnostic issuance. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeFamilyFlowStep
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedPreparedCanonicalCaptureReceipts («prefix»)
open CallableIndexedOwnedPreparedNativeFamilyStaticQualification (OccurrenceFactory)
open CallableIndexedOwnedPreparedCanonicalFlowBounds (Origin)
open CallableIndexedOwnedTypedLambdaBodyContinuations (Validity)
open CallableIndexedOwnedTypedLambdaProtocolContinuations (FlowPreserves FlowReflects)
open CallableIndexedOwnedContextualLambdaSourceDiagnostics
open CallableIndexedOwnedContextualLambdaJointStaticReceipts (JointBody trackedFactory)
open RecursiveNamedCatalogInvocationBounds (Below)

universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {named : Named}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  (namedCompilation : Compilation compiled.indexed named diagnostics namedCode)
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) named diagnostics namedCode namedCompilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  (callerEvidence : Option Dynamic.EvidenceEnvironment)
  {headers : RecursiveNamedCatalog.Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions (Program.ofChecked compiled.sourceProgram)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}

private abbrev Trees (readFuel : Nat) (currentContext : SourceSemantics.Context)
    (compilerScope : SourceCoreLocalCell.Scope) : GenericExpressionMeaning.Certificate :=
  CallableIndexedOwnedPreparedReachedNativeExpressionTreeBounds.RuntimeTree
    (sourceContext := currentContext) (compilerScope := compilerScope) (fuel := readFuel)
    (solved := (context compiled.indexed named).solvedRequirements)
    root expressionSyntax callerEvidence headers («prefix» (compiled := compiled) named)

section Select
variable {readFuel : Nat} {currentContext : SourceSemantics.Context}
  (factory : OccurrenceFactory root expressionSyntax callerEvidence headers readFuel)
  (unique : NodeOccurrencesUnique (source named))
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (CallableIndexedOwnedFunctionState.Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (evidence : Dynamic.EvidenceEnvironment)

/-- Pointwise selection consumes the retained action itself. The Tree is
manufactured internally; the E hypothesis is the same graded child family. -/
private theorem preserves_accepted
    (factory : OccurrenceFactory root expressionSyntax callerEvidence headers readFuel)
    (unique : NodeOccurrencesUnique (source named)) {sourceAt : TypedSource}
    (sameSource : sourceAt = source named) (size : Nat)
    (induction : ∀ compilerScope, CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      currentContext evidence (source named)
      (Trees (headers := headers) namedCompilation root expressionSyntax callerEvidence readFuel currentContext compilerScope) faults size) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      currentContext evidence sourceAt
      (CallableIndexedOwnedPreparedNativeCompilerChildren.certificates root expressionSyntax
        («prefix» (compiled := compiled) named) readFuel sourceAt currentContext) faults size := by
  cases sameSource
  intro scope id lowered accepted
  exact induction scope (OccurrenceFactory.runtime_tree root expressionSyntax callerEvidence headers readFuel factory unique accepted)

private theorem reflects_accepted
    (factory : OccurrenceFactory root expressionSyntax callerEvidence headers readFuel)
    (unique : NodeOccurrencesUnique (source named)) {sourceAt : TypedSource}
    (sameSource : sourceAt = source named) (size : Nat)
    (induction : ∀ compilerScope, CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      currentContext evidence (source named)
      (Trees (headers := headers) namedCompilation root expressionSyntax callerEvidence readFuel currentContext compilerScope) faults size) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      currentContext evidence sourceAt
      (CallableIndexedOwnedPreparedNativeCompilerChildren.certificates root expressionSyntax
        («prefix» (compiled := compiled) named) readFuel sourceAt currentContext) faults size := by
  cases sameSource
  intro scope id lowered accepted
  exact induction scope (OccurrenceFactory.runtime_tree root expressionSyntax callerEvidence headers readFuel factory unique accepted)
end Select

variable {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative)
  (sameSource : function.source = source named)
  (issued : IssuedSource compiled code.compilation.owner function.source)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (body : JointBody namedCompilation code (Program.ofChecked compiled.sourceProgram) expressionSyntax
    (CallableIndexedOwnedPreparedNativeCompilerChildren.certificates root expressionSyntax
      («prefix» (compiled := compiled) named))
    diagnosticPolicy issued.invalidOperand issued.invalidUnary issued.invalidProjection issued.missingDefault)
  (factory : OccurrenceFactory root expressionSyntax callerEvidence headers body.readFuel)
  (origin : Origin compiled) (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {table : SourceCoreFaultSites.Table}
  (rebuilt : issued.diagnostics.tableForRegistry registry extension = .ok table)
  (operandIncluded : ∀ reason token, GenericAssignmentDiagnostics.OperandRep issued.assignments reason token → faults reason token)
  (unaryIncluded : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep issued.assignments reason token → faults reason token)
  (interprets : ∀ currentContext, Validity (program := Program.ofChecked compiled.sourceProgram) captured code currentContext →
    CallableIndexedOwnedContextualLambdaAssignmentReadiness.ReachedInterpretations
      (context := currentContext)
      (certificates := CallableIndexedOwnedPreparedNativeCompilerChildren.certificates root expressionSyntax
        («prefix» (compiled := compiled) named) body.readFuel function.source)
      (administrative := captured.administrative)
      (factory := trackedFactory diagnosticPolicy function.source issued.invalidOperand)
      (faults := faults) (registry := registry) issued
      (Origin.bridge (headers := headers) origin owner) functions table)

include sameSource factory extension faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets in
/-- E at sizes at most n constructs F at n using the same actual body recipe.
All E premises here are induction hypotheses; none is stored in qualification. -/
theorem preserves_flow (budget : Nat)
    (expressionIH : ∀ currentContext, Validity (program := Program.ofChecked compiled.sourceProgram) captured code currentContext →
      RecursiveNamedHeaderContracts.AtMost budget (fun size => ∀ compilerScope,
        CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
          (Origin.bridge (headers := headers) origin owner)
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          currentContext function.evidence (source named)
          (Trees (headers := headers) namedCompilation root expressionSyntax callerEvidence body.readFuel currentContext compilerScope) faults size)) :
    RecursiveNamedHeaderContracts.AtMost budget
      (FlowPreserves captured code body.toBody functions (Origin.bridge (headers := headers) origin owner)
        (registry := registry) (faults := faults)) := by
  apply CallableIndexedOwnedPreparedCanonicalFlowBounds.preserves_flow namedCompilation captured code issued body origin owner
    functions extension faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets budget
  intro currentContext valid size within
  have unique : NodeOccurrencesUnique (source named) := by simpa only [sameSource] using body.unique
  exact @preserves_accepted (namedCompilation := namedCompilation) (root := root)
    (expressionSyntax := expressionSyntax) (callerEvidence := callerEvidence) (factory := factory) (unique := unique)
    (bridge := Origin.bridge (headers := headers) origin owner) (functions := functions)
    (evidence := function.evidence) (sourceAt := function.source) (sameSource := sameSource) (size := size) (induction := expressionIH currentContext valid size within)

include sameSource factory extension faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets in
/-- The native strict E family constructs F reflection with its independently
measured Source grade. The original prepared flow executes only once. -/
theorem reflects_flow (budget : Nat) (functionTypes : FunctionRuntimeViews functions)
    (expressionIH : ∀ currentContext, Validity (program := Program.ofChecked compiled.sourceProgram) captured code currentContext →
      Below budget (fun size => ∀ compilerScope,
        CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
          (Origin.bridge (headers := headers) origin owner)
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          currentContext function.evidence (source named)
          (Trees (headers := headers) namedCompilation root expressionSyntax callerEvidence body.readFuel currentContext compilerScope) faults size)) :
    Below budget
      (FlowReflects captured code body.toBody functions (Origin.bridge (headers := headers) origin owner)
        (registry := registry) (faults := faults)) := by
  apply CallableIndexedOwnedPreparedCanonicalFlowBounds.reflects_flow namedCompilation captured code issued body origin owner
    functions extension faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets budget functionTypes
  intro currentContext valid size within
  have unique : NodeOccurrencesUnique (source named) := by simpa only [sameSource] using body.unique
  exact @reflects_accepted (namedCompilation := namedCompilation) (root := root)
    (expressionSyntax := expressionSyntax) (callerEvidence := callerEvidence) (factory := factory) (unique := unique)
    (bridge := Origin.bridge (headers := headers) origin owner) (functions := functions)
    (evidence := function.evidence) (sourceAt := function.source) (sameSource := sameSource) (size := size) (induction := expressionIH currentContext valid size within)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeFamilyFlowStep
