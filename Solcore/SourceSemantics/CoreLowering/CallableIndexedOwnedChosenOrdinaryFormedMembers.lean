import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedMixedBodySiteInputs
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryFormedMembers

/-! One real formation retains the selected certificate factory beside its
actual ordinary index. This positive receipt is not recovered from an opaque
value relation or from an arbitrary stored closure. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryFormedMembers
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport
open CallableIndexedOwnedPreparedMixedBodyCompilerFactory
open CallableIndexedOwnedPreparedMixedBodySiteInputs
open CallableIndexedOwnedPreparedRuntimeFamilyMembers (OrdinaryIndex)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)

section Index
variable {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.Receipt caller diagnostics namedCode compilation
    sourceContext evidence scope id lowered)
  (environment : Dynamic.Environment) {mapping : LocationMap} {world : StoreTyping} {actual : Environment}
  (captured : Captures compiled.indexed mapping world scope (receipt.formation.function environment).captured actual)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) caller)

/-- The genuine prefix equality transports two typing proofs while all
runtime capture fields remain the original literal data. -/
def capture_at : Captures compiled.indexed mapping world scope
    (receipt.formation.function environment).captured actual where
  administrative := RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) caller
  canonical := captured.canonical
  actualContext := captured.actualContext
  embedding := captured.embedding
  represented := by rw [← prefixContext]; exact captured.represented
  agrees := captured.agrees
  respects := by rw [← prefixContext]; exact captured.respects
  typed := captured.typed

/-- Code, Support and prepared body are the literal chosen Formation fields. -/
def index : OrdinaryIndex compiled :=
  ⟨receipt.formation.function environment, mapping, world, scope, actual,
    capture_at receipt environment captured prefixContext,
    receipt.formation.code environment, receipt.formation.support environment, receipt.formation.prepared environment⟩
end Index

/-- A positive constructor records the literal chosen receipt and recapture.
It supplies no inverse on FormedAt, Represents, Code, or HeapRepresents. -/
inductive FactoryMember : OrdinaryIndex compiled → Prop where
  | formed {sourceContext evidence scope id lowered mapping world actual}
      (receipt : CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.Receipt caller diagnostics namedCode compilation
        sourceContext evidence scope id lowered)
      (chosen : ChosenFactory root expressionSyntax receipt) (environment : Dynamic.Environment)
      (captured : Captures compiled.indexed mapping world scope (receipt.formation.function environment).captured actual)
      (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
        (values := .initial compiled.compatible.checked) caller) :
      FactoryMember (index receipt environment captured prefixContext)

/-- The retained certificate family belongs to that exact selected Support. -/
theorem FactoryMember.factories {i : OrdinaryIndex compiled} (member : FactoryMember root expressionSyntax i) :
    i.support.expressionSyntax = expressionSyntax ∧
    i.support.certificates = certificates root expressionSyntax := by
  cases member with
  | formed receipt chosen environment captured prefixContext =>
    exact ⟨(recaptured_factory root expressionSyntax receipt chosen environment).1,
      (recaptured_factory root expressionSyntax receipt chosen environment).2.1⟩

/-- Actual map/world growth keeps the same chosen factory and captured Source
spine. It does not assert that any mutated heap still stores this value. -/
theorem FactoryMember.extend {i : OrdinaryIndex compiled} (member : FactoryMember root expressionSyntax i)
    {futureMap : LocationMap} {futureWorld : StoreTyping}
    (maps : LocationMap.Extends i.mapping futureMap) (worlds : WorldExtends i.world futureWorld) :
    FactoryMember root expressionSyntax {
      function := i.function, mapping := futureMap, world := futureWorld, scope := i.scope
      capturedActual := i.capturedActual, captured := i.captured.extend maps worlds
      code := i.code, support := i.support, prepared := i.prepared } := by
  cases member with
  | formed receipt chosen environment captured prefixContext =>
    exact .formed receipt chosen environment (captured.extend maps worlds) prefixContext

section Formation
variable {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.Receipt caller diagnostics namedCode compilation
    sourceContext evidence scope id lowered)
  (chosen : ChosenFactory root expressionSyntax receipt) (environment : Dynamic.Environment)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {actual canonical : Environment} {heap : Dynamic.Heap} {store : Store}
  (captured : Captures compiled.indexed mapping world scope (receipt.formation.function environment).captured actual)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) caller)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner caller _ initial)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)

include chosen observed in
/-- The original formation producer runs once. The same complete tuple and
known formed member retain the positive chosen-factory companion. -/
theorem formation_member_with_factory
    (stored : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions) :
    let i := index receipt environment captured prefixContext
    let history := CallableIndexedOwnedPreparedOrdinaryLambdaFormation.history_at
      i.captured i.code i.support owner initial packet
    Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) i.function.context i.function.evidence
      i.function.source i.function.captured heap i.code.id (.closure i.function) heap ∧
    Evaluates actual store (i.code.lowered.expression.rename i.captured.embedding)
      (.inRight .word (value i.code i.captured.embedding history.native actual)) store ∧
    (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile).Represents
      registry mapping world (FunctionValues.sourceType i.function) (.closure i.function)
      (value i.code i.captured.embedding history.native actual)
      (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore) ∧
    (∀ result finalStore, Evaluates actual store (i.code.lowered.expression.rename i.captured.embedding) result finalStore →
      result = .inRight .word (value i.code i.captured.embedding history.native actual) ∧ finalStore = store) ∧
    CallableIndexedOwnedPreparedOrdinaryFormedMembers.FormedAt headers keys registry faults
      mapping world (FunctionValues.sourceType i.function) (.closure i.function)
      (value i.code i.captured.embedding history.native actual)
      (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore) ∧
    FactoryMember root expressionSyntax i := by
  obtain ⟨sourceTrace, evaluated, related, determined, formed⟩ :=
    CallableIndexedOwnedPreparedOrdinaryFormedMembers.formation_member
      (capture_at receipt environment captured prefixContext) (receipt.formation.code environment) (receipt.formation.support environment)
      (receipt.formation.prepared environment) owner initial packet profile rfl observed stored
      receipt.formation.ordinary receipt.formation.coercions
  exact ⟨sourceTrace, evaluated, related, determined, formed, .formed receipt chosen environment captured prefixContext⟩

include chosen in
/-- A real certificate of this same recaptured Support is interpreted by the
original accepted-child compiler producer; no Tree is supplied by the caller. -/
theorem coverage_at_formed
    {currentContext : SourceSemantics.Context} {childScope : SourceCoreLocalCell.Scope}
    (headers : RecursiveNamedCatalog.Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions (Program.ofChecked compiled.sourceProgram))
    (domain : DomainAt root expressionSyntax receipt.formation.body.readFuel currentContext evidence childScope headers)
    (valid : CompatibleRuntimeContextValidity.Valid (context compiled.indexed caller.named).solvedRequirements currentContext evidence)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) currentContext (source caller.named))
    {child : ExpressionId} {output : SourceCoreBasic.LoweredExpr}
    (actual : (receipt.formation.support environment).certificates
      (receipt.formation.support environment).body.readFuel (receipt.formation.function environment).source
      currentContext childScope child output) :
    RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsFor
      (BodyCalls root expressionSyntax (indirect_factory root expressionSyntax headers domain valid) headers)
      receipt.formation.body.readFuel (.initial compiled.compatible.checked) (source caller.named) currentContext
      (context compiled.indexed caller.named).solvedRequirements rootReasonAt childScope child output :=
  coverage_at_support root expressionSyntax receipt chosen environment headers domain valid runtime actual
end Formation
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryFormedMembers
