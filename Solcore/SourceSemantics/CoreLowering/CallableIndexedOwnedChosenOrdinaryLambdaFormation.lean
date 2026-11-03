import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryLambdaValues

/-! The actual chosen compiler receipt supplies the local member constructor
at its literal recaptured index. Each endpoint invokes the committed formation
core once with one model for the input heap and returned relation. The
formation copies the captured cells, so the member sits at the formed
closure's index over the copies. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryLambdaFormation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedRuntimeFamilyMembers (OrdinaryIndex)
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open CallableIndexedOwnedPreparedMixedBodySiteInputs (ChosenFactory)
open CallableIndexedOwnedChosenOrdinaryFormedMembers (FactoryMember index)
open CallableIndexedOwnedChosenOrdinaryStoredMembers (ChosenAt)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)


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
/-- The known receipt and actual packet build this positive member directly at
the formed closure's literal recaptured index, over the copies. Typing is
supplied independently by the original formation core. -/
theorem chosen_at
    {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) projects
      compiled.indexed.layouts.definitions} {location : Location}
    (formed : Formed model (index receipt environment captured prefixContext).captured
      (index receipt environment captured prefixContext).code
      (CallableIndexedOwnedPreparedOrdinaryLambdaFormation.history_at
        (index receipt environment captured prefixContext).captured
        (index receipt environment captured prefixContext).code
        (index receipt environment captured prefixContext).support owner initial packet) heap store location)
    (nativeTyped : RuntimeValueHasType formed.finalWorld
      (value (index receipt environment captured prefixContext).code formed.embedding
        (CallableIndexedOwnedPreparedOrdinaryLambdaFormation.history_at
          (index receipt environment captured prefixContext).captured
          (index receipt environment captured prefixContext).code
          (index receipt environment captured prefixContext).support owner initial packet).native formed.closureActual)
      (CallableContract.functionType (index receipt environment captured prefixContext).code.receipt.parameterCore
        (index receipt environment captured prefixContext).code.receipt.resultCore) compiled.indexed.layouts.definitions) :
    ChosenAt root expressionSyntax headers keys registry faults (index receipt formed.captured formed.captures rfl)
      formed.closureHistory := by
  let i := index receipt environment captured prefixContext
  exact .ordinary owner (.formed receipt chosen formed.captured formed.captures rfl)
    ⟨(CallableIndexedOwnedPreparedOrdinaryLambdaFormation.source_origin i.captured i.code i.support owner initial packet).metadata⟩
    rfl (observed.of_slots formed.slots)
    (CallableIndexedOwnedPreparedOrdinaryLambdaFormation.reference_index i.captured i.code i.support) nativeTyped

include chosen observed in
/-- One actual formation over the copies creates the new model member at the
formed closure's literal recaptured index. There is no whole-model inclusion
premise. -/
theorem formation
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile)
      mapping world heap store) :
    let i := index receipt environment captured prefixContext
    let history := CallableIndexedOwnedPreparedOrdinaryLambdaFormation.history_at i.captured i.code i.support owner initial packet
    ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile))
        i.captured i.code history heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) i.function.context i.function.evidence
        i.function.source i.function.captured heap i.code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (i.code.lowered.expression.rename i.captured.embedding)
        (.inRight .word (value i.code formed.embedding history.native formed.closureActual)) formed.finalStore ∧
      (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile).Represents
        registry formed.finalMap formed.finalWorld (FunctionValues.sourceType i.function) (.closure formed.closure)
        (value i.code formed.embedding history.native formed.closureActual)
        (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore) ∧
      (∀ result finalStore, Evaluates actual store (i.code.lowered.expression.rename i.captured.embedding) result finalStore →
        result = .inRight .word (value i.code formed.embedding history.native formed.closureActual) ∧
          finalStore = formed.finalStore) := by
  let i := index receipt environment captured prefixContext
  exact CallableIndexedOwnedPreparedOrdinaryLambdaFormation.formation_with_member
    i.captured i.code i.support owner initial packet profile observed
    (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile)
    (fun formed nativeTyped => .chosen_ordinary (index receipt formed.captured formed.captures rfl) formed.closureHistory
      (chosen_at root expressionSyntax receipt chosen environment captured prefixContext owner initial packet observed
        formed nativeTyped))
    heaps (receipt.formation.snapshots environment) receipt.formation.ordinary receipt.formation.coercions

variable
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
    (receipt.formation.function environment).context (receipt.formation.function environment).source)
  (covers : (receipt.formation.function environment).evidence.Covers (receipt.formation.function environment).context)
  (locals : Dynamic.EnvironmentAgrees heap (receipt.formation.function environment).context.locals
    (receipt.formation.function environment).captured)
  (typed : ExpressionHasType (receipt.formation.function environment).source (receipt.formation.function environment).context
    (receipt.formation.code environment).id (receipt.formation.code environment).sourceNode.type)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile)
    mapping world heap store)
  (admitted : Admission (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller)
    (receipt.formation.function environment).context ⟨initial, packet⟩)

include chosen observed wellFormed runtime covers locals typed heaps admitted in
/-- The Source endpoint supplies the actual member of the formed closure
internally and preserves all heap/effect/admission fields, in the formed state,
under this same function model. -/
theorem preserves_at {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      (receipt.formation.function environment).context (receipt.formation.function environment).evidence
      (receipt.formation.function environment).source (receipt.formation.function environment).captured
      heap (receipt.formation.code environment).id outcome after) :
    let i := index receipt environment captured prefixContext
    ∃ result finalStore, CallableIndexedOwnedPreparedOrdinaryLambdaFormation.ResultAt
      (registry := registry) (faults := faults) i.captured i.code i.support owner initial packet
      (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile)
      outcome after result finalStore := by
  let i := index receipt environment captured prefixContext
  exact CallableIndexedOwnedPreparedOrdinaryLambdaFormation.preserves_at_with_member
    i.captured i.code i.support owner initial packet profile observed
    (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile)
    wellFormed runtime covers locals typed receipt.formation.sourceType (receipt.formation.snapshots environment)
    receipt.formation.ordinary receipt.formation.coercions heaps admitted
    (fun formed nativeTyped => .chosen_ordinary (index receipt formed.captured formed.captures rfl) formed.closureHistory
      (chosen_at root expressionSyntax receipt chosen environment captured prefixContext owner initial packet observed
        formed nativeTyped)) trace

include chosen observed wellFormed runtime covers locals typed heaps admitted in
/-- Native reflection uses the same actual closure formation and current packet;
its Source execution size is independent of the native completion. -/
theorem reflects_at {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store
      ((receipt.formation.code environment).lowered.expression.rename captured.embedding) result finalStore) :
    let i := index receipt environment captured prefixContext
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        i.function.context i.function.evidence i.function.source i.function.captured heap i.code.id outcome after ∧
      CallableIndexedOwnedPreparedOrdinaryLambdaFormation.ResultAt
        (registry := registry) (faults := faults) i.captured i.code i.support owner initial packet
        (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile)
        outcome after result finalStore := by
  let i := index receipt environment captured prefixContext
  exact CallableIndexedOwnedPreparedOrdinaryLambdaFormation.reflects_at_with_member
    i.captured i.code i.support owner initial packet profile observed
    (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile)
    wellFormed runtime covers locals typed receipt.formation.sourceType (receipt.formation.snapshots environment)
    receipt.formation.ordinary receipt.formation.coercions heaps admitted
    (fun formed nativeTyped => .chosen_ordinary (index receipt formed.captured formed.captures rfl) formed.closureHistory
      (chosen_at root expressionSyntax receipt chosen environment captured prefixContext owner initial packet observed
        formed nativeTyped)) completed

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryLambdaFormation
