import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedCallBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedExpressions
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNamedInvocation

/-! The expression closure with direct calls at the roots of a named-row body.
`ClosedCalls` states that every expression the compiler accepts for the body is
an extended root (`CallSubset`). The receipt of each accepted expression is
extracted from the compiler's own acceptance and closed by the extended bounds;
the inputs are the call authority of the body's call receipts and the
application of every admitted callee header below the budget. The bridge is
the ordinary caller carrier of the slot-retaining protocol. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedCallExpressions
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CellAwareInvocationAcceptedTerminals (children)
open CellAwareInvocationAcceptedNamedInvocation (rowIndex)
open CellAwareInvocationAcceptedCallTrees (CallSubset)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Receipt)
open CallableIndexedOwnedPreparedStagedDirectCallAuthority (Port)
open GeneralizedLocalInitializerCompilation (namedPolicy namedLowerBody)

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header whole (Program.ofChecked whole.sourceProgram))}
  {keys : List (Key whole (Program.ofChecked whole.sourceProgram))}
  {named : SourceCoreGeneralFunctions.Function}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (generation : CallableIndexedNamedGeneration.Compilation whole.indexed named diagnostics code)
  (record : SourceCompilationPlan.exactSpecialization whole.indexed.base.plan named.signature.key =
    .ok named.specialized)
  (called : DeclarationInstantiation → Prop)

/-- The extended expression roots as a predicate on the actual accepted
receipts of the named row. -/
def Accepted (fuel : Nat) : GenericExpressionMeaning.Certificate :=
  fun scope expression lowered => children (rowIndex generation record) fuel scope expression lowered ∧
    CallSubset whole.indexed named (CallableIndexedNamedGeneration.source named) called expression

/-- Every expression the compiler accepts for the named row, at any fuel and
scope, is an extended root. -/
def ClosedCalls : Prop :=
  ∀ fuel scope expression lowered, children (rowIndex generation record) fuel scope expression lowered →
    CallSubset whole.indexed named (CallableIndexedNamedGeneration.source named) called expression

/-- Every direct-call receipt of the named row's compiler selects a header of
the catalog. -/
def Ports : Prop :=
  ∀ {rootFuel fuel : Nat} {scope : SourceCoreLocalCell.Scope} {callId callee : ExpressionId}
    {ids : List ExpressionId} {instantiation : DeclarationInstantiation} {callCode : SourceCoreBasic.LoweredExpr}
    (receipt : Receipt (namedPolicy generation rootFuel) (namedLowerBody generation) fuel
      (CallableIndexedNamedGeneration.context whole.indexed named) (.initial whole.compatible.checked)
      (CallableIndexedNamedGeneration.source named) scope callId callee ids instantiation
      (rowIndex generation record).reasonAt callCode),
    Nonempty (Port receipt headers)

variable {receiving : SourceCoreRawMetadata.Registry}
  {functions : FunctionModel whole.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions whole.indexed)}
  (owner : OwnedKey keys) (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep)

local notation "model" => CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions

private theorem reads_lowered {fuel : Nat} {context : SourceSemantics.Context}
    (sourceEq : invocation.source = (rowIndex generation record).source)
    (reads : CellAwareInvocationAcceptedExpressions.Reads (rowIndex generation record) faults) :
    ∀ scope id lowered,
      CompatibleExpressionReads.LoweredRead fuel
        (SourceCoreCompatibleValues.Context.initial whole.compatible.checked)
        invocation.source context (rowIndex generation record).reasonAt scope id lowered →
      ∀ location, faults (.semantic (.uninitializedLocation location))
        ((rowIndex generation record).reasonAt id) := by
  intro scope id lowered receipt location
  obtain ⟨certificate, _type, _binding⟩ := receipt
  exact reads id certificate.node certificate.name certificate.binder
    (sourceEq ▸ certificate.metadata.found) certificate.form location

/-- Every accepted extended root of the named row preserves its staged Source
execution at every grade, given the call authority and the application of
every admitted callee header below the grade. -/
theorem preserves (fuel : Nat) {context : SourceSemantics.Context}
    (sourceEq : invocation.source = (rowIndex generation record).source)
    (extension : SourceCoreRawMetadata.Extends
      (SourceCoreCompatibleValues.Context.initial whole.compatible.checked).registry receiving)
    (reads : CellAwareInvocationAcceptedExpressions.Reads (rowIndex generation record) faults)
    (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies (Program.ofChecked whole.sourceProgram)
      registry)
    (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked whole.sourceProgram) context
      (rowIndex generation record).source)
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = (rowIndex generation record).compilation.solvedRequirements)
    (ports : Ports (headers := headers) generation record) (size : Nat)
    (applications : ∀ header, header ∈ headers → called header.instantiation →
      CellAwareInvocationAcceptedDirectCalls.PreservesBelow (attachment := fun _ _ _ => True) (headers := headers) (keys := keys) model registry faults
        header size) :
    CellAwareInvocationExpressionBounds.PreservesAt (attachment := fun _ _ _ => True)
      (CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner 1 keyPhysical.locations).forgetSlots context model (rowIndex generation record) registry
      invocation (Accepted generation record called fuel) faults size := by
  have sourceRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked whole.sourceProgram) context invocation.source :=
    sourceEq ▸ runtime
  have uninitialized := reads_lowered generation record invocation faults (fuel := whole.indexed.fuel)
    (context := context) sourceEq reads
  intro scope id lowered accepted node found typed mapping world administrative environment canonical
    actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped
    initial admitted authority physical
  obtain ⟨generated, subset⟩ := accepted
  have sourceNamed : invocation.source = CallableIndexedNamedGeneration.source named := sourceEq
  change SourceCoreGeneralFunctions.lowerContextualExpression _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ at generated
  cases fuel with
  | zero => simp [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at generated
  | succ rootFuel =>
    rw [GeneralizedLocalInitializerCompilation.named_contextual generation record] at generated
    have unique := sourceRuntime.graph.nodeOccurrencesUnique
    rw [sourceNamed] at unique found typed
    have tree := CellAwareInvocationAcceptedCallTrees.of_call_subset (headers := headers) generation rootFuel subset
      unique physical.declarations found typed generated ports
    rw [← sourceNamed] at tree found typed
    exact CellAwareInvocationAcceptedCallBounds.preserves_call_tree (attachment := fun _ _ _ => True)
      (compilation := CallableIndexedNamedGeneration.context whole.indexed named) owner
      (CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner 1 keyPhysical.locations) keyPhysical
      (fun state => state.physical) functions extension sameLedger faults uninitialized selectedBodies wellFormed
      sourceRuntime covers tree size applications ⟨rfl, rfl, rfl⟩ found typed environments heaps locals agrees
      actualTyped initial admitted authority physical

/-- Every completed native run of an accepted extended root reconstructs an
independent Source grade, outcome and reached heap. -/
theorem reflects (fuel : Nat) {context : SourceSemantics.Context}
    (sourceEq : invocation.source = (rowIndex generation record).source)
    (extension : SourceCoreRawMetadata.Extends
      (SourceCoreCompatibleValues.Context.initial whole.compatible.checked).registry receiving)
    (reads : CellAwareInvocationAcceptedExpressions.Reads (rowIndex generation record) faults)
    (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies (Program.ofChecked whole.sourceProgram)
      registry)
    (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked whole.sourceProgram) context
      (rowIndex generation record).source)
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = (rowIndex generation record).compilation.solvedRequirements)
    (ports : Ports (headers := headers) generation record) (size : Nat)
    (applications : ∀ header, header ∈ headers → called header.instantiation →
      CellAwareInvocationAcceptedDirectCalls.ReflectsBelow (attachment := fun _ _ _ => True) (headers := headers) (keys := keys) model registry faults
        header size) :
    CellAwareInvocationExpressionBounds.ReflectsAt (attachment := fun _ _ _ => True)
      (CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner 1 keyPhysical.locations).forgetSlots context model (rowIndex generation record) registry
      invocation (Accepted generation record called fuel) faults size := by
  have sourceRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked whole.sourceProgram) context invocation.source :=
    sourceEq ▸ runtime
  have uninitialized := reads_lowered generation record invocation faults (fuel := whole.indexed.fuel)
    (context := context) sourceEq reads
  intro scope id lowered accepted node found typed mapping world administrative environment canonical
    actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped
    initial admitted authority physical
  obtain ⟨generated, subset⟩ := accepted
  have sourceNamed : invocation.source = CallableIndexedNamedGeneration.source named := sourceEq
  change SourceCoreGeneralFunctions.lowerContextualExpression _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ at generated
  cases fuel with
  | zero => simp [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at generated
  | succ rootFuel =>
    rw [GeneralizedLocalInitializerCompilation.named_contextual generation record] at generated
    have unique := sourceRuntime.graph.nodeOccurrencesUnique
    rw [sourceNamed] at unique found typed
    have tree := CellAwareInvocationAcceptedCallTrees.of_call_subset (headers := headers) generation rootFuel subset
      unique physical.declarations found typed generated ports
    rw [← sourceNamed] at tree found typed
    exact CellAwareInvocationAcceptedCallBounds.reflects_call_tree (attachment := fun _ _ _ => True)
      (compilation := CallableIndexedNamedGeneration.context whole.indexed named) owner
      (CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner 1 keyPhysical.locations) keyPhysical
      (fun state => state.physical) functions extension sameLedger faults uninitialized selectedBodies wellFormed
      sourceRuntime covers tree size applications ⟨rfl, rfl, rfl⟩ found typed environments heaps locals agrees
      actualTyped initial admitted authority physical

/-- A named row whose accepted expressions are all extended roots discharges
the accepted-expression input of the statement closure on the slot-retaining
protocol at a budget, given the call authority and the application of every
admitted callee header below the budget. -/
theorem expressions (closed : ClosedCalls generation record called) (budget : Nat)
    (sourceEq : invocation.source = (rowIndex generation record).source)
    (extension : SourceCoreRawMetadata.Extends
      (SourceCoreCompatibleValues.Context.initial whole.compatible.checked).registry receiving)
    (reads : CellAwareInvocationAcceptedExpressions.Reads (rowIndex generation record) faults)
    (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies (Program.ofChecked whole.sourceProgram)
      registry)
    (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))
    (ports : Ports (headers := headers) generation record)
    (applications : ∀ header, header ∈ headers → called header.instantiation →
      CellAwareInvocationAcceptedDirectCalls.PreservesBelow (attachment := fun _ _ _ => True) (headers := headers) (keys := keys) model registry faults
        header budget ∧
      CellAwareInvocationAcceptedDirectCalls.ReflectsBelow (attachment := fun _ _ _ => True) (headers := headers) (keys := keys) model registry faults
        header budget) :
    CellAwareInvocationAcceptedInputs.Expressions (attachment := fun _ _ _ => True) (receiving := receiving)
      (functions := functions)
      (CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner 1 keyPhysical.locations).forgetSlots (rowIndex generation record) registry invocation faults budget := by
  intro fuel context runtime covers sameLedger
  refine ⟨?_, ?_⟩
  · intro size smaller scope id lowered generated
    exact preserves generation record called owner keyPhysical registry invocation faults fuel sourceEq extension
      reads selectedBodies wellFormed runtime covers sameLedger ports size
      (fun header member admitted below less => (applications header member admitted).1 below
        (Nat.lt_trans less smaller))
      ⟨generated, closed fuel scope id lowered generated⟩
  · intro size smaller scope id lowered generated
    exact reflects generation record called owner keyPhysical registry invocation faults fuel sourceEq extension
      reads selectedBodies wellFormed runtime covers sameLedger ports size
      (fun header member admitted below less => (applications header member admitted).2 below
        (Nat.lt_trans less smaller))
      ⟨generated, closed fuel scope id lowered generated⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedCallExpressions
