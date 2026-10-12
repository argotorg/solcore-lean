import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodySupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport

/-! Numeric recursion supplies the selected called bodies internally. The
  carrier is the concrete owned pool at universe zero. Each recursive use
  consumes an authentic original Source Root at a strictly smaller grade;
  structural caller recursion handles equal native grades for groups and
  singleton tuples. Static support stores no execution or semantic callback.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds (TerminalFor ReflectsBelowFor)
open CallableIndexedOwnedPreparedStagedTerminalClosureParentPreservation (PreservesBelowFor)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (RootAt SelectedBody NamedSupport ClosureSupportFor)
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge
  (compiled := compiled) (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys)
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics

/-- The IH ranges over the exact original Source, parameter context and
  compiler child. All states, stores, mappings and renamings stay quantified
  inside the admitted expression law. -/
def PreservesRootsAt (size : Nat) : Prop :=
  ∀ {context invocation scope expression lowered},
    RootAt compiled context invocation scope expression lowered semanticFaults →
    PreservesAt poolBridge context model stages invocation
      (Point scope expression lowered) callFaults size

/-- Reflection retains its independent Source grade and exact failure scope. -/
def ReflectsRootsAt (size : Nat) : Prop :=
  ∀ {context invocation scope expression lowered},
    RootAt compiled context invocation scope expression lowered semanticFaults →
    ReflectsAt poolBridge context model stages invocation
      (Point scope expression lowered) callFaults size

variable {profile}

theorem selected_body_preserves_below
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}
    {inputs : CallableIndexedLambdaEntryPrefix.Context
      (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code}
    {packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages}
    (support : SelectedBody code inputs stages packet semanticFaults)
    {budget : Nat} (children : ∀ size, size < budget →
      PreservesRootsAt (completion := completion) (stages := stages)
        (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile size)
    {size : Nat} (within : size ≤ budget) :
    ∀ child : Staging.Recursive.Scope, stages.Closure function child →
      PreservesBelow poolBridge inputs.context model stages child packet.certificate callFaults size := by
  intro child selected childSize smaller current id lowered point
  rw [support.point] at point
  exact children childSize (Nat.lt_of_lt_of_le smaller within)
    (support.rootAt child selected) point

theorem selected_body_reflects_below
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}
    {inputs : CallableIndexedLambdaEntryPrefix.Context
      (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code}
    {packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages}
    (support : SelectedBody code inputs stages packet semanticFaults)
    {budget : Nat} (children : ∀ size, size < budget →
      ReflectsRootsAt (completion := completion) (stages := stages)
        (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile size)
    {size : Nat} (within : size ≤ budget) :
    ReflectsBelow poolBridge inputs.context model stages packet.child packet.certificate callFaults size := by
  intro childSize smaller current id lowered point
  rw [support.point] at point
  exact children childSize (Nat.lt_of_lt_of_le smaller within)
    (support.rootAt packet.child packet.selected) point

variable
  (closureTerminals : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore), TerminalFor association stages)
  (namedTerminals : ∀ header, header ∈ headers → Terminal header)
  (closureSupport : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore),
    ClosureSupportFor association stages (closureTerminals association))
  (namedSupport : ∀ header (member : header ∈ headers),
    CallableIndexedOwnedPreparedStagedNamedBodySupport.LegacySupport headers keys bodyRegistry
      header stages (namedTerminals header member) semanticFaults)

include closureSupport in
theorem closure_preserves_below
    {budget : Nat} (children : ∀ size, size < budget →
      PreservesRootsAt (completion := completion) (stages := stages)
        (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile size)
    {size : Nat} (within : size ≤ budget)
    {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore) :
    PreservesBelowFor (registry := completion.result.context.registry) (faults := callFaults)
      association (closureTerminals association) functions size := by
  have supported := closureSupport association
  cases association with
  | ordinary owner captured code history support origin prefixContext globals reference typed provenance =>
      exact selected_body_preserves_below supported children within
  | principal owner captured code history support origin globals leading reference typed provenance =>
      exact selected_body_preserves_below supported children within

include closureSupport in
theorem closure_reflects_below
    {budget : Nat} (children : ∀ size, size < budget →
      ReflectsRootsAt (completion := completion) (stages := stages)
        (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile size)
    {size : Nat} (within : size ≤ budget)
    {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore) :
    ReflectsBelowFor (registry := completion.result.context.registry) (faults := callFaults)
      association (closureTerminals association) functions size := by
  have supported := closureSupport association
  cases association with
  | ordinary owner captured code history support origin prefixContext globals reference typed provenance =>
      exact selected_body_reflects_below supported children within
  | principal owner captured code history support origin globals leading reference typed provenance =>
      exact selected_body_reflects_below supported children within

include namedSupport in
theorem named_preserves_below
    {budget : Nat} (children : ∀ size, size < budget →
      PreservesRootsAt (completion := completion) (stages := stages)
        (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile size)
    {size : Nat} (within : size ≤ budget)
    (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (member : header ∈ headers) {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child) :
    CallableIndexedOwnedPreparedStagedNamedChildBounds.PreservesBelow (headers := headers) (keys := keys)
      header model stages child
      (namedTerminals header member).certificate callFaults size := by
  cases namedSupport header member with
  | recursive static =>
    apply CallableIndexedOwnedPreparedStagedNamedChildBounds.PreservesBelow.pool
    intro childSize smaller current id lowered point
    rw [static.point] at point
    exact children childSize (Nat.lt_of_lt_of_le smaller within)
      (static.roots child selected).val point
  | formation static =>
    exact CallableIndexedOwnedPreparedStagedNamedBodySupport.Formation.preserves
      (profile := profile) (faults := callFaults) static selected size

include namedSupport in
theorem named_reflects_below
    {budget : Nat} (children : ∀ size, size < budget →
      ReflectsRootsAt (completion := completion) (stages := stages)
        (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile size)
    {size : Nat} (within : size ≤ budget)
    (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (member : header ∈ headers) {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child) :
    CallableIndexedOwnedPreparedStagedNamedChildBounds.ReflectsBelow (headers := headers) (keys := keys)
      header model stages child
      (namedTerminals header member).certificate callFaults size := by
  cases namedSupport header member with
  | recursive static =>
    apply CallableIndexedOwnedPreparedStagedNamedChildBounds.ReflectsBelow.pool
    intro childSize smaller current id lowered point
    rw [static.point] at point
    exact children childSize (Nat.lt_of_lt_of_le smaller within)
      (static.roots child selected).val point
  | formation static =>
    exact CallableIndexedOwnedPreparedStagedNamedBodySupport.Formation.reflects
      (profile := profile) (faults := callFaults) static selected size

variable
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry
    completion.result.context.registry)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)

include receiver stagePrepared observations extension semantic
  closureTerminals namedTerminals closureSupport namedSupport in
/-- This family constructs every recursive called-body preservation law.
  Only static original compiler authority and chosen terminal support enter. -/
theorem preserves (size : Nat) :
    PreservesRootsAt (completion := completion) (stages := stages)
      (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile size := by
  induction size using Nat.strongRecOn with
  | ind size ih =>
      intro context invocation scope expression lowered root
      exact CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.preserves_reached
        poolBridge receiver stagePrepared profile root.support.wellFormed root.support.runtime
        root.support.covers root.support.unique root.support.actualFunctionType observations
        extension semantic closureTerminals namedTerminals root.support.sameLedger
        root.support.runtimeLedger root.support.uninitialized size
        (fun childSize within => closure_preserves_below closureTerminals closureSupport ih within)
        (fun childSize within => named_preserves_below namedTerminals namedSupport ih within)
        root.support.certificate (.root (by simp)) root.support.noDirect root.support.callsReady size (Nat.le_refl _)

include receiver stagePrepared observations extension semantic
  closureTerminals namedTerminals closureSupport namedSupport in
/-- Native grades decrease through called bodies. The structural fold handles
  equal-grade native group and singleton tuple children without changing the
  independent Source grade returned by reflection. -/
theorem reflects (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    (size : Nat) :
    ReflectsRootsAt (completion := completion) (stages := stages)
      (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile size := by
  induction size using Nat.strongRecOn with
  | ind size ih =>
      intro context invocation scope expression lowered root
      exact CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.reflects_reached
        poolBridge receiver stagePrepared profile root.support.wellFormed root.support.runtime
        root.support.covers root.support.unique root.support.actualFunctionType observations
        extension semantic closureTerminals namedTerminals root.support.sameLedger
        root.support.runtimeLedger root.support.uninitialized stageEq size
        (fun childSize within => closure_reflects_below closureTerminals closureSupport ih within)
        (fun childSize within => named_reflects_below namedTerminals namedSupport ih within)
        root.support.certificate (.root (by simp)) root.support.noDirect root.support.callsReady size (Nat.le_refl _)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds
