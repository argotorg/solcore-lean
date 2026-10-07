import Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyReadyOrigins

/-! Structural inputs and finite producers for the existing measured body
family. Each kit supplies only the actual assignment prefixes and individual
head or loop recipes consumed inside the shared catalog fold. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyReadyInputs
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableRuntimeBodyOrigins
open RecursiveNamedLexicalContracts.Stateful.WithReady
open ProtectedStateImperativeCatalogReady
universe u v
variable {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {Records : Type v}
  (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (readiness : Readiness protocol)
  (stateBindings : ProtectedStateTransition.Bindings protocol)
  (program : Program) (origin : StaticOrigin values ambient registry faults)

/-- Predicates and genuine site/transfer receipts at this exact static origin. -/
structure Inputs where
  facts : SourceSemantics.Context → Bool → List StatementId → TypeSystem.Ty → Prop
  headFacts : SourceSemantics.Context → StatementId → TypeSystem.Ty → Prop
  exprFacts : SourceSemantics.Context → ExpressionId → ExpressionNode → Prop
  loopFacts : SourceSemantics.Context → ExpressionId → List ForItemForm → List StatementId → TypeSystem.Ty → Prop
  initializerFacts : SourceSemantics.Context → List ForItemForm → ExpressionId → List ForItemForm → List StatementId → TypeSystem.Ty → Prop
  assignmentFacts : SourceSemantics.Context → AssignmentResolution → Syntax.ValueAssignOp → ExpressionId → Prop
  snapshotFacts : SourceSemantics.Context → AssignmentResolution → Prop
  sites : StaticSites facts headFacts exprFacts program origin.function.evidence origin.function.source
  initializerSites : InitializerSites initializerFacts loopFacts origin.function.source
  assignmentSites : AssignmentSites headFacts assignmentFacts snapshotFacts origin.function.source
  transfers : AllocationTransfers protocol readiness stateBindings origin.function.source
  snapshots : SnapshotTransfers protocol readiness origin.validity snapshotFacts program origin.function.evidence origin.function.source

variable (functions : FunctionModel values.checked.catalog ambient)
  (conditionGate : Location → CallableIndexedHistory.NativeFrame → Prop)
  (inputs : Inputs protocol readiness stateBindings program origin) (budget : Nat)

/-- Finite source producers; no completed catalog or body law is stored. -/
structure PreservingKits : Prop where
  assignments : ∀ context, origin.validity context → Assignment.AssignmentPrefixPreservesAt protocol readiness inputs.assignmentFacts functions
      (registry := registry) program origin.function.evidence origin.function.source (origin.certificates context) context origin.administrative budget
  assignmentFaults : ∀ context, origin.validity context → Assignment.AssignmentFaultPreservesAt protocol readiness inputs.assignmentFacts functions
      (registry := registry) program origin.function.evidence origin.function.source (origin.certificates context) context origin.administrative faults budget
  headFor : PreservingHeads protocol readiness conditionGate inputs.headFacts functions program origin.function.evidence origin.validity budget
      (layouts := origin.layouts) (owner := origin.owner) (active := origin.active) (frame := origin.frameLayout) (globals := origin.globals) (onError := origin.onError)
      (source := origin.function.source) (expressionSyntax := origin.expressionSyntax) (certificates := origin.certificates) (administrative := origin.administrative)
      (registry := registry) (faults := faults)
      (RecursiveNamedImperativeFor.Stateful.WithReady.PreservesAtWith protocol readiness conditionGate inputs.facts inputs.loopFacts inputs.initializerFacts
        (validity := origin.validity) (diagnosticPolicy := origin.diagnosticPolicy) (certificates := origin.certificates) (layouts := origin.layouts)
        (owner := origin.owner) (active := origin.active) (frame := origin.frameLayout) (globals := origin.globals) (onError := origin.onError)
        (source := origin.function.source) (administrative := origin.administrative) (registry := registry) (faults := faults)
        functions program origin.function.evidence budget)
  loopFor : PreservingLoops protocol readiness conditionGate inputs.loopFacts functions program origin.function.evidence origin.validity budget
      (layouts := origin.layouts) (owner := origin.owner) (active := origin.active) (frame := origin.frameLayout) (globals := origin.globals) (onError := origin.onError)
      (source := origin.function.source) (expressionSyntax := origin.expressionSyntax) (certificates := origin.certificates) (administrative := origin.administrative)
      (registry := registry) (faults := faults)
      (RecursiveNamedImperativeFor.Stateful.WithReady.PreservesAtWith protocol readiness conditionGate inputs.facts inputs.loopFacts inputs.initializerFacts
        (validity := origin.validity) (diagnosticPolicy := origin.diagnosticPolicy) (certificates := origin.certificates) (layouts := origin.layouts)
        (owner := origin.owner) (active := origin.active) (frame := origin.frameLayout) (globals := origin.globals) (onError := origin.onError)
        (source := origin.function.source) (administrative := origin.administrative) (registry := registry) (faults := faults)
        functions program origin.function.evidence budget) origin.diagnosticPolicy

/-- Finite native producers use the same real head and loop child goals. -/
structure ReflectingKits : Prop where
  assignments : ∀ context, origin.validity context → Assignment.AssignmentReflectsAt protocol readiness inputs.assignmentFacts functions
      (registry := registry) program origin.function.evidence origin.function.source (origin.certificates context) context origin.administrative faults budget
  headFor : ReflectingHeads protocol readiness conditionGate inputs.headFacts functions program origin.function.evidence origin.validity budget
      (layouts := origin.layouts) (owner := origin.owner) (active := origin.active) (frame := origin.frameLayout) (globals := origin.globals) (onError := origin.onError)
      (source := origin.function.source) (expressionSyntax := origin.expressionSyntax) (certificates := origin.certificates) (administrative := origin.administrative)
      (registry := registry) (faults := faults)
      (RecursiveNamedImperativeFor.Stateful.WithReady.ReflectsAtWith protocol readiness conditionGate inputs.facts inputs.loopFacts inputs.initializerFacts
        (validity := origin.validity) (diagnosticPolicy := origin.diagnosticPolicy) (certificates := origin.certificates) (layouts := origin.layouts)
        (owner := origin.owner) (active := origin.active) (frame := origin.frameLayout) (globals := origin.globals) (onError := origin.onError)
        (source := origin.function.source) (administrative := origin.administrative) (registry := registry) (faults := faults)
        functions program origin.function.evidence budget)
  loopFor : ReflectingLoops protocol readiness conditionGate inputs.loopFacts functions program origin.function.evidence origin.validity budget
      (layouts := origin.layouts) (owner := origin.owner) (active := origin.active) (frame := origin.frameLayout) (globals := origin.globals) (onError := origin.onError)
      (source := origin.function.source) (expressionSyntax := origin.expressionSyntax) (certificates := origin.certificates) (administrative := origin.administrative)
      (registry := registry) (faults := faults)
      (RecursiveNamedImperativeFor.Stateful.WithReady.ReflectsAtWith protocol readiness conditionGate inputs.facts inputs.loopFacts inputs.initializerFacts
        (validity := origin.validity) (diagnosticPolicy := origin.diagnosticPolicy) (certificates := origin.certificates) (layouts := origin.layouts)
        (owner := origin.owner) (active := origin.active) (frame := origin.frameLayout) (globals := origin.globals) (onError := origin.onError)
        (source := origin.function.source) (administrative := origin.administrative) (registry := registry) (faults := faults)
        functions program origin.function.evidence budget) origin.diagnosticPolicy

/-- The compatibility specialization requests no additional proof facets. -/
def Inputs.trivial : Inputs protocol (Readiness.trivial protocol) stateBindings program origin where
  facts := fun _ _ _ _ => True
  headFacts := fun _ _ _ => True
  exprFacts := fun _ _ _ => True
  loopFacts := fun _ _ _ _ _ => True
  initializerFacts := fun _ _ _ _ _ _ => True
  assignmentFacts := fun _ _ _ _ => True
  snapshotFacts := fun _ _ => True
  sites := StaticSites.trivial program origin.function.evidence origin.function.source
  initializerSites := InitializerSites.trivial origin.function.source
  assignmentSites := AssignmentSites.trivial origin.function.source
  transfers := AllocationTransfers.trivial protocol stateBindings origin.function.source
  snapshots := ProtectedForHeader.Stateful.WithReady.SnapshotTransfers.trivial protocol origin.validity program origin.function.evidence origin.function.source

section Compatibility
variable (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (producer : ProtectedStateTransition.MarkedAllocation.Producer protocol origin.layouts origin.frameLayout
    (CompatibleAmbientHeap.payloadModel values.checked registry functions))
  (acquire : ∀ location native, conditionGate location native →
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary location native)
  (stateTransport : ProtectedStateTransition.AdministrativeTransport protocol)

include extension faithful observations producer acquire stateTransport in
/-- Compatibility kits delegate the original finite producers. -/
theorem PreservingKits.trivial
    (expressions : ∀ context, origin.validity context → RecursiveNamedHeaderContracts.AtMost budget (fun child =>
      ProtectedStateTransition.PreservesAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context origin.function.evidence origin.function.source (origin.certificates context) faults child)) :
    PreservingKits protocol (Readiness.trivial protocol) stateBindings program origin functions conditionGate
      (Inputs.trivial protocol stateBindings program origin) budget := by
  have assignments := RecursiveNamedImperativeFor.Stateful.WithReady.assignment_prefix_uniform
    (administrative := origin.administrative) (functions := functions) (extension := extension) (program := program) (evidence := origin.function.evidence)
    (protocol := protocol) (stateTransport := stateTransport) (validity := origin.validity)
    (faithful := faithful) (observations := observations) (budget := budget) (meaningMost := expressions)
  have assignmentFaults := RecursiveNamedImperativeFor.Stateful.WithReady.assignment_fault_uniform
    (administrative := origin.administrative) (functions := functions) (extension := extension) (program := program) (evidence := origin.function.evidence)
    (protocol := protocol) (stateTransport := stateTransport) (validity := origin.validity)
    (faithful := faithful) (observations := observations) (budget := budget) (meaningMost := expressions)
  exact {
    assignments := (fun context valid => ProtectedForHeader.Stateful.WithReady.assignment_prefix_trivial protocol functions program origin.function.evidence
      origin.function.source (origin.certificates context) context origin.administrative budget (assignments context valid))
    assignmentFaults := (fun context valid => ProtectedForHeader.Stateful.WithReady.assignment_fault_trivial protocol functions program origin.function.evidence
      origin.function.source (origin.certificates context) context origin.administrative faults budget (assignmentFaults context valid))
    headFor := (RecursiveNamedImperativeFor.Stateful.WithReady.preserving_heads_trivial
    (administrative := origin.administrative) (functions := functions) (definitions := origin.definitions) (registered := origin.registered)
    (extension := extension) (program := program) (evidence := origin.function.evidence)
    (protocol := protocol) (producer := producer) (conditionGate := conditionGate) (acquire := acquire)
    (stateTransport := stateTransport) (stateBindings := stateBindings)
    (validity := origin.validity) (extend := origin.extend) (solved := origin.solved)
    (faithful := faithful) (observations := observations) (budget := budget) (runtimeOf := fun _ valid => origin.runtimeOf valid) (meaningMost := expressions)
    origin.diagnosticPolicy origin.body.unique)
    loopFor := (RecursiveNamedImperativeFor.Stateful.WithReady.preserving_loops_trivial
    (administrative := origin.administrative) (functions := functions) (definitions := origin.definitions) (registered := origin.registered)
    (extension := extension) (program := program) (evidence := origin.function.evidence)
    (protocol := protocol) (producer := producer) (conditionGate := conditionGate) (acquire := acquire)
    (stateTransport := stateTransport) (stateBindings := stateBindings)
    (validity := origin.validity) (extend := origin.extend) (solved := origin.solved)
    (faithful := faithful) (observations := observations) (budget := budget) (meaningMost := expressions) origin.diagnosticPolicy origin.body.unique)
  }

include extension faithful observations functionTypes producer acquire stateTransport in
/-- Compatibility kits delegate the original finite producers. -/
theorem ReflectingKits.trivial
    (expressions : ∀ context, origin.validity context → RecursiveNamedBoundedContracts.Below budget (fun child =>
      ProtectedStateTransition.ReflectsAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context origin.function.evidence origin.function.source (origin.certificates context) faults child)) :
    ReflectingKits protocol (Readiness.trivial protocol) stateBindings program origin functions conditionGate
      (Inputs.trivial protocol stateBindings program origin) budget := by
  have assignments := RecursiveNamedImperativeFor.Stateful.WithReady.assignment_reflection_uniform
    (administrative := origin.administrative) (functions := functions) (extension := extension) (program := program) (evidence := origin.function.evidence)
    (protocol := protocol) (stateTransport := stateTransport) (validity := origin.validity)
    (faithful := faithful) (observations := observations) (budget := budget) (reflection := expressions) functionTypes
  exact {
    assignments := (fun context valid => ProtectedForHeader.Stateful.WithReady.assignment_reflection_trivial protocol functions program origin.function.evidence
      origin.function.source (origin.certificates context) context origin.administrative faults budget (assignments context valid))
    headFor := (RecursiveNamedImperativeFor.Stateful.WithReady.reflecting_heads_trivial
    (administrative := origin.administrative) (functions := functions) (definitions := origin.definitions) (registered := origin.registered)
    (extension := extension) (program := program) (evidence := origin.function.evidence)
    (protocol := protocol) (producer := producer) (conditionGate := conditionGate) (acquire := acquire)
    (stateTransport := stateTransport) (stateBindings := stateBindings)
    (validity := origin.validity) (extend := origin.extend) (solved := origin.solved)
    (faithful := faithful) (observations := observations) (budget := budget) (runtimeOf := fun _ valid => origin.runtimeOf valid) (reflection := expressions)
    origin.diagnosticPolicy functionTypes origin.body.unique)
    loopFor := (RecursiveNamedImperativeFor.Stateful.WithReady.reflecting_loops_trivial
    (administrative := origin.administrative) (functions := functions) (definitions := origin.definitions) (registered := origin.registered)
    (extension := extension) (program := program) (evidence := origin.function.evidence)
    (protocol := protocol) (producer := producer) (conditionGate := conditionGate) (acquire := acquire)
    (stateTransport := stateTransport) (stateBindings := stateBindings)
    (validity := origin.validity) (extend := origin.extend) (solved := origin.solved)
    (faithful := faithful) (observations := observations) (budget := budget) (reflection := expressions) origin.diagnosticPolicy functionTypes origin.body.unique)
  }

end Compatibility

section ExpressionCompatibility
variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  {context : SourceSemantics.Context} {source : TypedSource} {evidence : Dynamic.EvidenceEnvironment}
  {expressionFaults : FunctionCalls.FaultRep}
  (model : GenericHeap.PayloadModel catalog projects definitions)
  (certificate : GenericExpressionMeaning.Certificate)

/-- Forget only the trivial input and output facets at the same actual post. -/
theorem expression_preserves_forget_true {size : Nat}
    (meaning : ExpressionPreservesAt protocol (Readiness.trivial protocol) program evidence model (fun _ _ _ => True)
      certificate (source := source) (context := context) (faults := expressionFaults) size) :
    ProtectedStateTransition.PreservesAt protocol model program context evidence source certificate expressionFaults size := by
  intro scope id lowered certified node found mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped initial trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, reached, related, _post⟩ :=
    meaning certified found trivial environments heaps locals agrees actualTyped initial trivial trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, reached, related⟩

/-- The reflected Source grade and actual post are retained verbatim. -/
theorem expression_reflects_forget_true {size : Nat}
    (meaning : ExpressionReflectsAt protocol (Readiness.trivial protocol) program evidence model (fun _ _ _ => True)
      certificate (source := source) (context := context) (faults := expressionFaults) size) :
    ProtectedStateTransition.ReflectsAt protocol model program context evidence source certificate expressionFaults size := by
  intro scope id lowered certified node found mapping world administrativeContext environment canonical actual actualContext before store finalStore ξ value environments heaps locals agrees actualTyped initial evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, reached, related, _post⟩ :=
    meaning certified found trivial environments heaps locals agrees actualTyped initial trivial evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, reached, related⟩
end ExpressionCompatibility

end Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyReadyInputs
