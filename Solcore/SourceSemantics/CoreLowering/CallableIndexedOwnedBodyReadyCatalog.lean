import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodySourceOrigin
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedCatalogProducers
import Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyReadyInputs

/-! Genuine body Source receipts choose the finite readiness catalog at the
same compiler origin. Every site follows original Source typing and syntax;
expression and callee obligations remain strict child interfaces. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyReadyCatalog
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open CallableRuntimeBodyOrigins CallableIndexedOwnedBodySourceOrigin
open ProtectedStateTransition ProtectedStateImperativeCatalogReady
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {callerProtocol : Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (origin : StaticOrigin (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) registry faults)
  (runtime : Dynamic.SourceRuntimeValid program origin.context origin.function.source)

/-- Each assignment fact comes from the independently typed Source parent. -/
theorem assignment_sites : AssignmentSites
    (ProtectedStateImperativeTypedSourceSites.HeadFacts origin.function.source origin.expressionSyntax)
    (SourceAssignmentHasType origin.function.source)
    (SourceBitNotAssignmentValid origin.function.source) origin.function.source where
  assignment := by
    intro context id expected node resolution operator rhs facts found form
    obtain ⟨mode, rest, _syntax, typing⟩ := facts
    exact ProtectedStateImperativeTypedSourceSites.assignment origin.body.unique
      (ProtectedStateImperativeTypedSourceSites.head typing) found form
  snapshot := by
    intro context id expected node resolution facts found form
    obtain ⟨mode, rest, _syntax, typing⟩ := facts
    exact ProtectedStateImperativeTypedSourceSites.bit_not origin.body.unique
      (ProtectedStateImperativeTypedSourceSites.head typing) found form

variable (bindings : Bindings callerProtocol) (wellFormed : ProgramWellFormed program)

/-- Genuine Source site judgments and actual admission define this origin's
readiness inputs. There is no arbitrary-state Source typing transport. -/
def inputs : CallableRuntimeBodyReadyInputs.Inputs callerProtocol (readiness bridge) bindings
    program (source_origin origin runtime) where
  facts := ProtectedStateImperativeTypedSourceSites.Facts origin.function.source origin.expressionSyntax
  headFacts := ProtectedStateImperativeTypedSourceSites.HeadFacts origin.function.source origin.expressionSyntax
  exprFacts := ProtectedStateLexicalSourceSites.ExpressionFacts origin.function.source
  loopFacts := CallableIndexedOwnedAdmittedForBounds.LoopFacts origin.function.source origin.expressionSyntax
  initializerFacts := ProtectedStateImperativeInitializerSourceSites.Facts origin.function.source origin.expressionSyntax
  assignmentFacts := SourceAssignmentHasType origin.function.source
  snapshotFacts := SourceBitNotAssignmentValid origin.function.source
  sites := ProtectedStateImperativeTypedSourceSites.sites program origin.function.evidence runtime.graph
  initializerSites := ProtectedStateImperativeInitializerSourceSites.sites
  assignmentSites := assignment_sites origin
  transfers := CallableIndexedOwnedAdmittedLexicalReadiness.allocation_transfers bridge bindings origin.function.source
  snapshots := CallableIndexedOwnedAdmittedForHeaderReadiness.snapshot_transfers bridge origin.function.evidence wellFormed
    (source_origin origin runtime).validity (fun _ valid => valid.2)
    (fun _ valid => (origin.runtimeOf valid.1).covers)

variable (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (guard : Location → NativeFrame → Prop)
  (producer : MarkedAllocation.Producer callerProtocol origin.layouts origin.frameLayout
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
  (acquire : ∀ location native, guard location native → OrdinaryAllocation.ReadyAt producer.toOrdinary location native)
  (transport : AdministrativeTransport callerProtocol) (budget : Nat)

include extension faithful observations producer acquire transport in
/-- Strict admitted expression children construct only the finite Source
prefixes and recipe producers used by the existing shared body fold. -/
theorem preserving_kits
    (expressions : ∀ context, (source_origin origin runtime).validity context →
      RecursiveNamedHeaderContracts.AtMost budget (fun size =>
        CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          context origin.function.evidence origin.function.source (origin.certificates context) faults size)) :
    CallableRuntimeBodyReadyInputs.PreservingKits callerProtocol (readiness bridge) bindings program
      (source_origin origin runtime) functions guard (inputs bridge origin runtime bindings wellFormed) budget := by
  have below : ∀ context, (source_origin origin runtime).validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size =>
        CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          context origin.function.evidence origin.function.source (origin.certificates context) faults size) :=
    fun context valid size bounded => expressions context valid size (Nat.le_of_lt bounded)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro context valid scope assignment operator rhs
    exact CallableIndexedOwnedAdmittedForHeaderReadiness.assignment_prefix
      (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (registry := registry) (certificate := origin.certificates context) (administrative := origin.administrative) (faults := faults) bridge functions extension origin.function.evidence
      transport faithful observations origin.body.unique wellFormed valid.2 (origin.runtimeOf valid.1).covers budget (below context valid)
  · intro context valid scope assignment operator rhs
    exact CallableIndexedOwnedAdmittedForHeaderReadiness.assignment_fault
      (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (registry := registry) (certificate := origin.certificates context) (administrative := origin.administrative) (faults := faults) bridge functions extension origin.function.evidence
      transport faithful observations origin.body.unique wellFormed valid.2 (origin.runtimeOf valid.1).covers budget (below context valid)
  · exact CallableIndexedOwnedAdmittedCatalogProducers.preserving_heads
      (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (source := origin.function.source) (expressionSyntax := origin.expressionSyntax)
      (certificates := origin.certificates) (administrative := origin.administrative)
      (layouts := origin.layouts) (owner := origin.owner) (active := origin.active)
      (frame := origin.frameLayout) (globals := origin.globals) (onError := origin.onError)
      (registry := registry) (faults := faults) (solved := origin.solved) bridge functions origin.definitions origin.registered extension
      origin.function.evidence faithful observations guard producer acquire transport bindings origin.body.unique wellFormed
      (source_origin origin runtime).validity (fun _ valid => valid.2) (fun _ valid => (origin.runtimeOf valid.1).covers)
      (source_origin origin runtime).extend budget origin.diagnosticPolicy
      (fun _ valid => (source_origin origin runtime).runtimeOf valid) below
  · exact CallableIndexedOwnedAdmittedCatalogProducers.preserving_loops
      (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (source := origin.function.source) (expressionSyntax := origin.expressionSyntax)
      (certificates := origin.certificates) (administrative := origin.administrative)
      (layouts := origin.layouts) (owner := origin.owner) (active := origin.active)
      (frame := origin.frameLayout) (globals := origin.globals) (onError := origin.onError)
      (registry := registry) (faults := faults) bridge functions origin.definitions origin.registered extension
      origin.function.evidence faithful observations guard producer acquire transport bindings origin.body.unique wellFormed
      (source_origin origin runtime).validity (fun _ valid => valid.2) (fun _ valid => (origin.runtimeOf valid.1).covers)
      (source_origin origin runtime).extend budget origin.diagnosticPolicy below

include extension faithful observations producer acquire transport in
/-- Native children retain their own strict budget. The same actual recipe
producers return independent Source grades and the original reached states. -/
theorem reflecting_kits (functionTypes : FunctionRuntimeViews functions)
    (expressions : ∀ context, (source_origin origin runtime).validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size =>
        CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          context origin.function.evidence origin.function.source (origin.certificates context) faults size)) :
    CallableRuntimeBodyReadyInputs.ReflectingKits callerProtocol (readiness bridge) bindings program
      (source_origin origin runtime) functions guard (inputs bridge origin runtime bindings wellFormed) budget := by
  refine ⟨?_, ?_, ?_⟩
  · intro context valid scope assignment operator rhs
    exact CallableIndexedOwnedAdmittedForHeaderReadiness.assignment_reflection
      (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (registry := registry) (certificate := origin.certificates context) (administrative := origin.administrative) (faults := faults) bridge functions extension origin.function.evidence
      transport faithful observations origin.body.unique wellFormed valid.2 (origin.runtimeOf valid.1).covers budget functionTypes (expressions context valid)
  · exact CallableIndexedOwnedAdmittedCatalogProducers.reflecting_heads
      (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (source := origin.function.source) (expressionSyntax := origin.expressionSyntax)
      (certificates := origin.certificates) (administrative := origin.administrative)
      (layouts := origin.layouts) (owner := origin.owner) (active := origin.active)
      (frame := origin.frameLayout) (globals := origin.globals) (onError := origin.onError)
      (registry := registry) (faults := faults) (solved := origin.solved) bridge functions origin.definitions origin.registered extension
      origin.function.evidence faithful observations guard producer acquire transport bindings origin.body.unique wellFormed
      (source_origin origin runtime).validity (fun _ valid => valid.2) (fun _ valid => (origin.runtimeOf valid.1).covers)
      (source_origin origin runtime).extend budget origin.diagnosticPolicy
      (fun _ valid => (source_origin origin runtime).runtimeOf valid) functionTypes expressions
  · exact CallableIndexedOwnedAdmittedCatalogProducers.reflecting_loops
      (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (source := origin.function.source) (expressionSyntax := origin.expressionSyntax)
      (certificates := origin.certificates) (administrative := origin.administrative)
      (layouts := origin.layouts) (owner := origin.owner) (active := origin.active)
      (frame := origin.frameLayout) (globals := origin.globals) (onError := origin.onError)
      (registry := registry) (faults := faults) bridge functions origin.definitions origin.registered extension
      origin.function.evidence faithful observations guard producer acquire transport bindings origin.body.unique wellFormed
      (source_origin origin runtime).validity (fun _ valid => valid.2) (fun _ valid => (origin.runtimeOf valid.1).covers)
      (source_origin origin runtime).extend budget origin.diagnosticPolicy functionTypes expressions

/-- Convert the genuine admission record beside the same actual child post. -/
theorem preserving_expressions
    (expressions : ∀ context, (source_origin origin runtime).validity context →
      RecursiveNamedHeaderContracts.AtMost budget (fun size =>
        CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          context origin.function.evidence origin.function.source (origin.certificates context) faults size)) :
    ∀ context, (source_origin origin runtime).validity context →
      RecursiveNamedHeaderContracts.AtMost budget (fun size =>
        RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionPreservesAt callerProtocol (readiness bridge)
          program origin.function.evidence (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          (inputs bridge origin runtime bindings wellFormed).exprFacts (origin.certificates context)
          (source := origin.function.source) (context := context) (faults := faults) size) :=
  fun context valid size bounded => CallableIndexedOwnedAdmittedLexicalReadiness.preserves_at bridge _
    (expressions context valid size bounded)

/-- The native converter retains its actual witness and independent Source
trace, including successful raw value typing at that same post. -/
theorem reflecting_expressions
    (expressions : ∀ context, (source_origin origin runtime).validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size =>
        CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          context origin.function.evidence origin.function.source (origin.certificates context) faults size)) :
    ∀ context, (source_origin origin runtime).validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size =>
        RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionReflectsAt callerProtocol (readiness bridge)
          program origin.function.evidence (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          (inputs bridge origin runtime bindings wellFormed).exprFacts (origin.certificates context)
          (source := origin.function.source) (context := context) (faults := faults) size) :=
  fun context valid size bounded => CallableIndexedOwnedAdmittedLexicalReadiness.reflects_at bridge _
    (expressions context valid size bounded)

/-- This concrete readiness already contains genuine raw value and heap
facts on success, and only authentic reached-row histories on fault. -/
theorem admitted_post {context : SourceSemantics.Context} {type : TypeSystem.Ty}
    {outcome : Dynamic.ExpressionOutcome} {index : Index} {state : callerProtocol.State index}
    (post : RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionPost callerProtocol (readiness bridge)
      context type outcome state) :
    CallableIndexedOwnedSourceAdmission.PostAdmission bridge context type outcome state := by
  cases outcome with
  | fault _ =>
    refine ⟨post, ?_⟩
    intro value same
    cases same
  | value _ =>
    refine ⟨post.1.rows, ?_⟩
    intro value same
    cases same
    exact ⟨post.2, post.1.heap⟩

/-- The reverse child adapter returns the identical real post and relation. -/
theorem admitted_child_preserves {context : SourceSemantics.Context} {size : Nat}
    (meaning : RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionPreservesAt callerProtocol (readiness bridge)
      program origin.function.evidence (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      (inputs bridge origin runtime bindings wellFormed).exprFacts (origin.certificates context)
      (source := origin.function.source) (context := context) (faults := faults) size) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context origin.function.evidence origin.function.source (origin.certificates context) faults size := by
  intro scope id lowered certified node found sourceTyped mapping world administrativeContext environment canonical actual
    actualContext before store ξ outcome after environments heaps locals agrees typed initial admitted trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds,
      frame, metadata, reached, related, post⟩ :=
    meaning certified found sourceTyped environments heaps locals agrees typed initial admitted trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds,
    frame, metadata, reached, related, admitted_post bridge post⟩

/-- Native reflection retains its original completion and independent Source
trace while translating only the actual post's proof facets. -/
theorem admitted_child_reflects {context : SourceSemantics.Context} {size : Nat}
    (meaning : RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionReflectsAt callerProtocol (readiness bridge)
      program origin.function.evidence (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      (inputs bridge origin runtime bindings wellFormed).exprFacts (origin.certificates context)
      (source := origin.function.source) (context := context) (faults := faults) size) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context origin.function.evidence origin.function.source (origin.certificates context) faults size := by
  intro scope id lowered certified node found sourceTyped mapping world administrativeContext environment canonical actual
    actualContext before store ξ value finalStore environments heaps locals agrees typed initial admitted evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
      frame, metadata, reached, related, post⟩ :=
    meaning certified found sourceTyped environments heaps locals agrees typed initial admitted evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
    frame, metadata, reached, related, admitted_post bridge post⟩

include extension faithful observations producer acquire transport in
/-- The shared Ready family supplies these exact smaller expression results;
the finite catalog producers are constructed internally from them. -/
theorem preserving_ready_kits
    (expressions : ∀ context, (source_origin origin runtime).validity context →
      RecursiveNamedHeaderContracts.AtMost budget (fun size =>
        RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionPreservesAt callerProtocol (readiness bridge)
          program origin.function.evidence (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          (inputs bridge origin runtime bindings wellFormed).exprFacts (origin.certificates context)
          (source := origin.function.source) (context := context) (faults := faults) size)) :
    CallableRuntimeBodyReadyInputs.PreservingKits callerProtocol (readiness bridge) bindings program
      (source_origin origin runtime) functions guard (inputs bridge origin runtime bindings wellFormed) budget :=
  preserving_kits bridge origin runtime bindings wellFormed functions extension faithful observations guard producer acquire transport budget
    (fun context valid size bounded => admitted_child_preserves bridge origin runtime bindings wellFormed functions
      (expressions context valid size bounded))

include extension faithful observations producer acquire transport in
/-- The native family uses the same real child witness at its strict budget. -/
theorem reflecting_ready_kits (functionTypes : FunctionRuntimeViews functions)
    (expressions : ∀ context, (source_origin origin runtime).validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size =>
        RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionReflectsAt callerProtocol (readiness bridge)
          program origin.function.evidence (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          (inputs bridge origin runtime bindings wellFormed).exprFacts (origin.certificates context)
          (source := origin.function.source) (context := context) (faults := faults) size)) :
    CallableRuntimeBodyReadyInputs.ReflectingKits callerProtocol (readiness bridge) bindings program
      (source_origin origin runtime) functions guard (inputs bridge origin runtime bindings wellFormed) budget :=
  reflecting_kits bridge origin runtime bindings wellFormed functions extension faithful observations guard producer acquire transport budget functionTypes
    (fun context valid size bounded => admitted_child_reflects bridge origin runtime bindings wellFormed functions
      (expressions context valid size bounded))

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyReadyCatalog
