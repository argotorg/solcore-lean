import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageNamedInvocationLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftConstructors
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalDirectBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedArgumentTraceBounds

/-! A direct declaration call lifts its exact ordered arguments and retained
named invocation. The physical caller frame supplies the original capture. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageDirectLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof DataPatternValues
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Receipt)
open CallableIndexedOwnedPreparedStagedDirectCallAuthority (Port EvidenceAt)
open SelectedCompilationStageLiftBounds (LiftsAt)
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
open SelectedCompilationStageBodyLiftBounds (NamedLiftsBelow)
open Staging.Recursive.Lifting (ExpressionLift Adapted embed)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : Receipt policy body fuel compilation (.initial compiled.compatible.checked)
    invocation.source scope id callee ids instantiation reasonAt lowered)
  (port : Port receipt headers)
  (evidenceAt : EvidenceAt receipt port context invocation.evidence)
  (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => CallableIndexedOwnedExpressionHeads.Globals (headers := headers)
      owner compilation.administrativePrefix index.scope index.canonical) callerProtocol)
  (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  (physical : ∀ {index}, callerProtocol.State index →
    CallableIndexedOwnedPhysicalGlobals.Authority compiled index.mapping index.store)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  (faults : RecursiveStageMeaning.FaultRep)
  (idsUnique : RequirementIdsUnique context)
  (unique : NodeOccurrencesUnique invocation.source)
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  (certified : SelectedCompilationNamedSourceTyping.Certified port.header)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)

local notation "bridge" => callerBridge.forgetSlots
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions


variable {stages : Staging.Recursive.Registry}

include owner receipt port evidenceAt callerBridge keyPhysical physical functions faults idsUnique unique owners certified runtime in
theorem direct {children : GenericExpressionMeaning.Certificate}
    {child : Staging.Recursive.Scope} (selected : stages.Closure port.header.function child)
    (size : Nat)
    (sequence : DataExpressionSequence.Tree invocation.source children scope ids
      (port.header.bindings.map (fun binding => binding.1.scheme.body)) receipt.codes)
    (childLift : ∀ childSize, childSize < size → LiftsAt bridge context model stages invocation children childSize)
    (preservation : ∀ childSize, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model stages invocation children faults childSize)
    (bodyLift : NamedLiftsBelow (headers := headers) (keys := keys) port.header model stages child size) :
    LiftsAt bridge context model stages invocation (Point scope id lowered) size := by
  intro current expression code point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals layout actualTyped initial admitted execution
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans receipt.metadata.found)
  obtain ⟨sourceTypes, calleeValid, _application, typing⟩ :=
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.source_types unique receipt.metadata.found
      receipt.form receipt.metadata.coercions typed
  cases SelectedCompilationStageLiftConstructors.tree_types sequence unique typing
  obtain ⟨name, calleeOccurrence, valid⟩ :=
    CallableIndexedOwnedPreparedStagedDirectArgumentRows.callee_receipt receipt runtime calleeValid
  obtain ⟨calleeNode, calleeContains, calleeForm, calleeRequirements, calleeCoercions⟩ := calleeOccurrence
  have calleeFound := lookupExpression?_complete unique calleeContains
  have calleeOccurrence : Staging.Recursive.Occurrence invocation callee (.reference name (.declaration instantiation)) :=
    ⟨calleeNode, calleeContains, calleeForm, calleeRequirements, calleeCoercions⟩
  have occurrence : Staging.Recursive.Occurrence invocation expression
      (.call callee ids (.declaration instantiation)) receipt.node.requirements :=
    ⟨receipt.node, lookupExpression?_sound receipt.metadata.found, receipt.form, rfl, receipt.metadata.coercions⟩
  cases RecursiveNamedArgumentTraceBounds.source_inv_with_evidence receipt.metadata.found receipt.metadata.coercions
    receipt.form calleeFound evidenceAt.produces idsUnique unique execution with
  | argumentFault failed smaller =>
    obtain ⟨staged, reached, trace, adapted⟩ := SelectedCompilationStageLiftSequence.fault bridge
      size sequence unique typing childLift preservation environments heaps locals layout actualTyped
      initial admitted failed (Nat.le_of_lt smaller)
    cases adapted with
    | completed => exact ⟨_, _, .directArgumentsFault occurrence calleeOccurrence trace, .completed⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, .directArgumentsFault occurrence calleeOccurrence trace, .rejected origin call reason _⟩
  | apply evaluated called argumentsSmaller callSmaller =>
    obtain ⟨staged, reached, trace, adapted⟩ := SelectedCompilationStageLiftSequence.values bridge
      size sequence unique typing childLift preservation environments heaps locals layout actualTyped
      initial admitted evaluated (Nat.le_of_lt argumentsSmaller)
    cases adapted with
    | rejected origin call reason reached =>
      exact ⟨_, _, .directArgumentsFault occurrence calleeOccurrence trace, .rejected origin call reason _⟩
    | completed =>
      obtain ⟨stageSize, sized⟩ := Staging.Recursive.Size.Expressions.of_trace trace
      obtain ⟨values, middleStore, middleMap, middleWorld, _argumentsEvaluated, represented, middleHeaps,
          _argumentMaps, _argumentWorlds, _argumentFrame, _argumentMetadata, reached, _related, post⟩ :=
        SelectedCompilationExpressionSequence.preserves_values bridge stageSize sequence unique typing
          (fun size _ => preservation size) environments heaps locals layout actualTyped initial admitted sized (Nat.le_refl _)
      obtain ⟨parameters, headerHeap, headerArguments, _supports⟩ :=
        SelectedCompilationDirectArgumentRows.at_successful_arguments receipt port
          certified runtime post.at_values.heap post.values_typed represented
      have sourceEq := CallableIndexedOwnedPreparedStagedDirectArgumentRows.global_eq receipt port evidenceAt evidenceAt.produces
      rw [sourceEq] at called
      obtain ⟨capture⟩ := CallableIndexedOwnedNamedPhysicalCaptures.of_headerAt
        port.prepared port.aligned port.member keyPhysical (physical reached) middleHeaps.runtime_hasTypes
      obtain ⟨staged, finalHeap, applied, adapted⟩ :=
        SelectedCompilationStageNamedInvocationLifting.lifts_invocation functions owner (callerBridge.pool reached)
          port.header capture port.sourceAt port.aligned.layouts (physical reached) port.member owners certified
          post.at_values.rows headerHeap headerArguments parameters middleHeaps selected size bodyLift called (Nat.le_of_lt callSmaller)
      rw [← sourceEq] at applied
      exact ⟨staged, finalHeap, .directApplied occurrence calleeOccurrence valid trace evidenceAt.produces applied, adapted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageDirectLifting
