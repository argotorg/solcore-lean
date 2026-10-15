import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedPhysicalLambdaFormationBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalCellOrigins
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalLambdaFormationBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedReturnLambdaFormation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedTerminalBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch

/-! A named terminal lambda forms its actual captured value in the physical
positive model. The original parameter packet supplies the full caller seed;
all physical references come from the real entered state. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalNamedFormationSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedContextualLambdaFormationReceipts (OrdinaryFormation)
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedAdmittedStagedExpressionBounds

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {receiving bodyRegistry : SourceCoreRawMetadata.Registry}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {faults : RecursiveStageMeaning.FaultRep}
local notation "functions" => CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

structure Support (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (terminal : Terminal header) where
  point : terminal.certificate = Point
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    terminal.expression terminal.receipt.child
  formations : ∀ child, stages.Closure header.function child →
    Nonempty (Sum
      (OrdinaryFormation (registry := bodyRegistry) (faults := semanticFaults)
        header header.context child.evidence
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
        terminal.expression terminal.receipt.child)
      (PreparedBranchingLambdaFormation.Formation
        header header.context child.evidence
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
        terminal.expression terminal.receipt.child))

variable {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {terminal : Terminal header}
  (static : Support (bodyRegistry := bodyRegistry) (stages := stages) (semanticFaults := semanticFaults) header terminal)
  {child : Staging.Recursive.Scope} (selected : stages.Closure header.function child)
  (certified : SelectedCompilationNamedSourceTyping.Certified header)
  (globals : header.globals = compiled.indexed.base.globals.length)

local notation "nestedBridge" owner => CallableIndexedOwnedPhysicalNestedCanonicalState.bridge (headers := headers) owner header

include profile static selected certified globals in
theorem preserves {budget : Nat} :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow
      (headers := headers) (keys := keys) header model stages child faults budget := by
  intro mapping world administrative actualContext environment canonical actual before store ξ
    environments heaps locals agrees typed initial admitted owner packet keyPhysical physical slots
    size finalContext bodyOutcome outcome after trace matched within
  let entered : (CallableIndexedOwnedPhysicalNestedCanonicalState.protocol (headers := headers) owner header).State
      ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
        mapping, world, before, store, canonical⟩ := ⟨⟨⟨initial, packet keyPhysical.prefixZero globals⟩, slots⟩, physical⟩
  have enteredAdmission : Admission (nestedBridge owner) header.context entered := ⟨admitted.heap, admitted.rows⟩
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) header.context child.source := by
    rw [stages.source selected]
    exact certified.runtime.transport (RecursiveNamedInitialContextValidity.mono_fields header.extended)
  have covers : child.evidence.Covers header.context := by
    rw [stages.evidence selected]
    exact RecursiveNamedInitialContextValidity.covers header.frame header.extended
  have childMeaning : PreservesBelow (nestedBridge owner) header.context model stages child
      terminal.certificate faults budget := by
    intro childSize _smaller current id lowered point
    rw [static.point] at point
    obtain ⟨rfl, rfl, rfl⟩ := point
    obtain ⟨formation⟩ := static.formations child selected
    cases formation with
    | inl formation =>
      exact SelectedCompilationPhysicalLambdaFormationBounds.preserves
        header owner header.context child profile globals
        (RecursiveNamedLambdaFormationHeads.cached_capture_slots compiled headers) keyPhysical.prefixZero
        (by rw [stages.source selected]; exact header.agreement.source)
        (by rw [stages.source selected]; exact header.unique)
        runtime covers faults childSize ⟨formation⟩
    | inr formation =>
      exact SelectedCompilationPreparedPhysicalLambdaFormationBounds.preserves
        header owner header.context child profile globals
        (RecursiveNamedLambdaFormationHeads.cached_capture_slots compiled headers) keyPhysical.prefixZero
        (by rw [stages.source selected]; exact header.agreement.source)
        (by rw [stages.source selected]; exact header.unique)
        runtime covers faults childSize ⟨formation⟩
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, finalHeaps,
    maps, worlds, frame, metadata, reached, related, post⟩ :=
    SelectedCompilationNamedTerminalBounds.preserves_body
      (nestedBridge owner) selected certified terminal.receipt terminal.certifies
      environments heaps locals agrees typed entered enteredAdmission budget childMeaning trace matched within
  refine ⟨value, finalStore, finalMap, finalWorld, evaluated, result, finalHeaps,
    maps, worlds, frame, metadata, reached.base.val.val, related, ?_⟩
  cases outcome with
  | value => exact ⟨post.rows, post.successful⟩
  | fault failure =>
    cases failure with
    | semantic => exact ⟨post.rows, post.successful⟩
    | stage => exact post

include profile static selected certified globals in
theorem reflects {budget : Nat} :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow
      (headers := headers) (keys := keys) header model stages child faults budget := by
  intro mapping world administrative actualContext environment canonical actual before store ξ
    environments heaps locals agrees typed initial admitted owner packet keyPhysical physical slots
    size value finalStore completed within
  let entered : (CallableIndexedOwnedPhysicalNestedCanonicalState.protocol (headers := headers) owner header).State
      ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
        mapping, world, before, store, canonical⟩ := ⟨⟨⟨initial, packet keyPhysical.prefixZero globals⟩, slots⟩, physical⟩
  have enteredAdmission : Admission (nestedBridge owner) header.context entered := ⟨admitted.heap, admitted.rows⟩
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) header.context child.source := by
    rw [stages.source selected]
    exact certified.runtime.transport (RecursiveNamedInitialContextValidity.mono_fields header.extended)
  have covers : child.evidence.Covers header.context := by
    rw [stages.evidence selected]
    exact RecursiveNamedInitialContextValidity.covers header.frame header.extended
  have childMeaning : ReflectsBelow (nestedBridge owner) header.context model stages child
      terminal.certificate faults budget := by
    intro childSize _smaller current id lowered point
    rw [static.point] at point
    obtain ⟨rfl, rfl, rfl⟩ := point
    obtain ⟨formation⟩ := static.formations child selected
    cases formation with
    | inl formation =>
      exact SelectedCompilationPhysicalLambdaFormationBounds.reflects
        header owner header.context child profile globals
        (RecursiveNamedLambdaFormationHeads.cached_capture_slots compiled headers) keyPhysical.prefixZero
        (by rw [stages.source selected]; exact header.agreement.source)
        runtime covers faults childSize ⟨formation⟩
    | inr formation =>
      exact SelectedCompilationPreparedPhysicalLambdaFormationBounds.reflects
        header owner header.context child profile globals
        (RecursiveNamedLambdaFormationHeads.cached_capture_slots compiled headers) keyPhysical.prefixZero
        (by rw [stages.source selected]; exact header.agreement.source)
        runtime covers faults childSize ⟨formation⟩
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, matched, result, finalHeaps,
    maps, worlds, frame, metadata, reached, related, post⟩ :=
    SelectedCompilationNamedTerminalBounds.reflects_body
      (nestedBridge owner) selected certified terminal.receipt terminal.certifies
      environments heaps locals agrees typed entered enteredAdmission budget childMeaning completed within
  refine ⟨sourceSize, header.context, _, outcome, after, finalMap, finalWorld, trace, matched,
    result, finalHeaps, maps, worlds, frame, metadata, reached.base.val.val, related, ?_⟩
  cases outcome with
  | value => exact ⟨post.rows, post.successful⟩
  | fault failure =>
    cases failure with
    | semantic => exact ⟨post.rows, post.successful⟩
    | stage => exact post

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalNamedFormationSupport
