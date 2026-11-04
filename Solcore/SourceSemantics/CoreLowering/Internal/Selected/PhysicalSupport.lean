import Solcore.SourceSemantics.CoreLowering.Internal.Selected.MethodRoots
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.NamedAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.PreparedMethodRoots
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalCellOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.PhysicalClosures
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedReturnLambdaFormation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.NamedScopedRoots
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.PhysicalCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.AcceptedFactories
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.MethodBodies
import Solcore.SourceSemantics.CoreLowering.PreparedAssignmentDiagnosticAuthorityReception
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.DirectCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.ExpressionBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBootstrapRootState
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedPhysicalCaptures
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.CatalogOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBuiltinArgumentRows

/-!
# Selected compilations: physical support

Static support of named bodies on the physical protocol, the mixed caller family, coercion method bounds, the physical bootstrap and builtin origins.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalMixedNamedTerminalSupport
/-! Ordinary terminal bodies use the same physical root family as method bodies.
The actual parameter packet supplies the pool, complete cache and slot layout;
strict expression children establish both body directions. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalMixedNamedTerminalSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key)
open SelectedCompilationMixedRootSupport (RootAt)
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedAdmittedStagedExpressionBounds

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {faults : RecursiveStageMeaning.FaultRep}

structure Support (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (terminal : Terminal header) where
  point : terminal.certificate = Point
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    terminal.expression terminal.receipt.child
  roots : ∀ child, stages.Closure header.function child →
    { root : RootAt compiled headers stages header.context child
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
        terminal.expression terminal.receipt.child semanticFaults //
      root.rawType = header.function.resultType ∧ root.reasonAt = header.reasonAt ∧
      root.compilation.administrativePrefix = 1 }

variable {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {terminal : Terminal header}
  (static : Support (headers := headers) (stages := stages) (semanticFaults := semanticFaults) header terminal)
  {child : Staging.Recursive.Scope} (selected : stages.Closure header.function child)
  (certified : SelectedCompilationNamedSourceTyping.Certified header)

local notation "physicalBridge" =>
  CallableIndexedOwnedNamedCallerProtocol.Carrier.forgetSlots
    (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) 1)

include static selected certified in
theorem preserves {budget : Nat}
    (children : ∀ size, size < budget →
      SelectedCompilationMixedRootBounds.PreservesRootsAt
        (headers := headers) (keys := keys) model stages semanticFaults faults size) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow
      (headers := headers) (keys := keys) header model stages child faults budget := by
  intro mapping world administrative actualContext environment canonical actual before store ξ
    environments heaps locals agrees typed initial admitted owner _packet keyPhysical physical slots
    size finalContext bodyOutcome outcome after trace matched within
  let entered : (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1).State
      ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
        mapping, world, before, store, canonical⟩ := ⟨⟨initial, slots⟩, physical⟩
  have enteredAdmission : Admission physicalBridge header.context entered := ⟨admitted.heap, admitted.rows⟩
  have childMeaning : PreservesBelow physicalBridge header.context model stages child
      terminal.certificate faults budget := by
    intro childSize smaller current id lowered point
    rw [static.point] at point
    let root := (static.roots child selected).val
    have meaning : PreservesAt
        (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys)
          root.compilation.administrativePrefix).forgetSlots
        header.context model stages child
        (Point (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
          terminal.expression terminal.receipt.child) faults childSize :=
      children childSize smaller root owner keyPhysical
    have prefixEq : root.compilation.administrativePrefix = 1 := (static.roots child selected).property.2.2
    rw [prefixEq] at meaning
    intro node
    exact meaning point (node := node)
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, finalHeaps,
    maps, worlds, frame, metadata, reached, related, post⟩ :=
    SelectedCompilationNamedTerminalBounds.preserves_body
      physicalBridge selected certified terminal.receipt terminal.certifies
      environments heaps locals agrees typed entered enteredAdmission budget childMeaning trace matched within
  refine ⟨value, finalStore, finalMap, finalWorld, evaluated, result, finalHeaps,
    maps, worlds, frame, metadata, reached.base.val, related, ?_⟩
  cases outcome with
  | value => exact ⟨post.rows, post.successful⟩
  | fault failure =>
    cases failure with
    | semantic => exact ⟨post.rows, post.successful⟩
    | stage => exact post

include static selected certified in
theorem reflects {budget : Nat}
    (children : ∀ size, size < budget →
      SelectedCompilationMixedRootBounds.ReflectsRootsAt
        (headers := headers) (keys := keys) model stages semanticFaults faults size) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow
      (headers := headers) (keys := keys) header model stages child faults budget := by
  intro mapping world administrative actualContext environment canonical actual before store ξ
    environments heaps locals agrees typed initial admitted owner _packet keyPhysical physical slots
    size value finalStore completed within
  let entered : (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1).State
      ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
        mapping, world, before, store, canonical⟩ := ⟨⟨initial, slots⟩, physical⟩
  have enteredAdmission : Admission physicalBridge header.context entered := ⟨admitted.heap, admitted.rows⟩
  have childMeaning : ReflectsBelow physicalBridge header.context model stages child
      terminal.certificate faults budget := by
    intro childSize smaller current id lowered point
    rw [static.point] at point
    let root := (static.roots child selected).val
    have meaning : ReflectsAt
        (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys)
          root.compilation.administrativePrefix).forgetSlots
        header.context model stages child
        (Point (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
          terminal.expression terminal.receipt.child) faults childSize :=
      children childSize smaller root owner keyPhysical
    have prefixEq : root.compilation.administrativePrefix = 1 := (static.roots child selected).property.2.2
    rw [prefixEq] at meaning
    intro node
    exact meaning point (node := node)
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, matched, result, finalHeaps,
    maps, worlds, frame, metadata, reached, related, post⟩ :=
    SelectedCompilationNamedTerminalBounds.reflects_body
      physicalBridge selected certified terminal.receipt terminal.certifies
      environments heaps locals agrees typed entered enteredAdmission budget childMeaning completed within
  refine ⟨sourceSize, header.context, _, outcome, after, finalMap, finalWorld, trace, matched,
    result, finalHeaps, maps, worlds, frame, metadata, reached.base.val, related, ?_⟩
  cases outcome with
  | value => exact ⟨post.rows, post.successful⟩
  | fault failure =>
    cases failure with
    | semantic => exact ⟨post.rows, post.successful⟩
    | stage => exact post

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalMixedNamedTerminalSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalNamedFormationSupport
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
      (Sum
        (PreparedBranchingLambdaFormation.Formation
          header header.context child.evidence
          (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
          terminal.expression terminal.receipt.child)
        (PreparedLambdaBodyFormation.Formation
          header header.context child.evidence
          (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
          terminal.expression terminal.receipt.child)))

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
      cases formation with
      | inl formation =>
        exact SelectedCompilationPreparedPhysicalLambdaFormationBounds.preserves
          header owner header.context child profile globals
          (RecursiveNamedLambdaFormationHeads.cached_capture_slots compiled headers) keyPhysical.prefixZero
          (by rw [stages.source selected]; exact header.agreement.source)
          (by rw [stages.source selected]; exact header.unique)
          runtime covers faults childSize ⟨formation⟩
      | inr formation =>
        exact SelectedCompilationPreparedBranchingPhysicalLambdaFormationBounds.preserves
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
      cases formation with
      | inl formation =>
        exact SelectedCompilationPreparedPhysicalLambdaFormationBounds.reflects
          header owner header.context child profile globals
          (RecursiveNamedLambdaFormationHeads.cached_capture_slots compiled headers) keyPhysical.prefixZero
          (by rw [stages.source selected]; exact header.agreement.source)
          runtime covers faults childSize ⟨formation⟩
      | inr formation =>
        exact SelectedCompilationPreparedBranchingPhysicalLambdaFormationBounds.reflects
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalNamedBodySupport
/-! Static named body coverage retains the actual prepared body carrier. Its
terminal, formation and scoped alternatives derive the same physical body ports. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalNamedBodySupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body of_terminal)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {stages : Staging.Recursive.Registry}
  {semanticFaults : FunctionCalls.FaultRep}

inductive Support (header : Header compiled (Program.ofChecked compiled.sourceProgram)) : Body header → Type where
  | terminal (terminal : Terminal header)
      (support : SelectedCompilationPhysicalMixedNamedTerminalSupport.Support
        (headers := headers) (stages := stages) (semanticFaults := semanticFaults) header terminal) :
      Support header (of_terminal terminal)
  | formation (terminal : Terminal header)
      (support : SelectedCompilationPhysicalNamedFormationSupport.Support
        (bodyRegistry := bodyRegistry) (stages := stages) (semanticFaults := semanticFaults) header terminal)
      (globals : header.globals = compiled.indexed.base.globals.length) :
      Support header (of_terminal terminal)
  | scoped (body : Body header)
      (receipt : CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.Receipt header)
      (compilation : body.compilation = .canonicalBranching receipt)
      (support : SelectedCompilationNamedScopedSupport.Support
        headers header stages receipt semanticFaults) : Support header body

/-- The previous terminal API embeds without changing any receipt. -/
def of_terminal_support {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (terminal : Terminal header)
    (support : Sum (SelectedCompilationPhysicalMixedNamedTerminalSupport.Support
      (headers := headers) (stages := stages) (semanticFaults := semanticFaults) header terminal)
      { _support : SelectedCompilationPhysicalNamedFormationSupport.Support
          (bodyRegistry := bodyRegistry) (stages := stages) (semanticFaults := semanticFaults)
          header terminal // header.globals = compiled.indexed.base.globals.length }) :
    Support (headers := headers) (bodyRegistry := bodyRegistry) (stages := stages)
      (semanticFaults := semanticFaults) header (of_terminal terminal) :=
  match support with
  | .inl static => .terminal terminal static
  | .inr static => .formation terminal static.val static.property

variable {header : Header compiled (Program.ofChecked compiled.sourceProgram)} {body : Body header}
  (support : Support (headers := headers) (bodyRegistry := bodyRegistry) (stages := stages)
    (semanticFaults := semanticFaults) header body)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (certified : SelectedCompilationNamedSourceTyping.Certified header)
  {receiving : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
  {faults : RecursiveStageMeaning.FaultRep}
  {child : Staging.Recursive.Scope} (selected : stages.Closure header.function child)
local notation "functions" => CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry semanticFaults profile

variable (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)
  (assignmentInterpretation : PreparedAssignmentDiagnosticAuthority.Interprets compiled receiving
    (fun reason token => faults (.semantic reason) token))

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

include support profile certified extension selected semantic assignmentInterpretation in
theorem preserves {budget : Nat}
    (children : ∀ size, size < budget →
      SelectedCompilationMixedRootBounds.PreservesRootsAt
        (headers := headers) (keys := keys) model stages semanticFaults faults size) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow
      (headers := headers) (keys := keys) header model stages child faults budget := by
  cases support with
  | terminal terminal static =>
    exact SelectedCompilationPhysicalMixedNamedTerminalSupport.preserves
      static selected certified children
  | formation terminal static globals =>
    exact SelectedCompilationPhysicalNamedFormationSupport.preserves
      profile static selected certified globals
  | «scoped» body receipt compilation static =>
    exact SelectedCompilationNamedScopedBounds.preserves (semantic := semantic)
      (assignmentInterpretation := assignmentInterpretation)
      static body.aligned.globals functions
      (CallableIndexedLambdaValues.identity_faithful compiled.indexed)
      (CallableIndexedOwnedPreparedPhysicalCellOrigins.observations profile) selected extension body.layouts children

include support profile certified extension selected semantic assignmentInterpretation in
theorem reflects {budget : Nat}
    (children : ∀ size, size < budget →
      SelectedCompilationMixedRootBounds.ReflectsRootsAt
        (headers := headers) (keys := keys) model stages semanticFaults faults size) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow
      (headers := headers) (keys := keys) header model stages child faults budget := by
  cases support with
  | terminal terminal static =>
    exact SelectedCompilationPhysicalMixedNamedTerminalSupport.reflects
      static selected certified children
  | formation terminal static globals =>
    exact SelectedCompilationPhysicalNamedFormationSupport.reflects
      profile static selected certified globals
  | «scoped» body receipt compilation static =>
    exact SelectedCompilationNamedScopedBounds.reflects (semantic := semantic)
      (assignmentInterpretation := assignmentInterpretation)
      static body.aligned.globals functions
      (CallableIndexedOwnedPreparedPhysicalCellOrigins.runtime_views profile)
      (CallableIndexedLambdaValues.identity_faithful compiled.indexed)
      (CallableIndexedOwnedPreparedPhysicalCellOrigins.observations profile) selected extension body.layouts children

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalNamedBodySupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalCoercedDirectRawBounds
/-! Every raw argument and named body comes from the same physical numerical
family. The original call metadata and conversion partition remain unchanged. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalCoercedDirectRawBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open SelectedCompilationMixedRootSupport (CoercedDirectRoot RootAt)
open SelectedCompilationMixedRootBounds
open CallableIndexedOwnedAdmittedStagedExpressionBounds

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
  {expression : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {rawType : TypeSystem.Ty}
  (root : CoercedDirectRoot compiled headers stages policy lowerBody compilation readFuel context invocation
    reasonAt scope expression lowered rawType semanticFaults)
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry} (faults : RecursiveStageMeaning.FaultRep)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions
local notation "callerBridge" => CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller
  owner compilation.administrativePrefix keyPhysical.locations

private theorem tree_types {source : TypedSource} {certificate : GenericExpressionMeaning.Certificate}
    {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {stored : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    (tree : DataExpressionSequence.Tree source certificate scope ids stored codes)
    (unique : NodeOccurrencesUnique source) (typing : ExpressionsHaveTypes source context ids types) : stored = types := by
  induction tree generalizing types with
  | nil => cases typing; rfl
  | single found _generated =>
    cases typing with
    | cons head tail =>
      cases tail
      obtain ⟨actual, contains, sourceType⟩ := head.stored_type
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      exact congrArg (fun type => [type]) sourceType
  | cons found _generated tail ih =>
    cases typing with
    | cons head rest =>
      obtain ⟨actual, contains, sourceType⟩ := head.stored_type
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      rw [sourceType, ih rest]

private theorem argument_types : root.argumentTypes =
    root.port.header.bindings.map (fun binding => binding.1.scheme.body) := by
  obtain ⟨types, _callee, application, typed⟩ :=
    CallableIndexedOwnedPreparedStagedRawDirectArguments.source_types root.actual root.unique root.typed
  have rows := SelectedCompilationRawDirectSourceTypes.source_types
    root.actual root.port.toReady root.shape root.runtime.signatures application
  exact (tree_types root.argumentTree root.unique typed).trans rows.1

include owners in
theorem preserves (budget : Nat)
    (children : ∀ size, size < budget → PreservesRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults faults size)
    (namedBodies : ∀ size, size ≤ budget → ∀ {child : Staging.Recursive.Scope},
      stages.Closure root.port.header.function child →
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow
        (headers := headers) (keys := keys) root.port.header model stages child faults size)
    (size : Nat) (within : size ≤ budget) :
    SelectedCompilationPhysicalRawDirectBounds.RawPreservesAt
      (context := context) (receiving := receiving) owner root.actual callerBridge functions faults stages size := by
  have childMeaning : PreservesBelow (callerBridge).forgetSlots context model
      stages invocation root.argumentCertificate faults size := by
    intro smaller strict current id code member
    obtain ⟨type, ⟨supported⟩⟩ := root.argumentRoots member
    exact children smaller (Nat.lt_of_lt_of_le strict within)
      (RootAt.ofRoot supported) owner keyPhysical ⟨rfl, rfl, rfl⟩
  exact SelectedCompilationPhysicalRawDirectBounds.preserves
    owner root.actual root.port.toPort root.port.evidence callerBridge keyPhysical
    (fun state => state.physical) functions faults root.unique owners root.certified root.shape root.runtime
    size (argument_types root ▸ root.argumentTree) childMeaning
    (fun selected => namedBodies size within selected)

variable (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
  (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
    (.named root.port.header.named.signature.key))

include stagePrepared stageEq descriptor in
theorem reflects (budget : Nat)
    (children : ∀ size, size < budget → ReflectsRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults faults size)
    (namedBodies : ∀ size, size ≤ budget → ∀ {child : Staging.Recursive.Scope},
      stages.Closure root.port.header.function child →
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow
        (headers := headers) (keys := keys) root.port.header model stages child faults size)
    (size : Nat) (within : size ≤ budget) :
    SelectedCompilationPhysicalRawDirectBounds.RawReflectsAt
      (context := context) (receiving := receiving) owner root.actual callerBridge functions faults stages size := by
  subst stages
  have childMeaning : ReflectsBelow (callerBridge).forgetSlots context model
      (RecursiveNamedPreparedStageScopes.registry stagePrepared) invocation root.argumentCertificate faults size := by
    intro smaller strict current id code member
    obtain ⟨type, ⟨supported⟩⟩ := root.argumentRoots member
    exact children smaller (Nat.lt_of_lt_of_le strict within)
      (RootAt.ofRoot supported) owner keyPhysical ⟨rfl, rfl, rfl⟩
  exact SelectedCompilationPhysicalRawDirectBounds.reflects
    owner root.actual root.port.toPort root.port.evidence callerBridge keyPhysical
    (fun state => state.physical) functions faults root.unique root.certified root.shape root.runtime
    stagePrepared descriptor
    size (argument_types root ▸ root.argumentTree) childMeaning
    (fun selected => namedBodies size within selected)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalCoercedDirectRawBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalCoercionMethodBounds
/-! The shared numerical induction supplies every conversion body from the
actual terminal packet, preserving the exact SourceAt and reached caller. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalCoercionMethodBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open SelectedCompilationMixedRootBounds
open SelectedCompilationMixedRootSupport (CoercionMethods)
open CallableIndexedOwnedPreparedStagedCoercionChain (Chain)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {project : SourceCoreEvidence.Projector} {compilation : SourceCoreFunctions.Context}
  {caller : SourceSpecialization.SpecializedFunction}
  {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
  {scope : SourceCoreBasic.Scope} {node : ExpressionNode}
  {policy : SourceCoreFunctions.CallablePolicy}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {stages : Staging.Recursive.Registry}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {semanticFaults : FunctionCalls.FaultRep}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry} (faults : RecursiveStageMeaning.FaultRep)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
  {source target : TypeSystem.Ty} {input output : SourceCoreBasic.LoweredExpr}
  {steps : List CoercionStep} {calls : List CallableCoercionSpine.Call}
  (chain : Chain compiled project compilation caller available scope node policy context invocation stages
    source target input steps output calls)
  (support : CoercionMethods headers semanticFaults chain)


variable (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

include keyPhysical support in
theorem source_bodies (budget : Nat)
    (children : ∀ size, size < budget → PreservesRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults faults size) :
    SelectedCompilationCoercionPathBounds.SourceBodies
      (headers := headers) (receiving := receiving) owner functions faults chain budget := by
  induction chain with
  | nil => trivial
  | cons step port valid tail ih =>
      obtain ⟨⟨packet, sourceAt, certified, static⟩, remaining⟩ := support
      refine ⟨⟨sourceAt ▸ certified, ?_⟩, ih remaining⟩
      intro mapping world heap store callerScope canonical administrative arguments payloads caller installed
        _parameters heapTyped argumentsTyped stable child selected
      have packetArguments : Dynamic.ValuesHaveTypes port.principal.sourceFunction.context heap
          arguments packet.sourceAt.types := by
        simpa only [sourceAt] using argumentsTyped
      simpa only [SelectedCompilationMethodBodies.Packet.sourceAt, sourceAt] using
        SelectedCompilationMethodTerminalBounds.source_continuation
          port.principal packet static certified functions selected installed
          owner keyPhysical caller heapTyped packetArguments stable budget
          (fun size smaller _context _invocation _scope _expression _lowered root owner physical =>
            children size smaller
              (SelectedCompilationMixedRootSupport.RootAt.ofMethod root) owner physical)

include keyPhysical support in
theorem native_bodies (budget : Nat)
    (children : ∀ size, size < budget → ReflectsRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults faults size) :
    SelectedCompilationCoercionPathBounds.NativeBodies
      (headers := headers) (receiving := receiving) owner functions faults chain budget := by
  induction chain with
  | nil => trivial
  | cons step port valid tail ih =>
      obtain ⟨⟨packet, sourceAt, certified, static⟩, remaining⟩ := support
      refine ⟨⟨sourceAt ▸ certified, ?_⟩, ih remaining⟩
      intro mapping world heap store callerScope canonical administrative arguments payloads caller installed
        _parameters heapTyped argumentsTyped stable child selected
      have packetArguments : Dynamic.ValuesHaveTypes port.principal.sourceFunction.context heap
          arguments packet.sourceAt.types := by
        simpa only [sourceAt] using argumentsTyped
      simpa only [SelectedCompilationMethodBodies.Packet.sourceAt, sourceAt] using
        SelectedCompilationMethodTerminalBounds.native_continuation
          port.principal packet static certified functions selected installed
          owner keyPhysical caller heapTyped packetArguments stable budget
          (fun size smaller _context _invocation _scope _expression _lowered root owner physical =>
            children size smaller
              (SelectedCompilationMixedRootSupport.RootAt.ofMethod root) owner physical)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalCoercionMethodBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalMixedCallerFamily
/-! One strong induction closes ordinary calls, selected methods and retained indirect callees
at actual complete physical cache states. Every body continuation comes from
an authentic static packet and a strictly smaller expression proof. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalMixedCallerFamily
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open SelectedCompilationMixedRootBounds
open CallableIndexedOwnedPreparedStagedCallerHeadHandlers
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedOperatorMethodCertificates (Receipt)
open CallableIndexedOwnedPreparedStagedOperatorMethodAuthority (Port)
open SelectedCompilationMethodBodySupport (Packet Support)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry} {semanticFaults : FunctionCalls.FaultRep}

/-- Genuine packets for every selected method, at the exact retained SourceAt.
No execution, allocation or body law is part of this static family. -/
def MethodSupports : Prop :=
  ∀ {policy body fuel compilation source scope id reasonAt lowered context caller}
    (receipt : Receipt policy body fuel compilation (.initial compiled.compatible.checked) source scope id reasonAt lowered)
    (port : Port (compiled := compiled) receipt context caller stages),
    Dynamic.TypedOperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context caller
      port.principal.traitName port.principal.methodName receipt.node.requirements
      port.principal.sourceBody port.principal.dictionary →
    ∃ packet : Packet port.principal, packet.sourceAt = port.sourceAt ∧
      Support port.principal packet headers stages semanticFaults

/-- Method bodies may retain either an actual terminal or scoped compiler packet. -/
def MixedMethodSupports : Prop :=
  ∀ {policy body fuel compilation source scope id reasonAt lowered context caller}
    (receipt : Receipt policy body fuel compilation (.initial compiled.compatible.checked) source scope id reasonAt lowered)
    (port : Port (compiled := compiled) receipt context caller stages),
    Dynamic.TypedOperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context caller
      port.principal.traitName port.principal.methodName receipt.node.requirements
      port.principal.sourceBody port.principal.dictionary →
    ∃ packet : SelectedCompilationMethodBodies.Packet port.principal,
      packet.sourceAt = port.sourceAt ∧
      SelectedCompilationMethodBodies.Support port.principal packet headers stages semanticFaults

/-- Existing terminal method support embeds without changing its static receipts. -/
theorem MethodSupports.toMixed
    (support : MethodSupports (compiled := compiled) (headers := headers)
      (stages := stages) (semanticFaults := semanticFaults)) :
    MixedMethodSupports (compiled := compiled) (headers := headers)
      (stages := stages) (semanticFaults := semanticFaults) := by
  intro policy body fuel compilation source scope id reasonAt lowered context caller receipt port selection
  obtain ⟨packet, sourceAt, supported⟩ := support receipt port selection
  exact ⟨.terminal packet, sourceAt, supported⟩

private theorem tree_types {source : TypedSource} {certificate : GenericExpressionMeaning.Certificate}
    {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {stored : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    (tree : DataExpressionSequence.Tree source certificate scope ids stored codes)
    (unique : NodeOccurrencesUnique source) (typing : ExpressionsHaveTypes source context ids types) : stored = types := by
  induction tree generalizing types with
  | nil => cases typing; rfl
  | single found _generated =>
    cases typing with
    | cons head tail =>
      cases tail
      obtain ⟨actual, contains, sourceType⟩ := head.stored_type
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      exact congrArg (fun type => [type]) sourceType
  | cons found _generated tail ih =>
    cases typing with
    | cons head rest =>
      obtain ⟨actual, contains, sourceType⟩ := head.stored_type
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      rw [sourceType, ih rest]

private theorem named_descriptor (header : Header compiled (Program.ofChecked compiled.sourceProgram)) :
    Nonempty (SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key)) := by
  obtain ⟨origin, index, metadata, found, _history, _emitted⟩ :=
    CallableIndexedFormation.namedBody_history compiled.indexed.ancestry header.hook
  cases h : SourceCoreCallableContracts.descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key) with
  | error _ =>
    unfold SourceCoreCallableContracts.descriptor at h
    split at h
    · rename_i missing
      rw [found] at missing
      contradiction
    · contradiction
  | ok descriptor => exact ⟨descriptor⟩

variable {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  {bodyRegistry : SourceCoreRawMetadata.Registry}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (bodyTyping : SelectedCompilationBodyTyping.Bodies compiled)
  (certificates : ∀ header, header ∈ headers → SelectedCompilationNamedSourceTyping.Certified header)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry completion.result.context.registry)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (terminals : ∀ header, header ∈ headers → Terminal header)
  (namedSupport : ∀ header (member : header ∈ headers),
    Sum (SelectedCompilationPhysicalMixedNamedTerminalSupport.Support (headers := headers)
      (stages := stages) (semanticFaults := semanticFaults) header (terminals header member))
      { _support : SelectedCompilationPhysicalNamedFormationSupport.Support
          (bodyRegistry := bodyRegistry) (stages := stages) (semanticFaults := semanticFaults)
          header (terminals header member) // header.globals = compiled.indexed.base.globals.length })
  (bodies : ∀ header, header ∈ headers → CallableIndexedOwnedPreparedStagedNamedBodies.Body header)
  (bodySupport : ∀ header (member : header ∈ headers),
    SelectedCompilationPhysicalNamedBodySupport.Support
      (headers := headers) (bodyRegistry := bodyRegistry) (stages := stages)
      (semanticFaults := semanticFaults) header (bodies header member))
  (closurePackets : ∀ {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPreparedPhysicalClosureAssociation.Association headers keys bodyRegistry semanticFaults
      mapping world function native bindings parameter result),
    SelectedCompilationPhysicalClosureStaticSupport.PacketFor association stages)
  (closureSupport : ∀ {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPreparedPhysicalClosureAssociation.Association headers keys bodyRegistry semanticFaults
      mapping world function native bindings parameter result),
    SelectedCompilationPhysicalClosureStaticSupport.SupportFor association stages (closurePackets association))
  (owners : ∀ owner : OwnedKey keys, CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  (methodSupport : MethodSupports (compiled := compiled) (headers := headers) (stages := stages) (semanticFaults := semanticFaults))
  (mixedMethodSupport : MixedMethodSupports (compiled := compiled) (headers := headers) (stages := stages) (semanticFaults := semanticFaults))

local notation "functions" => CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include closurePackets closureSupport owners stagePrepared receiver profile bodyTyping certificates observations extension semantic bodies bodySupport mixedMethodSupport in
/-- Every ordinary and method body uses only strictly smaller Source grades. -/
theorem preserves_with_methods (size : Nat) :
    PreservesRootsAt (headers := headers) (keys := keys) model stages semanticFaults callFaults size := by
  induction size using Nat.strongRecOn with
  | ind budget ih =>
    intro context invocation scope expression lowered root owner keyPhysical
    let callerBridge := CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller
      owner root.compilation.administrativePrefix keyPhysical.locations
    have namedBodies : ∀ size, size ≤ budget → ∀ header (member : header ∈ headers),
        ∀ {child : Staging.Recursive.Scope}, stages.Closure header.function child →
        CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow
          (headers := headers) (keys := keys) header model stages child callFaults size := by
      intro size within header member child selected
      exact SelectedCompilationPhysicalNamedBodySupport.preserves (semantic := semantic)
        (assignmentInterpretation := PreparedAssignmentDiagnosticAuthority.interprets receiver)
        (bodySupport header member) profile (certificates header member) extension selected
        (fun smaller strict => ih smaller (Nat.lt_of_lt_of_le strict within))
    cases root.support with
    | ordinary support =>
      have directHeads : PreservesDirect callerBridge.forgetSlots model stages callFaults budget support.certificate := by
        intro fuel current id callee ids instantiation code types compiler path calleeTyped application sequence size within childMeaning
        obtain ⟨⟨port, certified, shaped⟩⟩ := support.directReady compiler path
        have rows := SelectedCompilationDirectSourceTypes.source_types
          compiler port.toReady shaped support.runtime.signatures application
        have ordered := rows.1 ▸ sequence
        intro current child code point
        obtain ⟨rfl, rfl, rfl⟩ := point
        exact SelectedCompilationPhysicalDirectBounds.preserves
          owner compiler port.toPort port.evidence callerBridge keyPhysical (fun state => state.physical)
          functions callFaults support.unique bodyTyping.function_ids certified shaped support.runtime
          size ordered childMeaning
          (fun selected => namedBodies size within port.header port.member selected) ⟨rfl, rfl, rfl⟩
      have methodHeads : PreservesMethod callerBridge.forgetSlots model stages callFaults budget support.certificate := by
        intro fuel current id code types compiler path sequence size within childMeaning
        obtain ⟨⟨port, selection⟩⟩ := support.methodReady compiler path
        obtain ⟨packet, sourceAtEq, static⟩ := mixedMethodSupport compiler port selection
        have certified := SelectedCompilationMethodBodySupport.Certified.of_typed port.principal packet.sourceAt selection
        have bodies : SelectedCompilationMethodHeadBounds.SourceBodies
            (headers := headers) (receiving := completion.result.context.registry) owner compiler port functions callFaults size := by
          intro mapping world heap store callerScope canonical administrative arguments payloads caller installed _parameters
            heapTyped argumentsTyped stable child selected
          have packetArguments : Dynamic.ValuesHaveTypes port.principal.sourceFunction.context heap arguments packet.sourceAt.types := by
            simpa only [sourceAtEq] using argumentsTyped
          simpa only [sourceAtEq] using
            SelectedCompilationMethodBodyBounds.source_continuation (semantic := semantic)
              (assignmentInterpretation := PreparedAssignmentDiagnosticAuthority.interprets receiver)
              port.principal packet static certified functions
              (CallableIndexedLambdaValues.identity_faithful compiled.indexed)
              (CallableIndexedOwnedPreparedPhysicalCellOrigins.observations profile) selected installed owner keyPhysical caller
              heapTyped packetArguments stable extension size
              (fun smaller strict => ih smaller (Nat.lt_of_lt_of_le strict within))
        intro actualScope actualId actualCode point actual found typed
        obtain ⟨rfl, rfl, rfl⟩ := point
        cases Option.some.inj (found.symm.trans compiler.metadata.found)
        have rows := SelectedCompilationMethodArgumentRows.raw_types compiler port
          support.catalog selection support.runtime support.unique typed
        have ordered := tree_types sequence support.unique rows.1 ▸ sequence
        intro mapping world administrativeContext environment canonical actualEnvironment actualContext before store ξ outcome after
        exact SelectedCompilationMethodHeadBounds.preserves
          owner compiler port callerBridge keyPhysical.frame (fun state => state.physical)
          (fun state => state.base.property) functions callFaults support.unique support.catalog selection
          support.runtime size ordered childMeaning bodies ⟨rfl, rfl, rfl⟩ found typed
      have indirectHeads : PreservesIndirect callerBridge.forgetSlots model stages callFaults budget support.certificate := by
        intro fuel current id callee ids metadata code types compiler path sequence size within childMeaning
        obtain ⟨port⟩ := support.callsReady compiler path
        have calleeCertified : RecursiveStageTupleMeaning.Entries current compiler.entries
            current callee compiler.calleeCode := ⟨rfl, by simp [CallableIndirectCallCertificates.Receipt.entries]⟩
        intro actualScope actualId actualCode point
        obtain ⟨rfl, rfl, rfl⟩ := point
        exact SelectedCompilationPhysicalIndirectHeadBounds.preserves (semantic := semantic)
          callerBridge.forgetSlots (fun state => state.physical) owners receiver stagePrepared rfl profile
          bodyTyping certificates support.runtime support.unique support.actualFunctionType
          observations closurePackets closureSupport bodies
          (PreparedAssignmentDiagnosticAuthority.interprets receiver) compiler port calleeCertified sequence size childMeaning budget ih (namedBodies size within) within ⟨rfl, rfl, rfl⟩
      intro current id code point
      exact SelectedCompilationSharedCallerBounds.preserves_reached_with_functions
        callerBridge.forgetSlots receiver functions support.runtime support.unique
        observations (CallableIndexedOwnedPreparedPhysicalCellOrigins.runtime_views profile)
        (CallableIndexedOwnedPreparedPhysicalCellOrigins.observations profile) extension semantic support.sameLedger support.runtimeLedger support.uninitialized
        budget support.certificate (.root (by simp)) directHeads methodHeads support.indexReady indirectHeads
        budget (Nat.le_refl _) point
    | coercedDirect support =>
      have rawMeaning := SelectedCompilationPhysicalCoercedDirectRawBounds.preserves
        support bodyTyping.function_ids owner keyPhysical functions callFaults
        budget ih (fun size within {_} selected => namedBodies size within support.port.header support.port.member selected)
      have conversionBodies := SelectedCompilationPhysicalCoercionMethodBounds.source_bodies
        owner keyPhysical functions callFaults support.chain support.methods budget ih
      intro current id code point actual found typed
      obtain ⟨rfl, rfl, rfl⟩ := point
      cases Option.some.inj (found.symm.trans support.actual.found)
      intro mapping world administrativeContext environment canonical actualEnvironment actualContext before store ξ outcome after
        environments heaps locals agrees actualTyped initial admitted trace
      exact SelectedCompilationCoercedDirectExpressionBounds.preserves
        owner support.actual callerBridge (fun state => state.physical) (fun state => state.base.property)
        keyPhysical.frame functions callFaults support.chain support.nonempty support.unique
        support.runtime support.ledger typed environments heaps locals agrees actualTyped initial admitted
        budget rawMeaning conversionBodies trace (Nat.le_refl _)


include closurePackets closureSupport owners receiver stagePrepared profile bodyTyping certificates observations extension semantic bodies bodySupport mixedMethodSupport in
/-- Every ordinary and method body uses only strictly smaller native grades. -/
theorem reflects_with_methods (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared) (size : Nat) :
    ReflectsRootsAt (headers := headers) (keys := keys) model stages semanticFaults callFaults size := by
  subst stages
  induction size using Nat.strongRecOn with
  | ind budget ih =>
    intro context invocation scope expression lowered root owner keyPhysical
    let callerBridge := CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller
      owner root.compilation.administrativePrefix keyPhysical.locations
    have namedBodies : ∀ size, size ≤ budget → ∀ header (member : header ∈ headers),
        ∀ {child : Staging.Recursive.Scope}, (RecursiveNamedPreparedStageScopes.registry stagePrepared).Closure header.function child →
        CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow
          (headers := headers) (keys := keys) header model (RecursiveNamedPreparedStageScopes.registry stagePrepared) child callFaults size := by
      intro size within header member child selected
      exact SelectedCompilationPhysicalNamedBodySupport.reflects (semantic := semantic)
        (assignmentInterpretation := PreparedAssignmentDiagnosticAuthority.interprets receiver)
        (bodySupport header member) profile (certificates header member) extension selected
        (fun smaller strict => ih smaller (Nat.lt_of_lt_of_le strict within))
    cases root.support with
    | ordinary support =>
      have directHeads : ReflectsDirect callerBridge.forgetSlots model (RecursiveNamedPreparedStageScopes.registry stagePrepared) callFaults budget support.certificate := by
        intro fuel current id callee ids instantiation code types compiler path calleeTyped application sequence size within childMeaning
        obtain ⟨⟨port, certified, shaped⟩⟩ := support.directReady compiler path
        have rows := SelectedCompilationDirectSourceTypes.source_types
          compiler port.toReady shaped support.runtime.signatures application
        have ordered := rows.1 ▸ sequence
        obtain ⟨descriptor⟩ := named_descriptor port.header
        intro current child code point
        obtain ⟨rfl, rfl, rfl⟩ := point
        exact SelectedCompilationPhysicalDirectBounds.reflects
          owner compiler port.toPort port.evidence callerBridge keyPhysical (fun state => state.physical)
          functions callFaults support.unique certified shaped support.runtime stagePrepared descriptor
          size ordered childMeaning
          (fun selected => namedBodies size within port.header port.member selected) ⟨rfl, rfl, rfl⟩
      have methodHeads : ReflectsMethod callerBridge.forgetSlots model (RecursiveNamedPreparedStageScopes.registry stagePrepared) callFaults budget support.certificate := by
        intro fuel current id code types compiler path sequence size within childMeaning
        obtain ⟨⟨port, selection⟩⟩ := support.methodReady compiler path
        obtain ⟨packet, sourceAtEq, static⟩ := mixedMethodSupport compiler port selection
        have certified := SelectedCompilationMethodBodySupport.Certified.of_typed port.principal packet.sourceAt selection
        have bodies : SelectedCompilationMethodHeadBounds.NativeBodies
            (headers := headers) (receiving := completion.result.context.registry) owner compiler port functions callFaults size := by
          intro mapping world heap store callerScope canonical administrative arguments payloads caller installed _parameters
            heapTyped argumentsTyped stable child selected
          have packetArguments : Dynamic.ValuesHaveTypes port.principal.sourceFunction.context heap arguments packet.sourceAt.types := by
            simpa only [sourceAtEq] using argumentsTyped
          simpa only [sourceAtEq] using
            SelectedCompilationMethodBodyBounds.native_continuation (semantic := semantic)
              (assignmentInterpretation := PreparedAssignmentDiagnosticAuthority.interprets receiver)
              port.principal packet static certified functions
              (CallableIndexedOwnedPreparedPhysicalCellOrigins.runtime_views profile)
              (CallableIndexedLambdaValues.identity_faithful compiled.indexed)
              (CallableIndexedOwnedPreparedPhysicalCellOrigins.observations profile) selected installed owner keyPhysical caller
              heapTyped packetArguments stable extension size
              (fun smaller strict => ih smaller (Nat.lt_of_lt_of_le strict within))
        intro actualScope actualId actualCode point actual found typed
        obtain ⟨rfl, rfl, rfl⟩ := point
        cases Option.some.inj (found.symm.trans compiler.metadata.found)
        have rows := SelectedCompilationMethodArgumentRows.raw_types compiler port
          support.catalog selection support.runtime support.unique typed
        have ordered := tree_types sequence support.unique rows.1 ▸ sequence
        intro mapping world administrativeContext environment canonical actualEnvironment actualContext before store ξ value finalStore
        exact SelectedCompilationMethodHeadBounds.reflects
          owner compiler port callerBridge keyPhysical.frame (fun state => state.physical)
          (fun state => state.base.property) functions callFaults support.unique support.catalog selection
          support.runtime size ordered childMeaning bodies ⟨rfl, rfl, rfl⟩ found typed
      have indirectHeads : ReflectsIndirect callerBridge.forgetSlots model (RecursiveNamedPreparedStageScopes.registry stagePrepared) callFaults budget support.certificate := by
        intro fuel current id callee ids metadata code types compiler path sequence size within childMeaning
        obtain ⟨port⟩ := support.callsReady compiler path
        have calleeCertified : RecursiveStageTupleMeaning.Entries current compiler.entries
            current callee compiler.calleeCode := ⟨rfl, by simp [CallableIndirectCallCertificates.Receipt.entries]⟩
        intro actualScope actualId actualCode point
        obtain ⟨rfl, rfl, rfl⟩ := point
        exact SelectedCompilationPhysicalIndirectHeadBounds.reflects (semantic := semantic)
          callerBridge.forgetSlots (fun state => state.physical) owners receiver stagePrepared rfl profile
          bodyTyping certificates support.runtime support.unique support.actualFunctionType
          observations closurePackets closureSupport bodies
          (PreparedAssignmentDiagnosticAuthority.interprets receiver) rfl compiler port calleeCertified sequence size childMeaning budget ih (namedBodies size within) within ⟨rfl, rfl, rfl⟩
      intro current id code point
      exact SelectedCompilationSharedCallerBounds.reflects_reached_with_functions
        callerBridge.forgetSlots receiver functions support.runtime support.unique
        observations (CallableIndexedOwnedPreparedPhysicalCellOrigins.runtime_views profile)
        (CallableIndexedOwnedPreparedPhysicalCellOrigins.observations profile) extension semantic support.sameLedger support.runtimeLedger support.uninitialized
        budget support.certificate (.root (by simp)) directHeads methodHeads support.indexReady indirectHeads
        budget (Nat.le_refl _) point
    | coercedDirect support =>
      obtain ⟨descriptor⟩ := named_descriptor support.port.header
      have rawMeaning := SelectedCompilationPhysicalCoercedDirectRawBounds.reflects
        support owner keyPhysical functions callFaults
        stagePrepared rfl descriptor
        budget ih (fun size within {_} selected => namedBodies size within support.port.header support.port.member selected)
      have conversionBodies := SelectedCompilationPhysicalCoercionMethodBounds.native_bodies
        owner keyPhysical functions callFaults support.chain support.methods budget ih
      intro current id code point actual found typed
      obtain ⟨rfl, rfl, rfl⟩ := point
      cases Option.some.inj (found.symm.trans support.actual.found)
      intro mapping world administrativeContext environment canonical actualEnvironment actualContext before store ξ value finalStore
        environments heaps locals agrees actualTyped initial admitted trace
      exact SelectedCompilationCoercedDirectExpressionBounds.reflects
        owner support.actual callerBridge (fun state => state.physical) (fun state => state.base.property)
        keyPhysical.frame functions callFaults support.chain support.nonempty
        support.runtime typed environments heaps locals agrees actualTyped initial admitted
        budget rawMeaning conversionBodies trace (Nat.le_refl _)


include closurePackets closureSupport owners receiver stagePrepared profile bodyTyping certificates observations extension semantic bodies bodySupport methodSupport in
/-- The existing named-body API embeds its terminal method packets. -/
theorem preserves_with_bodies (size : Nat) :
    PreservesRootsAt (headers := headers) (keys := keys) model stages semanticFaults callFaults size :=
  preserves_with_methods receiver stagePrepared profile bodyTyping certificates observations extension semantic
    bodies bodySupport closurePackets closureSupport owners methodSupport.toMixed size

include closurePackets closureSupport owners receiver stagePrepared profile bodyTyping certificates observations extension semantic bodies bodySupport methodSupport in
/-- The existing named-body API embeds its terminal method packets. -/
theorem reflects_with_bodies (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared) (size : Nat) :
    ReflectsRootsAt (headers := headers) (keys := keys) model stages semanticFaults callFaults size :=
  reflects_with_methods receiver stagePrepared profile bodyTyping certificates observations extension semantic
    bodies bodySupport closurePackets closureSupport owners methodSupport.toMixed stageEq size

include closurePackets closureSupport owners receiver stagePrepared profile bodyTyping certificates observations extension semantic terminals namedSupport methodSupport in
/-- Existing terminal families delegate to the same body-generic induction. -/
theorem preserves (size : Nat) :
    PreservesRootsAt (headers := headers) (keys := keys) model stages semanticFaults callFaults size :=
  preserves_with_bodies receiver stagePrepared profile bodyTyping certificates observations extension semantic
    (fun header member => CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (terminals header member))
    (fun header member => SelectedCompilationPhysicalNamedBodySupport.of_terminal_support
      (terminals header member) (namedSupport header member))
    closurePackets closureSupport owners methodSupport size

include closurePackets closureSupport owners receiver stagePrepared profile bodyTyping certificates observations extension semantic terminals namedSupport methodSupport in
/-- Existing terminal reflection retains its original arguments and conclusion. -/
theorem reflects (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared) (size : Nat) :
    ReflectsRootsAt (headers := headers) (keys := keys) model stages semanticFaults callFaults size :=
  reflects_with_bodies receiver stagePrepared profile bodyTyping certificates observations extension semantic
    (fun header member => CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (terminals header member))
    (fun header member => SelectedCompilationPhysicalNamedBodySupport.of_terminal_support
      (terminals header member) (namedSupport header member))
    closurePackets closureSupport owners methodSupport stageEq size

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalMixedCallerFamily
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalMixedNamedFamilyPorts
/-! The closed physical mixed family supplies named body ports for actual
terminal expressions, genuine lambda formation or scoped statements at every reached registry. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalMixedNamedFamilyPorts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open SelectedCompilationPhysicalMixedCallerFamily (MethodSupports MixedMethodSupports)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry} {semanticFaults : FunctionCalls.FaultRep}

variable {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  {bodyRegistry : SourceCoreRawMetadata.Registry}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (bodyTyping : SelectedCompilationBodyTyping.Bodies compiled)
  (certificates : ∀ header, header ∈ headers → SelectedCompilationNamedSourceTyping.Certified header)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry completion.result.context.registry)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (terminals : ∀ header, header ∈ headers → Terminal header)
  (namedSupport : ∀ header (member : header ∈ headers),
    Sum (SelectedCompilationPhysicalMixedNamedTerminalSupport.Support (headers := headers)
      (stages := stages) (semanticFaults := semanticFaults) header (terminals header member))
      { _support : SelectedCompilationPhysicalNamedFormationSupport.Support
          (bodyRegistry := bodyRegistry) (stages := stages) (semanticFaults := semanticFaults)
          header (terminals header member) // header.globals = compiled.indexed.base.globals.length })
  (bodies : ∀ header, header ∈ headers → CallableIndexedOwnedPreparedStagedNamedBodies.Body header)
  (bodySupport : ∀ header (member : header ∈ headers),
    SelectedCompilationPhysicalNamedBodySupport.Support
      (headers := headers) (bodyRegistry := bodyRegistry) (stages := stages)
      (semanticFaults := semanticFaults) header (bodies header member))
  (closurePackets : ∀ {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPreparedPhysicalClosureAssociation.Association headers keys bodyRegistry semanticFaults
      mapping world function native bindings parameter result),
    SelectedCompilationPhysicalClosureStaticSupport.PacketFor association stages)
  (closureSupport : ∀ {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPreparedPhysicalClosureAssociation.Association headers keys bodyRegistry semanticFaults
      mapping world function native bindings parameter result),
    SelectedCompilationPhysicalClosureStaticSupport.SupportFor association stages (closurePackets association))
  (owners : ∀ owner : OwnedKey keys, CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  (methodSupport : MethodSupports (compiled := compiled) (headers := headers) (stages := stages) (semanticFaults := semanticFaults))
  (mixedMethodSupport : MixedMethodSupports (compiled := compiled) (headers := headers) (stages := stages) (semanticFaults := semanticFaults))

local notation "functions" => CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include closurePackets closureSupport owners receiver stagePrepared profile bodyTyping certificates observations extension semantic bodies bodySupport mixedMethodSupport in
theorem preserves_with_methods
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (member : header ∈ headers) {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow
      (headers := headers) (keys := keys) header model stages child callFaults budget := by
  exact SelectedCompilationPhysicalNamedBodySupport.preserves (semantic := semantic)
        (assignmentInterpretation := PreparedAssignmentDiagnosticAuthority.interprets receiver)
    (bodySupport header member) profile (certificates header member) extension selected
    (fun size _ => SelectedCompilationPhysicalMixedCallerFamily.preserves_with_methods
      receiver stagePrepared profile bodyTyping certificates observations extension semantic bodies bodySupport
      closurePackets closureSupport owners mixedMethodSupport size)

include closurePackets closureSupport owners receiver stagePrepared profile bodyTyping certificates observations extension semantic bodies bodySupport mixedMethodSupport in
theorem reflects_with_methods (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (member : header ∈ headers) {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow
      (headers := headers) (keys := keys) header model stages child callFaults budget := by
  exact SelectedCompilationPhysicalNamedBodySupport.reflects (semantic := semantic)
        (assignmentInterpretation := PreparedAssignmentDiagnosticAuthority.interprets receiver)
    (bodySupport header member) profile (certificates header member) extension selected
    (fun size _ => SelectedCompilationPhysicalMixedCallerFamily.reflects_with_methods
      receiver stagePrepared profile bodyTyping certificates observations extension semantic bodies bodySupport
      closurePackets closureSupport owners mixedMethodSupport stageEq size)

include closurePackets closureSupport owners receiver stagePrepared profile bodyTyping certificates observations extension semantic bodies bodySupport methodSupport in
theorem preserves_with_bodies
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (member : header ∈ headers) {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow
      (headers := headers) (keys := keys) header model stages child callFaults budget := by
  exact SelectedCompilationPhysicalNamedBodySupport.preserves (semantic := semantic)
        (assignmentInterpretation := PreparedAssignmentDiagnosticAuthority.interprets receiver)
    (bodySupport header member) profile (certificates header member) extension selected
    (fun size _ => SelectedCompilationPhysicalMixedCallerFamily.preserves_with_bodies
      receiver stagePrepared profile bodyTyping certificates observations extension semantic bodies bodySupport
      closurePackets closureSupport owners methodSupport size)

include closurePackets closureSupport owners receiver stagePrepared profile bodyTyping certificates observations extension semantic bodies bodySupport methodSupport in
theorem reflects_with_bodies (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (member : header ∈ headers) {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow
      (headers := headers) (keys := keys) header model stages child callFaults budget := by
  exact SelectedCompilationPhysicalNamedBodySupport.reflects (semantic := semantic)
        (assignmentInterpretation := PreparedAssignmentDiagnosticAuthority.interprets receiver)
    (bodySupport header member) profile (certificates header member) extension selected
    (fun size _ => SelectedCompilationPhysicalMixedCallerFamily.reflects_with_bodies
      receiver stagePrepared profile bodyTyping certificates observations extension semantic bodies bodySupport
      closurePackets closureSupport owners methodSupport stageEq size)

include closurePackets closureSupport owners receiver stagePrepared profile bodyTyping certificates observations extension semantic terminals namedSupport methodSupport in
/-- The previous terminal family keeps its original public body-port API. -/
theorem preserves
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (member : header ∈ headers) {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow
      (headers := headers) (keys := keys) header model stages child callFaults budget :=
  preserves_with_bodies receiver stagePrepared profile bodyTyping certificates observations extension semantic
    (fun header member => CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (terminals header member))
    (fun header member => SelectedCompilationPhysicalNamedBodySupport.of_terminal_support
      (terminals header member) (namedSupport header member))
    closurePackets closureSupport owners methodSupport header member selected budget

include closurePackets closureSupport owners receiver stagePrepared profile bodyTyping certificates observations extension semantic terminals namedSupport methodSupport in
/-- The previous terminal family keeps its original public body-port API. -/
theorem reflects (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (member : header ∈ headers) {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow
      (headers := headers) (keys := keys) header model stages child callFaults budget :=
  reflects_with_bodies receiver stagePrepared profile bodyTyping certificates observations extension semantic
    (fun header member => CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (terminals header member))
    (fun header member => SelectedCompilationPhysicalNamedBodySupport.of_terminal_support
      (terminals header member) (namedSupport header member))
    closurePackets closureSupport owners methodSupport stageEq header member selected budget

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalMixedNamedFamilyPorts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalNamedFormationCollectors
/-! Original named compilation and observed lambda nodes produce physical
formation support. No execution law or full ordinary-header inventory is used. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalNamedFormationCollectors
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedNamedGeneration
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {recipe : SourceCoreIndexedSession.Recipe}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (terminal : Terminal header)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

theorem of_actual
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {stages : Staging.Recursive.Registry}
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    {node : ExpressionNode} {reported : Ty} {result : TypeSystem.Ty}
    {parameters : List TypedBinder}
    {statement : StatementId} {returnNode : StatementNode} {expression : ExpressionId}
    (found : header.function.source.lookupExpression? terminal.expression = some node)
    (form : node.form = .lambda parameters result [statement])
    (owner : terminal.expression.occurrence.owner = header.function.source.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed terminal.prepared.named).owner ∧
        binding.initializer = terminal.expression)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked
      header.function.source terminal.expression = .ok (node, reported))
    (returnFound : header.function.source.lookupStatement? statement = some returnNode)
    (returnForm : returnNode.form = .returnStmt (some expression))
    (returnType : returnNode.type = result)
    (point : terminal.certificate = CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) :
    Nonempty (SelectedCompilationPhysicalNamedFormationSupport.Support
      (bodyRegistry := registry) (stages := stages) (semanticFaults := faults) header terminal) := by
  refine ⟨⟨point, ?_⟩⟩
  intro child selected
  have formed := SelectedCompilationNamedReturnLambdaFormation.of_terminal_parameters (registry := registry) (faults := faults) terminal
    prepared diagnostic certified profile selected member found form owner requirements coercions ordinary read
    returnFound returnForm returnType
  obtain ⟨formed⟩ := formed
  exact ⟨.inl (by simpa only [stages.evidence selected] using formed)⟩

/-- Original scoped body syntax and the accepted lambda compiler supply full
formation support before any closure body runs. -/
theorem of_branching
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (_receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (_included : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics reason token → faults reason token)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    (_catalog : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {stages : Staging.Recursive.Registry}
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    {node : ExpressionNode} {reported : Ty} {result : TypeSystem.Ty}
    {parameters : List TypedBinder}
    {statements : List StatementId}
    (found : header.function.source.lookupExpression? terminal.expression = some node)
    (form : node.form = .lambda parameters result statements)
    (owner : terminal.expression.occurrence.owner = header.function.source.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed terminal.prepared.named).owner ∧
        binding.initializer = terminal.expression)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked
      header.function.source terminal.expression = .ok (node, reported))
    (_shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape header.function.source true statements)
    (syntaxFor : ∀ {context final bodyFacts},
      StatementsHaveType header.function.source {returnType := result} context statements final bodyFacts →
      GenericImperativeMatch.Syntax header.function.source
        (CallableIndexedOwnedPreparedBranchingLambdaBodySupport.Syntax header.function.source)
        context (.statements true statements) result)
    (point : terminal.certificate = CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) :
    Nonempty (SelectedCompilationPhysicalNamedFormationSupport.Support
      (bodyRegistry := registry) (stages := stages) (semanticFaults := faults) header terminal) := by
  refine ⟨⟨point, ?_⟩⟩
  intro child selected
  have formed := SelectedCompilationNamedPreparedBranchingLambdaFormation.of_terminal terminal
    prepared diagnostic certified profile selected member found form owner requirements coercions ordinary read
    syntaxFor
  obtain ⟨formed⟩ := formed
  exact ⟨.inr (.inl (by simpa only [stages.evidence selected] using formed))⟩


/-- Original scoped body syntax and the accepted lambda compiler supply full
formation support before any closure body runs. -/
theorem of_prepared_branching
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (_receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (_included : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics reason token → faults reason token)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    (catalog : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {stages : Staging.Recursive.Registry}
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    {node : ExpressionNode} {reported : Ty} {result : TypeSystem.Ty}
    {parameters : List TypedBinder}
    {statements : List StatementId}
    (found : header.function.source.lookupExpression? terminal.expression = some node)
    (form : node.form = .lambda parameters result statements)
    (owner : terminal.expression.occurrence.owner = header.function.source.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed terminal.prepared.named).owner ∧
        binding.initializer = terminal.expression)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked
      header.function.source terminal.expression = .ok (node, reported))
    (shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape header.function.source true statements)
    (syntaxFor : ∀ {context final bodyFacts},
      StatementsHaveType header.function.source {returnType := result} context statements final bodyFacts →
      GenericImperativeMatch.PreparedSyntax header.function.source
        (CallableIndexedOwnedPreparedBranchingLambdaBodySupport.Syntax header.function.source)
        context (.statements true statements) result)
    (point : terminal.certificate = CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) :
    Nonempty (SelectedCompilationPhysicalNamedFormationSupport.Support
      (bodyRegistry := registry) (stages := stages) (semanticFaults := faults) header terminal) := by
  refine ⟨⟨point, ?_⟩⟩
  intro child selected
  have formed := SelectedCompilationNamedPreparedLambdaBodyFormation.of_terminal terminal
    prepared diagnostic certified profile (by rw [CallableIndexedOwnedPublicSignatureCatalog.signatures compiled]; exact catalog) selected member found form owner requirements coercions ordinary read
    shape syntaxFor
  obtain ⟨formed⟩ := formed
  exact ⟨.inr (.inr (by simpa only [stages.evidence selected] using formed))⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalNamedFormationCollectors
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalBootstrap
/-! Actual finite ordinary inputs and the completed native bootstrap establish
both the old semantic pool and every physical cache row, including methods.
No complete ordinary Header inventory or body execution premise is needed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalBootstrap
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- The finite bootstrap owner's association is the actual installed layout. -/
theorem key_physical (compiled : SourceCoreUnifiedCompilation.Compiled)
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))) :
    CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical (owner compiled).key headers := by
  constructor
  · rfl
  · rfl
  · intro header _member
    rfl

theorem of_completed
    (bodyTyping : SelectedCompilationBodyTyping.Bodies compiled)
    (inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled))
    (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (distinct : (inputs.map (fun input => input.prepared.index)).Nodup)
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    (registry : SourceCoreRawMetadata.Registry)
    {fuel : Nat} {value : Value} {finalStore : Store}
    (completed : runStateful fuel (.initial recipe.bootstrap [] []) = .done value finalStore) :
    value = .inRight .word .unit ∧
      finalStore = RecursiveNamedCatalogPreparedInitialization.store compiled ∧
      ∃ caller : (CallableIndexedOwnedPhysicalCanonicalState.protocol
          (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) (keys compiled) 0).State
          ⟨[], [], finalStore.map Value.type, ⟨[]⟩, finalStore,
            SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩,
        CallableIndexedOwnedIndirectExpressionHeads.StableRows caller.base.val ∧
        CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions []
          (finalStore.map Value.type) ⟨[]⟩ finalStore ∧
        (∀ header, header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows →
          (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)[header.slot]? =
            some (.cellRef (OptionalCell.cellType header.named.signature.functionType)
              ((owner compiled).key.locations header))) ∧
        (∀ context, Dynamic.HeapWellTyped context ⟨[]⟩) := by
  obtain ⟨valueEq, storeEq, caller, stable, heaps, globals, sourceTyped⟩ :=
    SelectedCompilationBootstrapRootState.of_completed bodyTyping inputs rows accepted distinct functions registry completed
  refine ⟨valueEq, storeEq, ⟨⟨caller, CallableIndexedOwnedPhysicalGlobals.environment_slots compiled⟩,
    CallableIndexedOwnedPhysicalGlobals.of_completed accepted completed⟩, stable, heaps, globals, sourceTyped⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalBootstrap
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalBuiltinOrigins
/-! A builtin leaf retains its original compiler receipt inside the prepared
physical model. Projection uses the actual source value and preserves wrappers. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalBuiltinOrigins
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {mapping : LocationMap} {world : StoreTyping}

theorem builtin_member {sourceType : TypeSystem.Ty} {sourceValue : Dynamic.Value}
    {carrier : Value} {type : Ty}
    (represented : CallableIndexedOwnedPreparedPhysicalCellOrigins.PayloadOrigins
      headers keys bodyRegistry registry faults profile mapping world sourceType sourceValue carrier type) :
    ∀ function, sourceValue = .builtin function →
      CallableIndexedBuiltinValues.Represents compiled.indexed world
        function.id.type (.builtin function) carrier type := by
  intro function same
  cases same
  exact CallableIndexedOwnedPreparedStagedBuiltinArgumentRows.builtin_member
    (SelectedCompilationBuiltinFunctionOrigins.ErasesBuiltinsToContextual.erase
      (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry)
      (faults := faults) (profile := profile) represented) function rfl

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalBuiltinOrigins
end
