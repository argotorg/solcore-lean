import Solcore.SourceSemantics.CoreLowering.PreparedAssignmentDiagnosticAuthority
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.PhysicalClosures
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalNamedCalls
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBranchingCatalogSites
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.BranchingTrees
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedLambdaFormationHeads
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.PhysicalDirectCalls
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalBodies
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedReturnLambdaFormation
import Solcore.SourceSemantics.Staging.RecursiveTypedControlBoundary
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalLambdaCaptures
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedScopedImperativeFlow
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedScopedImperativePreservation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedLexicalFooter
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderSourceTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalFunctionViews
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.Coercions
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MethodScopedRoots
import Solcore.SourceSemantics.CoreLowering.PreparedAssignmentDiagnosticAuthorityReception
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MethodSelection
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.DirectCallers

/-!
# Staged bounds: physical mixed families

Static support, scoped bounds and family ports of mixed named bodies on the physical protocol, with coercion method bounds.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalMixedNamedScopedStaticSupport
/-! Each named scoped child retains its actual physical mixed root and compiler
prefix. The authentic named receipt supplies the complete collected statement
tree and its catalog sites; execution is supplied by the shared numeric family. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalMixedNamedScopedStaticSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedStagedPhysicalMixedRootStaticSupport (RootAt)
open CallableIndexedOwnedPreparedStagedNamedBranchingReceipts (Receipt parameterScope)
open CallableIndexedOwnedPreparedStagedLexicalTree (TypedCertificate)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

def Certificate
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (stages : Staging.Recursive.Registry) (semanticFaults : FunctionCalls.FaultRep)
    (context : SourceSemantics.Context) (invocation : Staging.Recursive.Scope)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) : Prop :=
  ∃ root : RootAt compiled headers stages context invocation scope id lowered semanticFaults,
    root.compilation.administrativePrefix = 1

structure Support
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (stages : Staging.Recursive.Registry) (receipt : Receipt header)
    (semanticFaults : FunctionCalls.FaultRep) : Type where
  wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)
  invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word
  missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word
  assignmentAuthority : Nonempty (PreparedAssignmentDiagnosticAuthority.SourcePort compiled
    header.function.source invalidProjection missingDefault)
  tree : ∀ child, stages.Closure header.function child →
    ∃ expressionSyntax : ExpressionId → Prop,
    CallableIndexedOwnedPreparedBranchingCatalogSites.Collected invalidProjection missingDefault (faults := semanticFaults)
      header.layouts header.owner header.active compiled.indexed.ancestry.layout.frame
      header.globals header.onError (.initial compiled.compatible.checked) child.source expressionSyntax
      (TypedCertificate child.source (fun context => Certificate headers stages semanticFaults context child))
      compiled.indexed.layouts.definitions
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      header.context (parameterScope header) (.statements true header.function.body)
      header.function.resultType header.output receipt.flow

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalMixedNamedScopedStaticSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalMixedNamedTerminalSupport
/-! Ordinary terminal bodies use the same physical root family as method bodies.
The actual parameter packet supplies the pool, complete cache and slot layout;
strict expression children establish both body directions. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalMixedNamedTerminalSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedStagedPhysicalMixedRootStaticSupport (RootAt)
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
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))

local notation "physicalBridge" =>
  CallableIndexedOwnedNamedCallerProtocol.Carrier.forgetSlots
    (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) 1)

include static selected wellFormed in
theorem preserves {budget : Nat}
    (children : ∀ size, size < budget →
      CallableIndexedOwnedPreparedStagedPhysicalMixedRootBounds.PreservesRootsAt
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
    CallableIndexedOwnedPreparedStagedTerminalNamedBodyBounds.preserves_body
      physicalBridge selected wellFormed terminal.receipt terminal.certifies
      environments heaps locals agrees typed entered enteredAdmission budget childMeaning trace matched within
  refine ⟨value, finalStore, finalMap, finalWorld, evaluated, result, finalHeaps,
    maps, worlds, frame, metadata, reached.base.val, related, ?_⟩
  cases outcome with
  | value => exact ⟨post.rows, post.successful⟩
  | fault failure =>
    cases failure with
    | semantic => exact ⟨post.rows, post.successful⟩
    | stage => exact post

include static selected wellFormed in
theorem reflects {budget : Nat}
    (children : ∀ size, size < budget →
      CallableIndexedOwnedPreparedStagedPhysicalMixedRootBounds.ReflectsRootsAt
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
    CallableIndexedOwnedPreparedStagedTerminalNamedBodyBounds.reflects_body
      physicalBridge selected wellFormed terminal.receipt terminal.certifies
      environments heaps locals agrees typed entered enteredAdmission budget childMeaning completed within
  refine ⟨sourceSize, header.context, _, outcome, after, finalMap, finalWorld, trace, matched,
    result, finalHeaps, maps, worlds, frame, metadata, reached.base.val, related, ?_⟩
  cases outcome with
  | value => exact ⟨post.rows, post.successful⟩
  | fault failure =>
    cases failure with
    | semantic => exact ⟨post.rows, post.successful⟩
    | stage => exact post

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalMixedNamedTerminalSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalNamedFormationSupport
/-! A named terminal lambda forms its actual captured value in the physical
positive model. The original parameter packet supplies the full caller seed;
all physical references come from the real entered state. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalNamedFormationSupport
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
local notation "functions" => CallableIndexedOwnedPhysicalCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

structure Support (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (terminal : Terminal header) where
  point : terminal.certificate = Point
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    terminal.expression terminal.receipt.child
  formations : ∀ child, stages.Closure header.function child →
    Nonempty (OrdinaryFormation (registry := bodyRegistry) (faults := semanticFaults)
      header header.context child.evidence
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child)

variable {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {terminal : Terminal header}
  (static : Support (bodyRegistry := bodyRegistry) (stages := stages) (semanticFaults := semanticFaults) header terminal)
  {child : Staging.Recursive.Scope} (selected : stages.Closure header.function child)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (globals : header.globals = compiled.indexed.base.globals.length)

local notation "nestedBridge" owner => CallableIndexedOwnedPhysicalNestedCanonicalState.bridge (headers := headers) owner header

include profile static selected wellFormed globals in
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
    obtain ⟨_, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
    have original : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) header.function.context header.function.source := by
      rw [header.frame.context, header.frame.source]
      exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid
    exact original.transport (RecursiveNamedInitialContextValidity.mono_fields header.extended)
  have covers : child.evidence.Covers header.context := by
    rw [stages.evidence selected]
    exact RecursiveNamedInitialContextValidity.covers header.frame header.extended
  have childMeaning : PreservesBelow (nestedBridge owner) header.context model stages child
      terminal.certificate faults budget := by
    intro childSize _smaller current id lowered point
    rw [static.point] at point
    obtain ⟨rfl, rfl, rfl⟩ := point
    obtain ⟨formation⟩ := static.formations child selected
    exact CallableIndexedOwnedPreparedStagedPhysicalLambdaFormationBounds.preserves
      header owner header.context child profile globals
      (RecursiveNamedLambdaFormationHeads.cached_capture_slots compiled headers) keyPhysical.prefixZero
      (by rw [stages.source selected]; exact header.agreement.source)
      (by rw [stages.source selected]; exact header.unique)
      wellFormed runtime covers faults childSize ⟨formation⟩
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, finalHeaps,
    maps, worlds, frame, metadata, reached, related, post⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalNamedBodyBounds.preserves_body
      (nestedBridge owner) selected wellFormed terminal.receipt terminal.certifies
      environments heaps locals agrees typed entered enteredAdmission budget childMeaning trace matched within
  refine ⟨value, finalStore, finalMap, finalWorld, evaluated, result, finalHeaps,
    maps, worlds, frame, metadata, reached.base.val.val, related, ?_⟩
  cases outcome with
  | value => exact ⟨post.rows, post.successful⟩
  | fault failure =>
    cases failure with
    | semantic => exact ⟨post.rows, post.successful⟩
    | stage => exact post

include profile static selected wellFormed globals in
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
    obtain ⟨_, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
    have original : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) header.function.context header.function.source := by
      rw [header.frame.context, header.frame.source]
      exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid
    exact original.transport (RecursiveNamedInitialContextValidity.mono_fields header.extended)
  have covers : child.evidence.Covers header.context := by
    rw [stages.evidence selected]
    exact RecursiveNamedInitialContextValidity.covers header.frame header.extended
  have childMeaning : ReflectsBelow (nestedBridge owner) header.context model stages child
      terminal.certificate faults budget := by
    intro childSize _smaller current id lowered point
    rw [static.point] at point
    obtain ⟨rfl, rfl, rfl⟩ := point
    obtain ⟨formation⟩ := static.formations child selected
    exact CallableIndexedOwnedPreparedStagedPhysicalLambdaFormationBounds.reflects
      header owner header.context child profile globals
      (RecursiveNamedLambdaFormationHeads.cached_capture_slots compiled headers) keyPhysical.prefixZero
      (by rw [stages.source selected]; exact header.agreement.source)
      wellFormed runtime covers faults childSize ⟨formation⟩
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, matched, result, finalHeaps,
    maps, worlds, frame, metadata, reached, related, post⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalNamedBodyBounds.reflects_body
      (nestedBridge owner) selected wellFormed terminal.receipt terminal.certifies
      environments heaps locals agrees typed entered enteredAdmission budget childMeaning completed within
  refine ⟨sourceSize, header.context, _, outcome, after, finalMap, finalWorld, trace, matched,
    result, finalHeaps, maps, worlds, frame, metadata, reached.base.val.val, related, ?_⟩
  cases outcome with
  | value => exact ⟨post.rows, post.successful⟩
  | fault failure =>
    cases failure with
    | semantic => exact ⟨post.rows, post.successful⟩
    | stage => exact post

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalNamedFormationSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalMixedNamedScopedBounds
/-! Actual named parameter entry supplies the physical slots, current authority,
and original frame used by the existing scoped flow engine. Every expression
child is discharged by the strictly smaller mixed root family. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalMixedNamedScopedBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPreparedStagedNamedBranchingReceipts (Receipt parameterScope)
open CallableIndexedOwnedPreparedStagedPhysicalMixedNamedScopedStaticSupport (Support)
open CallableIndexedOwnedAdmittedStagedExpressionBounds

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {semanticFaults : FunctionCalls.FaultRep}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {stages : Staging.Recursive.Registry} {receipt : Receipt header}
  (support : Support headers header stages receipt semanticFaults)
  (globals : header.globals = compiled.indexed.base.globals.length)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (functionTypes : FunctionRuntimeViews functions)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  {receiving : SourceCoreRawMetadata.Registry} {faults : RecursiveStageMeaning.FaultRep}
  {invocation : Staging.Recursive.Scope} (selected : stages.Closure header.function invocation)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions
local notation "physicalBridge" =>
  CallableIndexedOwnedNamedCallerProtocol.Carrier.forgetSlots
    (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) 1)

variable (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)
  (assignmentInterpretation : PreparedAssignmentDiagnosticAuthority.Interprets compiled receiving
    (fun reason token => faults (.semantic reason) token))

include support globals selected semantic faithful observations assignmentInterpretation in
/-- The original named body enters the same protected lexical engine and
returns the exact reached pool, including cells captured by its result. -/
theorem preserves
    (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
    (layouts : header.layouts = compiled.indexed.layouts) {budget : Nat}
    (children : ∀ size, size < budget →
      CallableIndexedOwnedPreparedStagedPhysicalMixedRootBounds.PreservesRootsAt
        (headers := headers) (keys := keys) model stages semanticFaults faults size) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow
      (headers := headers) (keys := keys) header model stages invocation faults budget := by
  intro mapping world administrative actualContext environment canonical actual before store ξ
    environments heaps locals agrees actualTyped initial admitted owner packet keyPhysical physical slots size finalContext bodyOutcome outcome after trace matched within
  have originalPacket := packet keyPhysical.prefixZero globals
  let actualEntry := CallableIndexedOwnedLambdaViewHeads.nested_entry (caller := header) initial owner
    keyPhysical.prefixZero (originalPacket.observed owner header) originalPacket.carried originalPacket.bundle globals
  have prefixAgreement := CallableIndexedOwnedPhysicalLambdaCaptures.entry_prefix_for
    slots globals actualEntry environments
  have environments := RecursiveNamedLambdaFormationHeads.environments_prefix environments
    (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header) prefixAgreement
  have agrees : EnvironmentsAgree ξ
      (canonical.take ((parameterScope header).length +
        (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header).length)) actual :=
    RecursiveNamedLambdaFormationHeads.agrees_prefix agrees
    ((parameterScope header).length +
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header).length)
  have packet := CallableIndexedOwnedPreparedStagedNamedBranchingEntryPrefix.packet_take
    header owner initial originalPacket (RecursiveNamedLambdaFormationHeads.cached_capture_slots compiled headers)
  have retainedSlots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 1 (parameterScope header)
      (canonical.take ((parameterScope header).length +
        (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header).length)) := by
    intro slot signature found
    have bound := (List.getElem?_eq_some_iff.mp found).1
    rw [List.getElem?_take, if_pos]
    · exact slots slot signature found
    · simp only [RecursiveNamedLambdaFormationHeads.nativePrefix, List.length_cons, List.length_append,
        List.length_map, List.length_nil]
      omega
  let canonical := canonical.take ((parameterScope header).length +
    (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header).length)
  let wrapped : (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1).State
      ⟨parameterScope header, mapping, world, before, store, canonical⟩ := ⟨⟨initial, retainedSlots⟩, physical⟩
  have nestedAdmitted : Admission physicalBridge header.context wrapped :=
    ⟨admitted.heap, admitted.rows⟩
  obtain ⟨expressionSyntax, collected⟩ := support.tree invocation selected
  rw [layouts] at collected
  have tree := collected.tree
  have catalogSites := collected.sites receiving
  obtain ⟨assignmentAuthority⟩ := support.assignmentAuthority
  have assignmentDiagnostics : PreparedAssignmentReachedDiagnostics.Ready
      (values := .initial compiled.compatible.checked) functions (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1)
      header.function.source support.invalidProjection support.missingDefault receiving
      (fun reason token => faults (.semantic reason) token) :=
    assignmentInterpretation assignmentAuthority functions (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1)
  rw [← stages.source selected] at assignmentDiagnostics
  have shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape invocation.source true header.function.body := by
    rw [stages.source selected]
    exact receipt.shape
  have reference : canonical[(parameterScope header).length + 1 + header.globals]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
    simpa only [canonical, globals, parameterScope] using packet.reference
  obtain ⟨sourceFinal, sourceFacts, sourceTyped, _sourceComplete⟩ :=
    RecursiveNamedHeaderSourceTyping.statements header support.wellFormed
  rw [← stages.source selected] at sourceTyped
  have originalTyping : ProtectedStateImperativeTypedSourceSites.Statements invocation.source header.context header.function.body :=
    ⟨_, _, _, sourceTyped⟩
  have read := CallableIndexedOwnedFunctionEntries.reached_frame_read initial owner.position
  have unmapped : owner.key.frameLocation ∉ mapping := by
    have original := (initial.rows owner.position).authority.unmapped
    rw [(initial.rows owner.position).frame_eq] at original
    exact original
  have conditioned := CallableIndexedOwnedAllocationProducer.stableOwner_selected owner.position packet.carried
  obtain ⟨flowValue, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    CallableIndexedOwnedAdmittedStagedScopedImperativePreservation.preserves_at (compiled := compiled)
      physicalBridge (CallableIndexedOwnedPhysicalCanonicalState.bindings 1)
      (CallableIndexedOwnedPhysicalCanonicalState.administrativeTransport 1)
      functions faithful observations extension rfl header.registered
      (CallableIndexedOwnedPhysicalCanonicalState.markedProducer model 1)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (fun _ _ stable => CallableIndexedOwnedPhysicalCanonicalState.readyAt_of_stableOwner (headers := headers) model 1 stable)
      (fun context size smaller scope id lowered certified => by
        obtain ⟨root, samePrefix⟩ := certified
        have meaning : PreservesAt
            (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys)
              root.compilation.administrativePrefix).forgetSlots context model stages invocation
            (CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point scope id lowered) faults size :=
          children size smaller root owner keyPhysical
        rw [samePrefix] at meaning
        intro node
        exact meaning ⟨rfl, rfl, rfl⟩ (node := node))
      (by rw [stages.source selected]; exact header.unique)
      tree catalogSites semantic assignmentDiagnostics rfl shape originalTyping receipt.projection within environments heaps locals agrees actualTyped reference read unmapped
      wrapped conditioned nestedAdmitted trace
  have post := CallableIndexedOwnedAdmittedStagedFlowOutcomes.Post.to_function represented post
  have controlClosed := Staging.Recursive.TypedControlBoundary.function
    (by rw [stages.source selected]; exact header.unique) sourceTyped rfl trace.sound
  have represented := CallableIndexedOwnedAdmittedStagedFlowOutcomes.Represents.to_function receipt.projection represented controlClosed
  obtain ⟨value, evaluatedBody, representedBody⟩ :=
    CallableIndexedOwnedAdmittedStagedLexicalFooter.evaluates represented evaluated header.fellThrough header.escaped ξ
  have outcomeEq := CallableIndexedOwnedAdmittedStagedLexicalFooter.outcome_eq matched
  subst outcome
  refine ⟨value, finalStore, finalMap, finalWorld, ?_, representedBody, finalHeaps,
    maps, worlds, frame, metadata, reached.base.val, related, ?_⟩
  · simpa only [receipt.emitted, CallableIndexedOwnedAdmittedStagedLexicalFooter.finish_rename] using evaluatedBody
  · cases bodyOutcome with
    | breaking environment => exact (controlClosed.1 environment rfl).elim
    | continuing environment => exact (controlClosed.2 environment rfl).elim
    | returned => exact ⟨post.rows, post.successful⟩
    | fallthrough => exact ⟨post.rows, post.successful⟩
    | fault failure => cases failure with
      | semantic => exact ⟨post.rows, post.successful⟩
      | stage => exact post

include support globals selected semantic functionTypes faithful observations assignmentInterpretation in
/-- Native completion is inverted through its real flow prefix and footer;
no selected final Source context is assumed. -/
theorem reflects
    (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
    (layouts : header.layouts = compiled.indexed.layouts) {budget : Nat}
    (children : ∀ size, size < budget →
      CallableIndexedOwnedPreparedStagedPhysicalMixedRootBounds.ReflectsRootsAt
        (headers := headers) (keys := keys) model stages semanticFaults faults size) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow
      (headers := headers) (keys := keys) header model stages invocation faults budget := by
  intro mapping world administrative actualContext environment canonical actual before store ξ
    environments heaps locals agrees actualTyped initial admitted owner packet keyPhysical physical slots size value finalStore completed within
  have originalPacket := packet keyPhysical.prefixZero globals
  let actualEntry := CallableIndexedOwnedLambdaViewHeads.nested_entry (caller := header) initial owner
    keyPhysical.prefixZero (originalPacket.observed owner header) originalPacket.carried originalPacket.bundle globals
  have prefixAgreement := CallableIndexedOwnedPhysicalLambdaCaptures.entry_prefix_for
    slots globals actualEntry environments
  have environments := RecursiveNamedLambdaFormationHeads.environments_prefix environments
    (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header) prefixAgreement
  have agrees : EnvironmentsAgree ξ
      (canonical.take ((parameterScope header).length +
        (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header).length)) actual :=
    RecursiveNamedLambdaFormationHeads.agrees_prefix agrees
    ((parameterScope header).length +
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header).length)
  have packet := CallableIndexedOwnedPreparedStagedNamedBranchingEntryPrefix.packet_take
    header owner initial originalPacket (RecursiveNamedLambdaFormationHeads.cached_capture_slots compiled headers)
  have retainedSlots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 1 (parameterScope header)
      (canonical.take ((parameterScope header).length +
        (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header).length)) := by
    intro slot signature found
    have bound := (List.getElem?_eq_some_iff.mp found).1
    rw [List.getElem?_take, if_pos]
    · exact slots slot signature found
    · simp only [RecursiveNamedLambdaFormationHeads.nativePrefix, List.length_cons, List.length_append,
        List.length_map, List.length_nil]
      omega
  let canonical := canonical.take ((parameterScope header).length +
    (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header).length)
  let wrapped : (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1).State
      ⟨parameterScope header, mapping, world, before, store, canonical⟩ := ⟨⟨initial, retainedSlots⟩, physical⟩
  have nestedAdmitted : Admission physicalBridge header.context wrapped :=
    ⟨admitted.heap, admitted.rows⟩
  obtain ⟨expressionSyntax, collected⟩ := support.tree invocation selected
  rw [layouts] at collected
  have tree := collected.tree
  have catalogSites := collected.sites receiving
  obtain ⟨assignmentAuthority⟩ := support.assignmentAuthority
  have assignmentDiagnostics : PreparedAssignmentReachedDiagnostics.Ready
      (values := .initial compiled.compatible.checked) functions (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1)
      header.function.source support.invalidProjection support.missingDefault receiving
      (fun reason token => faults (.semantic reason) token) :=
    assignmentInterpretation assignmentAuthority functions (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1)
  rw [← stages.source selected] at assignmentDiagnostics
  have shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape invocation.source true header.function.body := by
    rw [stages.source selected]
    exact receipt.shape
  have reference : canonical[(parameterScope header).length + 1 + header.globals]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
    simpa only [canonical, globals, parameterScope] using packet.reference
  obtain ⟨sourceFinal, sourceFacts, sourceTyped, _sourceComplete⟩ :=
    RecursiveNamedHeaderSourceTyping.statements header support.wellFormed
  rw [← stages.source selected] at sourceTyped
  have originalTyping : ProtectedStateImperativeTypedSourceSites.Statements invocation.source header.context header.function.body :=
    ⟨_, _, _, sourceTyped⟩
  have read := CallableIndexedOwnedFunctionEntries.reached_frame_read initial owner.position
  have unmapped : owner.key.frameLocation ∉ mapping := by
    have original := (initial.rows owner.position).authority.unmapped
    rw [(initial.rows owner.position).frame_eq] at original
    exact original
  have conditioned := CallableIndexedOwnedAllocationProducer.stableOwner_selected owner.position packet.carried
  obtain ⟨_, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate header support.wellFormed
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      header.function.context header.function.source := by
    rw [header.frame.context, header.frame.source]
    exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid
  have graph : OccurrenceGraphWellFormed invocation.source := by
    rw [stages.source selected]
    exact runtime.graph
  have bodyTrace := completed
  rw [receipt.emitted, CallableIndexedOwnedAdmittedStagedLexicalFooter.finish_rename] at bodyTrace
  obtain ⟨flowSize, flowValue, flowStore, flowTrace, strict⟩ :=
    CallableIndexedOwnedAdmittedStagedTerminalBody.flow_prefix bodyTrace within
  obtain ⟨sourceSize, finalContext, bodyOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    CallableIndexedOwnedAdmittedStagedScopedImperativeFlow.reflects_at (compiled := compiled)
      physicalBridge (CallableIndexedOwnedPhysicalCanonicalState.bindings 1)
      (CallableIndexedOwnedPhysicalCanonicalState.administrativeTransport 1)
      functions functionTypes faithful observations extension rfl header.registered
      (CallableIndexedOwnedPhysicalCanonicalState.markedProducer model 1)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (fun _ _ stable => CallableIndexedOwnedPhysicalCanonicalState.readyAt_of_stableOwner (headers := headers) model 1 stable)
      (fun context size smaller scope id lowered certified => by
        obtain ⟨root, samePrefix⟩ := certified
        have meaning : ReflectsAt
            (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys)
              root.compilation.administrativePrefix).forgetSlots context model stages invocation
            (CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point scope id lowered) faults size :=
          children size smaller root owner keyPhysical
        rw [samePrefix] at meaning
        intro node
        exact meaning ⟨rfl, rfl, rfl⟩ (node := node))
      graph tree catalogSites semantic assignmentDiagnostics rfl shape originalTyping receipt.projection (Nat.le_of_lt strict) environments heaps locals agrees actualTyped reference read unmapped
      wrapped conditioned nestedAdmitted flowTrace
  have post := CallableIndexedOwnedAdmittedStagedFlowOutcomes.Post.to_function represented post
  have controlClosed := Staging.Recursive.TypedControlBoundary.function
    graph.nodeOccurrencesUnique sourceTyped rfl trace.sound
  have represented := CallableIndexedOwnedAdmittedStagedFlowOutcomes.Represents.to_function receipt.projection represented controlClosed
  obtain ⟨bodyValue, evaluatedBody, representedBody⟩ :=
    CallableIndexedOwnedAdmittedStagedLexicalFooter.evaluates represented flowTrace.sound header.fellThrough header.escaped ξ
  obtain ⟨sameValue, sameStore⟩ := evaluation_deterministic bodyTrace.sound evaluatedBody
  subst bodyValue
  subst flowStore
  refine ⟨sourceSize, finalContext, bodyOutcome, _, after, finalMap, finalWorld,
    trace, represented.body_result, representedBody, finalHeaps, maps, worlds, frame, metadata,
    reached.base.val, related, ?_⟩
  cases bodyOutcome with
  | breaking environment => exact (controlClosed.1 environment rfl).elim
  | continuing environment => exact (controlClosed.2 environment rfl).elim
  | returned => exact ⟨post.rows, post.successful⟩
  | fallthrough => exact ⟨post.rows, post.successful⟩
  | fault failure => cases failure with
    | semantic => exact ⟨post.rows, post.successful⟩
    | stage => exact post

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalMixedNamedScopedBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport
/-! Static named body coverage retains the actual prepared body carrier. Its
terminal, formation and scoped alternatives derive the same physical body ports. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport
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
      (support : CallableIndexedOwnedPreparedStagedPhysicalMixedNamedTerminalSupport.Support
        (headers := headers) (stages := stages) (semanticFaults := semanticFaults) header terminal) :
      Support header (of_terminal terminal)
  | formation (terminal : Terminal header)
      (support : CallableIndexedOwnedPreparedStagedPhysicalNamedFormationSupport.Support
        (bodyRegistry := bodyRegistry) (stages := stages) (semanticFaults := semanticFaults) header terminal)
      (globals : header.globals = compiled.indexed.base.globals.length) :
      Support header (of_terminal terminal)
  | scoped (body : Body header)
      (receipt : CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.Receipt header)
      (compilation : body.compilation = .canonicalBranching receipt)
      (support : CallableIndexedOwnedPreparedStagedPhysicalMixedNamedScopedStaticSupport.Support
        headers header stages receipt semanticFaults) : Support header body

/-- The previous terminal API embeds without changing any receipt. -/
def of_terminal_support {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (terminal : Terminal header)
    (support : Sum (CallableIndexedOwnedPreparedStagedPhysicalMixedNamedTerminalSupport.Support
      (headers := headers) (stages := stages) (semanticFaults := semanticFaults) header terminal)
      { _support : CallableIndexedOwnedPreparedStagedPhysicalNamedFormationSupport.Support
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
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {receiving : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
  {faults : RecursiveStageMeaning.FaultRep}
  {child : Staging.Recursive.Scope} (selected : stages.Closure header.function child)
local notation "functions" => CallableIndexedOwnedPhysicalCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

variable (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)
  (assignmentInterpretation : PreparedAssignmentDiagnosticAuthority.Interprets compiled receiving
    (fun reason token => faults (.semantic reason) token))

include support profile wellFormed extension selected semantic assignmentInterpretation in
theorem preserves {budget : Nat}
    (children : ∀ size, size < budget →
      CallableIndexedOwnedPreparedStagedPhysicalMixedRootBounds.PreservesRootsAt
        (headers := headers) (keys := keys) model stages semanticFaults faults size) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow
      (headers := headers) (keys := keys) header model stages child faults budget := by
  cases support with
  | terminal terminal static =>
    exact CallableIndexedOwnedPreparedStagedPhysicalMixedNamedTerminalSupport.preserves
      static selected wellFormed children
  | formation terminal static globals =>
    exact CallableIndexedOwnedPreparedStagedPhysicalNamedFormationSupport.preserves
      profile static selected wellFormed globals
  | «scoped» body receipt compilation static =>
    exact CallableIndexedOwnedPreparedStagedPhysicalMixedNamedScopedBounds.preserves (semantic := semantic)
      (assignmentInterpretation := assignmentInterpretation)
      static body.aligned.globals functions
      (CallableIndexedLambdaValues.identity_faithful compiled.indexed)
      (CallableIndexedOwnedPhysicalFunctionViews.observations profile) selected extension body.layouts children

include support profile wellFormed extension selected semantic assignmentInterpretation in
theorem reflects {budget : Nat}
    (children : ∀ size, size < budget →
      CallableIndexedOwnedPreparedStagedPhysicalMixedRootBounds.ReflectsRootsAt
        (headers := headers) (keys := keys) model stages semanticFaults faults size) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow
      (headers := headers) (keys := keys) header model stages child faults budget := by
  cases support with
  | terminal terminal static =>
    exact CallableIndexedOwnedPreparedStagedPhysicalMixedNamedTerminalSupport.reflects
      static selected wellFormed children
  | formation terminal static globals =>
    exact CallableIndexedOwnedPreparedStagedPhysicalNamedFormationSupport.reflects
      profile static selected wellFormed globals
  | «scoped» body receipt compilation static =>
    exact CallableIndexedOwnedPreparedStagedPhysicalMixedNamedScopedBounds.reflects (semantic := semantic)
      (assignmentInterpretation := assignmentInterpretation)
      static body.aligned.globals functions
      (CallableIndexedOwnedPhysicalFunctionViews.runtime_views profile)
      (CallableIndexedLambdaValues.identity_faithful compiled.indexed)
      (CallableIndexedOwnedPhysicalFunctionViews.observations profile) selected extension body.layouts children

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalCoercedDirectRawBounds
/-! Every raw argument and named body comes from the same physical numerical
family. The original call metadata and conversion partition remain unchanged. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalCoercedDirectRawBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedPreparedStagedPhysicalMixedRootStaticSupport (CoercedDirectRoot RootAt)
open CallableIndexedOwnedPreparedStagedPhysicalMixedRootBounds
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
  have rows := CallableIndexedOwnedPreparedStagedRawDirectAuthority.Ready.source_types
    root.actual root.port.toReady root.wellFormed root.runtime.signatures application
  exact (tree_types root.argumentTree root.unique typed).trans rows.1

theorem preserves (budget : Nat)
    (children : ∀ size, size < budget → PreservesRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults faults size)
    (namedBodies : ∀ size, size ≤ budget → ∀ {child : Staging.Recursive.Scope},
      stages.Closure root.port.header.function child →
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow
        (headers := headers) (keys := keys) root.port.header model stages child faults size)
    (size : Nat) (within : size ≤ budget) :
    CallableIndexedOwnedPreparedStagedPhysicalRawDirectHeadBounds.RawPreservesAt
      (context := context) (receiving := receiving) owner root.actual callerBridge functions faults stages size := by
  have childMeaning : PreservesBelow (callerBridge).forgetSlots context model
      stages invocation root.argumentCertificate faults size := by
    intro smaller strict current id code member
    obtain ⟨type, ⟨supported⟩⟩ := root.argumentRoots member
    exact children smaller (Nat.lt_of_lt_of_le strict within)
      (RootAt.ofRoot supported) owner keyPhysical ⟨rfl, rfl, rfl⟩
  exact CallableIndexedOwnedPreparedStagedPhysicalRawDirectHeadBounds.preserves
    owner root.actual root.port.toPort root.port.evidence callerBridge keyPhysical
    (fun state => state.physical) functions faults root.unique root.wellFormed root.runtime root.covers
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
    CallableIndexedOwnedPreparedStagedPhysicalRawDirectHeadBounds.RawReflectsAt
      (context := context) (receiving := receiving) owner root.actual callerBridge functions faults stages size := by
  subst stages
  have childMeaning : ReflectsBelow (callerBridge).forgetSlots context model
      (RecursiveNamedPreparedStageScopes.registry stagePrepared) invocation root.argumentCertificate faults size := by
    intro smaller strict current id code member
    obtain ⟨type, ⟨supported⟩⟩ := root.argumentRoots member
    exact children smaller (Nat.lt_of_lt_of_le strict within)
      (RootAt.ofRoot supported) owner keyPhysical ⟨rfl, rfl, rfl⟩
  exact CallableIndexedOwnedPreparedStagedPhysicalRawDirectHeadBounds.reflects
    owner root.actual root.port.toPort root.port.evidence callerBridge keyPhysical
    (fun state => state.physical) functions faults root.unique root.wellFormed root.runtime root.covers
    stagePrepared descriptor
    size (argument_types root ▸ root.argumentTree) childMeaning
    (fun selected => namedBodies size within selected)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalCoercedDirectRawBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalCoercionMethodBounds
/-! The shared numerical induction supplies every conversion body from the
actual terminal packet, preserving the exact SourceAt and reached caller. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalCoercionMethodBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedPreparedStagedPhysicalMixedRootBounds
open CallableIndexedOwnedPreparedStagedPhysicalMixedRootStaticSupport (CoercionMethods)
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
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
  {source target : TypeSystem.Ty} {input output : SourceCoreBasic.LoweredExpr}
  {steps : List CoercionStep} {calls : List CallableCoercionSpine.Call}
  (chain : Chain compiled project compilation caller available scope node policy context invocation stages
    source target input steps output calls)
  (support : CoercionMethods headers semanticFaults chain)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

variable (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)

include keyPhysical wellFormed support in
theorem source_bodies (budget : Nat)
    (children : ∀ size, size < budget → PreservesRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults faults size) :
    CallableIndexedOwnedPreparedStagedCoercionPathBounds.SourceBodies
      (headers := headers) (receiving := receiving) owner functions faults chain budget := by
  induction chain with
  | nil => trivial
  | cons step port valid tail ih =>
      obtain ⟨⟨packet, sourceAt, static⟩, remaining⟩ := support
      refine ⟨?_, ih remaining⟩
      intro mapping world heap store callerScope canonical administrative arguments payloads caller installed
        _parameters heapTyped argumentsTyped stable child selected
      have packetArguments : Dynamic.ValuesHaveTypes port.principal.sourceFunction.context heap
          arguments packet.sourceAt.types := by
        simpa only [sourceAt] using argumentsTyped
      simpa only [CallableIndexedOwnedPreparedStagedMethodBodies.Packet.sourceAt, sourceAt] using
        CallableIndexedOwnedPreparedStagedMethodTerminalBounds.source_continuation
          port.principal packet static wellFormed functions selected installed
          owner keyPhysical caller heapTyped packetArguments stable budget
          (fun size smaller _context _invocation _scope _expression _lowered root owner physical =>
            children size smaller
              (CallableIndexedOwnedPreparedStagedPhysicalMixedRootStaticSupport.RootAt.ofMethod root) owner physical)

include keyPhysical wellFormed support in
theorem native_bodies (budget : Nat)
    (children : ∀ size, size < budget → ReflectsRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults faults size) :
    CallableIndexedOwnedPreparedStagedCoercionPathBounds.NativeBodies
      (headers := headers) (receiving := receiving) owner functions faults chain budget := by
  induction chain with
  | nil => trivial
  | cons step port valid tail ih =>
      obtain ⟨⟨packet, sourceAt, static⟩, remaining⟩ := support
      refine ⟨?_, ih remaining⟩
      intro mapping world heap store callerScope canonical administrative arguments payloads caller installed
        _parameters heapTyped argumentsTyped stable child selected
      have packetArguments : Dynamic.ValuesHaveTypes port.principal.sourceFunction.context heap
          arguments packet.sourceAt.types := by
        simpa only [sourceAt] using argumentsTyped
      simpa only [CallableIndexedOwnedPreparedStagedMethodBodies.Packet.sourceAt, sourceAt] using
        CallableIndexedOwnedPreparedStagedMethodTerminalBounds.native_continuation
          port.principal packet static wellFormed functions selected installed
          owner keyPhysical caller heapTyped packetArguments stable budget
          (fun size smaller _context _invocation _scope _expression _lowered root owner physical =>
            children size smaller
              (CallableIndexedOwnedPreparedStagedPhysicalMixedRootStaticSupport.RootAt.ofMethod root) owner physical)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalCoercionMethodBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalMixedCallerFamily
/-! One strong induction closes ordinary calls, selected methods and retained indirect callees
at actual complete physical cache states. Every body continuation comes from
an authentic static packet and a strictly smaller expression proof. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalMixedCallerFamily
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedPreparedStagedPhysicalMixedRootBounds
open CallableIndexedOwnedPreparedStagedCallerHeadHandlers
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedOperatorMethodCertificates (Receipt)
open CallableIndexedOwnedPreparedStagedOperatorMethodAuthority (Port)
open CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport (Packet Support)

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
    ∃ packet : Packet port.principal, packet.sourceAt = port.sourceAt ∧
      Support port.principal packet headers stages semanticFaults

/-- Method bodies may retain either an actual terminal or scoped compiler packet. -/
def MixedMethodSupports : Prop :=
  ∀ {policy body fuel compilation source scope id reasonAt lowered context caller}
    (receipt : Receipt policy body fuel compilation (.initial compiled.compatible.checked) source scope id reasonAt lowered)
    (port : Port (compiled := compiled) receipt context caller stages),
    ∃ packet : CallableIndexedOwnedPreparedStagedMethodBodies.Packet port.principal,
      packet.sourceAt = port.sourceAt ∧
      CallableIndexedOwnedPreparedStagedMethodBodies.Support port.principal packet headers stages semanticFaults

/-- Existing terminal method support embeds without changing its static receipts. -/
theorem MethodSupports.toMixed
    (support : MethodSupports (compiled := compiled) (headers := headers)
      (stages := stages) (semanticFaults := semanticFaults)) :
    MixedMethodSupports (compiled := compiled) (headers := headers)
      (stages := stages) (semanticFaults := semanticFaults) := by
  intro policy body fuel compilation source scope id reasonAt lowered context caller receipt port
  obtain ⟨packet, sourceAt, supported⟩ := support receipt port
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
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedPhysicalCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry completion.result.context.registry)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (terminals : ∀ header, header ∈ headers → Terminal header)
  (namedSupport : ∀ header (member : header ∈ headers),
    Sum (CallableIndexedOwnedPreparedStagedPhysicalMixedNamedTerminalSupport.Support (headers := headers)
      (stages := stages) (semanticFaults := semanticFaults) header (terminals header member))
      { _support : CallableIndexedOwnedPreparedStagedPhysicalNamedFormationSupport.Support
          (bodyRegistry := bodyRegistry) (stages := stages) (semanticFaults := semanticFaults)
          header (terminals header member) // header.globals = compiled.indexed.base.globals.length })
  (bodies : ∀ header, header ∈ headers → CallableIndexedOwnedPreparedStagedNamedBodies.Body header)
  (bodySupport : ∀ header (member : header ∈ headers),
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.Support
      (headers := headers) (bodyRegistry := bodyRegistry) (stages := stages)
      (semanticFaults := semanticFaults) header (bodies header member))
  (closurePackets : ∀ {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPhysicalClosureAssociation.Association headers keys bodyRegistry semanticFaults
      mapping world function native bindings parameter result),
    CallableIndexedOwnedPreparedStagedPhysicalClosureStaticSupport.PacketFor association.original stages)
  (closureSupport : ∀ {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPhysicalClosureAssociation.Association headers keys bodyRegistry semanticFaults
      mapping world function native bindings parameter result),
    CallableIndexedOwnedPreparedStagedPhysicalClosureStaticSupport.SupportFor association.original stages (closurePackets association))
  (owners : ∀ owner : OwnedKey keys, CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  (methodSupport : MethodSupports (compiled := compiled) (headers := headers) (stages := stages) (semanticFaults := semanticFaults))
  (mixedMethodSupport : MixedMethodSupports (compiled := compiled) (headers := headers) (stages := stages) (semanticFaults := semanticFaults))

local notation "functions" => CallableIndexedOwnedPhysicalCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include closurePackets closureSupport owners stagePrepared receiver profile wellFormed observations extension semantic bodies bodySupport mixedMethodSupport in
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
      exact CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.preserves (semantic := semantic)
        (assignmentInterpretation := PreparedAssignmentDiagnosticAuthority.interprets receiver)
        (bodySupport header member) profile wellFormed extension selected
        (fun smaller strict => ih smaller (Nat.lt_of_lt_of_le strict within))
    cases root.support with
    | ordinary support =>
      have directHeads : PreservesDirect callerBridge.forgetSlots model stages callFaults budget support.certificate := by
        intro fuel current id callee ids instantiation code types compiler path calleeTyped application sequence size within childMeaning
        obtain ⟨port⟩ := support.directReady compiler path
        have rows := CallableIndexedOwnedPreparedStagedDirectCallAuthority.Ready.source_types
          compiler port.toReady wellFormed support.runtime.signatures application
        have ordered := rows.1 ▸ sequence
        intro current child code point
        obtain ⟨rfl, rfl, rfl⟩ := point
        exact CallableIndexedOwnedPreparedStagedPhysicalDirectHeadBounds.preserves
          owner compiler port.toPort port.evidence callerBridge keyPhysical (fun state => state.physical)
          functions callFaults support.unique wellFormed support.runtime support.covers
          size ordered childMeaning
          (fun selected => namedBodies size within port.header port.member selected) ⟨rfl, rfl, rfl⟩
      have methodHeads : PreservesMethod callerBridge.forgetSlots model stages callFaults budget support.certificate := by
        intro fuel current id code types compiler path sequence size within childMeaning
        obtain ⟨port⟩ := support.methodReady compiler path
        obtain ⟨packet, sourceAtEq, static⟩ := mixedMethodSupport compiler port
        have bodies : CallableIndexedOwnedPreparedStagedMethodHeadBounds.SourceBodies
            (headers := headers) (receiving := completion.result.context.registry) owner compiler port functions callFaults size := by
          intro mapping world heap store callerScope canonical administrative arguments payloads caller installed _parameters
            heapTyped argumentsTyped stable child selected
          have packetArguments : Dynamic.ValuesHaveTypes port.principal.sourceFunction.context heap arguments packet.sourceAt.types := by
            simpa only [sourceAtEq] using argumentsTyped
          simpa only [sourceAtEq] using
            CallableIndexedOwnedPreparedStagedMethodBodyBounds.source_continuation (semantic := semantic)
              (assignmentInterpretation := PreparedAssignmentDiagnosticAuthority.interprets receiver)
              port.principal packet static wellFormed functions
              (CallableIndexedLambdaValues.identity_faithful compiled.indexed)
              (CallableIndexedOwnedPhysicalFunctionViews.observations profile) selected installed owner keyPhysical caller
              heapTyped packetArguments stable extension size
              (fun smaller strict => ih smaller (Nat.lt_of_lt_of_le strict within))
        intro actualScope actualId actualCode point actual found typed
        obtain ⟨rfl, rfl, rfl⟩ := point
        cases Option.some.inj (found.symm.trans compiler.metadata.found)
        have rows := CallableIndexedOwnedPreparedStagedMethodArgumentRows.raw_types compiler port
          wellFormed support.runtime support.unique typed
        have ordered := tree_types sequence support.unique rows.1 ▸ sequence
        intro mapping world administrativeContext environment canonical actualEnvironment actualContext before store ξ outcome after
        exact CallableIndexedOwnedPreparedStagedMethodHeadBounds.preserves
          owner compiler port callerBridge keyPhysical.frame (fun state => state.physical)
          (fun state => state.base.property) functions callFaults support.unique wellFormed
          support.runtime support.covers size ordered childMeaning bodies ⟨rfl, rfl, rfl⟩ found typed
      have indirectHeads : PreservesIndirect callerBridge.forgetSlots model stages callFaults budget support.certificate := by
        intro fuel current id callee ids metadata code types compiler path sequence size within childMeaning
        obtain ⟨port⟩ := support.callsReady compiler path
        have calleeCertified : RecursiveStageTupleMeaning.Entries current compiler.entries
            current callee compiler.calleeCode := ⟨rfl, by simp [CallableIndirectCallCertificates.Receipt.entries]⟩
        intro actualScope actualId actualCode point
        obtain ⟨rfl, rfl, rfl⟩ := point
        exact CallableIndexedOwnedPreparedStagedPhysicalIndirectHeadBounds.preserves (semantic := semantic)
          callerBridge.forgetSlots (fun state => state.physical) owners receiver stagePrepared rfl profile
          wellFormed support.runtime support.covers support.unique support.actualFunctionType
          observations closurePackets closureSupport bodies
          compiler port calleeCertified sequence size childMeaning budget ih (namedBodies size within) within ⟨rfl, rfl, rfl⟩
      intro current id code point
      exact CallableIndexedOwnedPreparedStagedSharedRecursiveCallerBounds.preserves_reached_with_functions
        callerBridge.forgetSlots receiver functions wellFormed support.runtime support.covers support.unique
        observations (CallableIndexedOwnedPhysicalFunctionViews.runtime_views profile)
        (CallableIndexedOwnedPhysicalFunctionViews.observations profile) extension semantic support.sameLedger support.runtimeLedger support.uninitialized
        budget support.certificate (.root (by simp)) directHeads methodHeads support.indexReady indirectHeads
        budget (Nat.le_refl _) point
    | coercedDirect support =>
      have rawMeaning := CallableIndexedOwnedPreparedStagedPhysicalCoercedDirectRawBounds.preserves
        support owner keyPhysical functions callFaults
        budget ih (fun size within {_} selected => namedBodies size within support.port.header support.port.member selected)
      have conversionBodies := CallableIndexedOwnedPreparedStagedPhysicalCoercionMethodBounds.source_bodies
        owner keyPhysical functions callFaults wellFormed support.chain support.methods budget ih
      intro current id code point actual found typed
      obtain ⟨rfl, rfl, rfl⟩ := point
      cases Option.some.inj (found.symm.trans support.actual.found)
      intro mapping world administrativeContext environment canonical actualEnvironment actualContext before store ξ outcome after
        environments heaps locals agrees actualTyped initial admitted trace
      exact CallableIndexedOwnedPreparedStagedCoercedDirectExpressionBounds.preserves
        owner support.actual callerBridge (fun state => state.physical) (fun state => state.base.property)
        keyPhysical.frame functions callFaults support.chain support.nonempty support.unique wellFormed
        support.runtime support.covers support.ledger typed environments heaps locals agrees actualTyped initial admitted
        budget rawMeaning conversionBodies trace (Nat.le_refl _)


include closurePackets closureSupport owners receiver stagePrepared profile wellFormed observations extension semantic bodies bodySupport mixedMethodSupport in
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
      exact CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.reflects (semantic := semantic)
        (assignmentInterpretation := PreparedAssignmentDiagnosticAuthority.interprets receiver)
        (bodySupport header member) profile wellFormed extension selected
        (fun smaller strict => ih smaller (Nat.lt_of_lt_of_le strict within))
    cases root.support with
    | ordinary support =>
      have directHeads : ReflectsDirect callerBridge.forgetSlots model (RecursiveNamedPreparedStageScopes.registry stagePrepared) callFaults budget support.certificate := by
        intro fuel current id callee ids instantiation code types compiler path calleeTyped application sequence size within childMeaning
        obtain ⟨port⟩ := support.directReady compiler path
        have rows := CallableIndexedOwnedPreparedStagedDirectCallAuthority.Ready.source_types
          compiler port.toReady wellFormed support.runtime.signatures application
        have ordered := rows.1 ▸ sequence
        obtain ⟨descriptor⟩ := named_descriptor port.header
        intro current child code point
        obtain ⟨rfl, rfl, rfl⟩ := point
        exact CallableIndexedOwnedPreparedStagedPhysicalDirectHeadBounds.reflects
          owner compiler port.toPort port.evidence callerBridge keyPhysical (fun state => state.physical)
          functions callFaults support.unique wellFormed support.runtime support.covers stagePrepared descriptor
          size ordered childMeaning
          (fun selected => namedBodies size within port.header port.member selected) ⟨rfl, rfl, rfl⟩
      have methodHeads : ReflectsMethod callerBridge.forgetSlots model (RecursiveNamedPreparedStageScopes.registry stagePrepared) callFaults budget support.certificate := by
        intro fuel current id code types compiler path sequence size within childMeaning
        obtain ⟨port⟩ := support.methodReady compiler path
        obtain ⟨packet, sourceAtEq, static⟩ := mixedMethodSupport compiler port
        have bodies : CallableIndexedOwnedPreparedStagedMethodHeadBounds.NativeBodies
            (headers := headers) (receiving := completion.result.context.registry) owner compiler port functions callFaults size := by
          intro mapping world heap store callerScope canonical administrative arguments payloads caller installed _parameters
            heapTyped argumentsTyped stable child selected
          have packetArguments : Dynamic.ValuesHaveTypes port.principal.sourceFunction.context heap arguments packet.sourceAt.types := by
            simpa only [sourceAtEq] using argumentsTyped
          simpa only [sourceAtEq] using
            CallableIndexedOwnedPreparedStagedMethodBodyBounds.native_continuation (semantic := semantic)
              (assignmentInterpretation := PreparedAssignmentDiagnosticAuthority.interprets receiver)
              port.principal packet static wellFormed functions
              (CallableIndexedOwnedPhysicalFunctionViews.runtime_views profile)
              (CallableIndexedLambdaValues.identity_faithful compiled.indexed)
              (CallableIndexedOwnedPhysicalFunctionViews.observations profile) selected installed owner keyPhysical caller
              heapTyped packetArguments stable extension size
              (fun smaller strict => ih smaller (Nat.lt_of_lt_of_le strict within))
        intro actualScope actualId actualCode point actual found typed
        obtain ⟨rfl, rfl, rfl⟩ := point
        cases Option.some.inj (found.symm.trans compiler.metadata.found)
        have rows := CallableIndexedOwnedPreparedStagedMethodArgumentRows.raw_types compiler port
          wellFormed support.runtime support.unique typed
        have ordered := tree_types sequence support.unique rows.1 ▸ sequence
        intro mapping world administrativeContext environment canonical actualEnvironment actualContext before store ξ value finalStore
        exact CallableIndexedOwnedPreparedStagedMethodHeadBounds.reflects
          owner compiler port callerBridge keyPhysical.frame (fun state => state.physical)
          (fun state => state.base.property) functions callFaults support.unique wellFormed
          support.runtime support.covers size ordered childMeaning bodies ⟨rfl, rfl, rfl⟩ found typed
      have indirectHeads : ReflectsIndirect callerBridge.forgetSlots model (RecursiveNamedPreparedStageScopes.registry stagePrepared) callFaults budget support.certificate := by
        intro fuel current id callee ids metadata code types compiler path sequence size within childMeaning
        obtain ⟨port⟩ := support.callsReady compiler path
        have calleeCertified : RecursiveStageTupleMeaning.Entries current compiler.entries
            current callee compiler.calleeCode := ⟨rfl, by simp [CallableIndirectCallCertificates.Receipt.entries]⟩
        intro actualScope actualId actualCode point
        obtain ⟨rfl, rfl, rfl⟩ := point
        exact CallableIndexedOwnedPreparedStagedPhysicalIndirectHeadBounds.reflects (semantic := semantic)
          callerBridge.forgetSlots (fun state => state.physical) owners receiver stagePrepared rfl profile
          wellFormed support.runtime support.covers support.unique support.actualFunctionType
          observations closurePackets closureSupport bodies
          rfl compiler port calleeCertified sequence size childMeaning budget ih (namedBodies size within) within ⟨rfl, rfl, rfl⟩
      intro current id code point
      exact CallableIndexedOwnedPreparedStagedSharedRecursiveCallerBounds.reflects_reached_with_functions
        callerBridge.forgetSlots receiver functions wellFormed support.runtime support.covers support.unique
        observations (CallableIndexedOwnedPhysicalFunctionViews.runtime_views profile)
        (CallableIndexedOwnedPhysicalFunctionViews.observations profile) extension semantic support.sameLedger support.runtimeLedger support.uninitialized
        budget support.certificate (.root (by simp)) directHeads methodHeads support.indexReady indirectHeads
        budget (Nat.le_refl _) point
    | coercedDirect support =>
      obtain ⟨descriptor⟩ := named_descriptor support.port.header
      have rawMeaning := CallableIndexedOwnedPreparedStagedPhysicalCoercedDirectRawBounds.reflects
        support owner keyPhysical functions callFaults
        stagePrepared rfl descriptor
        budget ih (fun size within {_} selected => namedBodies size within support.port.header support.port.member selected)
      have conversionBodies := CallableIndexedOwnedPreparedStagedPhysicalCoercionMethodBounds.native_bodies
        owner keyPhysical functions callFaults wellFormed support.chain support.methods budget ih
      intro current id code point actual found typed
      obtain ⟨rfl, rfl, rfl⟩ := point
      cases Option.some.inj (found.symm.trans support.actual.found)
      intro mapping world administrativeContext environment canonical actualEnvironment actualContext before store ξ value finalStore
        environments heaps locals agrees actualTyped initial admitted trace
      exact CallableIndexedOwnedPreparedStagedCoercedDirectExpressionBounds.reflects
        owner support.actual callerBridge (fun state => state.physical) (fun state => state.base.property)
        keyPhysical.frame functions callFaults support.chain support.nonempty support.unique wellFormed
        support.runtime support.covers typed environments heaps locals agrees actualTyped initial admitted
        budget rawMeaning conversionBodies trace (Nat.le_refl _)


include closurePackets closureSupport owners receiver stagePrepared profile wellFormed observations extension semantic bodies bodySupport methodSupport in
/-- The existing named-body API embeds its terminal method packets. -/
theorem preserves_with_bodies (size : Nat) :
    PreservesRootsAt (headers := headers) (keys := keys) model stages semanticFaults callFaults size :=
  preserves_with_methods receiver stagePrepared profile wellFormed observations extension semantic
    bodies bodySupport closurePackets closureSupport owners methodSupport.toMixed size

include closurePackets closureSupport owners receiver stagePrepared profile wellFormed observations extension semantic bodies bodySupport methodSupport in
/-- The existing named-body API embeds its terminal method packets. -/
theorem reflects_with_bodies (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared) (size : Nat) :
    ReflectsRootsAt (headers := headers) (keys := keys) model stages semanticFaults callFaults size :=
  reflects_with_methods receiver stagePrepared profile wellFormed observations extension semantic
    bodies bodySupport closurePackets closureSupport owners methodSupport.toMixed stageEq size

include closurePackets closureSupport owners receiver stagePrepared profile wellFormed observations extension semantic terminals namedSupport methodSupport in
/-- Existing terminal families delegate to the same body-generic induction. -/
theorem preserves (size : Nat) :
    PreservesRootsAt (headers := headers) (keys := keys) model stages semanticFaults callFaults size :=
  preserves_with_bodies receiver stagePrepared profile wellFormed observations extension semantic
    (fun header member => CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (terminals header member))
    (fun header member => CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.of_terminal_support
      (terminals header member) (namedSupport header member))
    closurePackets closureSupport owners methodSupport size

include closurePackets closureSupport owners receiver stagePrepared profile wellFormed observations extension semantic terminals namedSupport methodSupport in
/-- Existing terminal reflection retains its original arguments and conclusion. -/
theorem reflects (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared) (size : Nat) :
    ReflectsRootsAt (headers := headers) (keys := keys) model stages semanticFaults callFaults size :=
  reflects_with_bodies receiver stagePrepared profile wellFormed observations extension semantic
    (fun header member => CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (terminals header member))
    (fun header member => CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.of_terminal_support
      (terminals header member) (namedSupport header member))
    closurePackets closureSupport owners methodSupport stageEq size

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalMixedCallerFamily
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalMixedNamedFamilyPorts
/-! The closed physical mixed family supplies named body ports for actual
terminal expressions, genuine lambda formation or scoped statements at every reached registry. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalMixedNamedFamilyPorts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedPhysicalMixedCallerFamily (MethodSupports MixedMethodSupports)

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
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedPhysicalCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry completion.result.context.registry)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (terminals : ∀ header, header ∈ headers → Terminal header)
  (namedSupport : ∀ header (member : header ∈ headers),
    Sum (CallableIndexedOwnedPreparedStagedPhysicalMixedNamedTerminalSupport.Support (headers := headers)
      (stages := stages) (semanticFaults := semanticFaults) header (terminals header member))
      { _support : CallableIndexedOwnedPreparedStagedPhysicalNamedFormationSupport.Support
          (bodyRegistry := bodyRegistry) (stages := stages) (semanticFaults := semanticFaults)
          header (terminals header member) // header.globals = compiled.indexed.base.globals.length })
  (bodies : ∀ header, header ∈ headers → CallableIndexedOwnedPreparedStagedNamedBodies.Body header)
  (bodySupport : ∀ header (member : header ∈ headers),
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.Support
      (headers := headers) (bodyRegistry := bodyRegistry) (stages := stages)
      (semanticFaults := semanticFaults) header (bodies header member))
  (closurePackets : ∀ {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPhysicalClosureAssociation.Association headers keys bodyRegistry semanticFaults
      mapping world function native bindings parameter result),
    CallableIndexedOwnedPreparedStagedPhysicalClosureStaticSupport.PacketFor association.original stages)
  (closureSupport : ∀ {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPhysicalClosureAssociation.Association headers keys bodyRegistry semanticFaults
      mapping world function native bindings parameter result),
    CallableIndexedOwnedPreparedStagedPhysicalClosureStaticSupport.SupportFor association.original stages (closurePackets association))
  (owners : ∀ owner : OwnedKey keys, CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  (methodSupport : MethodSupports (compiled := compiled) (headers := headers) (stages := stages) (semanticFaults := semanticFaults))
  (mixedMethodSupport : MixedMethodSupports (compiled := compiled) (headers := headers) (stages := stages) (semanticFaults := semanticFaults))

local notation "functions" => CallableIndexedOwnedPhysicalCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include closurePackets closureSupport owners receiver stagePrepared profile wellFormed observations extension semantic bodies bodySupport mixedMethodSupport in
theorem preserves_with_methods
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (member : header ∈ headers) {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow
      (headers := headers) (keys := keys) header model stages child callFaults budget := by
  exact CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.preserves (semantic := semantic)
        (assignmentInterpretation := PreparedAssignmentDiagnosticAuthority.interprets receiver)
    (bodySupport header member) profile wellFormed extension selected
    (fun size _ => CallableIndexedOwnedPreparedStagedPhysicalMixedCallerFamily.preserves_with_methods
      receiver stagePrepared profile wellFormed observations extension semantic bodies bodySupport
      closurePackets closureSupport owners mixedMethodSupport size)

include closurePackets closureSupport owners receiver stagePrepared profile wellFormed observations extension semantic bodies bodySupport mixedMethodSupport in
theorem reflects_with_methods (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (member : header ∈ headers) {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow
      (headers := headers) (keys := keys) header model stages child callFaults budget := by
  exact CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.reflects (semantic := semantic)
        (assignmentInterpretation := PreparedAssignmentDiagnosticAuthority.interprets receiver)
    (bodySupport header member) profile wellFormed extension selected
    (fun size _ => CallableIndexedOwnedPreparedStagedPhysicalMixedCallerFamily.reflects_with_methods
      receiver stagePrepared profile wellFormed observations extension semantic bodies bodySupport
      closurePackets closureSupport owners mixedMethodSupport stageEq size)

include closurePackets closureSupport owners receiver stagePrepared profile wellFormed observations extension semantic bodies bodySupport methodSupport in
theorem preserves_with_bodies
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (member : header ∈ headers) {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow
      (headers := headers) (keys := keys) header model stages child callFaults budget := by
  exact CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.preserves (semantic := semantic)
        (assignmentInterpretation := PreparedAssignmentDiagnosticAuthority.interprets receiver)
    (bodySupport header member) profile wellFormed extension selected
    (fun size _ => CallableIndexedOwnedPreparedStagedPhysicalMixedCallerFamily.preserves_with_bodies
      receiver stagePrepared profile wellFormed observations extension semantic bodies bodySupport
      closurePackets closureSupport owners methodSupport size)

include closurePackets closureSupport owners receiver stagePrepared profile wellFormed observations extension semantic bodies bodySupport methodSupport in
theorem reflects_with_bodies (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (member : header ∈ headers) {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow
      (headers := headers) (keys := keys) header model stages child callFaults budget := by
  exact CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.reflects (semantic := semantic)
        (assignmentInterpretation := PreparedAssignmentDiagnosticAuthority.interprets receiver)
    (bodySupport header member) profile wellFormed extension selected
    (fun size _ => CallableIndexedOwnedPreparedStagedPhysicalMixedCallerFamily.reflects_with_bodies
      receiver stagePrepared profile wellFormed observations extension semantic bodies bodySupport
      closurePackets closureSupport owners methodSupport stageEq size)

include closurePackets closureSupport owners receiver stagePrepared profile wellFormed observations extension semantic terminals namedSupport methodSupport in
/-- The previous terminal family keeps its original public body-port API. -/
theorem preserves
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (member : header ∈ headers) {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow
      (headers := headers) (keys := keys) header model stages child callFaults budget :=
  preserves_with_bodies receiver stagePrepared profile wellFormed observations extension semantic
    (fun header member => CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (terminals header member))
    (fun header member => CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.of_terminal_support
      (terminals header member) (namedSupport header member))
    closurePackets closureSupport owners methodSupport header member selected budget

include closurePackets closureSupport owners receiver stagePrepared profile wellFormed observations extension semantic terminals namedSupport methodSupport in
/-- The previous terminal family keeps its original public body-port API. -/
theorem reflects (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (member : header ∈ headers) {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow
      (headers := headers) (keys := keys) header model stages child callFaults budget :=
  reflects_with_bodies receiver stagePrepared profile wellFormed observations extension semantic
    (fun header member => CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (terminals header member))
    (fun header member => CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.of_terminal_support
      (terminals header member) (namedSupport header member))
    closurePackets closureSupport owners methodSupport stageEq header member selected budget

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalMixedNamedFamilyPorts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalNamedFamilyPorts
/-! Actual ordinary named bodies obtain both physical invocation ports from
the closed numeric family. Public adapters need only the genuine static packets. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalNamedFamilyPorts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  {stages : Staging.Recursive.Registry}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry completion.result.context.registry)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (terminals : ∀ header, header ∈ headers → Terminal header)
  (namedSupport : ∀ header (member : header ∈ headers),
    CallableIndexedOwnedPreparedStagedPhysicalNamedTerminalSupport.Support (headers := headers)
      (stages := stages) (semanticFaults := semanticFaults) header (terminals header member))
  (methodSupport : CallableIndexedOwnedPreparedStagedPhysicalCallerFamily.MethodSupports
    (compiled := compiled) (headers := headers) (stages := stages) (semanticFaults := semanticFaults))

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include receiver profile wellFormed observations extension semantic terminals namedSupport methodSupport in
theorem preserves (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (member : header ∈ headers) {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow
      (headers := headers) (keys := keys) header model stages child callFaults budget :=
  CallableIndexedOwnedPreparedStagedPhysicalNamedTerminalSupport.preserves
    (namedSupport header member) selected wellFormed
    (fun size _ => CallableIndexedOwnedPreparedStagedPhysicalCallerFamily.preserves
      receiver profile wellFormed observations extension semantic terminals namedSupport methodSupport size)

include receiver stagePrepared profile wellFormed observations extension semantic terminals namedSupport methodSupport in
theorem reflects (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (member : header ∈ headers) {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow
      (headers := headers) (keys := keys) header model stages child callFaults budget :=
  CallableIndexedOwnedPreparedStagedPhysicalNamedTerminalSupport.reflects
    (namedSupport header member) selected wellFormed
    (fun size _ => CallableIndexedOwnedPreparedStagedPhysicalCallerFamily.reflects
      receiver stagePrepared profile wellFormed observations extension semantic terminals namedSupport methodSupport stageEq size)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalNamedFamilyPorts
end
