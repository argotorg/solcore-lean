import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalMixedRootBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedBodyBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch

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
