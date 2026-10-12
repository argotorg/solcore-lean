import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderSourceTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedInitialContextValidity
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLambdaFormationHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedChildBounds

/-! A named terminal body retains either the existing recursive expression
certificate or the exact ordinary lambda producer. The latter keeps its static
body support and needs the genuine zero-prefix inventory; dynamic captures
are obtained later from the actual parameter packet. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodySupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedContextualLambdaFormationReceipts (OrdinaryFormation)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
  (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
  (bodyRegistry : SourceCoreRawMetadata.Registry)
  (header : Header compiled (Program.ofChecked compiled.sourceProgram))
  (stages : Staging.Recursive.Registry) (terminal : Terminal header)
  (semanticFaults : FunctionCalls.FaultRep)

structure Formation where
  point : terminal.certificate = Point
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    terminal.expression terminal.receipt.child
  complete : RecursiveNamedCatalogNativeContexts.Complete
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers
  zero : ∀ owner : OwnedKey keys, owner.key.capturePrefix = 0
  actual : ∀ child, stages.Closure header.function child →
    Nonempty (OrdinaryFormation (registry := bodyRegistry) (faults := semanticFaults)
      header header.context child.evidence
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child)
  wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)

/-- One actual compiler occurrence suffices for every selected invocation:
selection preserves its evidence, and no runtime capture is supplied here. -/
theorem Formation.of_actual
    (point : terminal.certificate = Point
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
    (zero : ∀ owner : OwnedKey keys, owner.key.capturePrefix = 0)
    (actual : OrdinaryFormation (registry := bodyRegistry) (faults := semanticFaults)
      header header.context header.function.evidence
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    Formation headers keys bodyRegistry header stages terminal semanticFaults where
  point := point
  complete := complete
  zero := zero
  actual child selected := by
    rw [stages.evidence selected]
    exact ⟨actual⟩
  wellFormed := wellFormed

inductive LegacySupport where
  | recursive (static : CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.NamedSupport
      header stages terminal semanticFaults)
  | formation (static : Formation headers keys bodyRegistry header stages terminal semanticFaults)

inductive Support where
  | recursive (static : CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.NamedSupport
      header stages terminal semanticFaults)
  | formation (static : Formation headers keys bodyRegistry header stages terminal semanticFaults)
  | canonical (static : CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.NamedSupport
      (headers := headers) (keys := keys) stages semanticFaults header terminal)

variable {headers keys bodyRegistry header stages terminal semanticFaults}
  {receiving : SourceCoreRawMetadata.Registry}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (faults : RecursiveStageMeaning.FaultRep)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

private theorem original_source {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child) :
    child.source = CallableIndexedNamedGeneration.source header.named := by
  rw [stages.source selected]
  exact header.agreement.source

private theorem Formation.runtime
    (static : Formation headers keys bodyRegistry header stages terminal semanticFaults)
    {child : Staging.Recursive.Scope} (selected : stages.Closure header.function child) :
    Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) header.context child.source := by
  obtain ⟨facts, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate header static.wellFormed
  have original : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      header.function.context header.function.source := by
    rw [header.frame.context, header.frame.source]
    exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid
  rw [stages.source selected]
  exact original.transport (RecursiveNamedInitialContextValidity.mono_fields header.extended)

private theorem Formation.covers
    {child : Staging.Recursive.Scope} (selected : stages.Closure header.function child) :
    child.evidence.Covers header.context := by
  rw [stages.evidence selected]
  exact RecursiveNamedInitialContextValidity.covers header.frame header.extended

/-- The static lambda alternative closes the same named-child preservation
interface; the actual invocation still supplies the packet and capture state. -/
theorem Formation.preserves (static : Formation headers keys bodyRegistry header stages terminal semanticFaults)
    {child : Staging.Recursive.Scope} (selected : stages.Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedNamedChildBounds.PreservesBelow
      (headers := headers) (keys := keys) header model stages child terminal.certificate faults budget := by
  refine .nested terminal.aligned.globals static.zero ?_
  intro owner size _smaller current id lowered certified
  rw [static.point] at certified
  obtain ⟨rfl, rfl, rfl⟩ := certified
  exact CallableIndexedOwnedPreparedStagedLambdaFormationHeads.preserves
    header owner header.context child profile static.complete terminal.aligned.globals
    (RecursiveNamedLambdaFormationHeads.cached_capture_slots compiled headers) (static.zero owner)
    (original_source selected) (by rw [stages.source selected]; exact header.unique)
    static.wellFormed (static.runtime selected) (Formation.covers selected) faults size
    (static.actual child selected)

/-- Native formation produces its independent Source grade and the full
reached-state result of the current named body interface. -/
theorem Formation.reflects (static : Formation headers keys bodyRegistry header stages terminal semanticFaults)
    {child : Staging.Recursive.Scope} (selected : stages.Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedNamedChildBounds.ReflectsBelow
      (headers := headers) (keys := keys) header model stages child terminal.certificate faults budget := by
  refine .nested terminal.aligned.globals static.zero ?_
  intro owner size _smaller current id lowered certified
  rw [static.point] at certified
  obtain ⟨rfl, rfl, rfl⟩ := certified
  exact CallableIndexedOwnedPreparedStagedLambdaFormationHeads.reflects
    header owner header.context child profile static.complete terminal.aligned.globals
    (RecursiveNamedLambdaFormationHeads.cached_capture_slots compiled headers) (static.zero owner)
    (original_source selected)
    static.wellFormed (static.runtime selected) (Formation.covers selected) faults size
    (static.actual child selected)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodySupport
