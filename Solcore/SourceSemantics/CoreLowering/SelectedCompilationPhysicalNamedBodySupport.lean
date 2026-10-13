import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodies
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalMixedNamedTerminalSupport
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalNamedFormationSupport
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedScopedBounds

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
local notation "functions" => CallableIndexedOwnedPhysicalCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

include support profile certified extension selected in
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
    exact SelectedCompilationNamedScopedBounds.preserves
      static body.aligned.globals functions selected extension body.layouts children

include support profile certified extension selected in
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
    exact SelectedCompilationNamedScopedBounds.reflects
      static body.aligned.globals functions selected extension body.layouts children

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalNamedBodySupport
