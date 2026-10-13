import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodies
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalMixedNamedTerminalSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalNamedFormationSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalMixedNamedScopedBounds

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

include support profile wellFormed extension selected in
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
    exact CallableIndexedOwnedPreparedStagedPhysicalMixedNamedScopedBounds.preserves
      static body.aligned.globals functions selected extension body.layouts children

include support profile wellFormed extension selected in
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
    exact CallableIndexedOwnedPreparedStagedPhysicalMixedNamedScopedBounds.reflects
      static body.aligned.globals functions selected extension body.layouts children

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport
