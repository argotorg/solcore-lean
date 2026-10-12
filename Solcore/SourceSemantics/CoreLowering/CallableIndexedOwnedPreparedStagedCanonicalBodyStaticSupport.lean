import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCallerSlotForgetting
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaEntries
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedChildBounds

/-! Canonical roots retain compiler-selected Headers. Their laws quantify over
an actual caller carrying those global slots. Named terminals obtain this
receipt from the existing parameter packet, without changing the reached pool. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (CanonicalRootAt)
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment}
  (model : GenericHeap.PayloadModel catalog projects definitions)
  (stages : Staging.Recursive.Registry) (semanticFaults : FunctionCalls.FaultRep)
  (faults : RecursiveStageMeaning.FaultRep)

/-- Physical global values are retained by the actual caller protocol. -/
def PreservesRootsAt (size : Nat) : Prop :=
  ∀ {context invocation scope expression lowered}
    (root : CanonicalRootAt compiled headers context invocation scope expression lowered semanticFaults)
    (owner : OwnedKey keys)
    {caller : ProtectedStateTransition.Protocol.{0, 0} (Records keys)}
    (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
      (fun index => CallableIndexedOwnedExpressionHeads.Globals (headers := headers)
        owner root.compilation.administrativePrefix index.scope index.canonical) caller),
    PreservesAt bridge.forgetSlots context model stages invocation (Point scope expression lowered) faults size

def ReflectsRootsAt (size : Nat) : Prop :=
  ∀ {context invocation scope expression lowered}
    (root : CanonicalRootAt compiled headers context invocation scope expression lowered semanticFaults)
    (owner : OwnedKey keys)
    {caller : ProtectedStateTransition.Protocol.{0, 0} (Records keys)}
    (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
      (fun index => CallableIndexedOwnedExpressionHeads.Globals (headers := headers)
        owner root.compilation.administrativePrefix index.scope index.canonical) caller),
    ReflectsAt bridge.forgetSlots context model stages invocation (Point scope expression lowered) faults size

/-- Every selected scope uses one actual named compiler root; the prefix and
zero-capture facts identify the existing named parameter packet. -/
structure NamedSupport (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (terminal : Terminal header) where
  point : terminal.certificate = Point
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    terminal.expression terminal.receipt.child
  zero : ∀ owner : OwnedKey keys, owner.key.capturePrefix = 0
  roots : ∀ child, stages.Closure header.function child →
    { root : CanonicalRootAt compiled headers header.context child
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
        terminal.expression terminal.receipt.child semanticFaults //
      root.rawType = header.function.resultType ∧ root.reasonAt = header.reasonAt ∧
      root.compilation.administrativePrefix = 1 }

variable {model stages semanticFaults faults}

/-- The stronger bridge projects the actual packet's global observations.
Its pool and restoration operation are definitionally the existing bridge. -/
def nestedCaller (owner : OwnedKey keys)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (callerPrefix : Nat) (samePrefix : callerPrefix = 1) :
    CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
      (fun index => CallableIndexedOwnedExpressionHeads.Globals (headers := headers)
        owner callerPrefix index.scope index.canonical)
      (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header) where
  pool := (CallableIndexedOwnedOrdinaryLambdaEntries.bridge owner header).pool
  records_eq := (CallableIndexedOwnedOrdinaryLambdaEntries.bridge owner header).records_eq
  related := (CallableIndexedOwnedOrdinaryLambdaEntries.bridge owner header).related
  slots := fun state => samePrefix.symm ▸ state.property.globals
  restore := (CallableIndexedOwnedOrdinaryLambdaEntries.bridge owner header).restore

theorem NamedSupport.preserves
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)} {terminal : Terminal header}
    (static : NamedSupport (headers := headers) (keys := keys) stages semanticFaults header terminal)
    {child : Staging.Recursive.Scope} (selected : stages.Closure header.function child)
    {budget : Nat}
    (children : ∀ size, size < budget → PreservesRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults faults size) :
    CallableIndexedOwnedPreparedStagedNamedChildBounds.PreservesBelow (headers := headers) (keys := keys)
      header model stages child terminal.certificate faults budget := by
  refine .nested terminal.aligned.globals static.zero ?_
  intro owner size smaller current id lowered point
  rw [static.point] at point
  let root := (static.roots child selected).val
  intro node
  exact children size smaller root owner
    (nestedCaller owner header root.compilation.administrativePrefix (static.roots child selected).property.2.2) point (node := node)

theorem NamedSupport.reflects
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)} {terminal : Terminal header}
    (static : NamedSupport (headers := headers) (keys := keys) stages semanticFaults header terminal)
    {child : Staging.Recursive.Scope} (selected : stages.Closure header.function child)
    {budget : Nat}
    (children : ∀ size, size < budget → ReflectsRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults faults size) :
    CallableIndexedOwnedPreparedStagedNamedChildBounds.ReflectsBelow (headers := headers) (keys := keys)
      header model stages child terminal.certificate faults budget := by
  refine .nested terminal.aligned.globals static.zero ?_
  intro owner size smaller current id lowered point
  rw [static.point] at point
  let root := (static.roots child selected).val
  intro node
  exact children size smaller root owner
    (nestedCaller owner header root.compilation.administrativePrefix (static.roots child selected).property.2.2) point (node := node)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport
