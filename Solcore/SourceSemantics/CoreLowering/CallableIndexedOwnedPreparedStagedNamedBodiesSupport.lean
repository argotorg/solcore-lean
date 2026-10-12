import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodies
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodySupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedLexicalSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedBodyPorts

/-! Actual named compiler packets select terminal or lexical static support.
Both alternatives supply the same body ports from strict expression children;
no execution law belongs to the static support. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodiesSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body)
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (RootAt)
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
open CallableIndexedOwnedAdmittedStagedExpressionBounds

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

def Support
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (stages : Staging.Recursive.Registry) (body : Body header)
    (semanticFaults : FunctionCalls.FaultRep) : Type :=
  match body.compilation with
  | .terminal expression receipt certificate certifies =>
      CallableIndexedOwnedPreparedStagedNamedBodySupport.Support headers keys bodyRegistry header stages
        ⟨body.row, body.prepared, body.instantiation, body.aligned, body.layouts,
          expression, receipt, certificate, certifies⟩ semanticFaults
  | .lexical receipt =>
      CallableIndexedOwnedPreparedStagedNamedLexicalSupport.Support
        headers keys bodyRegistry header stages receipt semanticFaults

variable {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {stages : Staging.Recursive.Registry} {body : Body header}
  (static : Support headers keys bodyRegistry header stages body semanticFaults)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {receiving : SourceCoreRawMetadata.Registry} {faults : RecursiveStageMeaning.FaultRep}
  {invocation : Staging.Recursive.Scope} (selected : stages.Closure header.function invocation)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge
  (compiled := compiled) (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys)

include static wellFormed selected in
theorem Support.preserves {budget : Nat}
    (children : ∀ size, size < budget → ∀ {context child scope expression lowered},
      RootAt compiled context child scope expression lowered semanticFaults →
      PreservesAt poolBridge context model stages child (Point scope expression lowered) faults size) :
    CallableIndexedOwnedPreparedStagedNamedBodyPorts.PreservesBelow
      (headers := headers) (keys := keys) header model stages invocation faults budget := by
  cases body with
  | mk row prepared instantiation aligned layouts compilation =>
    cases compilation with
    | terminal expression receipt certificate certifies =>
      apply CallableIndexedOwnedPreparedStagedTerminalNamedBodyPorts.preserves
        selected wellFormed receipt certifies budget
      cases static with
      | recursive support =>
        apply CallableIndexedOwnedPreparedStagedNamedChildBounds.PreservesBelow.pool
        intro size within scope id lowered point
        have same := support.point
        change certificate = _ at same
        rw [same] at point
        intro node
        exact children size within (support.roots invocation selected).val point (node := node)
      | formation support =>
        exact CallableIndexedOwnedPreparedStagedNamedBodySupport.Formation.preserves
          (profile := profile) (faults := faults) support selected budget
    | lexical receipt =>
      exact CallableIndexedOwnedPreparedStagedNamedLexicalSupport.preserves
        static aligned.globals profile selected layouts children

include static wellFormed selected in
theorem Support.reflects {budget : Nat}
    (children : ∀ size, size < budget → ∀ {context child scope expression lowered},
      RootAt compiled context child scope expression lowered semanticFaults →
      ReflectsAt poolBridge context model stages child (Point scope expression lowered) faults size) :
    CallableIndexedOwnedPreparedStagedNamedBodyPorts.ReflectsBelow
      (headers := headers) (keys := keys) header model stages invocation faults budget := by
  cases body with
  | mk row prepared instantiation aligned layouts compilation =>
    cases compilation with
    | terminal expression receipt certificate certifies =>
      apply CallableIndexedOwnedPreparedStagedTerminalNamedBodyPorts.reflects
        selected wellFormed receipt certifies budget
      cases static with
      | recursive support =>
        apply CallableIndexedOwnedPreparedStagedNamedChildBounds.ReflectsBelow.pool
        intro size within scope id lowered point
        have same := support.point
        change certificate = _ at same
        rw [same] at point
        intro node
        exact children size within (support.roots invocation selected).val point (node := node)
      | formation support =>
        exact CallableIndexedOwnedPreparedStagedNamedBodySupport.Formation.reflects
          (profile := profile) (faults := faults) support selected budget
    | lexical receipt =>
      exact CallableIndexedOwnedPreparedStagedNamedLexicalSupport.reflects
        static aligned.globals profile selected layouts children

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodiesSupport
