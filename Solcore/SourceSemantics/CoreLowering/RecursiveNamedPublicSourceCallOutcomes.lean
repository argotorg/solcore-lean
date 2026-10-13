import Solcore.SourceSemantics.Staging.RecursiveCallableErasure
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionState

/-! A public Source call projects to its independent Dynamic callable outcome.
The same retained named function, dictionary, arguments and heap remain in the
conclusion. A stage rejection keeps its actual rejected source guard. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionState
open Core Frontend SourceInference
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- The named row and its complete independent successful application. -/
def PlainValue (anchor header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (arguments : List Dynamic.Value)
    (value : Dynamic.Value) (after : Dynamic.Heap) : Prop :=
  ∃ rawD function, NamedSourceAt header rawD function ∧
    Dynamic.CallableApplies (Program.ofChecked compiled.sourceProgram) anchor.function.context
      invocation.evidence function.evidence before (.global function) arguments value after

/-- Semantic failure retains its original reason and exact prefix heap. -/
def PlainFault (anchor header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (arguments : List Dynamic.Value)
    (reason : Dynamic.SemanticFault) (after : Dynamic.Heap) : Prop :=
  ∃ rawD function, NamedSourceAt header rawD function ∧
    Dynamic.CallableFaults (Program.ofChecked compiled.sourceProgram) anchor.function.context
      invocation.evidence function.evidence before (.global function) arguments reason after

variable {anchor header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {invocation : Staging.Recursive.Scope} {before after : Dynamic.Heap} {arguments : List Dynamic.Value}

theorem SourceCall.value_plain {value : Dynamic.Value}
    (trace : SourceCall anchor header invocation before arguments (.value value) after) :
    PlainValue anchor header invocation before arguments value after := by
  obtain ⟨rawD, function, size, retained, applied⟩ := trace
  exact ⟨rawD, function, retained, applied.sound.value_plain⟩

theorem SourceCall.semanticFault_plain {reason : Dynamic.SemanticFault}
    (trace : SourceCall anchor header invocation before arguments (.fault (.semantic reason)) after) :
    PlainFault anchor header invocation before arguments reason after := by
  obtain ⟨rawD, function, size, retained, applied⟩ := trace
  exact ⟨rawD, function, retained, applied.sound.semanticFault_plain⟩

/-- The original failure constructor determines which source judgment exists. -/
def FailureProjection (anchor header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (arguments : List Dynamic.Value)
    (failure : Staging.Recursive.Failure) (after : Dynamic.Heap) : Prop :=
  match failure with
  | .semantic reason => PlainFault anchor header invocation before arguments reason after
  | .stage origin call reason => Staging.Recursive.Generated origin call reason

theorem SourceCall.failure_plain {failure : Staging.Recursive.Failure}
    (trace : SourceCall anchor header invocation before arguments (.fault failure) after) :
    FailureProjection anchor header invocation before arguments failure after := by
  cases failure with
  | semantic reason => exact trace.semanticFault_plain
  | stage origin call reason =>
    obtain ⟨_rawD, _function, _size, _retained, applied⟩ := trace
    exact applied.sound.stage_origin rfl

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionState
