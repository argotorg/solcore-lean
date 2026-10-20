import Solcore.SourceSemantics.SourceCompiledSelectedFinalization
import Solcore.Frontend.ProgramSignatureFormationProperties

/-! The selected original checker receipt derives its actual inference-ready
states and substitution continuation from successful program checking. These
facts precede declarative body typing and apply to generalized local bodies. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem

structure BodyInferenceProgress {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature} {fuel : Nat} {checked : CheckedFunction}
    (receipt : BodyReceipt environment signatures signature fuel checked) : Prop where
  initialReady : (initial signature receipt.declaration).InferenceReady
  returnBelow : (Ty.productMany signature.returnTypes).VariablesBelow
    (initial signature receipt.declaration).inference.next
  body : (initial signature receipt.declaration).InferenceProgress receipt.body.state
  bodyReady : receipt.body.state.InferenceReady
  bodyTypeBelow : receipt.body.type.VariablesBelow receipt.body.state.inference.next
  returnUnification : receipt.body.state.InferenceProgress receipt.returned
  returnedReady : receipt.returned.InferenceReady
  finalization : receipt.returned.InferenceProgress receipt.resources.finalState

namespace BodyInferenceProgress
variable {environment : ProgramEnvironment} {signatures : ProgramSignatures}
  {signature : ProgramFunctionSignature} {fuel : Nat} {checked : CheckedFunction}
  {receipt : BodyReceipt environment signatures signature fuel checked}

theorem final_substitution (progress : BodyInferenceProgress receipt) :
    receipt.finalized.substitution.SemanticallyExtends receipt.body.state.inference.substitution := by
  rw [receipt.resources.substitution_eq]
  exact (progress.returnUnification.trans progress.finalization).substitution_extends

theorem initial_substitution (progress : BodyInferenceProgress receipt) :
    receipt.finalized.substitution.SemanticallyExtends
      (initial signature receipt.declaration).inference.substitution := by
  rw [receipt.resources.substitution_eq]
  exact (progress.body.trans (progress.returnUnification.trans progress.finalization)).substitution_extends

end BodyInferenceProgress

theorem Selected.inferenceProgress {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : Selected compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program) :
    BodyInferenceProgress selected.body := by
  have formation := Frontend.checkProgram_success_signature_formation checked
  have functions : ∀ candidate ∈ compiled.program.signatures.functions,
      candidate.scheme.body = .function (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes) := by
    intro candidate member
    exact (Frontend.checkProgram_success_function_signature_shape checked member).2
  have ready : (initial selected.signature selected.body.declaration).InferenceReady :=
    State.InferenceReady.initial _ _ _
  have returns : (Ty.productMany selected.signature.returnTypes).VariablesBelow
      (initial selected.signature selected.body.declaration).inference.next :=
    Ty.variablesBelow_productMany
      ((formation.functions selected.signature selected.signatureMember).2.1.variablesBelow _)
  have body := Detail.inferStatementsFuel_inferenceProperties ready formation functions returns selected.body.inferred
  have returnBound := returns.weaken body.1.next_le
  have unified := Detail.unify_inferenceProgress body.2.1.solved body.2.2 returnBound selected.body.unified
  have returned := Detail.unify_preserves_inferenceReady body.2.1 body.2.2 returnBound selected.body.unified
  exact ⟨ready, returns, body.1, body.2.1, body.2.2, unified, returned,
    selected.body.resources.progress_of_ready returned⟩

/-- Actual selected compilation supplies the whole inference continuation,
including the final solver, without a body-typing or monomorphism premise. -/
theorem compile_inference_progress {raw : Workspace.RawWorkspace} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction} (member : row ∈ compiled.plan.specializations) :
    ∃ selected : Selected compiled row options.checkingFuel, BodyInferenceProgress selected.body := by
  obtain ⟨selected⟩ := of_compile accepted member
  exact ⟨selected, selected.inferenceProgress (SourceCoreCompiler.compile_checked_source accepted)⟩

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
