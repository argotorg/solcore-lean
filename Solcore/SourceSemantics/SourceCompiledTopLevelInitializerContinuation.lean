import Solcore.SourceSemantics.SourceCompiledSelectedInferenceProgress
import Solcore.Frontend.SourceInference.StatementInferenceContinuation

/-! Selected accepted compilation supplies a top-level initializer's actual
return state and its continuation through the remaining body, return unification
and final solver. No initializer-typing or substitution-continuation premise is
supplied by the caller. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem

structure InitializerContinuation {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : Selected compiled row fuel) (source : Syntax.Statement) where
  childFuel : Nat
  entry : State
  result : Detail.StatementResult
  receipt : LocalLetRequirementTiming.Receipt childFuel
    (context compiled.program.environment compiled.program.signatures
      selected.signature selected.body.declaration) source entry result
  retained : result.state.nodes <+: selected.body.body.state.nodes
  ready : receipt.ready.InferenceReady
  bodyContinuation : receipt.ready.InferenceProgress selected.body.body.state
  finalContinuation : receipt.ready.InferenceProgress selected.body.resources.finalState

namespace InitializerContinuation
variable {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction}
    {fuel : Nat} {selected : Selected compiled row fuel} {source : Syntax.Statement}

theorem substitution (continuation : InitializerContinuation selected source) :
    selected.body.finalized.substitution.SemanticallyExtends
      continuation.receipt.ready.inference.substitution := by
  rw [selected.body.resources.substitution_eq]
  exact continuation.finalContinuation.substitution_extends

/-- The same actual declaration reaches the finalizer's original node table. -/
theorem original_retained (continuation : InitializerContinuation selected source) :
    .statement {
      id := continuation.entry.allocateStatementId.1, span := source.span, type := .unit,
      form := .letDecl continuation.receipt.binding.1 (some continuation.receipt.value.id)
    } ∈ selected.body.returned.nodes := by
  rw [selected.body.returned_nodes]
  exact continuation.retained.subset continuation.receipt.recorded

/-- Capture avoidance is validated for this initializer's exact allocated binder. -/
theorem no_capture (continuation : InitializerContinuation selected source) :
    Detail.LocalBinderInstantiationNoCapture selected.body.finalized.substitution
      continuation.receipt.binding.1 := by
  apply selected.body.resources.local_no_capture
  unfold TypedSource.initializedLetBinders
  apply List.mem_flatMap.mpr
  refine ⟨.statement {
    id := continuation.entry.allocateStatementId.1, span := source.span, type := .unit,
    form := .letDecl continuation.receipt.binding.1 (some continuation.receipt.value.id)
  }, continuation.original_retained, ?_⟩
  exact List.mem_singleton_self _

end InitializerContinuation

theorem Selected.topLevelInitializer {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : Selected compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement}
    (position : selected.signature.source.value.body.value[index]? = some source)
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (form : source.value = .letDecl name annotation (some initializer)) :
    Nonempty (InitializerContinuation selected source) := by
  have progress := selected.inferenceProgress checked
  have formation := Frontend.checkProgram_success_signature_formation checked
  have canonical : ∀ signature ∈ compiled.program.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes) := by
    intro signature member
    exact (Frontend.checkProgram_success_function_signature_shape checked member).2
  obtain ⟨occurrence⟩ := StatementInferenceContinuation.of_position progress.initialReady
    (State.initial_nodesBelowNextOccurrence _ _ _) formation canonical progress.returnBelow selected.body.inferred position
  obtain ⟨childFuel, receipt, ready, bodyContinuation⟩ :=
    occurrence.initialized form formation canonical
  exact ⟨⟨childFuel, occurrence.entry, occurrence.result, receipt, occurrence.retained, ready, bodyContinuation,
    bodyContinuation.trans (progress.returnUnification.trans progress.finalization)⟩⟩

/-- The entry is selected by the real specialization row. The premise names
an original source position, rather than an independently reconstructed body. -/
theorem compile_top_level_initializer_continuation {raw : Workspace.RawWorkspace}
    {seeds : List SourceCoreCompiler.Seed} {options : SourceCoreCompiler.Options}
    {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction} (member : row ∈ compiled.plan.specializations) :
    ∃ selected : Selected compiled row options.checkingFuel,
      ∀ {index : Nat} {source : Syntax.Statement},
        selected.signature.source.value.body.value[index]? = some source →
        ∀ {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr},
          source.value = .letDecl name annotation (some initializer) →
          Nonempty (InitializerContinuation selected source) := by
  obtain ⟨selected⟩ := of_compile accepted member
  refine ⟨selected, ?_⟩
  intro index source position name annotation initializer form
  exact selected.topLevelInitializer (SourceCoreCompiler.compile_checked_source accepted) position form

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
