import Solcore.SourceSemantics.CoreLowering.TypedLexicalWhileNativeCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleStatementInitializedTree

/-! Native typing facts of the actual emitted statement code. Every flow the
compiler emits reports failure as a Word, so the initializer of a declaration
is typed at its own language result. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNative
open Core Frontend SourceInference
open TypedLexicalWhile.Native (remove_front)

/-- Every native typing of `code` has a Word failure component. -/
def WordFailure (context : Core.Context) (code : Expr) (definitions : DataEnvironment) : Prop :=
  ∀ {type : Ty}, HasType context code type definitions → ∃ success, type = LanguageResult.resultType success

section Leaves
variable {context : Core.Context} {definitions : DataEnvironment}

theorem success_word {payload : Expr} :
    WordFailure context (LanguageResult.success payload) definitions := by
  intro type typed
  cases typed with
  | inRight => exact ⟨_, rfl⟩

theorem fallthrough_word (result : Ty) : WordFailure context (LocalLoop.fallthrough result) definitions :=
  success_word

theorem returned_word (value : Expr) : WordFailure context (LocalLoop.returned value) definitions :=
  success_word

theorem breaking_word (result : Ty) : WordFailure context (LocalLoop.breaking result) definitions :=
  success_word

theorem continuing_word (result : Ty) : WordFailure context (LocalLoop.continuing result) definitions :=
  success_word

theorem returnValue_word (result : Ty) (computation : Expr) :
    WordFailure context (LocalLoop.returnValue result computation) definitions := by
  intro type typed
  cases typed with
  | caseE _ _ returned => exact success_word returned

theorem sequence_word (result : Ty) (computation next : Expr) :
    WordFailure context (LocalLoop.sequence result computation next) definitions := by
  intro type typed
  cases typed with
  | caseE _ _ control =>
    cases control with
    | caseE _ _ transfer => exact success_word transfer

end Leaves

/-- A discarded computation keeps the continuation's exact native type. -/
theorem discard_tail {definitions : DataEnvironment} {context : Core.Context} {output result : Ty}
    {computation next : Expr}
    (typed : HasType context (LocalSequence.discard output computation next) result definitions) :
    HasType context next result definitions := by
  cases typed with
  | caseE _ _ body => exact remove_front body

/-- The marked initialized allocation reads its payload from the innermost
binder, so that binder has the request's payload type. -/
theorem allocation_payload {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {binder : TypedBinder} {payload : Ty}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active
      (CompatibleStatementInitialized.request source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (CompatibleStatementInitialized.request source scope binder payload))
    (same : annotation.original = allocation.expression)
    {definitions : DataEnvironment} {context : Core.Context} {bound result : Ty}
    (typed : HasType (bound :: context) annotation.expression result definitions) :
    bound = payload := by
  rw [annotation.exact] at typed
  cases typed with
  | letE _ original =>
    have allocated := remove_front original
    rw [same, allocation.expressionExact] at allocated
    unfold SourceCoreAllocationLayouts.allocation at allocated
    simp only [CompatibleStatementInitialized.request] at allocated
    unfold SourceCoreHeapMarkers.allocateInitialized at allocated
    cases allocated with
    | letE initial rest =>
      cases initial with
      | var found =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at found
        subst found
        cases rest with
        | letE _ cell =>
          unfold OptionalCell.allocateInitialized at cell
          cases cell with
          | newCell value =>
            cases value with
            | inRight _ read =>
              cases read with
              | var found =>
                simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at found
                exact found

/-- At a Word failure component, the initializer of an emitted declaration is
typed at the language result of the declared payload. -/
theorem initialized_initializer {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {binder : TypedBinder} {payload : Ty}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active
      (CompatibleStatementInitialized.request source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (CompatibleStatementInitialized.request source scope binder payload))
    (same : annotation.original = allocation.expression)
    {definitions : DataEnvironment} {context : Core.Context} {type success : Ty} {initializer body : Expr}
    (typed : HasType context (CompatibleStatementInitialized.sequence type initializer annotation.expression body)
      (LanguageResult.resultType success) definitions) :
    HasType context initializer (LanguageResult.resultType payload) definitions := by
  cases typed with
  | caseE initialized failure next =>
    cases failure with
    | inLeft _ reason =>
      cases reason with
      | var found =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at found
        subst found
        cases next with
        | letE allocated _ =>
          have bound := allocation_payload allocation annotation same allocated
          subst bound
          exact initialized

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNative
