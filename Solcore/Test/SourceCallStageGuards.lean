import Solcore.SourceSemantics.CoreLowering.CallStageGuard

/-! Stage-guard ordering and bypass regressions in independent source rules.
The compiler equivalence is universal over all retained caller/contract metadata;
these examples exercise the ordering cases most easily lost in a refactor. -/

set_option autoImplicit false
namespace Tests.SourceCallStageGuards
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Staging.CallGuard

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"call_stage_guards", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def parameter (index : Nat) (comptime : Bool) (type : TypeSystem.Ty := .word) : TypedBinder :=
  { id := ⟨owner, index⟩, name := "parameter", scheme := .mono type, comptime }
private def ordinary : Frame := ⟨false, .unit, fun _ => some .runtime⟩
private def firstKnown : Frame := ⟨false, .unit, fun expression => if expression = id 1 then some .comptime else none⟩
private def argumentsKnown : Frame := ⟨false, .unit, fun expression => if expression = id 0 then some .runtime else some .comptime⟩

private theorem not_effectful : ¬ Effectful ordinary := by
  rintro (flag | only)
  · cases flag
  · cases only

private theorem runtime_word : ¬ RequiresComptime false (parameter 0 false) := by
  rintro (force | explicit | only)
  · cases force
  · cases explicit
  · cases only

/-- A parameter without a comptime requirement does not inspect its stage. -/
example : Accepts ordinary ⟨[parameter 0 false], false⟩ (id 0) [id 1] :=
  .ordinary not_effectful (.cons (.ordinary runtime_word) (.nil _)) (.ordinary rfl)

/-- Earlier stage mismatch wins over the missing trailing argument. -/
private theorem first_failure : Rejects ordinary ⟨[parameter 0 true, parameter 1 true], false⟩ (id 0) [id 1]
    (.argumentStage 0 (id 1) .runtime) :=
  .arguments not_effectful (.head (.wrongStage (.inr (.inl rfl)) rfl (by decide)))

example : ¬ Rejects ordinary ⟨[parameter 0 true, parameter 1 true], false⟩ (id 0) [id 1] (.arity 1 0) := by
  intro later
  have impossible := first_failure.functional later
  cases impossible

/-- After a successful first parameter, the arity diagnostic counts the
remaining suffix. It does not report the original full list lengths. -/
example : Rejects firstKnown ⟨[parameter 0 true, parameter 1 true], false⟩ (id 0) [id 1] (.arity 1 0) := by
  apply Rejects.arguments
  · rintro (flag | only)
    · cases flag
    · cases only
  · exact .tail (.comptime (by simp [firstKnown])) (.parametersRemain 1 (parameter 1 true) [])

/-- A staged result forces ordinary-looking parameters to be comptime too. -/
example : Rejects ordinary ⟨[parameter 0 false], true⟩ (id 0) [id 1] (.argumentStage 0 (id 1) .runtime) :=
  .arguments not_effectful (.head (.wrongStage (.inl rfl) rfl (by decide)))

/-- Result availability is checked only after every argument passes. -/
example : Rejects argumentsKnown ⟨[parameter 0 false], true⟩ (id 0) [id 1] (.resultStage .runtime) := by
  apply Rejects.result
  · rintro (flag | only)
    · cases flag
    · cases only
  · exact .cons (.comptime (by decide)) (.nil _)
  · exact .wrongStage rfl (by simp [argumentsKnown]) (by decide)

/-- Native Integer retains its source staging requirement independently of
whether its runtime carrier can be represented by Core. -/
example : Rejects ordinary ⟨[parameter 0 false .integer], false⟩ (id 0) [id 1] (.argumentStage 0 (id 1) .runtime) :=
  .arguments not_effectful (.head (.wrongStage (.inr (.inr .integer)) rfl (by decide)))

/-- An effectful-staging caller bypasses this pre-argument check, including its
arity check. Ordinary callable application checks arity after argument effects. -/
example : Accepts ⟨false, .integer, fun _ => none⟩ ⟨[parameter 0 true], true⟩ (id 0) [] :=
  .effectful (.inr .integer)

example : Accepts ⟨true, .unit, fun _ => none⟩ ⟨[parameter 0 true], true⟩ (id 0) [] :=
  .effectful (.inl rfl)

/-- The sealed metadata receipt is interpreted by the independent relation,
including all exact diagnostic coordinates and source stages. -/
example (guard : SourceCoreStageContracts.Guard) (diagnostic : SourceCompilationPlan.Error)
    (failed : guard.decision = .error diagnostic) :
    ∃ reason, Rejects (CoreLowering.CallStageGuard.frame guard.sidecar.caller)
      ⟨guard.contract.parameters, guard.contract.stagedResult⟩ guard.node.id guard.arguments reason ∧
      diagnostic = CoreLowering.CallStageGuard.error guard.sidecar.caller guard.node guard.contract.owner reason :=
  (CoreLowering.CallStageGuard.guard_rejects_iff guard diagnostic).mp failed

end Tests.SourceCallStageGuards
