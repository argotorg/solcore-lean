import Solcore.SourceSemantics.CoreLowering.CallableCoercionSpineCertificates
import Solcore.Core.Renaming
import Solcore.SourceSemantics.CoreLowering.CoreEvaluationSize

/-! Finite native execution of the actual ordered coercion calls. Saved closure
code and captures are observed from the store, without identifying them with a
source method body. Source coercion judgments need that separate connection. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionSpine
open Core Frontend CoreProof

/-- A native call either propagates an earlier failure, reads an absent global,
or enters the exact stored closure. Sum tags and closure annotations remain the
actual values; no typing premise is silently inferred from a compiler row. -/
inductive Invoke (environment : Environment) (reason : Word) (call : Call) :
    Store → Value → Value → Store → Prop where
  | skipped {store : Store} {tag : Ty} {payload : Value} :
      Invoke environment reason call store (.inLeft tag payload)
        (.inLeft call.signature.resultType payload) store
  | absent {store : Store} {tag cellType absentTag : Ty} {argument absentPayload : Value}
      {location : Location}
      (reference : environment[call.index]? = some (.cellRef cellType location))
      (read : store.read? location = some (.inLeft absentTag absentPayload)) :
      Invoke environment reason call store (.inRight tag argument)
        (.inLeft call.signature.resultType (.word reason)) store
  | applied {before after : Store} {tag cellType storedTag parameter result : Ty}
      {argument value : Value} {location : Location} {body : Expr} {captured : Environment}
      (reference : environment[call.index]? = some (.cellRef cellType location))
      (read : before.read? location = some (.inRight storedTag (.closure parameter result body captured)))
      (bodyEvaluation : Evaluates (argument :: captured) before body value after) :
      Invoke environment reason call before (.inRight tag argument) value after

inductive Runs (environment : Environment) (reason : Word) :
    Store → Value → List Call → Value → Store → Prop where
  | nil {store : Store} {value : Value} : Runs environment reason store value [] value store
  | cons {before middle after : Store} {input result value : Value} {call : Call} {calls : List Call}
      (head : Invoke environment reason call before input result middle)
      (tail : Runs environment reason middle result calls value after) :
      Runs environment reason before input (call :: calls) value after

/-- Ordered native calls can retain additional receipts for each actual
invocation without changing the intermediate stores or call order. -/
inductive RunsFor (invocation : Call → Store → Value → Value → Store → Prop) :
    Store → Value → List Call → Value → Store → Prop where
  | nil {store : Store} {value : Value} : RunsFor invocation store value [] value store
  | cons {before middle after : Store} {input result value : Value} {call : Call} {calls : List Call}
      (head : invocation call before input result middle)
      (tail : RunsFor invocation middle result calls value after) :
      RunsFor invocation before input (call :: calls) value after

theorem RunsFor.map {invocation target : Call → Store → Value → Value → Store → Prop}
    (transform : ∀ {call before input result after}, invocation call before input result after →
      target call before input result after)
    {before after : Store} {input value : Value} {calls : List Call}
    (runs : RunsFor invocation before input calls value after) :
    RunsFor target before input calls value after := by
  induction runs with
  | nil => exact .nil
  | cons head _ ih => exact .cons (transform head) ih

theorem Runs.toFor {environment : Environment} {reason : Word}
    {before after : Store} {input value : Value} {calls : List Call}
    (runs : Runs environment reason before input calls value after) :
    RunsFor (Invoke environment reason) before input calls value after := by
  induction runs with
  | nil => exact .nil
  | cons head _ ih => exact .cons head ih

theorem RunsFor.toRuns {environment : Environment} {reason : Word}
    {before after : Store} {input value : Value} {calls : List Call}
    (runs : RunsFor (Invoke environment reason) before input calls value after) :
    Runs environment reason before input calls value after := by
  induction runs with
  | nil => exact .nil
  | cons head _ ih => exact .cons head ih

/-- Applied calls retain the body child of the original native completion.
The actual closure annotations, code, captures and cell observation remain. -/
inductive InvokeSized (budget : Nat) (environment : Environment) (reason : Word) (call : Call) :
    Store → Value → Value → Store → Prop where
  | skipped {store : Store} {tag : Ty} {payload : Value} :
      InvokeSized budget environment reason call store (.inLeft tag payload)
        (.inLeft call.signature.resultType payload) store
  | absent {store : Store} {tag cellType absentTag : Ty} {argument absentPayload : Value}
      {location : Location}
      (reference : environment[call.index]? = some (.cellRef cellType location))
      (read : store.read? location = some (.inLeft absentTag absentPayload)) :
      InvokeSized budget environment reason call store (.inRight tag argument)
        (.inLeft call.signature.resultType (.word reason)) store
  | applied {before after : Store} {tag cellType storedTag parameter result : Ty}
      {argument value : Value} {location : Location} {body : Expr} {captured : Environment} {bodySize : Nat}
      (reference : environment[call.index]? = some (.cellRef cellType location))
      (read : before.read? location = some (.inRight storedTag (.closure parameter result body captured)))
      (bodyEvaluation : EvaluationSize bodySize (argument :: captured) before body value after)
      (smaller : bodySize < budget) :
      InvokeSized budget environment reason call before (.inRight tag argument) value after

theorem InvokeSized.mono {budget larger : Nat} {environment : Environment} {reason : Word} {call : Call}
    {before after : Store} {input value : Value}
    (invoked : InvokeSized budget environment reason call before input value after)
    (bound : budget ≤ larger) : InvokeSized larger environment reason call before input value after := by
  cases invoked with
  | skipped => exact .skipped
  | absent reference read => exact .absent reference read
  | applied reference read evaluated smaller =>
    exact .applied reference read evaluated (Nat.lt_of_lt_of_le smaller bound)

theorem InvokeSized.forget {budget : Nat} {environment : Environment} {reason : Word} {call : Call}
    {before after : Store} {input value : Value}
    (invoked : InvokeSized budget environment reason call before input value after) :
    Invoke environment reason call before input value after := by
  cases invoked with
  | skipped => exact .skipped
  | absent reference read => exact .absent reference read
  | applied reference read evaluated _ => exact .applied reference read evaluated.sound

theorem RunsFor.forget {invocation : Call → Store → Value → Value → Store → Prop}
    {environment : Environment} {reason : Word}
    {before after : Store} {input value : Value} {calls : List Call}
    (runs : RunsFor invocation before input calls value after)
    (forgetInvocation : ∀ {call before input result after}, invocation call before input result after →
      Invoke environment reason call before input result after) :
    Runs environment reason before input calls value after :=
  (runs.map forgetInvocation).toRuns

theorem RunsFor.mono {budget larger : Nat} {environment : Environment} {reason : Word}
    {before after : Store} {input value : Value} {calls : List Call}
    (runs : RunsFor (InvokeSized budget environment reason) before input calls value after)
    (bound : budget ≤ larger) :
    RunsFor (InvokeSized larger environment reason) before input calls value after :=
  runs.map (fun invoked => invoked.mono bound)


theorem Invoke.evaluates {environment : Environment} {reason : Word} {call : Call}
    {before middle after : Store} {input value : Value} {arguments : Expr}
    (argumentsEvaluation : Evaluates environment before arguments input middle)
    (invoked : Invoke environment reason call middle input value after) :
    Evaluates environment before (SourceCoreCalls.call call.signature call.index arguments reason) value after := by
  cases invoked with
  | skipped => exact .caseLeft argumentsEvaluation (.inLeft (.var rfl))
  | absent reference read =>
    exact .caseRight argumentsEvaluation (.caseLeft
      (.caseLeft (.loadCell (.var (by simpa using reference)) read) (.inLeft .word))
      (.inLeft (.var rfl)))
  | applied reference read bodyEvaluation =>
    exact .caseRight argumentsEvaluation (.caseRight
      (.caseRight (.loadCell (.var (by simpa using reference)) read) (.inRight (.var rfl)))
      (.apply (.var rfl) (.var rfl) bodyEvaluation))

/-- Completion itself supplies the argument trace, actual cell observation and
saved-body trace. It cannot supply source method authenticity. -/
theorem call_complete_sized {environment : Environment} {reason : Word} {call : Call}
    {size : Nat} {before after : Store} {value : Value} {arguments : Expr}
    (completed : EvaluationSize size environment before (SourceCoreCalls.call call.signature call.index arguments reason) value after) :
    ∃ argumentSize input middle, argumentSize < size ∧
      EvaluationSize argumentSize environment before arguments input middle ∧
      InvokeSized size environment reason call middle input value after := by
  cases completed with
  | caseLeft argument branch =>
    cases branch with
    | inLeft payload =>
      cases payload with
      | var found =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at found
        subst_vars
        exact ⟨_, _, _, by omega, argument, .skipped⟩
  | caseRight argument branch =>
    cases branch with
    | caseLeft loaded branch =>
      cases loaded with
      | caseLeft loaded absent =>
        cases loaded with
        | loadCell reference read =>
          cases reference with
          | var reference =>
            cases absent with
            | inLeft reasonValue =>
              cases reasonValue
              cases branch with
              | inLeft payload =>
                cases payload with
                | var found =>
                  simp only [List.getElem?_cons_zero, Option.some.injEq] at found
                  subst_vars
                  exact ⟨_, _, _, by omega, argument, .absent (by simpa using reference) read⟩
      | caseRight loaded present => cases present
    | caseRight loaded branch =>
      cases loaded with
      | caseLeft loaded absent => cases absent
      | caseRight loaded present =>
        cases loaded with
        | loadCell reference read =>
          cases reference with
          | var reference =>
            cases present with
            | inRight payload =>
              cases payload with
              | var found =>
                simp only [List.getElem?_cons_zero, Option.some.injEq] at found
                subst_vars
                cases branch with
                | apply function argumentValue body =>
                  cases function with
                  | var functionFound =>
                    simp only [List.getElem?_cons_zero, Option.some.injEq] at functionFound
                    subst_vars
                    cases argumentValue with
                    | var argumentFound =>
                      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
                        Option.some.injEq] at argumentFound
                      subst_vars
                      exact ⟨_, _, _, by omega, argument, .applied (by simpa using reference) read body (by omega)⟩

theorem call_complete {environment : Environment} {reason : Word} {call : Call}
    {before after : Store} {value : Value} {arguments : Expr}
    (completed : Evaluates environment before (SourceCoreCalls.call call.signature call.index arguments reason) value after) :
    ∃ input middle, Evaluates environment before arguments input middle ∧
      Invoke environment reason call middle input value after := by
  obtain ⟨size, sized⟩ := evaluation_has_size completed
  obtain ⟨_, input, middle, _, argumentsEvaluation, invoked⟩ := call_complete_sized sized
  exact ⟨input, middle, argumentsEvaluation.sound, invoked.forget⟩

/-- Each body bound is inherited from its original call child. The initial
operand keeps its original size; it is strict exactly when a call is present. -/
theorem emit_complete_sized {environment : Environment} {reason : Word} {calls : List Call}
    {size : Nat} {before after : Store} {input : Expr} {value : Value}
    (completed : EvaluationSize size environment before (emit reason input calls) value after) :
    ∃ child initial middle, child ≤ size ∧ (calls ≠ [] → child < size) ∧
      EvaluationSize child environment before input initial middle ∧
      RunsFor (InvokeSized size environment reason) middle initial calls value after := by
  induction calls generalizing input size with
  | nil => exact ⟨size, _, _, Nat.le_refl _, by simp, completed, .nil⟩
  | cons call calls ih =>
    obtain ⟨callSize, result, reached, callBound, _, head, tail⟩ := ih completed
    obtain ⟨child, initial, middle, childLess, first, invoked⟩ := call_complete_sized head
    have smaller := Nat.lt_of_lt_of_le childLess callBound
    exact ⟨child, initial, middle, Nat.le_of_lt smaller, fun _ => smaller,
      first, .cons (invoked.mono callBound) tail⟩

/-- Forward native execution follows the retained ordered call trace. -/
theorem Runs.evaluates {environment : Environment} {reason : Word} {calls : List Call}
    {before middle after : Store} {input : Expr} {initial value : Value}
    (runs : Runs environment reason middle initial calls value after)
    (first : Evaluates environment before input initial middle) :
    Evaluates environment before (emit reason input calls) value after := by
  induction runs generalizing input before with
  | nil => exact first
  | cons head _ ih => exact ih (head.evaluates first)

theorem emit_evaluates_iff {environment : Environment} {reason : Word} {calls : List Call}
    {before after : Store} {input : Expr} {value : Value} :
    Evaluates environment before (emit reason input calls) value after ↔
      ∃ initial middle, Evaluates environment before input initial middle ∧
        Runs environment reason middle initial calls value after := by
  constructor
  · intro completed
    obtain ⟨size, sized⟩ := evaluation_has_size completed
    obtain ⟨_, initial, middle, _, _, first, runs⟩ := emit_complete_sized sized
    exact ⟨initial, middle, first.sound, runs.forget InvokeSized.forget⟩
  · rintro ⟨_, _, first, runs⟩
    exact runs.evaluates first

/-- Syntax renaming moves the selected caller slot and input expression. It
never renames an already captured closure value. -/
theorem call_rename (call : Call) (arguments : Expr) (reason : Word) (ξ : Renaming) :
    (SourceCoreCalls.call call.signature call.index arguments reason).rename ξ =
      SourceCoreCalls.call call.signature (ξ call.index) (arguments.rename ξ) reason := by
  simp [SourceCoreCalls.call, LanguageResult.bind, OptionalCell.read,
    LanguageResult.success, LanguageResult.failure, Expr.rename, Renaming.lift]

def Call.rename (ξ : Renaming) (call : Call) : Call := {call with index := ξ call.index}

theorem emit_rename (reason : Word) (input : Expr) (calls : List Call) (ξ : Renaming) :
    (emit reason input calls).rename ξ =
      emit reason (input.rename ξ) (calls.map (Call.rename ξ)) := by
  induction calls generalizing input with
  | nil => rfl
  | cons call calls ih => simp only [emit, List.map_cons, ih, call_rename, Call.rename]

def finalType (input : Ty) : List Call → Ty
  | [] => input
  | call :: calls => finalType call.signature.resultType calls

theorem Runs.failure (environment : Environment) (reason : Word) (store : Store)
    (tag : Ty) (payload : Value) (calls : List Call) :
    Runs environment reason store (.inLeft tag payload) calls
      (.inLeft (finalType tag calls) payload) store := by
  induction calls generalizing tag with
  | nil => exact .nil
  | cons call calls ih => exact .cons .skipped (ih call.signature.resultType)

theorem failure_suffix {environment : Environment} {reason : Word} {before after : Store}
    {input : Expr} {tag : Ty} {payload : Value} (calls : List Call)
    (failed : Evaluates environment before input (.inLeft tag payload) after) :
    Evaluates environment before (emit reason input calls)
      (.inLeft (finalType tag calls) payload) after :=
  emit_evaluates_iff.mpr ⟨_, _, failed, Runs.failure environment reason after tag payload calls⟩

theorem failure_store {environment : Environment} {reason : Word} {before reached after : Store}
    {input : Expr} {tag : Ty} {payload value : Value} {calls : List Call}
    (failed : Evaluates environment before input (.inLeft tag payload) reached)
    (completed : Evaluates environment before (emit reason input calls) value after) :
    value = .inLeft (finalType tag calls) payload ∧ after = reached :=
  evaluation_deterministic completed (failure_suffix calls failed)


theorem Spine.final_type {program : CheckedProgram} {project : Projector} {context : Context}
    {caller : Specialized} {available : RuntimeEvidence} {scope : Scope}
    {node : SourceInference.ExpressionNode} {policy : SourceCoreFunctions.CallablePolicy}
    {input output : Lowered} {steps : List SourceInference.CoercionStep} {calls : List Call}
    (receipt : Spine program project context caller available scope node policy input steps output calls) :
    finalType input.type calls = output.type := by
  induction receipt with
  | nil => rfl
  | cons head _ ih => simpa only [head.emitted, finalType] using ih

/-- The actual emitted spine keeps the operand child and every stored-body
child below the same original native budget. Source grades are independent. -/
theorem Spine.completed_sized {program : CheckedProgram} {project : Projector} {context : Context}
    {caller : Specialized} {available : RuntimeEvidence} {scope : Scope}
    {node : SourceInference.ExpressionNode} {policy : SourceCoreFunctions.CallablePolicy}
    {input output : Lowered} {steps : List SourceInference.CoercionStep} {calls : List Call}
    (receipt : Spine program project context caller available scope node policy input steps output calls)
    {size : Nat} {environment : Environment} {before after : Store} {value : Value}
    (completed : EvaluationSize size environment before output.expression value after) :
    ∃ child initial middle, child ≤ size ∧ (calls ≠ [] → child < size) ∧
      EvaluationSize child environment before input.expression initial middle ∧
      RunsFor (InvokeSized size environment context.internalReason) middle initial calls value after := by
  rw [receipt.code] at completed
  exact emit_complete_sized completed

/-- Renaming changes only the caller lookups. Actual stored closure captures
and body subderivations stay in the original native completion. -/
theorem Spine.renamed_completed_sized {program : CheckedProgram} {project : Projector} {context : Context}
    {caller : Specialized} {available : RuntimeEvidence} {scope : Scope}
    {node : SourceInference.ExpressionNode} {policy : SourceCoreFunctions.CallablePolicy}
    {input output : Lowered} {steps : List SourceInference.CoercionStep} {calls : List Call}
    (receipt : Spine program project context caller available scope node policy input steps output calls)
    (ξ : Renaming) {size : Nat} {environment : Environment} {before after : Store} {value : Value}
    (completed : EvaluationSize size environment before (output.expression.rename ξ) value after) :
    ∃ child initial middle, child ≤ size ∧ (calls ≠ [] → child < size) ∧
      EvaluationSize child environment before (input.expression.rename ξ) initial middle ∧
      RunsFor (InvokeSized size environment context.internalReason) middle initial (calls.map (Call.rename ξ)) value after := by
  rw [receipt.code, emit_rename] at completed
  obtain ⟨child, initial, middle, inclusive, strict, operand, runs⟩ := emit_complete_sized completed
  exact ⟨child, initial, middle, inclusive, fun nonempty => strict (by simpa using nonempty), operand, runs⟩

/-- Actual compiler success and finite completion determine the ordered native
trace. This includes absent globals and failures returned by actual bodies. -/
theorem Spine.completed_iff {program : CheckedProgram} {project : Projector} {context : Context}
    {caller : Specialized} {available : RuntimeEvidence} {scope : Scope}
    {node : SourceInference.ExpressionNode} {policy : SourceCoreFunctions.CallablePolicy}
    {input output : Lowered} {steps : List SourceInference.CoercionStep} {calls : List Call}
    (receipt : Spine program project context caller available scope node policy input steps output calls)
    {environment : Environment} {before after : Store} {value : Value} :
    Evaluates environment before output.expression value after ↔
      ∃ initial middle, Evaluates environment before input.expression initial middle ∧
        Runs environment context.internalReason middle initial calls value after := by
  rw [receipt.code]
  exact emit_evaluates_iff

/-- Hidden temporary slots are handled by renaming the real emitted code. The
native trace observes closures in that actual environment without modifying
stored captures. -/
theorem Spine.renamed_completed_iff {program : CheckedProgram} {project : Projector} {context : Context}
    {caller : Specialized} {available : RuntimeEvidence} {scope : Scope}
    {node : SourceInference.ExpressionNode} {policy : SourceCoreFunctions.CallablePolicy}
    {input output : Lowered} {steps : List SourceInference.CoercionStep} {calls : List Call}
    (receipt : Spine program project context caller available scope node policy input steps output calls)
    (ξ : Renaming) {environment : Environment} {before after : Store} {value : Value} :
    Evaluates environment before (output.expression.rename ξ) value after ↔
      ∃ initial middle, Evaluates environment before (input.expression.rename ξ) initial middle ∧
        Runs environment context.internalReason middle initial (calls.map (Call.rename ξ)) value after := by
  rw [receipt.code, emit_rename]
  exact emit_evaluates_iff

/-- An earlier language failure skips every method, even if those globals are
absent. The final result has the compiler's actual output tag and exact store. -/
theorem Spine.input_failure {program : CheckedProgram} {project : Projector} {context : Context}
    {caller : Specialized} {available : RuntimeEvidence} {scope : Scope}
    {node : SourceInference.ExpressionNode} {policy : SourceCoreFunctions.CallablePolicy}
    {input output : Lowered} {steps : List SourceInference.CoercionStep} {calls : List Call}
    (receipt : Spine program project context caller available scope node policy input steps output calls)
    {environment : Environment} {before after : Store} {payload : Value}
    (failed : Evaluates environment before input.expression (.inLeft input.type payload) after) :
    Evaluates environment before output.expression (.inLeft output.type payload) after := by
  rw [receipt.code, ← receipt.final_type]
  exact failure_suffix calls failed

end Solcore.SourceSemantics.CoreLowering.CallableCoercionSpine
