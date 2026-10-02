import Solcore.SourceSemantics.CoreLowering.CallableCoercionSpineCertificates
import Solcore.Core.Renaming

/-! Finite native execution of the actual ordered coercion calls. Saved closure
code and captures are observed from the store, without identifying them with a
source method body. Source coercion judgments need that separate connection. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionSpine
open Core Frontend

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
theorem call_complete {environment : Environment} {reason : Word} {call : Call}
    {before after : Store} {value : Value} {arguments : Expr}
    (completed : Evaluates environment before (SourceCoreCalls.call call.signature call.index arguments reason) value after) :
    ∃ input middle, Evaluates environment before arguments input middle ∧
      Invoke environment reason call middle input value after := by
  cases completed with
  | caseLeft argument branch =>
    cases branch with
    | inLeft payload =>
      cases payload with
      | var found =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at found
        subst_vars
        exact ⟨_, _, argument, .skipped⟩
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
                  exact ⟨_, _, argument, .absent (by simpa using reference) read⟩
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
                      exact ⟨_, _, argument, .applied (by simpa using reference) read body⟩

theorem emit_evaluates_iff {environment : Environment} {reason : Word} {calls : List Call}
    {before after : Store} {input : Expr} {value : Value} :
    Evaluates environment before (emit reason input calls) value after ↔
      ∃ initial middle, Evaluates environment before input initial middle ∧
        Runs environment reason middle initial calls value after := by
  induction calls generalizing input with
  | nil =>
    constructor
    · intro completed; exact ⟨_, _, completed, .nil⟩
    · rintro ⟨_, _, first, runs⟩; cases runs; exact first
  | cons call calls ih =>
    constructor
    · intro completed
      obtain ⟨result, reached, head, tail⟩ := ih.mp completed
      obtain ⟨initial, middle, first, invoked⟩ := call_complete head
      exact ⟨initial, middle, first, .cons invoked tail⟩
    · rintro ⟨initial, middle, first, runs⟩
      cases runs with
      | cons invoked tail => exact ih.mpr ⟨_, _, invoked.evaluates first, tail⟩

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
