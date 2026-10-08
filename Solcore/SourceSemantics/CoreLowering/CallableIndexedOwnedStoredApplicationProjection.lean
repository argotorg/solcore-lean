import Solcore.SourceSemantics.CoreLowering.CallableIndirectCallBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaCalls

/-! The pure application suffix of the original indirect call uses four
administrative environment entries. Its payload application has the same
measured body, captures, argument and stores after those pure reads. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredApplicationProjection
open Core CoreProof

/-- Preserve the exact grade while identifying only the original pure reads. -/
theorem to_payload {size : Nat} {environment : Core.Environment}
    {before after : Store} {function token argument arityToken value : Value}
    (evaluation : EvaluationSize size (arityToken :: argument :: token :: function :: environment) before
      (.apply (.second (.first (.var 3))) (.var 1)) value after) :
    EvaluationSize size [function, argument] before CallableIndexedLambdaCalls.applyPayload value after := by
  cases evaluation with
  | apply selected parameter body =>
      cases selected with
      | second tagged =>
          cases tagged with
          | first lookup =>
              cases lookup with
              | var found =>
                  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at found
                  cases Option.some.inj found
                  cases parameter with
                  | var read =>
                      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at read
                      cases Option.some.inj read
                      exact .apply (.second (.first (.var rfl))) (.var rfl) body

/-- Reinsert the same administrative entries without changing the body grade. -/
theorem from_payload {size : Nat} {environment : Core.Environment}
    {before after : Store} {function token argument arityToken value : Value}
    (evaluation : EvaluationSize size [function, argument] before
      CallableIndexedLambdaCalls.applyPayload value after) :
    EvaluationSize size (arityToken :: argument :: token :: function :: environment) before
      (.apply (.second (.first (.var 3))) (.var 1)) value after := by
  cases evaluation with
  | apply selected parameter body =>
      cases selected with
      | second tagged =>
          cases tagged with
          | first lookup =>
              cases lookup with
              | var found =>
                  simp only [List.getElem?_cons_zero] at found
                  cases Option.some.inj found
                  cases parameter with
                  | var read =>
                      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at read
                      cases Option.some.inj read
                      exact .apply (.second (.first (.var rfl))) (.var rfl) body

/-- Both original expressions have identical measured completion certificates. -/
theorem measured_iff {size : Nat} {environment : Core.Environment}
    {before after : Store} {function token argument arityToken value : Value} :
    EvaluationSize size (arityToken :: argument :: token :: function :: environment) before
      (.apply (.second (.first (.var 3))) (.var 1)) value after ↔
    EvaluationSize size [function, argument] before CallableIndexedLambdaCalls.applyPayload value after :=
  ⟨to_payload, from_payload⟩

/-- The existing finite-size theorem supplies the grade for ordinary completion. -/
theorem evaluates_to_payload {environment : Core.Environment}
    {before after : Store} {function token argument arityToken value : Value}
    (evaluation : Evaluates (arityToken :: argument :: token :: function :: environment) before
      (.apply (.second (.first (.var 3))) (.var 1)) value after) :
    Evaluates [function, argument] before CallableIndexedLambdaCalls.applyPayload value after := by
  obtain ⟨size, measured⟩ := evaluation_has_size evaluation
  exact (to_payload measured).sound

/-- Completion reuses the original body and exact stores under the actual prefix. -/
theorem evaluates_from_payload {environment : Core.Environment}
    {before after : Store} {function token argument arityToken value : Value}
    (evaluation : Evaluates [function, argument] before CallableIndexedLambdaCalls.applyPayload value after) :
    Evaluates (arityToken :: argument :: token :: function :: environment) before
      (.apply (.second (.first (.var 3))) (.var 1)) value after := by
  obtain ⟨size, measured⟩ := evaluation_has_size evaluation
  exact (from_payload measured).sound

theorem evaluates_iff {environment : Core.Environment}
    {before after : Store} {function token argument arityToken value : Value} :
    Evaluates (arityToken :: argument :: token :: function :: environment) before
      (.apply (.second (.first (.var 3))) (.var 1)) value after ↔
    Evaluates [function, argument] before CallableIndexedLambdaCalls.applyPayload value after :=
  ⟨evaluates_to_payload, evaluates_from_payload⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredApplicationProjection
