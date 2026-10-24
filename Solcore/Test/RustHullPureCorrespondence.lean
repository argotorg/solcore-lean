import Solcore.Frontend.RustHull.PureFunctionCorrespondence

/-! An arbitrary-word source derivation and public checkpoint regression for a
function with nested pure builtin calls. The source proof uses its own rules. -/
set_option autoImplicit false
namespace Tests.RustHullPureCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence

private def varExpr (name : String) : Expr := ⟨.word, .var name, none⟩
private def twice : Expr := ⟨.word, .call "mulWord"
  [varExpr "left", ⟨.word, .word "2", none⟩], none⟩
private def weightedExpression : Expr := ⟨.word, .call "primAddWord" [twice, varExpr "right"], none⟩

def weightedFunction : Function := {
  name := "weighted"
  args := [{name := "left", ty := .word}, {name := "right", ty := .word}]
  ret := .word
  body := [⟨.returnStmt weightedExpression, none⟩]
}

def weightedProgram : Program := {
  entryPoints := ["weighted"]
  functions := [weightedFunction]
  objects := []
}

theorem weighted_eligible : ∀ statement ∈ weightedFunction.body,
    PureStatement [weightedFunction] statement := by
  intro statement member
  simp only [weightedFunction, List.mem_cons, List.not_mem_nil, or_false] at member
  subst statement
  change PureExpression [weightedFunction] weightedExpression
  apply PureExpression.call (operation := .binary .add) rfl (by rfl)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · apply PureExpression.call (operation := .binary .mul) rfl (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .var _ _ _
    · exact .word _ _ _
  · exact .var _ _ _

theorem weighted_source {σ : Type} (effects : Semantics.ExternalSemantics σ)
    (external : σ) (left right : Core.Word) :
    Semantics.EvalFunction [weightedFunction] effects weightedFunction [.word left, .word right]
      ⟨[], external⟩ (.value (.word (Core.Word.add (Core.Word.mul left (Core.Word.ofNatModulo 2)) right)))
      ⟨[.word left, .word right], external⟩ := by
  let state : Semantics.State σ := ⟨[.word left, .word right], external⟩
  let environment : Semantics.Environment := [("right", 1), ("left", 0)]
  have readLeft : Semantics.EvalExpr [weightedFunction] effects environment (varExpr "left") state
      (.value (.word left)) state := by
    have read := Semantics.EvalExpr.var (functions := [weightedFunction]) (effects := effects)
      (env := environment) (state := state) (expression := varExpr "left") rfl
    simpa [environment, state, Semantics.readResult, Semantics.lookupLocation] using read
  have readRight : Semantics.EvalExpr [weightedFunction] effects environment (varExpr "right") state
      (.value (.word right)) state := by
    have read := Semantics.EvalExpr.var (functions := [weightedFunction]) (effects := effects)
      (env := environment) (state := state) (expression := varExpr "right") rfl
    simpa [environment, state, Semantics.readResult, Semantics.lookupLocation] using read
  have two : Semantics.EvalExpr [weightedFunction] effects environment
      (⟨.word, .word "2", none⟩ : Expr) state (.value (.word (Core.Word.ofNatModulo 2))) state := by
    exact .word (text := "2") rfl
  have doubled : Semantics.EvalExpr [weightedFunction] effects environment twice state
      (.value (.word (Core.Word.mul left (Core.Word.ofNatModulo 2)))) state := by
    apply Semantics.EvalExpr.call rfl
    · exact .cons readLeft (.cons two .nil)
    · exact .primitive (by rfl) rfl
  apply Semantics.EvalFunction.body (control :=
    .returned (.word (Core.Word.add (Core.Word.mul left (Core.Word.ofNatModulo 2)) right)))
  · rfl
  · apply Semantics.EvalStatements.stop
    · intros; intro equality; cases equality
    · apply Semantics.EvalStmt.returned rfl
      apply Semantics.EvalExpr.call rfl
      · exact .cons doubled (.cons readRight .nil)
      · exact .primitive (by rfl) rfl
    · intro equality; cases equality

private theorem weighted_signature {inputs : List String} {prepared : ScalarExecution.Prepared}
    (accepted : ScalarExecution.prepare weightedProgram "weighted" inputs 64 = .ok prepared) :
    prepared.compiled.parameters = [.word, .word] ∧ prepared.compiled.result = .word := by
  obtain ⟨compiled, argument, checked, _, rfl⟩ := ScalarExecution.prepare_components accepted
  obtain ⟨own, allocated, assembled, rfl⟩ := StatementCorrespondence.compile_components checked
  obtain ⟨_, signatureCompiled, _, _, _⟩ := assemble_single_components assembled
  have computed : signature 64 weightedFunction =
      .ok (⟨"weighted", [.word, .word], .word⟩ : Signature) := rfl
  change signature 64 weightedFunction = .ok own at signatureCompiled
  rw [computed] at signatureCompiled
  cases signatureCompiled
  exact ⟨rfl, rfl⟩

/-- This instance discharges the independent source execution as well as the
syntactic eligibility. Successful public preparation is the only operational
premise, and the source input words come from its actual parser. -/
theorem weighted_public {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ)
    {inputs : List String} {prepared : ScalarExecution.Prepared}
    (accepted : ScalarExecution.prepare weightedProgram "weighted" inputs 64 = .ok prepared) :
    ∃ left right world finalStore required,
      ScalarExecution.InputsRel [.word, .word] inputs [.word left, .word right] ∧
      HeapRel world [.word left, .word right] finalStore ∧
      ∀ fuel additional last, ScalarExecution.Resumes (ScalarExecution.run prepared fuel) additional last →
        (last = .done (.inRight .word (.word (Core.Word.add (Core.Word.mul left (Core.Word.ofNatModulo 2)) right)))
          finalStore ↔ required ≤ fuel + additional) ∧
        ((∃ checkpoint, last = .outOfFuel checkpoint) ↔ fuel + additional < required) := by
  have ⟨parameters, resultType⟩ := weighted_signature accepted
  obtain ⟨sources, inputsRelated, execute⟩ := prepare_pure_function_resumes rfl accepted weighted_eligible external
    (effects := effects)
  rw [parameters] at inputsRelated
  cases inputsRelated with
  | cons leftInput tail =>
      cases tail with
      | cons rightInput tail =>
          cases tail
          cases leftInput with
          | word leftParsed =>
              cases rightInput with
              | word rightParsed =>
                  rename_i leftText rightText left right
                  obtain ⟨world, target, finalStore, required, related, heap, completed⟩ :=
                    execute _ _ (weighted_source effects external left right) ⟨_, rfl⟩
                  rw [resultType] at related
                  cases related with
                  | value related =>
                      cases related
                      exact ⟨left, right, world, finalStore, required,
                        .cons (.word leftParsed) (.cons (.word rightParsed) .nil), heap, completed⟩

private def check (inputs : List String) (expected : Core.Word) : IO Unit := do
  let prepared ← match ScalarExecution.prepare weightedProgram "weighted" inputs 64 with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError s!"nested pure calls: preparation failed: {reprStr error}")
  let checkpoint ← match ScalarExecution.run prepared 0 with
    | .outOfFuel checkpoint => pure checkpoint
    | result => throw (IO.userError s!"zero fuel unexpectedly completed: {reprStr result}")
  let checkpoint ← match ScalarExecution.resume checkpoint 7 with
    | .outOfFuel checkpoint => pure checkpoint
    | result => throw (IO.userError s!"short first resume unexpectedly completed: {reprStr result}")
  match ScalarExecution.resume checkpoint 10000 with
  | .done (.inRight .word (.word value)) _ =>
      unless value == expected do throw (IO.userError "nested pure calls: incorrect result")
  | result => throw (IO.userError s!"nested pure calls: resume failed: {reprStr result}")

def run : IO Unit := do
  check ["21", "0"] (Core.Word.ofNatModulo 42)
  let maximum := Core.Word.ofNatModulo (Core.wordModulus - 1)
  check [toString maximum.val, "1"] maximum

end Tests.RustHullPureCorrespondence
