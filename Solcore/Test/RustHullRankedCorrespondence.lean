import Solcore.Frontend.RustHull.RankedProgramCorrespondence

/-! Three actual functions, with the selected entry in the middle of the
installation list. Named calls appear inside other calls and pure arithmetic;
source derivations cover arbitrary Word values and the exact growing heap. -/
set_option autoImplicit false
namespace Tests.RustHullRankedCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence

private def v (name : String) : Expr := ⟨.word, .var name, none⟩
private def invoke (name : String) (arguments : List Expr) : Expr := ⟨.word, .call name arguments, none⟩
private def twiceBody : Expr := invoke "mulWord" [v "value", ⟨.word, .word "2", none⟩]
private def quadBody : Expr := invoke "twice" [invoke "twice" [v "value"]]
private def weightedBody : Expr := invoke "primAddWord" [invoke "quad" [v "left"], v "right"]

def twiceFunction : Function := {
  name := "twice", args := [{name := "value", ty := .word}], ret := .word,
  body := [⟨.returnStmt twiceBody, none⟩]
}

def quadFunction : Function := {
  name := "quad", args := [{name := "value", ty := .word}], ret := .word,
  body := [⟨.returnStmt quadBody, none⟩]
}

def weightedFunction : Function := {
  name := "weighted", args := [{name := "left", ty := .word}, {name := "right", ty := .word}], ret := .word,
  body := [⟨.returnStmt weightedBody, none⟩]
}

def functions : List Function := [quadFunction, weightedFunction, twiceFunction]

def program : Program := {entryPoints := ["weighted"], functions, objects := []}

def rank (name : String) : Nat := if name = "weighted" then 2 else if name = "quad" then 1 else 0

theorem twice_eligible : ∀ statement ∈ twiceFunction.body,
    RankedStatement functions rank (rank twiceFunction.name) statement := by
  intro statement member
  simp only [twiceFunction, List.mem_cons, List.not_mem_nil, or_false] at member
  subst statement
  apply RankedExpression.builtin (operation := .binary .mul) rfl (by rfl)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact .var _ _ _
  · exact .word _ _ _

theorem quad_eligible : ∀ statement ∈ quadFunction.body,
    RankedStatement functions rank (rank quadFunction.name) statement := by
  intro statement member
  simp only [quadFunction, List.mem_cons, List.not_mem_nil, or_false] at member
  subst statement
  apply RankedExpression.named (function := twiceFunction) rfl (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst argument
  apply RankedExpression.named (function := twiceFunction) rfl (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst argument
  exact .var _ _ _

theorem weighted_eligible : ∀ statement ∈ weightedFunction.body,
    RankedStatement functions rank (rank weightedFunction.name) statement := by
  intro statement member
  simp only [weightedFunction, List.mem_cons, List.not_mem_nil, or_false] at member
  subst statement
  apply RankedExpression.builtin (operation := .binary .add) rfl (by rfl)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · apply RankedExpression.named (function := quadFunction) rfl (by decide)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    subst argument
    exact .var _ _ _
  · exact .var _ _ _

theorem program_eligible : ∀ function ∈ program.functions, ∀ statement ∈ function.body,
    RankedStatement program.functions rank (rank function.name) statement := by
  intro function member
  simp only [program, functions, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact quad_eligible
  · exact weighted_eligible
  · exact twice_eligible

private def doubled (value : Core.Word) : Core.Word := Core.Word.mul value (Core.Word.ofNatModulo 2)
private def pushed {σ : Type} (state : Semantics.State σ) (value : Core.Word) : Semantics.State σ :=
  {state with heap := state.heap ++ [.word value]}

private theorem read_pushed {σ : Type} (effects : Semantics.ExternalSemantics σ)
    (state : Semantics.State σ) (value : Core.Word) :
    Semantics.EvalExpr functions effects [("value", state.heap.length)] (v "value") (pushed state value)
      (.value (.word value)) (pushed state value) := by
  have evaluated := Semantics.EvalExpr.var (functions := functions) (effects := effects)
    (env := [("value", state.heap.length)]) (state := pushed state value) (expression := v "value") rfl
  simpa [pushed, Semantics.readResult, Semantics.lookupLocation] using evaluated

theorem twice_source {σ : Type} (effects : Semantics.ExternalSemantics σ)
    (state : Semantics.State σ) (value : Core.Word) :
    Semantics.EvalFunction functions effects twiceFunction [.word value] state
      (.value (.word (doubled value))) (pushed state value) := by
  apply Semantics.EvalFunction.body (control := .returned (.word (doubled value)))
  · rfl
  · apply Semantics.EvalStatements.stop
    · intros; intro equality; cases equality
    · apply Semantics.EvalStmt.returned rfl
      apply Semantics.EvalExpr.call rfl
      · have two : Semantics.EvalExpr functions effects [("value", state.heap.length)]
            (⟨.word, .word "2", none⟩ : Expr) (pushed state value)
            (.value (.word (Core.Word.ofNatModulo 2))) (pushed state value) := .word (text := "2") rfl
        exact .cons (read_pushed effects state value) (.cons two .nil)
      · exact .primitive (by rfl) rfl
    · intro equality; cases equality

theorem quad_source {σ : Type} (effects : Semantics.ExternalSemantics σ)
    (state : Semantics.State σ) (value : Core.Word) :
    Semantics.EvalFunction functions effects quadFunction [.word value] state
      (.value (.word (doubled (doubled value)))) (pushed (pushed (pushed state value) value) (doubled value)) := by
  have inner : Semantics.EvalExpr functions effects [("value", state.heap.length)]
      (invoke "twice" [v "value"]) (pushed state value)
      (.value (.word (doubled value))) (pushed (pushed state value) value) := by
    apply Semantics.EvalExpr.call rfl
    · exact .cons (read_pushed effects state value) .nil
    · exact .function (by rfl) (twice_source effects (pushed state value) value)
  apply Semantics.EvalFunction.body (control := .returned (.word (doubled (doubled value))))
  · rfl
  · apply Semantics.EvalStatements.stop
    · intros; intro equality; cases equality
    · apply Semantics.EvalStmt.returned rfl
      apply Semantics.EvalExpr.call rfl
      · exact .cons inner .nil
      · exact .function (by rfl) (twice_source effects (pushed (pushed state value) value) (doubled value))
    · intro equality; cases equality

theorem weighted_source {σ : Type} (effects : Semantics.ExternalSemantics σ)
    (external : σ) (left right : Core.Word) :
    Semantics.EvalFunction functions effects weightedFunction [.word left, .word right]
      ⟨[], external⟩ (.value (.word (Core.Word.add (doubled (doubled left)) right)))
      ⟨[.word left, .word right, .word left, .word left, .word (doubled left)], external⟩ := by
  let state : Semantics.State σ := ⟨[.word left, .word right], external⟩
  let final : Semantics.State σ := pushed (pushed (pushed state left) left) (doubled left)
  let environment : Semantics.Environment := [("right", 1), ("left", 0)]
  have readLeft : Semantics.EvalExpr functions effects environment (v "left") state
      (.value (.word left)) state := by
    have evaluated := Semantics.EvalExpr.var (functions := functions) (effects := effects)
      (env := environment) (state := state) (expression := v "left") rfl
    simpa [environment, state, Semantics.readResult, Semantics.lookupLocation] using evaluated
  have readRight : Semantics.EvalExpr functions effects environment (v "right") final
      (.value (.word right)) final := by
    have evaluated := Semantics.EvalExpr.var (functions := functions) (effects := effects)
      (env := environment) (state := final) (expression := v "right") rfl
    simpa [environment, state, final, pushed, Semantics.readResult, Semantics.lookupLocation] using evaluated
  have inner : Semantics.EvalExpr functions effects environment (invoke "quad" [v "left"]) state
      (.value (.word (doubled (doubled left)))) final := by
    apply Semantics.EvalExpr.call rfl
    · exact .cons readLeft .nil
    · exact .function (by rfl) (quad_source effects state left)
  apply Semantics.EvalFunction.body (control := .returned (.word (Core.Word.add (doubled (doubled left)) right)))
  · rfl
  · apply Semantics.EvalStatements.stop
    · intros; intro equality; cases equality
    · apply Semantics.EvalStmt.returned rfl
      apply Semantics.EvalExpr.call rfl
      · exact .cons inner (.cons readRight .nil)
      · exact .primitive (by rfl) rfl
    · intro equality; cases equality

private theorem weighted_signature {inputs : List String} {prepared : ScalarExecution.Prepared}
    (accepted : ScalarExecution.prepare program "weighted" inputs 64 = .ok prepared) :
    prepared.compiled.parameters = [.word, .word] ∧ prepared.compiled.result = .word := by
  obtain ⟨compiled, argument, checked, _, rfl⟩ := ScalarExecution.prepare_components accepted
  obtain ⟨own, allocated, assembled, rfl⟩ := StatementCorrespondence.compile_components checked
  obtain ⟨signatures, codes, function, code, index, _, selected, signatureCompiled, _⟩ :=
    assemble_selection assembled
  have actualSelected : program.functions.find? (·.name == "weighted") = some weightedFunction := rfl
  have same : weightedFunction = function := Option.some.inj (actualSelected.symm.trans selected)
  subst function
  have computed : signature 64 weightedFunction =
      .ok (⟨"weighted", [.word, .word], .word⟩ : Signature) := rfl
  rw [computed] at signatureCompiled
  cases signatureCompiled
  exact ⟨rfl, rfl⟩

/-- Actual public preparation is the only operational premise. Source inputs,
all three installed closures, nested calls, the exact result and source heap,
and every finite checkpoint chain are connected through the generic theorem. -/
theorem weighted_public {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ)
    {inputs : List String} {prepared : ScalarExecution.Prepared}
    (accepted : ScalarExecution.prepare program "weighted" inputs 64 = .ok prepared) :
    ∃ left right world finalStore required,
      ScalarExecution.InputsRel [.word, .word] inputs [.word left, .word right] ∧
      HeapRel world [.word left, .word right, .word left, .word left, .word (doubled left)] finalStore ∧
      ∀ fuel additional last, ScalarExecution.Resumes (ScalarExecution.run prepared fuel) additional last →
        (last = .done (.inRight .word (.word (Core.Word.add (doubled (doubled left)) right))) finalStore ↔
          required ≤ fuel + additional) ∧
        ((∃ checkpoint, last = .outOfFuel checkpoint) ↔ fuel + additional < required) := by
  have ⟨parameters, resultType⟩ := weighted_signature accepted
  obtain ⟨function, sources, selected, inputsRelated, execute⟩ :=
    prepare_ranked_program_resumes accepted program_eligible external (effects := effects)
  have actualSelected : program.functions.find? (·.name == "weighted") = some weightedFunction := rfl
  have same : weightedFunction = function := Option.some.inj (actualSelected.symm.trans selected)
  subst function
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
  let prepared ← match ScalarExecution.prepare program "weighted" inputs 64 with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError s!"ranked calls: preparation failed: {reprStr error}")
  let checkpoint ← match ScalarExecution.run prepared 0 with
    | .outOfFuel checkpoint => pure checkpoint
    | result => throw (IO.userError s!"ranked calls: zero fuel completed: {reprStr result}")
  let checkpoint ← match ScalarExecution.resume checkpoint 37 with
    | .outOfFuel checkpoint => pure checkpoint
    | result => throw (IO.userError s!"ranked calls: short resume completed: {reprStr result}")
  match ScalarExecution.resume checkpoint 10000 with
  | .done (.inRight .word (.word value)) _ =>
      unless value == expected do throw (IO.userError "ranked calls: incorrect result")
  | result => throw (IO.userError s!"ranked calls: resume failed: {reprStr result}")

def run : IO Unit := do
  check ["10", "2"] (Core.Word.ofNatModulo 42)
  let maximum := Core.Word.ofNatModulo (Core.wordModulus - 1)
  check [toString maximum.val, "3"] maximum

end Tests.RustHullRankedCorrespondence
