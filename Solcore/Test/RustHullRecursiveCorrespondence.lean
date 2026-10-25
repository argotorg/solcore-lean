import Solcore.Frontend.RustHull.RecursiveProgramCorrespondence

/-! A genuine recursive Hull function: decrement the Word parameter until zero,
then return 42. The independent source execution is derived for every Word
input, including its complete parameter-allocation heap. -/
set_option autoImplicit false
namespace Tests.RustHullRecursiveCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence

private def v : Expr := ⟨.word, .var "remaining", none⟩
private def literal (text : String) : Expr := ⟨.word, .word text, none⟩
private def test : Expr := ⟨.bool, .call "eq" [v, literal "0"], none⟩
private def predecessor : Expr := ⟨.word, .call "subWord" [v, literal "1"], none⟩
private def recursiveCall : Expr := ⟨.word, .call "countdown" [predecessor], none⟩
private def answerCall : Expr := ⟨.word, .call "answer" [], none⟩
private def body : Expr := ⟨.word, .ifThen .word test answerCall recursiveCall, none⟩

def answer : Function := {
  name := "answer", args := [], ret := .word,
  body := [⟨.returnStmt (literal "42"), none⟩]
}

def countdown : Function := {
  name := "countdown", args := [{name := "remaining", ty := .word}], ret := .word,
  body := [⟨.returnStmt body, none⟩]
}

def program : Program := {entryPoints := ["countdown"], functions := [countdown, answer], objects := []}

theorem countdown_eligible : ∀ statement ∈ countdown.body,
    RecursiveStatement program.functions statement := by
  intro statement statementMember
  simp only [countdown, List.mem_cons, List.not_mem_nil, or_false] at statementMember
  subst statement
  simp only [RecursiveStatement]
  apply RecursiveExpression.conditional
  · apply RecursiveExpression.builtin (operation := .comparison .eq) rfl (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .var _ _ _
    · exact .word _ _ _
  · apply RecursiveExpression.named (function := answer) rfl
    intro argument member
    cases member
  · apply RecursiveExpression.named (function := countdown) rfl
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    subst argument
    apply RecursiveExpression.builtin (operation := .binary .sub) rfl (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .var _ _ _
    · exact .word _ _ _

theorem program_eligible : RecursiveProgram program.functions := by
  intro function member
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact countdown_eligible
  · intro statement member
    simp only [answer, List.mem_cons, List.not_mem_nil, or_false] at member
    subst statement
    simp only [RecursiveStatement]
    exact .word _ _ _

/-- Every recursive invocation allocates its actual remaining counter. -/
def countdownHeap : Nat → List Semantics.Value
  | 0 => [.word (Core.Word.ofNatModulo 0)]
  | n + 1 => .word (Core.Word.ofNatModulo (n + 1)) :: countdownHeap n

private def pushed {σ : Type} (state : Semantics.State σ) (value : Core.Word) : Semantics.State σ :=
  {state with heap := state.heap ++ [.word value]}

private theorem read_pushed {σ : Type} (effects : Semantics.ExternalSemantics σ)
    (state : Semantics.State σ) (value : Core.Word) :
    Semantics.EvalExpr program.functions effects [("remaining", state.heap.length)] v (pushed state value)
      (.value (.word value)) (pushed state value) := by
  have evaluated := Semantics.EvalExpr.var (functions := program.functions) (effects := effects)
    (env := [("remaining", state.heap.length)]) (state := pushed state value) (expression := v) rfl
  simpa [pushed, Semantics.readResult, Semantics.lookupLocation] using evaluated

private theorem word_predecessor (n : Nat) (bound : n + 1 < Core.wordModulus) :
    Core.Word.sub (Core.Word.ofNatModulo (n + 1)) (Core.Word.ofNatModulo 1) = Core.Word.ofNatModulo n := by
  have small : n < Core.wordModulus := Nat.lt_trans (Nat.lt_succ_self n) bound
  change Core.Word.ofNatModulo (n + 1) - Core.Word.ofNatModulo 1 = _
  apply Fin.ext
  rw [Fin.sub_val_of_le (by
    change 1 % Core.wordModulus ≤ (n + 1) % Core.wordModulus
    rw [Nat.mod_eq_of_lt bound]
    exact Nat.le_trans (Nat.mod_le _ _) (Nat.succ_le_succ (Nat.zero_le n)))]
  simp only [Core.Word.ofNatModulo, Nat.mod_eq_of_lt bound, Nat.mod_eq_of_lt small]
  have one : 1 % Core.wordModulus = 1 := by decide
  rw [one]
  exact Nat.add_sub_cancel n 1

private theorem word_successor_not_zero (n : Nat) (bound : n + 1 < Core.wordModulus) :
    (Core.Word.ofNatModulo (n + 1) == Core.Word.ofNatModulo 0) = false := by
  apply beq_eq_false_iff_ne.mpr
  intro same
  have values := congrArg Fin.val same
  simp [Core.Word.ofNatModulo, Nat.mod_eq_of_lt bound] at values

theorem answer_source {σ : Type} (effects : Semantics.ExternalSemantics σ) (state : Semantics.State σ) :
    Semantics.EvalFunction program.functions effects answer [] state
      (.value (.word (Core.Word.ofNatModulo 42))) state := by
  apply Semantics.EvalFunction.body (control := .returned (.word (Core.Word.ofNatModulo 42)))
  · rfl
  · apply Semantics.EvalStatements.stop
    · intros; intro equality; cases equality
    · exact .returned rfl (.word (text := "42") rfl)
    · intro equality; cases equality

/-- A finite source derivation exists for every counter below the Word modulus.
The induction is on this concrete source computation, not the call graph. -/
theorem countdown_source {σ : Type} (effects : Semantics.ExternalSemantics σ)
    (n : Nat) (bound : n < Core.wordModulus) (state : Semantics.State σ) :
    Semantics.EvalFunction program.functions effects countdown [.word (Core.Word.ofNatModulo n)] state
      (.value (.word (Core.Word.ofNatModulo 42)))
      {state with heap := state.heap ++ countdownHeap n} := by
  induction n generalizing state with
  | zero =>
      apply Semantics.EvalFunction.body (control := .returned (.word (Core.Word.ofNatModulo 42)))
      · rfl
      · apply Semantics.EvalStatements.stop
        · intros; intro equality; cases equality
        · apply Semantics.EvalStmt.returned rfl
          apply Semantics.EvalExpr.ifTrue (value := .bool true) rfl
          · apply Semantics.EvalExpr.call rfl
            · exact .cons (read_pushed effects state (Core.Word.ofNatModulo 0))
                (.cons (.word (text := "0") rfl) .nil)
            · exact .primitive (by rfl) rfl
          · rfl
          · apply Semantics.EvalExpr.call rfl
            · exact .nil
            · exact .function (function := answer) (by rfl) (answer_source effects _)
        · intro equality; cases equality
  | succ n ih =>
      let allocated := pushed state (Core.Word.ofNatModulo (n + 1))
      let env : Semantics.Environment := [("remaining", state.heap.length)]
      have tested : Semantics.EvalExpr program.functions effects env test allocated
          (.value (.bool false)) allocated := by
        apply Semantics.EvalExpr.call rfl
        · exact .cons (read_pushed effects state (Core.Word.ofNatModulo (n + 1)))
            (.cons (.word (text := "0") rfl) .nil)
        · apply Semantics.EvalCall.primitive (by rfl)
          change some (Semantics.booleanResult .bool
            (Core.Word.ofNatModulo (n + 1) == Core.Word.ofNatModulo 0)) = some (.value (.bool false))
          rw [word_successor_not_zero n bound]
          rfl
      have previous : Semantics.EvalExpr program.functions effects env predecessor allocated
          (.value (.word (Core.Word.ofNatModulo n))) allocated := by
        apply Semantics.EvalExpr.call rfl
        · exact .cons (read_pushed effects state (Core.Word.ofNatModulo (n + 1)))
            (.cons (.word (text := "1") rfl) .nil)
        · apply Semantics.EvalCall.primitive (by rfl)
          change some (Semantics.Result.value (Semantics.Value.word (Core.Word.sub (Core.Word.ofNatModulo (n + 1))
            (Core.Word.ofNatModulo 1)))) = some (Semantics.Result.value (Semantics.Value.word (Core.Word.ofNatModulo n)))
          rw [word_predecessor n bound]
      have called := ih (Nat.lt_trans (Nat.lt_succ_self n) bound) allocated
      have selected : Semantics.EvalExpr program.functions effects env recursiveCall allocated
          (.value (.word (Core.Word.ofNatModulo 42)))
          {state with heap := state.heap ++ countdownHeap (n + 1)} := by
        apply Semantics.EvalExpr.call rfl
        · exact .cons previous .nil
        · apply Semantics.EvalCall.function (function := countdown) (by rfl)
          simpa [allocated, pushed, countdownHeap, List.append_assoc] using called
      apply Semantics.EvalFunction.body (control := .returned (.word (Core.Word.ofNatModulo 42)))
      · rfl
      · apply Semantics.EvalStatements.stop
        · intros; intro equality; cases equality
        · exact .returned rfl (.ifFalse (value := .bool false) rfl tested rfl selected)
        · intro equality; cases equality

theorem countdown_source_word {σ : Type} (effects : Semantics.ExternalSemantics σ)
    (value : Core.Word) (state : Semantics.State σ) :
    Semantics.EvalFunction program.functions effects countdown [.word value] state
      (.value (.word (Core.Word.ofNatModulo 42)))
      {state with heap := state.heap ++ countdownHeap value.val} := by
  have canonical : Core.Word.ofNatModulo value.val = value := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt value.isLt
  simpa only [canonical] using countdown_source effects value.val value.isLt state

private theorem countdown_signature {inputs : List String} {prepared : ScalarExecution.Prepared}
    (accepted : ScalarExecution.prepare program "countdown" inputs 64 = .ok prepared) :
    prepared.compiled.parameters = [.word] ∧ prepared.compiled.result = .word := by
  obtain ⟨compiled, argument, checked, _, rfl⟩ := ScalarExecution.prepare_components accepted
  obtain ⟨own, allocated, assembled, rfl⟩ := StatementCorrespondence.compile_components checked
  obtain ⟨signatures, codes, function, code, index, _, selected, signatureCompiled, _⟩ :=
    assemble_selection assembled
  have actualSelected : program.functions.find? (·.name == "countdown") = some countdown := rfl
  have same : countdown = function := Option.some.inj (actualSelected.symm.trans selected)
  subst function
  have computed : signature 64 countdown =
      .ok (⟨"countdown", [.word], .word⟩ : Signature) := rfl
  rw [computed] at signatureCompiled
  cases signatureCompiled
  exact ⟨rfl, rfl⟩

/-- Successful actual preparation supplies the Word argument. Its independent
recursive source execution is derived here for every such input, so no source
evaluation or body-preservation premise is left to callers. Every genuine
checkpoint chain preserves the result and the complete allocation trace. -/
theorem countdown_public {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ)
    {inputs : List String} {prepared : ScalarExecution.Prepared}
    (accepted : ScalarExecution.prepare program "countdown" inputs 64 = .ok prepared) :
    ∃ value world finalStore required,
      ScalarExecution.InputsRel [.word] inputs [.word value] ∧
      HeapRel world (countdownHeap value.val) finalStore ∧
      ∀ fuel additional last, ScalarExecution.Resumes (ScalarExecution.run prepared fuel) additional last →
        (last = .done (.inRight .word (.word (Core.Word.ofNatModulo 42))) finalStore ↔
          required ≤ fuel + additional) ∧
        ((∃ checkpoint, last = .outOfFuel checkpoint) ↔ fuel + additional < required) := by
  have ⟨parameters, resultType⟩ := countdown_signature accepted
  obtain ⟨function, sources, selected, inputsRelated, execute⟩ :=
    prepare_recursive_program_resumes accepted program_eligible external (effects := effects)
  have actualSelected : program.functions.find? (·.name == "countdown") = some countdown := rfl
  have same : countdown = function := Option.some.inj (actualSelected.symm.trans selected)
  subst function
  rw [parameters] at inputsRelated
  cases inputsRelated with
  | cons input tail =>
      cases tail
      cases input with
      | word parsed =>
          rename_i text value
          obtain ⟨world, target, finalStore, required, related, heap, completed⟩ :=
            execute _ _ (countdown_source_word effects value ⟨[], external⟩)
          rw [resultType] at related
          cases related with
          | value related =>
              cases related
              exact ⟨value, world, finalStore, required, .cons (.word parsed) .nil, heap, completed⟩

private def check (counter : Nat) : IO Unit := do
  let prepared ← match ScalarExecution.prepare program "countdown" [toString counter] 64 with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError s!"recursive calls: preparation failed: {reprStr error}")
  let checkpoint ← match ScalarExecution.run prepared 0 with
    | .outOfFuel checkpoint => pure checkpoint
    | result => throw (IO.userError s!"recursive calls: zero fuel completed: {reprStr result}")
  let checkpoint ← match ScalarExecution.resume checkpoint 7 with
    | .outOfFuel checkpoint => pure checkpoint
    | result => throw (IO.userError s!"recursive calls: short resume completed: {reprStr result}")
  match ScalarExecution.resume checkpoint 100000 with
  | .done (.inRight .word (.word value)) store =>
      unless value == Core.Word.ofNatModulo 42 do
        throw (IO.userError "recursive calls: incorrect result")
      let expected := (countdownHeap counter).map fun source => match source with
        | .word word => Core.Value.inRight .unit (.word word)
        | _ => Core.Value.unit
      unless store.drop 2 == expected do
        throw (IO.userError "recursive calls: incorrect recursive parameter heap")
  | result => throw (IO.userError s!"recursive calls: resume failed: {reprStr result}")

def run : IO Unit := do
  check 0
  check 5
  check 12

end Tests.RustHullRecursiveCorrespondence
