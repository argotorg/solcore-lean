import Solcore.Frontend.RustHull.RecursiveProgramCorrespondence

/-! Named calls cross local declaration, assignment, discarded expression and
return frames. A local deliberately shares the callee's name, so the test also
checks separation of source variables from installed global function cells. -/
set_option autoImplicit false
namespace Tests.RustHullLocalCallsCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence

private def v (name : String) : Expr := ⟨.word, .var name, none⟩
private def invoke (name : String) (arguments : List Expr) : Expr := ⟨.word, .call name arguments, none⟩
private def incremented (value : Core.Word) : Core.Word := Core.Word.add value (Core.Word.ofNatModulo 1)
private def incBody : Expr := invoke "primAddWord" [v "n", ⟨.word, .word "1", none⟩]

def incFunction : Function := {
  name := "inc", args := [{name := "n", ty := .word}], ret := .word,
  body := [⟨.returnStmt incBody, none⟩]
}

def mainFunction : Function := {
  name := "main", args := [{name := "input", ty := .word}], ret := .word,
  body := [⟨.letDecl "inc" .word, none⟩,
    ⟨.assign (v "inc") (invoke "inc" [v "input"]), none⟩,
    ⟨.expression (invoke "inc" [v "inc"]), none⟩,
    ⟨.returnStmt (invoke "inc" [v "inc"]), none⟩]
}

def program : Program := {entryPoints := ["main"], functions := [mainFunction, incFunction], objects := []}

private theorem inc_call_eligible (name : String) :
    RecursiveExpression program.functions (invoke "inc" [v name]) := by
  apply RecursiveExpression.named (function := incFunction) rfl
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst argument
  exact .var _ _ _

theorem program_eligible : RecursiveProgram program.functions := by
  intro function member statement statementMember
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · simp only [mainFunction, List.mem_cons, List.not_mem_nil, or_false] at statementMember
    rcases statementMember with rfl | rfl | rfl | rfl
    · simp only [RecursiveStatement]
    · simpa only [RecursiveStatement, v] using inc_call_eligible "input"
    · simpa only [RecursiveStatement] using inc_call_eligible "inc"
    · simpa only [RecursiveStatement] using inc_call_eligible "inc"
  · simp only [incFunction, List.mem_cons, List.not_mem_nil, or_false] at statementMember
    subst statement
    simp only [RecursiveStatement]
    apply RecursiveExpression.builtin (operation := .binary .add) rfl (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .var _ _ _
    · exact .word _ _ _

private def pushed {σ : Type} (state : Semantics.State σ) (value : Core.Word) : Semantics.State σ :=
  {state with heap := state.heap ++ [.word value]}

theorem inc_source {σ : Type} (effects : Semantics.ExternalSemantics σ)
    (state : Semantics.State σ) (value : Core.Word) :
    Semantics.EvalFunction program.functions effects incFunction [.word value] state
      (.value (.word (incremented value))) (pushed state value) := by
  have read : Semantics.EvalExpr program.functions effects [("n", state.heap.length)]
      (v "n") (pushed state value) (.value (.word value)) (pushed state value) := by
    have evaluated := Semantics.EvalExpr.var (functions := program.functions) (effects := effects)
      (env := [("n", state.heap.length)]) (state := pushed state value) (expression := v "n") rfl
    simpa [pushed, Semantics.readResult, Semantics.lookupLocation] using evaluated
  apply Semantics.EvalFunction.body (control := .returned (.word (incremented value)))
  · rfl
  · apply Semantics.EvalStatements.stop
    · intros; intro equality; cases equality
    · apply Semantics.EvalStmt.returned rfl
      apply Semantics.EvalExpr.call rfl
      · exact .cons read (.cons (.word (text := "1") rfl) .nil)
      · exact .primitive (by rfl) rfl
    · intro equality; cases equality

def finalHeap (value : Core.Word) : List Semantics.Value :=
  [.word value, .word (incremented value), .word value,
    .word (incremented value), .word (incremented value)]

/-- The ignored call still allocates its argument, while both later calls read
the assigned local rather than replacing or mutating the installed function. -/
theorem main_source {σ : Type} (effects : Semantics.ExternalSemantics σ)
    (external : σ) (value : Core.Word) :
    Semantics.EvalFunction program.functions effects mainFunction [.word value]
      ⟨[], external⟩ (.value (.word (incremented (incremented value)))) ⟨finalHeap value, external⟩ := by
  let initialized : Semantics.State σ := ⟨[.word value, .word (Core.Word.ofNatModulo 0)], external⟩
  let afterCall := pushed initialized value
  let assigned : Semantics.State σ := ⟨[.word value, .word (incremented value), .word value], external⟩
  let ignored := pushed assigned (incremented value)
  let environment : Semantics.Environment := [("inc", 1), ("input", 0)]
  have readInput : Semantics.EvalExpr program.functions effects environment (v "input") initialized
      (.value (.word value)) initialized := by
    have evaluated := Semantics.EvalExpr.var (functions := program.functions) (effects := effects)
      (env := environment) (state := initialized) (expression := v "input") rfl
    simpa [environment, initialized, Semantics.readResult, Semantics.lookupLocation] using evaluated
  have first : Semantics.EvalExpr program.functions effects environment (invoke "inc" [v "input"]) initialized
      (.value (.word (incremented value))) afterCall := by
    apply Semantics.EvalExpr.call rfl
    · exact .cons readInput .nil
    · exact .function (function := incFunction) (by rfl) (inc_source effects initialized value)
  have readAssigned : Semantics.EvalExpr program.functions effects environment (v "inc") assigned
      (.value (.word (incremented value))) assigned := by
    have evaluated := Semantics.EvalExpr.var (functions := program.functions) (effects := effects)
      (env := environment) (state := assigned) (expression := v "inc") rfl
    simpa [environment, assigned, Semantics.readResult, Semantics.lookupLocation] using evaluated
  have second : Semantics.EvalExpr program.functions effects environment (invoke "inc" [v "inc"]) assigned
      (.value (.word (incremented (incremented value)))) ignored := by
    apply Semantics.EvalExpr.call rfl
    · exact .cons readAssigned .nil
    · exact .function (function := incFunction) (by rfl) (inc_source effects assigned (incremented value))
  have readIgnored : Semantics.EvalExpr program.functions effects environment (v "inc") ignored
      (.value (.word (incremented value))) ignored := by
    have evaluated := Semantics.EvalExpr.var (functions := program.functions) (effects := effects)
      (env := environment) (state := ignored) (expression := v "inc") rfl
    simpa [environment, ignored, assigned, pushed, Semantics.readResult, Semantics.lookupLocation] using evaluated
  have third : Semantics.EvalExpr program.functions effects environment (invoke "inc" [v "inc"]) ignored
      (.value (.word (incremented (incremented value)))) ⟨finalHeap value, external⟩ := by
    apply Semantics.EvalExpr.call rfl
    · exact .cons readIgnored .nil
    · exact .function (function := incFunction) (by rfl) (inc_source effects ignored (incremented value))
  apply Semantics.EvalFunction.body (control := .returned (.word (incremented (incremented value))))
  · rfl
  · apply Semantics.EvalStatements.declare rfl (by rfl)
    apply Semantics.EvalStatements.next
    · intros; intro equality; cases equality
    · exact .assign (final := assigned) rfl first (by
        simp [Semantics.assignResult, Semantics.place?, v, Semantics.lookupLocation,
          afterCall, pushed, initialized, Semantics.updateProduct?, Semantics.write?, assigned])
    · apply Semantics.EvalStatements.next
      · intros; intro equality; cases equality
      · exact .expression rfl second
      · apply Semantics.EvalStatements.stop
        · intros; intro equality; cases equality
        · exact .returned rfl third
        · intro equality; cases equality

private theorem main_signature {inputs : List String} {prepared : ScalarExecution.Prepared}
    (accepted : ScalarExecution.prepare program "main" inputs 64 = .ok prepared) :
    prepared.compiled.parameters = [.word] ∧ prepared.compiled.result = .word := by
  obtain ⟨compiled, argument, checked, _, rfl⟩ := ScalarExecution.prepare_components accepted
  obtain ⟨own, allocated, assembled, rfl⟩ := StatementCorrespondence.compile_components checked
  obtain ⟨signatures, codes, function, code, index, _, selected, signatureCompiled, _⟩ :=
    assemble_selection assembled
  have actualSelected : program.functions.find? (·.name == "main") = some mainFunction := rfl
  have same : mainFunction = function := Option.some.inj (actualSelected.symm.trans selected)
  subst function
  have computed : signature 64 mainFunction = .ok (⟨"main", [.word], .word⟩ : Signature) := rfl
  rw [computed] at signatureCompiled
  cases signatureCompiled
  exact ⟨rfl, rfl⟩

/-- The sole operational premise is actual preparation. Parsed inputs,
assignment, all three named calls, the exact source heap and every public
checkpoint chain are connected for every Word, including overflow. -/
theorem main_public {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ)
    {inputs : List String} {prepared : ScalarExecution.Prepared}
    (accepted : ScalarExecution.prepare program "main" inputs 64 = .ok prepared) :
    ∃ value world finalStore required,
      ScalarExecution.InputsRel [.word] inputs [.word value] ∧
      HeapRel world (finalHeap value) finalStore ∧
      ∀ fuel additional last, ScalarExecution.Resumes (ScalarExecution.run prepared fuel) additional last →
        (last = .done (.inRight .word (.word (incremented (incremented value)))) finalStore ↔
          required ≤ fuel + additional) ∧
        ((∃ checkpoint, last = .outOfFuel checkpoint) ↔ fuel + additional < required) := by
  have ⟨parameters, resultType⟩ := main_signature accepted
  obtain ⟨function, sources, selected, inputsRelated, execute⟩ :=
    prepare_recursive_program_resumes accepted program_eligible external (effects := effects)
  have actualSelected : program.functions.find? (·.name == "main") = some mainFunction := rfl
  have same : mainFunction = function := Option.some.inj (actualSelected.symm.trans selected)
  subst function
  rw [parameters] at inputsRelated
  cases inputsRelated with
  | cons input tail =>
      cases tail
      cases input with
      | word parsed =>
          rename_i text value
          obtain ⟨world, target, finalStore, required, related, heap, completed⟩ :=
            execute _ _ (main_source effects external value)
          rw [resultType] at related
          cases related with
          | value related =>
              cases related
              exact ⟨value, world, finalStore, required, .cons (.word parsed) .nil, heap, completed⟩

private def check (input : Core.Word) (expected : Core.Word) : IO Unit := do
  let prepared ← match ScalarExecution.prepare program "main" [toString input.val] 64 with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError s!"local calls: preparation failed: {reprStr error}")
  let checkpoint ← match ScalarExecution.run prepared 0 with
    | .outOfFuel checkpoint => pure checkpoint
    | result => throw (IO.userError s!"local calls: zero fuel completed: {reprStr result}")
  let checkpoint ← match ScalarExecution.resume checkpoint 37 with
    | .outOfFuel checkpoint => pure checkpoint
    | result => throw (IO.userError s!"local calls: short resume completed: {reprStr result}")
  match ScalarExecution.resume checkpoint 10000 with
  | .done (.inRight .word (.word value)) store =>
      unless value == expected do throw (IO.userError "local calls: incorrect result")
      let expectedHeap := (finalHeap input).map fun source => match source with
        | .word word => Core.Value.inRight .unit (.word word)
        | _ => Core.Value.unit
      unless store.drop 2 == expectedHeap do
        throw (IO.userError "local calls: incorrect assignment/call heap")
  | result => throw (IO.userError s!"local calls: resume failed: {reprStr result}")

def run : IO Unit := do
  check (Core.Word.ofNatModulo 40) (Core.Word.ofNatModulo 42)
  check (Core.Word.ofNatModulo (Core.wordModulus - 1)) (Core.Word.ofNatModulo 1)

end Tests.RustHullLocalCallsCorrespondence
