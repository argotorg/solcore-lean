import Solcore.Frontend.RustHull.RecursiveProgramCorrespondence
import Solcore.Frontend.RustHull.Contract
import Solcore.Frontend.RustHull.PureFunctionCorrespondence
import Solcore.Frontend.RustHull.RankedProgramCorrespondence
import Solcore.Frontend.RustHull.ScalarExecutionSafety
import Solcore.Frontend.RustHull.YulLowering
import Solcore.Core.Machine
import Solcore.Frontend.RustHull.ContractCallModeExecutionCorrespondence
import Solcore.Frontend.RustHull.ContractCallModeSupported

/-!
# Hull correspondence tests

Hull meaning against Core: pure, ranked and recursive programs, local calls, loops, matches, products,
lowering and Yul.
-/

section
-- leanmerge: from Solcore.Test.RustHullLocalCallsCorrespondence
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
    · simp only [ExecutableStatement]
    · simpa only [ExecutableStatement, v] using inc_call_eligible "input"
    · simpa only [ExecutableStatement] using inc_call_eligible "inc"
    · simpa only [ExecutableStatement] using inc_call_eligible "inc"
  · simp only [incFunction, List.mem_cons, List.not_mem_nil, or_false] at statementMember
    subst statement
    simp only [ExecutableStatement]
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
end

section
-- leanmerge: from Solcore.Test.RustHullLoopCorrespondence
/-! Loop regressions use independent Hull derivations before invoking the real
compiler and public checkpoint API. Named calls in the condition and body
allocate source cells, while loop closures add separate Core-only cells. -/
set_option autoImplicit false
namespace Tests.RustHullLoopCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence

private def word (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def v (name : String) : Expr := ⟨.word, .var name, none⟩
private def lit (text : String) : Expr := ⟨.word, .word text, none⟩
private def invoke (name : String) (args : List Expr) (type : Ty := .word) : Expr := ⟨type, .call name args, none⟩
private def assign (name : String) (rhs : Expr) : Stmt := ⟨.assign (v name) rhs, none⟩
private def ret (value : Expr) : Stmt := ⟨.returnStmt value, none⟩
private def decl (name : String) : Stmt := ⟨.letDecl name .word, none⟩
private def continuing : Stmt := ⟨.continueStmt, none⟩
private def breaking : Stmt := ⟨.breakStmt, none⟩
private def yes : Expr := ⟨.bool, .bool true, none⟩
private def forever (post body : List Stmt) : Stmt := ⟨.forLoop [] yes post body, none⟩
private def condition : Expr := invoke "positive" [v "remaining"] .bool
private def loopBody : List Stmt :=
  [assign "total" (invoke "plus" [v "total", v "remaining"]), continuing, assign "total" (lit "999")]
private def loopPost : List Stmt :=
  [assign "remaining" (invoke "subWord" [v "remaining", lit "1"]), continuing, assign "total" (lit "999")]
private def loopInit : List Stmt := [decl "remaining", assign "remaining" (lit "3")]
private def loop : Stmt := ⟨.forLoop loopInit condition loopPost loopBody, none⟩

def positive : Function := {
  name := "positive", args := [{name := "value", ty := .word}], ret := .bool,
  body := [ret (invoke "gtWord" [v "value", lit "0"] .bool)]
}

def plus : Function := {
  name := "plus", args := [{name := "left", ty := .word}, {name := "right", ty := .word}], ret := .word,
  body := [ret (invoke "primAddWord" [v "left", v "right"])]
}

def sumLoop : Function := {
  name := "sumLoop", args := [], ret := .word,
  body := [decl "total", loop, ret (v "total")]
}

def breakBody : Function := {
  name := "breakBody", args := [], ret := .word,
  body := [decl "total", forever [assign "total" (lit "999")]
    [assign "total" (lit "7"), breaking, assign "total" (lit "999")], ret (v "total")]
}

def breakPost : Function := {
  name := "breakPost", args := [], ret := .word,
  body := [decl "total", forever [breaking, assign "total" (lit "999")]
    [assign "total" (lit "7")], ret (v "total")]
}

def nestedReturn : Function := {
  name := "nestedReturn", args := [], ret := .word,
  body := [forever [ret (lit "999")]
    [⟨.block [forever [ret (lit "888")] [ret (lit "9")]], none⟩], ret (lit "777")]
}

def nestedBreak : Function := {
  name := "nestedBreak", args := [], ret := .word,
  body := [forever [ret (lit "999")]
    [forever [] [breaking], ret (lit "11")], ret (lit "777")]
}

def postReturn : Function := {
  name := "postReturn", args := [], ret := .word,
  body := [decl "total", forever [ret (v "total"), assign "total" (lit "999")]
    [assign "total" (lit "13")], ret (lit "777")]
}

def program : Program := {
  entryPoints := ["sumLoop", "breakBody", "breakPost", "nestedReturn", "nestedBreak", "postReturn"],
  functions := [positive, sumLoop, plus, breakBody, breakPost, nestedReturn, nestedBreak, postReturn], objects := []
}

private theorem literal_eligible (text : String) : RecursiveExpression program.functions (lit text) := .word _ _ _
private theorem variable_eligible (name : String) : RecursiveExpression program.functions (v name) := .var _ _ _
private theorem yes_eligible : RecursiveExpression program.functions yes := .bool _ _ _

private theorem positive_eligible : RecursiveExpression program.functions
    (invoke "gtWord" [v "value", lit "0"] .bool) := by
  apply RecursiveExpression.builtin (operation := .comparison .gt) rfl (by rfl)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact variable_eligible _
  · exact literal_eligible _

private theorem plus_eligible : RecursiveExpression program.functions
    (invoke "primAddWord" [v "left", v "right"]) := by
  apply RecursiveExpression.builtin (operation := .binary .add) rfl (by rfl)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> exact variable_eligible _

private theorem condition_eligible : RecursiveExpression program.functions condition := by
  apply RecursiveExpression.named (function := positive) rfl
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst argument
  exact variable_eligible _

private theorem body_eligible : RecursiveExpression program.functions (invoke "plus" [v "total", v "remaining"]) := by
  apply RecursiveExpression.named (function := plus) rfl
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> exact variable_eligible _

private theorem post_eligible : RecursiveExpression program.functions (invoke "subWord" [v "remaining", lit "1"]) := by
  apply RecursiveExpression.builtin (operation := .binary .sub) rfl (by rfl)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact variable_eligible _
  · exact literal_eligible _

theorem program_eligible : RecursiveProgram program.functions := by
  intro function member
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [positive, sumLoop, plus, breakBody, breakPost, nestedReturn, nestedBreak, postReturn,
      ret, decl, assign, v, loop, loopInit, loopBody, loopPost, forever, continuing, breaking,
      ExecutableStatement, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, true_and, and_true]
  · exact positive_eligible
  · exact ⟨⟨literal_eligible _, condition_eligible, ⟨post_eligible, literal_eligible _⟩, body_eligible, literal_eligible _⟩,
      variable_eligible _⟩
  · exact plus_eligible
  · exact ⟨⟨yes_eligible, literal_eligible _, literal_eligible _, literal_eligible _⟩, variable_eligible _⟩
  · exact ⟨⟨yes_eligible, literal_eligible _, literal_eligible _⟩, variable_eligible _⟩
  · exact ⟨⟨yes_eligible, literal_eligible _, yes_eligible, literal_eligible _, literal_eligible _⟩,
      literal_eligible _⟩
  · exact ⟨⟨yes_eligible, literal_eligible _, yes_eligible, literal_eligible _⟩,
      literal_eligible _⟩
  · exact ⟨⟨yes_eligible, ⟨variable_eligible _, literal_eligible _⟩, literal_eligible _⟩, literal_eligible _⟩

private def state {σ : Type} (external : σ) (total remaining : Core.Word) (trace : List Semantics.Value) : Semantics.State σ :=
  ⟨[.word total, .word remaining] ++ trace, external⟩
private def env : Semantics.Environment := [("remaining", 1), ("total", 0)]

private theorem read {σ : Type} (effects : Semantics.ExternalSemantics σ)
    {environment : Semantics.Environment} {initial : Semantics.State σ}
    {name : String} {value : Semantics.Value}
    (found : Semantics.readResult environment initial name = .value value) :
    Semantics.EvalExpr program.functions effects environment (v name) initial (.value value) initial := by
  simpa only [found] using (Semantics.EvalExpr.var (functions := program.functions) (effects := effects)
    (env := environment) (state := initial) (expression := v name) rfl)

theorem positive_source {σ : Type} (effects : Semantics.ExternalSemantics σ)
    (initial : Semantics.State σ) (value : Core.Word) :
    Semantics.EvalFunction program.functions effects positive [.word value] initial
      (.value (.bool (decide (value.val > 0)))) {initial with heap := initial.heap ++ [.word value]} := by
  apply Semantics.EvalFunction.body (control := .returned (.bool (decide (value.val > 0))))
    (env := [("value", initial.heap.length)])
    (allocated := {initial with heap := initial.heap ++ [.word value]})
  · rfl
  · apply Semantics.EvalStatements.stop
    · intros; intro same; cases same
    · apply Semantics.EvalStmt.returned rfl
      apply Semantics.EvalExpr.call (values := [.word value, .word (word 0)]) rfl
      · refine .cons (read effects ?_) (.cons (.word (text := "0") rfl) .nil)
        simp [Semantics.readResult, Semantics.lookupLocation]
      · exact .primitive (by rfl) rfl
    · intro same; cases same

theorem plus_source {σ : Type} (effects : Semantics.ExternalSemantics σ)
    (initial : Semantics.State σ) (left right : Core.Word) :
    Semantics.EvalFunction program.functions effects plus [.word left, .word right] initial
      (.value (.word (Core.Word.add left right)))
      {initial with heap := initial.heap ++ [.word left, .word right]} := by
  apply Semantics.EvalFunction.body (control := .returned (.word (Core.Word.add left right)))
    (env := [("right", initial.heap.length + 1), ("left", initial.heap.length)])
    (allocated := {initial with heap := initial.heap ++ [.word left, .word right]})
  · simp [plus, Semantics.bindArguments, Semantics.allocate, List.append_assoc]
  · apply Semantics.EvalStatements.stop
    · intros; intro same; cases same
    · apply Semantics.EvalStmt.returned rfl
      apply Semantics.EvalExpr.call (values := [.word left, .word right]) rfl
      · refine .cons (read effects ?_) (.cons (read effects ?_) .nil)
        · simp [Semantics.readResult, Semantics.lookupLocation]
        · simp [Semantics.readResult, Semantics.lookupLocation]
      · exact .primitive (by rfl) rfl
    · intro same; cases same

private theorem condition_source {σ : Type} (effects : Semantics.ExternalSemantics σ)
    (external : σ) (total remaining : Core.Word) (trace : List Semantics.Value) :
    Semantics.EvalExpr program.functions effects env condition (state external total remaining trace)
      (.value (.bool (decide (remaining.val > 0))))
      (state external total remaining (trace ++ [.word remaining])) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (read effects rfl) .nil
  · apply Semantics.EvalCall.function (function := positive) (by rfl)
    simpa [state, List.append_assoc] using positive_source effects (state external total remaining trace) remaining

private theorem body_source {σ : Type} (effects : Semantics.ExternalSemantics σ)
    (external : σ) (total remaining : Core.Word) (trace : List Semantics.Value) :
    Semantics.EvalStatements program.functions effects env loopBody (state external total remaining trace)
      .continuing (state external (Core.Word.add total remaining) remaining
        (trace ++ [.word total, .word remaining])) := by
  apply Semantics.EvalStatements.next
    (middle := state external (Core.Word.add total remaining) remaining (trace ++ [.word total, .word remaining]))
  · intros; intro same; cases same
  · apply Semantics.EvalStmt.assign (value := .word (Core.Word.add total remaining)) rfl
    · apply Semantics.EvalExpr.call (values := [.word total, .word remaining]) rfl
      · exact .cons (read effects rfl) (.cons (read effects rfl) .nil)
      · apply Semantics.EvalCall.function (function := plus) (by rfl)
        exact plus_source effects _ total remaining
    · simp [Semantics.assignResult, Semantics.place?, Semantics.lookupLocation,
        Semantics.updateProduct?, Semantics.write?, state, env, v]
  · apply Semantics.EvalStatements.stop
    · intros; intro same; cases same
    · exact .continuing rfl
    · intro same; cases same

private theorem post_source {σ : Type} (effects : Semantics.ExternalSemantics σ)
    (external : σ) (total remaining : Core.Word) (trace : List Semantics.Value) :
    Semantics.EvalStatements program.functions effects env loopPost (state external total remaining trace)
      .continuing (state external total (Core.Word.sub remaining (word 1)) trace) := by
  apply Semantics.EvalStatements.next (middle := state external total (Core.Word.sub remaining (word 1)) trace)
  · intros; intro same; cases same
  · apply Semantics.EvalStmt.assign (value := .word (Core.Word.sub remaining (word 1))) rfl
    · apply Semantics.EvalExpr.call (values := [.word remaining, .word (word 1)]) rfl
      · exact .cons (read effects rfl) (.cons (.word (text := "1") rfl) .nil)
      · exact .primitive (by rfl) rfl
    · simp [Semantics.assignResult, Semantics.place?, Semantics.lookupLocation,
        Semantics.updateProduct?, Semantics.write?, state, env, v]
  · apply Semantics.EvalStatements.stop
    · intros; intro same; cases same
    · exact .continuing rfl
    · intro same; cases same

private theorem loop_step {σ : Type} (effects : Semantics.ExternalSemantics σ)
    (external : σ) (total remaining : Core.Word) (trace : List Semantics.Value)
    (positive : decide (remaining.val > 0) = true) {control : Semantics.Control} {final : Semantics.State σ}
    (next : Semantics.EvalLoop program.functions effects env condition loopPost loopBody
      (state external (Core.Word.add total remaining) (Core.Word.sub remaining (word 1))
        (trace ++ [.word remaining, .word total, .word remaining])) control final) :
    Semantics.EvalLoop program.functions effects env condition loopPost loopBody
      (state external total remaining trace) control final := by
  apply Semantics.EvalLoop.step (value := .bool true) (bodyControl := .continuing) (postControl := .continuing)
  · simpa only [positive] using condition_source effects external total remaining trace
  · rfl
  · exact body_source effects external total remaining _
  · exact Or.inr rfl
  · exact post_source effects external (Core.Word.add total remaining) remaining _
  · exact Or.inr rfl
  · simpa only [List.append_assoc, List.cons_append, List.nil_append] using next

private theorem loop_done {σ : Type} (effects : Semantics.ExternalSemantics σ)
    (external : σ) (total : Core.Word) (trace : List Semantics.Value) :
    Semantics.EvalLoop program.functions effects env condition loopPost loopBody
      (state external total (word 0) trace) .fallthrough
      (state external total (word 0) (trace ++ [.word (word 0)])) := by
  exact .done (value := .bool false) (condition_source effects external total (word 0) trace) rfl

def sourceHeap : List Semantics.Value :=
  ([6, 0, 3, 0, 3, 2, 3, 2, 1, 5, 1, 0] : List Nat).map (.word ∘ word)

theorem sum_loop_source {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ) :
    Semantics.EvalFunction program.functions effects sumLoop [] ⟨[], external⟩
      (.value (.word (word 6))) ⟨sourceHeap, external⟩ := by
  have iterated : Semantics.EvalLoop program.functions effects env condition loopPost loopBody
      (state external (word 0) (word 3) []) .fallthrough ⟨sourceHeap, external⟩ := by
    apply loop_step effects external (word 0) (word 3) [] rfl
    apply loop_step effects external (word 3) (word 2) _ rfl
    apply loop_step effects external (word 5) (word 1) _ rfl
    exact loop_done effects external (word 6) _
  apply Semantics.EvalFunction.body (control := .returned (.word (word 6)))
  · rfl
  · apply Semantics.EvalStatements.declare (name := "total") (value := .word (word 0)) rfl rfl
    apply Semantics.EvalStatements.next
    · intros; intro same; cases same
    · apply Semantics.EvalStmt.forInit (init := loopInit) (condition := condition)
        (post := loopPost) (body := loopBody) rfl (by decide)
      apply Semantics.EvalStatements.declare (name := "remaining") (value := .word (word 0)) rfl rfl
      apply Semantics.EvalStatements.next (middle := state external (word 0) (word 3) [])
      · intros; intro same; cases same
      · apply Semantics.EvalStmt.assign (value := .word (word 3)) rfl (.word (text := "3") rfl)
        simp [Semantics.assignResult, Semantics.place?, Semantics.lookupLocation,
          Semantics.updateProduct?, Semantics.write?, Semantics.allocate, state, v]
      · apply Semantics.EvalStatements.next
        · intros; intro same; cases same
        · exact .forLoop rfl iterated
        · exact .nil
    · apply Semantics.EvalStatements.stop
      · intros; intro same; cases same
      · exact .returned rfl (read effects rfl)
      · intro same; cases same

theorem break_body_source {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ) :
    Semantics.EvalFunction program.functions effects breakBody [] ⟨[], external⟩
      (.value (.word (word 7))) ⟨[.word (word 7)], external⟩ := by
  apply Semantics.EvalFunction.body (control := .returned (.word (word 7)))
  · rfl
  · apply Semantics.EvalStatements.declare (name := "total") (value := .word (word 0)) rfl rfl
    apply Semantics.EvalStatements.next
    · intros; intro same; cases same
    · apply Semantics.EvalStmt.forLoop rfl
      apply Semantics.EvalLoop.bodyBreak (value := .bool true) (.bool rfl) rfl
      apply Semantics.EvalStatements.next (middle := ⟨[.word (word 7)], external⟩)
      · intros; intro same; cases same
      · apply Semantics.EvalStmt.assign (value := .word (word 7)) rfl (.word (text := "7") rfl)
        simp [Semantics.assignResult, Semantics.place?, Semantics.lookupLocation,
          Semantics.updateProduct?, Semantics.write?, Semantics.allocate, v]
      · apply Semantics.EvalStatements.stop
        · intros; intro same; cases same
        · exact .breaking rfl
        · intro same; cases same
    · apply Semantics.EvalStatements.stop
      · intros; intro same; cases same
      · exact .returned rfl (read effects rfl)
      · intro same; cases same

theorem break_post_source {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ) :
    Semantics.EvalFunction program.functions effects breakPost [] ⟨[], external⟩
      (.value (.word (word 7))) ⟨[.word (word 7)], external⟩ := by
  apply Semantics.EvalFunction.body (control := .returned (.word (word 7)))
  · rfl
  · apply Semantics.EvalStatements.declare (name := "total") (value := .word (word 0)) rfl rfl
    apply Semantics.EvalStatements.next
    · intros; intro same; cases same
    · apply Semantics.EvalStmt.forLoop rfl
      apply Semantics.EvalLoop.postBreak (value := .bool true) (bodyControl := .fallthrough) (.bool rfl) rfl
      · apply Semantics.EvalStatements.next (middle := ⟨[.word (word 7)], external⟩)
        · intros; intro same; cases same
        · apply Semantics.EvalStmt.assign (value := .word (word 7)) rfl (.word (text := "7") rfl)
          simp [Semantics.assignResult, Semantics.place?, Semantics.lookupLocation,
            Semantics.updateProduct?, Semantics.write?, Semantics.allocate, v]
        · exact .nil
      · exact Or.inl rfl
      · apply Semantics.EvalStatements.stop
        · intros; intro same; cases same
        · exact .breaking rfl
        · intro same; cases same
    · apply Semantics.EvalStatements.stop
      · intros; intro same; cases same
      · exact .returned rfl (read effects rfl)
      · intro same; cases same

theorem nested_return_source {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ) :
    Semantics.EvalFunction program.functions effects nestedReturn [] ⟨[], external⟩
      (.value (.word (word 9))) ⟨[], external⟩ := by
  apply Semantics.EvalFunction.body (control := .returned (.word (word 9)))
  · rfl
  · apply Semantics.EvalStatements.stop
    · intros; intro same; cases same
    · apply Semantics.EvalStmt.forLoop rfl
      apply Semantics.EvalLoop.bodyStop (value := .bool true) (.bool rfl) rfl
      · apply Semantics.EvalStatements.stop
        · intros; intro same; cases same
        · apply Semantics.EvalStmt.block rfl
          apply Semantics.EvalStatements.stop
          · intros; intro same; cases same
          · apply Semantics.EvalStmt.forLoop rfl
            apply Semantics.EvalLoop.bodyStop (value := .bool true) (.bool rfl) rfl
            · apply Semantics.EvalStatements.stop
              · intros; intro same; cases same
              · exact .returned rfl (.word (text := "9") rfl)
              · intro same; cases same
            · exact Or.inl ⟨_, rfl⟩
          · intro same; cases same
        · intro same; cases same
      · exact Or.inl ⟨_, rfl⟩
    · intro same; cases same

theorem nested_break_source {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ) :
    Semantics.EvalFunction program.functions effects nestedBreak [] ⟨[], external⟩
      (.value (.word (word 11))) ⟨[], external⟩ := by
  apply Semantics.EvalFunction.body (control := .returned (.word (word 11)))
  · rfl
  · apply Semantics.EvalStatements.stop
    · intros; intro same; cases same
    · apply Semantics.EvalStmt.forLoop rfl
      apply Semantics.EvalLoop.bodyStop (value := .bool true) (.bool rfl) rfl
      · apply Semantics.EvalStatements.next
        · intros; intro same; cases same
        · apply Semantics.EvalStmt.forLoop rfl
          apply Semantics.EvalLoop.bodyBreak (value := .bool true) (.bool rfl) rfl
          apply Semantics.EvalStatements.stop
          · intros; intro same; cases same
          · exact .breaking rfl
          · intro same; cases same
        · apply Semantics.EvalStatements.stop
          · intros; intro same; cases same
          · exact .returned rfl (.word (text := "11") rfl)
          · intro same; cases same
      · exact Or.inl ⟨_, rfl⟩
    · intro same; cases same

theorem post_return_source {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ) :
    Semantics.EvalFunction program.functions effects postReturn [] ⟨[], external⟩
      (.value (.word (word 13))) ⟨[.word (word 13)], external⟩ := by
  apply Semantics.EvalFunction.body (control := .returned (.word (word 13)))
  · rfl
  · apply Semantics.EvalStatements.declare (name := "total") (value := .word (word 0)) rfl rfl
    apply Semantics.EvalStatements.stop
    · intros; intro same; cases same
    · apply Semantics.EvalStmt.forLoop rfl
      apply Semantics.EvalLoop.postStop (value := .bool true) (bodyControl := .fallthrough) (.bool rfl) rfl
      · apply Semantics.EvalStatements.next (middle := ⟨[.word (word 13)], external⟩)
        · intros; intro same; cases same
        · apply Semantics.EvalStmt.assign (value := .word (word 13)) rfl (.word (text := "13") rfl)
          simp [Semantics.assignResult, Semantics.place?, Semantics.lookupLocation,
            Semantics.updateProduct?, Semantics.write?, Semantics.allocate, v]
        · exact .nil
      · exact Or.inl rfl
      · apply Semantics.EvalStatements.stop
        · intros; intro same; cases same
        · exact .returned rfl (read effects rfl)
        · intro same; cases same
      · exact Or.inl ⟨_, rfl⟩
    · intro same; cases same

/-- Exact result and represented source heap for every real sequence of public
resumptions, including chains whose total fuel is insufficient. -/
def PublicResult (prepared : ScalarExecution.Prepared) (expected : Core.Word) (heap : Semantics.Heap) : Prop :=
  ∃ world finalStore required,
    HeapRel world heap finalStore ∧
    ∀ fuel additional last, ScalarExecution.Resumes (ScalarExecution.run prepared fuel) additional last →
      (last = .done (.inRight .word (.word expected)) finalStore ↔ required ≤ fuel + additional) ∧
      ((∃ checkpoint, last = .outOfFuel checkpoint) ↔ fuel + additional < required)

private theorem public_fixture {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ)
    {entry : String} {function : Function} {expected : Core.Word} {heap : Semantics.Heap}
    (selected : program.functions.find? (·.name == entry) = some function)
    (shape : function.args = [] ∧ function.ret = .word)
    (source : Semantics.EvalFunction program.functions effects function [] ⟨[], external⟩
      (.value (.word expected)) ⟨heap, external⟩)
    {prepared : ScalarExecution.Prepared}
    (accepted : ScalarExecution.prepare program entry [] 96 = .ok prepared) :
    PublicResult prepared expected heap := by
  have types : prepared.compiled.parameters = [] ∧ prepared.compiled.result = .word := by
    obtain ⟨compiled, argument, checked, _, rfl⟩ := ScalarExecution.prepare_components accepted
    obtain ⟨own, allocated, assembled, rfl⟩ := StatementCorrespondence.compile_components checked
    obtain ⟨signatures, codes, sourceFunction, code, index, _, sourceSelected, signatureCompiled, _⟩ :=
      assemble_selection assembled
    have same := Option.some.inj (selected.symm.trans sourceSelected)
    subst sourceFunction
    obtain ⟨arity, resultLowered⟩ := StatementCorrespondence.signature_components signatureCompiled
    rw [shape.1] at arity
    rw [shape.2] at resultLowered
    have resultSame : own.result = .word := by simpa only [lowerType, Pure.pure, Except.pure, Except.ok.injEq] using resultLowered.symm
    exact ⟨List.eq_nil_of_length_eq_zero arity.symm, resultSame⟩
  obtain ⟨sourceFunction, sources, sourceSelected, inputs, execute⟩ :=
    prepare_recursive_program_resumes accepted program_eligible external (effects := effects)
  have same := Option.some.inj (selected.symm.trans sourceSelected)
  subst sourceFunction
  rw [types.1] at inputs
  cases inputs
  obtain ⟨world, target, finalStore, required, related, relatedHeap, completed⟩ :=
    execute _ _ source
  rw [types.2] at related
  cases related with
  | value related =>
      cases related
      exact ⟨world, finalStore, required, relatedHeap, completed⟩

/-- This consumer's only operational premise is actual public preparation.
The full loop derivation, including named calls and both continue transfers,
is supplied by sum_loop_source rather than assumed from the caller. -/
theorem sum_loop_public {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ)
    {prepared : ScalarExecution.Prepared}
    (accepted : ScalarExecution.prepare program "sumLoop" [] 96 = .ok prepared) :
    PublicResult prepared (word 6) sourceHeap :=
  public_fixture effects external (function := sumLoop) rfl ⟨rfl, rfl⟩ (sum_loop_source effects external) accepted

theorem break_body_public {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ)
    {prepared : ScalarExecution.Prepared}
    (accepted : ScalarExecution.prepare program "breakBody" [] 96 = .ok prepared) :
    PublicResult prepared (word 7) [.word (word 7)] :=
  public_fixture effects external (function := breakBody) rfl ⟨rfl, rfl⟩ (break_body_source effects external) accepted

theorem break_post_public {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ)
    {prepared : ScalarExecution.Prepared}
    (accepted : ScalarExecution.prepare program "breakPost" [] 96 = .ok prepared) :
    PublicResult prepared (word 7) [.word (word 7)] :=
  public_fixture effects external (function := breakPost) rfl ⟨rfl, rfl⟩ (break_post_source effects external) accepted

theorem nested_return_public {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ)
    {prepared : ScalarExecution.Prepared}
    (accepted : ScalarExecution.prepare program "nestedReturn" [] 96 = .ok prepared) :
    PublicResult prepared (word 9) [] :=
  public_fixture effects external (function := nestedReturn) rfl ⟨rfl, rfl⟩ (nested_return_source effects external) accepted

theorem nested_break_public {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ)
    {prepared : ScalarExecution.Prepared}
    (accepted : ScalarExecution.prepare program "nestedBreak" [] 96 = .ok prepared) :
    PublicResult prepared (word 11) [] :=
  public_fixture effects external (function := nestedBreak) rfl ⟨rfl, rfl⟩ (nested_break_source effects external) accepted

theorem post_return_public {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ)
    {prepared : ScalarExecution.Prepared}
    (accepted : ScalarExecution.prepare program "postReturn" [] 96 = .ok prepared) :
    PublicResult prepared (word 13) [.word (word 13)] :=
  public_fixture effects external (function := postReturn) rfl ⟨rfl, rfl⟩ (post_return_source effects external) accepted

private def check (entry : String) (expected : Nat) (heap : List Semantics.Value) (loopCells : Nat) : IO Unit := do
  let prepared ← match ScalarExecution.prepare program entry [] 96 with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError s!"loop correspondence: {entry} preparation failed: {reprStr error}")
  let checkpoint ← match ScalarExecution.run prepared 0 with
    | .outOfFuel checkpoint => pure checkpoint
    | result => throw (IO.userError s!"loop correspondence: {entry} zero fuel completed: {reprStr result}")
  let checkpoint ← match ScalarExecution.resume checkpoint 17 with
    | .outOfFuel checkpoint => pure checkpoint
    | result => throw (IO.userError s!"loop correspondence: {entry} short resume completed: {reprStr result}")
  match ScalarExecution.resume checkpoint 100000 with
  | .done (.inRight .word (.word value)) store =>
      unless value == word expected do throw (IO.userError s!"loop correspondence: {entry} wrong result")
      unless store.length == program.functions.length + loopCells + heap.length do
        throw (IO.userError s!"loop correspondence: {entry} wrong loop allocation count")
      let sourceCells := store.filterMap fun cell => match cell with
        | .inRight .unit (.word value) => some (Semantics.Value.word value)
        | _ => none
      unless sourceCells == heap do throw (IO.userError s!"loop correspondence: {entry} wrong source heap")
  | result => throw (IO.userError s!"loop correspondence: {entry} resume failed: {reprStr result}")

def run : IO Unit := do
  check "sumLoop" 6 sourceHeap 1
  check "breakBody" 7 [.word (word 7)] 1
  check "breakPost" 7 [.word (word 7)] 1
  check "nestedReturn" 9 [] 2
  check "nestedBreak" 11 [] 2
  check "postReturn" 13 [.word (word 13)] 1

end Tests.RustHullLoopCorrespondence
end

section
-- leanmerge: from Solcore.Test.RustHullLowering
/-! Independent runtime and rejection regressions for imported Hull on Core. -/
set_option autoImplicit false
namespace Tests.RustHullLowering
open Solcore Solcore.Frontend.RustHull

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def get {α : Type} (label : String) : LowerM α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")

private def w (value : Nat) : Expr := ⟨.word, .word (toString value), none⟩
private def v (name : String) (ty : Ty := .word) : Expr := ⟨ty, .var name, none⟩
private def call (name : String) (args : List Expr) (ty : Ty := .word) : Expr := ⟨ty, .call name args, none⟩
private def stmt (kind : StmtKind) : Stmt := ⟨kind, none⟩
private def ret (value : Expr) : Stmt := stmt (.returnStmt value)
private def assign (name : String) (value : Expr) : Stmt := stmt (.assign (v name value.ty) value)
private def declareLocal (name : String) (ty : Ty := .word) : Stmt := stmt (.letDecl name ty)
private def fn (name : String) (names : List String) (body : List Stmt) (result : Ty := .word) : Function :=
  {name, args := names.map fun name => {name, ty := .word}, ret := result, body}
private def program (functions : List Function) : Program :=
  {entryPoints := ["main"], functions, objects := []}

private def wordResult (label : String) (source : Program) (expected : Nat)
    (arguments : List Nat := []) : IO Unit := do
  let compiled ← get label (compile source "main")
  let expression := Core.Expr.apply compiled.expression
    (bundle (arguments.map fun value => .word (Core.Word.ofNatModulo value)))
  match Core.runStateful 1000000 (.initial expression) with
  | .done (.inRight _ (.word value)) _ => do
    require (value.val == expected) s!"{label}: expected {expected}, received {value.val}"
  | result => throw (IO.userError s!"{label}: {reprStr result}")

private def rejects (label : String) (source : Program) : IO Unit :=
  match compile source "main" with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError s!"{label}: malformed Hull was accepted")

private def boolTy : Ty := .sum .unit .unit
private def conditional (condition : Expr) (yes no : List Stmt) : Stmt :=
  stmt (.matchStmt boolTy condition [
    {pat := {kind := .con .inr}, binder := "yes", body := yes},
    {pat := {kind := .con .inl}, binder := "no", body := no}])

private def yn (name : String) : YulName := {name}
private def yw (value : Nat) : YulExpr := ⟨.literal (.number (toString value)), none⟩
private def yc (name : String) (args : List YulExpr := []) : YulExpr :=
  ⟨.call (yn name) args, none⟩
private def ye (name : String) (args : List YulExpr := []) : YulStmt :=
  ⟨.expression (yc name args), none⟩
private def objectProgram (body : List YulStmt) : Program :=
  {entryPoints := [], functions := [], objects := [
    .object "runtime" {stmts := [stmt (.assembly body)], functions := []} [] none]}

private def prepare (label : String) (source : Program) (context : Contract.Context := {}) : IO Contract.Prepared :=
  get label (Contract.prepare source ["runtime"] context)

private def contractRejects (label : String) (source : Program) : IO Unit :=
  match Contract.prepare source ["runtime"] with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError s!"{label}: malformed runtime object was accepted")

private def returned (label : String) (outcome : Contract.Outcome) (expected : List UInt8)
    (storage : Core.WordMapping.Entries := []) : IO Unit :=
  match outcome with
  | .returned bytes actualStorage => do
    require (bytes == expected) s!"{label}: unexpected returned bytes {reprStr bytes}"
    require (actualStorage == storage) s!"{label}: unexpected storage {reprStr actualStorage}"
  | other => throw (IO.userError s!"{label}: {reprStr other}")

private def callsAndRecursion : IO Unit := do
  let weighted := fn "weighted" ["a", "b", "c"] [ret
    (call "add" [call "add" [call "mul" [v "a", w 100], call "mul" [v "b", w 10]], v "c"])]
  wordResult "three argument call" (program [weighted,
    fn "main" [] [ret (call "weighted" [w 1, w 3, w 5])]]) 135
  wordResult "local and function namespaces are separate" (program [weighted,
    fn "main" [] [declareLocal "weighted", assign "weighted" (w 99),
      ret (call "weighted" [w 1, w 3, w 5])]]) 135
  wordResult "parameter and function namespaces are separate" (program [weighted,
    fn "main" ["weighted"] [ret (call "weighted" [w 1, w 3, w 5])]]) 135 [99]
  let recurse : Expr := ⟨.word, .ifThen .word
    (call "eq" [v "n", w 0] boolTy) (w 1)
    (call "mul" [v "n", call "factorial" [call "sub" [v "n", w 1]]]), none⟩
  wordResult "recursive function cells" (program [
    fn "main" ["n"] [ret (call "factorial" [v "n"])],
    fn "factorial" ["n"] [ret recurse]]) 720 [6]
  let even : Expr := ⟨.word, .ifThen .word (call "eq" [v "n", w 0] boolTy)
    (w 1) (call "odd" [call "sub" [v "n", w 1]]), none⟩
  let odd : Expr := ⟨.word, .ifThen .word (call "eq" [v "n", w 0] boolTy)
    (w 0) (call "even" [call "sub" [v "n", w 1]]), none⟩
  wordResult "mutual recursion" (program [fn "odd" ["n"] [ret odd],
    fn "main" [] [ret (call "even" [w 8])], fn "even" ["n"] [ret even]]) 1

private def localsAndLoops : IO Unit := do
  wordResult "block local shadowing" (program [fn "main" [] [
    declareLocal "x", assign "x" (w 1), stmt (.block [declareLocal "x", assign "x" (w 99)]), ret (v "x")]]) 1
  wordResult "loop continue post and break" (program [fn "main" [] [
    declareLocal "total", assign "total" (w 0),
    stmt (.forLoop [declareLocal "i", assign "i" (w 0)] (call "lt" [v "i", w 10] boolTy)
      [assign "i" (call "add" [v "i", w 1])]
      [conditional (call "eq" [v "i", w 2] boolTy) [stmt .continueStmt] [],
       conditional (call "eq" [v "i", w 5] boolTy) [stmt .breakStmt] [],
       assign "total" (call "add" [v "total", v "i"])]), ret (v "total")]]) 8
  rejects "loop initializer scope ends" (program [fn "main" [] [
    stmt (.forLoop [declareLocal "i"] ⟨.bool, .bool false, none⟩ [] []), ret (v "i")]])
  wordResult "return exits enclosing loop" (program [fn "main" [] [
    stmt (.forLoop [] ⟨.bool, .bool true, none⟩ [] [ret (w 43)]), ret (w 99)]]) 43

private def productsAndMatches : IO Unit := do
  let payloadTy : Ty := .product .word .word
  let choiceTy : Ty := .sum .unit .word
  let selectArg : Function := {
    name := "select"
    args := [
      {name := "unused", ty := .unit}, {name := "pair", ty := payloadTy},
      {name := "choice", ty := choiceTy}]
    ret := .word
    body := [stmt (.matchStmt choiceTy (v "choice" choiceTy) [
      {pat := {kind := .con .inl}, binder := "u", body := [ret (w 0)]},
      {pat := {kind := .con .inr}, binder := "selected", body := [ret
        (call "add" [call "add" [
          call "mul" [⟨.word, .fst (v "pair" payloadTy), none⟩, w 100],
          call "mul" [⟨.word, .snd (v "pair" payloadTy), none⟩, w 10]], v "selected"])]}])]}
  wordResult "unit product and sum arguments" (program [selectArg, fn "main" [] [ret
    (call "select" [⟨.unit, .unit, none⟩, ⟨payloadTy, .pair (w 1) (w 3), none⟩,
      ⟨choiceTy, .inr choiceTy (w 5), none⟩])]]) 135
  let pairTy : Ty := .product .word (.product .word .word)
  let pair : Expr := ⟨pairTy, .pair (w 1) ⟨.product .word .word, .pair (w 2) (w 3), none⟩, none⟩
  let tail : Expr := ⟨.product .word .word, .snd (v "p" pairTy), none⟩
  let middle : Expr := ⟨.word, .fst tail, none⟩
  let first : Expr := ⟨.word, .fst (v "p" pairTy), none⟩
  let last : Expr := ⟨.word, .snd tail, none⟩
  wordResult "nested product assignment" (program [fn "main" [] [
    declareLocal "p" pairTy, assign "p" pair, stmt (.assign middle (w 7)),
    ret (call "add" [call "add" [call "mul" [first, w 100], call "mul" [middle, w 10]], last])]]) 173
  let sumTy : Ty := .sum .word (.sum .word .word)
  let sum : Expr := ⟨sumTy, .inK 2 sumTy (w 9), none⟩
  let arm (index bonus : Nat) : Alt := {
    pat := {kind := .con (.inK index)}, binder := "payload",
    body := [ret (call "add" [v "payload", w bonus])]}
  wordResult "third sum constructor" (program [fn "main" [] [
    stmt (.matchStmt sumTy sum [arm 0 100, arm 1 200, arm 2 300])]]) 309
  wordResult "word match and wildcard" (program [fn "main" [] [
    stmt (.matchStmt .word (w 17) [
      {pat := {kind := .intLit "0x10"}, binder := "x", body := [ret (w 1)]},
      {pat := {kind := .wildcard}, binder := "x", body := [ret (v "x")]}])]]) 17

private def recursiveLayouts : IO Unit := do
  let reference : Ty := .namedRef "Chain"
  let payload : Ty := .product .word reference
  let chain : Ty := .named "Chain" (.sum .word payload)
  let inspect : Function := {
    name := "inspect", args := [{name := "chain", ty := chain}], ret := .word,
    body := [stmt (.matchStmt chain (v "chain" chain) [
      {pat := {kind := .con .inl}, binder := "end", body := [ret (v "end")]},
      {pat := {kind := .con .inr}, binder := "link", body := [
        ret ⟨.word, .fst (v "link" payload), none⟩]}])]}
  let relay : Function := {
    name := "relay", args := [{name := "chain", ty := chain}], ret := chain,
    body := [ret (v "chain" chain)]}
  let leaf : Expr := ⟨chain, .inl chain (w 42), none⟩
  wordResult "recursive sum construction, named relay and payload match"
    (program [inspect, relay, fn "main" [] [
      declareLocal "chain" chain, assign "chain" leaf,
      ret (call "inspect" [call "relay" [v "chain" chain] chain])]]) 42
  wordResult "recursive layout zero initialization"
    (program [inspect, fn "main" [] [declareLocal "chain" chain,
      ret (call "inspect" [v "chain" chain])]]) 0
  let referenceRelay : Function := {
    name := "referenceRelay", args := [{name := "ref", ty := reference}], ret := reference,
    body := [ret (v "ref" reference)]}
  let extractReference : Function := {
    name := "extractReference", args := [{name := "chain", ty := chain}], ret := reference,
    body := [stmt (.matchStmt chain (v "chain" chain) [
      {pat := {kind := .con .inr}, binder := "link", body := [
        ret (call "referenceRelay" [⟨reference, .snd (v "link" payload), none⟩] reference)]}])]}
  let link : Expr := ⟨chain, .inr chain
    ⟨payload, .pair (w 7) (v "ref" reference), none⟩, none⟩
  let main : Function := {
    name := "main", args := [{name := "ref", ty := reference}], ret := reference,
    body := [declareLocal "chain" chain, assign "chain" link,
      ret (call "extractReference" [call "relay" [v "chain" chain] chain] reference)]}
  wordResult "opaque recursive reference survives construction, relay and extraction"
    (program [relay, referenceRelay, extractReference, main]) 99 [99]
  let nested : Expr := ⟨chain, .inr chain ⟨payload, .pair (w 7) leaf, none⟩, none⟩
  rejects "recursive reference does not implicitly box a complete value"
    (program [inspect, fn "main" [] [ret (call "inspect" [nested])]])
  let invalid : Function := {
    name := "main", args := [{name := "ref", ty := reference}], ret := .word,
    body := [ret (call "inspect" [v "ref" chain])]}
  rejects "recursive reference does not implicitly unfold to a complete value"
    (program [inspect, invalid])

private def malformed : IO Unit := do
  rejects "wrong word annotation" (program [fn "main" [] [ret ⟨.bool, .word "7", none⟩]])
  rejects "wrong injection annotation" (program [fn "main" [] [ret
    ⟨.word, .inl (.sum .word .unit) (w 1), none⟩]])
  rejects "wrong pair annotation" (program [fn "main" [] [ret
    ⟨.word, .pair (w 1) (w 2), none⟩]])
  rejects "projection annotation mismatch" (program [fn "main" [] [ret
    ⟨.bool, .fst ⟨.product .word .word, .pair (w 1) (w 2), none⟩, none⟩]])
  rejects "branch result mismatch" (program [fn "main" [] [ret
    ⟨.word, .ifThen .word ⟨.bool, .bool true, none⟩ (w 1) ⟨.unit, .unit, none⟩, none⟩]])
  rejects "sum constructor out of range" (program [fn "main" [] [ret
    ⟨.sum .word .word, .inK 2 (.sum .word .word) (w 1), none⟩]])
  rejects "sum payload mismatch" (program [fn "main" [] [ret
    ⟨.sum .unit .word, .inl (.sum .unit .word) (w 1), none⟩]])
  rejects "wrong match target" (program [fn "main" [] [
    stmt (.matchStmt .unit (w 1) []), ret (w 0)]])
  rejects "sum pattern on a word" (program [fn "main" [] [
    stmt (.matchStmt .word (w 1) [
      {pat := {kind := .con .inl}, binder := "x", body := [ret (w 0)]}])]])
  rejects "literal assignment target" (program [fn "main" [] [stmt (.assign (w 1) (w 2)), ret (w 0)]])
  rejects "function return mismatch" (program [fn "main" [] [ret ⟨.unit, .unit, none⟩]])
  rejects "callee result annotation mismatch" (program [fn "helper" [] [ret (w 1)],
    fn "main" [] [ret (call "helper" [] .bool)]])
  rejects "opaque recursive reference cannot be projected" (program [fn "main" [] [
    declareLocal "list" (.namedRef "List"),
    ret ⟨.word, .fst (v "list" (.namedRef "List")), none⟩]])
  rejects "residual function layout is explicit" (program [fn "main" [] [
    declareLocal "closure" (.function [.word] .word), ret (w 0)]])
  rejects "unbound local" (program [fn "main" [] [ret (v "missing")]])
  rejects "wrong call arity" (program [fn "helper" ["x"] [ret (v "x")],
    fn "main" [] [ret (call "helper" [])]])
  rejects "unknown callee" (program [fn "main" [] [ret (call "missing" [])]])
  rejects "duplicate functions" (program [fn "main" [] [ret (w 1)], fn "main" [] [ret (w 2)]])
  rejects "duplicate arguments" (program [fn "main" ["x", "x"] [ret (v "x")]])
  rejects "unexported entry" {entryPoints := [], functions := [fn "main" [] [ret (w 1)]], objects := []}
  for control in [StmtKind.breakStmt, .continueStmt] do
    rejects "loop transfer outside loop" (program [fn "main" [] [stmt control, ret (w 0)]])
    rejects "invalid control after return" (program [fn "main" [] [ret (w 0), stmt control]])
  rejects "product assignment type mismatch" (program [fn "main" [] [
    declareLocal "x", stmt (.assign (v "x") ⟨.bool, .bool true, none⟩), ret (v "x")]])
  let hidden := Effects.slotName "exit"
  rejects "reserved local" (program [fn "main" [] [declareLocal hidden, ret (w 0)]])
  rejects "reserved parameter" (program [fn "main" [hidden] [ret (w 0)]])
  rejects "reserved read" (program [fn "main" [] [ret (v hidden)]])
  rejects "reserved match binder" (program [fn "main" [] [
    stmt (.matchStmt .word (w 1) [
      {pat := {kind := .wildcard}, binder := hidden, body := [ret (w 0)]}])]])
  rejects "reserved global" (program [fn hidden [] [ret (w 0)], fn "main" [] [ret (w 0)]])
  contractRejects "reserved Yul local" (objectProgram [⟨.letDecl [yn hidden] (some (yw 1)), none⟩])
  contractRejects "reserved Yul assignment" (objectProgram [⟨.assign [yn hidden] (yw 1), none⟩])
  contractRejects "reserved Yul read" (objectProgram [ye "pop" [⟨.ident (yn hidden), none⟩]])
  contractRejects "duplicate object names" {entryPoints := [], functions := [], objects := [
    .object "runtime" {stmts := [], functions := []} [] none,
    .object "runtime" {stmts := [], functions := []} [] none]}

private def yulHullBridge : IO Unit := do
  let weighted := fn "weighted" ["a", "b", "c"] [ret
    (call "add" [call "add" [call "mul" [v "a", w 100], call "mul" [v "b", w 10]], v "c"])]
  let main (expression : YulExpr) := fn "main" [] [declareLocal "result",
    stmt (.assembly [⟨.assign [yn "result"] expression, none⟩]), ret (v "result")]
  wordResult "explicit Yul to Hull call" (program [weighted,
    main (yc "usr$weighted" [yw 1, yw 3, yw 5])]) 135
  wordResult "Yul local function retains explicit Hull scope" (program [weighted,
    fn "main" [] [declareLocal "result", stmt (.assembly [
      ⟨.functionDef (yn "wrapper") [yn "x"] [yn "y"] [
        ⟨.assign [yn "y"] (yc "usr$weighted" [yw 1, yw 3, ⟨.ident (yn "x"), none⟩]), none⟩], none⟩,
      ⟨.letDecl [yn "weighted"] (some (yw 99)), none⟩,
      ⟨.assign [yn "result"] (yc "wrapper" [yw 5]), none⟩]), ret (v "result")]]) 135
  let record := fn "record" ["value"] [
    stmt (.expression (call "sstore" [w 1, v "value"] .unit)), ret (v "value")]
  let store := fn "store" ["value"] [
    stmt (.expression (call "sstore" [w 2, v "value"] .unit))] .unit
  let combine := fn "combine" ["a", "b"] [ret (call "add" [call "mul" [v "a", w 10], v "b"])]
  let effectSource : Program := {entryPoints := [], functions := [record, store, combine], objects := [
    .object "runtime" {functions := [], stmts := [stmt (.assembly [
      ye "usr$store" [yw 17],
      ye "mstore" [yw 0, yc "usr$combine" [yc "usr$record" [yw 1], yc "usr$record" [yw 2]]],
      ye "return" [yw 0, yw 32]])]} [] none]}
  let effects ← prepare "Yul to Hull side effects" effectSource
  returned "Yul to Hull arguments execute right to left" (Contract.run effects)
    (List.replicate 31 0 ++ [12])
    [(Core.Word.ofNatModulo 2, Core.Word.ofNatModulo 17),
     (Core.Word.ofNatModulo 1, Core.Word.ofNatModulo 1)]
  rejects "unknown explicit Hull function" (program [main (yc "usr$missing")])
  rejects "explicit Hull call arity" (program [weighted, main (yc "usr$weighted" [yw 1])])
  rejects "plain Hull call is not silently renamed" (program [weighted,
    main (yc "weighted" [yw 1, yw 3, yw 5])])
  for ty in [Ty.unit, .bool, .product .word .word, .sum .unit .word] do
    let target : Function := {
      name := "incompatible"
      args := [{name := "x", ty}]
      ret := .word
      body := [ret (w 0)]}
    rejects "Yul Hull argument requires layout conversion" (program [target,
      main (yc "usr$incompatible" [yw 0])])
  let boolReturn := fn "boolean" [] [ret ⟨.bool, .bool true, none⟩] .bool
  rejects "Yul Hull Bool result requires layout conversion" (program [boolReturn,
    main (yc "usr$boolean")])
  let pairTy : Ty := .product .word .word
  let pairReturn := fn "pair" [] [ret ⟨pairTy, .pair (w 1) (w 2), none⟩] pairTy
  rejects "Yul Hull aggregate result requires layout conversion" (program [pairReturn,
    main (yc "usr$pair")])
  rejects "Yul Hull Unit result used as a word" (program [fn "unit" [] [] .unit,
    main (yc "usr$unit")])

private def objectSelection : IO Unit := do
  let leaf := Object.object "runtime" {functions := [], stmts := [
    stmt (.assembly [ye "mstore" [yw 0, yw 42], ye "return" [yw 0, yw 32]])]} [] none
  let nested : Program := {entryPoints := [], functions := [], objects := [
    .object "deployment" {stmts := [], functions := []} [leaf] none]}
  let prepared ← get "nested runtime object" (Contract.prepare nested ["deployment", "runtime"])
  returned "selected nested object" (Contract.run prepared) (List.replicate 31 0 ++ [42])
  for path in [[], ["runtime"], ["deployment", "missing"]] do
    match Contract.prepare nested path with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError s!"unknown object path accepted: {reprStr path}")
  let hiddenLeaf := Object.object "runtime" {functions := [], stmts := [
    stmt (.expression (call "outerOnly" []))]} [] none
  let isolated : Program := {entryPoints := [], functions := [], objects := [
    .object "deployment" {stmts := [], functions := [fn "outerOnly" [] [ret (w 42)]]}
      [hiddenLeaf] none]}
  match Contract.prepare isolated ["deployment", "runtime"] with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "inner object captured an outer object function")

private def effectsAndResume : IO Unit := do
  let store := [(Core.Word.ofNatModulo 5, Core.Word.ofNatModulo 11)]
  let bytes := List.replicate 31 (0 : UInt8) ++ [11]
  let prepared ← prepare "return effects" (objectProgram [
    ye "sstore" [yw 5, yw 11], ye "mstore" [yw 0, yc "sload" [yw 5]],
    ye "return" [yw 0, yw 32], ye "sstore" [yw 5, yw 99]])
    {storage := [(Core.Word.ofNatModulo 5, Core.Word.ofNatModulo 3)]}
  returned "return halts later effects" (Contract.run prepared) bytes store
  match Contract.run prepared 1 with
  | .outOfFuel pending => returned "contract fuel resumes" (Contract.resume pending) bytes store
  | result => throw (IO.userError s!"expected suspended Core execution: {reprStr result}")
  let stopped ← prepare "stop" (objectProgram [ye "stop", ye "sstore" [yw 5, yw 99]])
  returned "stop halts effects" (Contract.run stopped) []
  let reverted ← prepare "revert" (objectProgram [ye "sstore" [yw 5, yw 99],
    ye "mstore8" [yw 0, yw 42], ye "revert" [yw 0, yw 1]])
  match Contract.run reverted with
  | .reverted [42] => pure ()
  | other => throw (IO.userError s!"revert did not preserve exact bytes: {reprStr other}")
  let context ← prepare "context" (objectProgram [ye "mstore" [yw 0, yc "callvalue"],
    ye "return" [yw 0, yw 32]]) {value := Core.Word.ofNatModulo 9}
  returned "call value context" (Contract.run context) (List.replicate 31 0 ++ [9])
  let bounded ← prepare "return byte limit" (objectProgram [ye "return" [yw 0, yw 2]])
  match Contract.run bounded 1000000 1 with
  | .exportError _ => pure ()
  | other => throw (IO.userError s!"return byte export limit was ignored: {reprStr other}")
  let invalid ← prepare "invalid" (objectProgram [ye "invalid", ye "sstore" [yw 5, yw 99]])
  match Contract.run invalid with
  | .invalid => pure ()
  | other => throw (IO.userError s!"invalid instruction did not halt: {reprStr other}")
  let copy ← prepare "copy effects" (objectProgram [
    ye "calldatacopy" [yw 0, yw 0, yw 4], ye "mcopy" [yw 1, yw 0, yw 3],
    ye "return" [yw 0, yw 4]]) {calldata := [1, 2, 3, 4]}
  returned "overlapping memory copy uses source snapshot" (Contract.run copy) [1, 1, 2, 3]
  let transient ← prepare "transient storage" (objectProgram [
    ye "tstore" [yw 5, yw 17], ye "mstore" [yw 0, yc "tload" [yw 5]],
    ye "return" [yw 0, yw 32]])
  returned "transient effects do not modify persistent storage" (Contract.run transient)
    (List.replicate 31 0 ++ [17])
  let callee := fn "record" ["value"] [
    stmt (.expression (call "sstore" [w 1, v "value"] .unit)), ret (v "value")]
  let combine := fn "combine" ["a", "b"] [ret (call "add" [call "mul" [v "a", w 10], v "b"])]
  let ordered : Program := {entryPoints := [], functions := [callee, combine], objects := [
    .object "runtime" {functions := [], stmts := [
      stmt (.expression (call "mstore" [w 0,
        call "combine" [call "record" [w 1], call "record" [w 2]]] .unit)),
      stmt (.expression (call "return" [w 0, w 32] .unit))]} [] none]}
  let ordered ← prepare "Hull argument evaluation order" ordered
  returned "Hull arguments execute left to right" (Contract.run ordered)
    (List.replicate 31 0 ++ [12]) [(Core.Word.ofNatModulo 1, Core.Word.ofNatModulo 2)]
  let calldata ← prepare "calldata" (objectProgram [ye "mstore" [yw 0, yc "calldataload" [yw 0]],
    ye "return" [yw 0, yw 32]]) {calldata := [1, 2]}
  returned "calldata zero padding" (Contract.run calldata) ([1, 2] ++ List.replicate 30 0)

def run : IO Unit := do
  callsAndRecursion
  localsAndLoops
  productsAndMatches
  recursiveLayouts
  malformed
  yulHullBridge
  objectSelection
  effectsAndResume

end Tests.RustHullLowering
end

section
-- leanmerge: from Solcore.Test.RustHullMatchCorrespondence
/-! Match regressions connect independent source derivations to actual public
execution. Indexed alternatives skip two arms before returning from a loop;
Word alternatives fall back to a wildcard. Faults distinguish an allocated
selected binder from a scrutinee that fails before any binder allocation. -/
set_option autoImplicit false
namespace Tests.RustHullMatchCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence PureCallCorrespondence

private def word (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def v (name : String) : Expr := ⟨.word, .var name, none⟩
private def lit (text : String) : Expr := ⟨.word, .word text, none⟩
private def invoke (name : String) (args : List Expr := []) : Expr := ⟨.word, .call name args, none⟩
private def ret (value : Expr) : Stmt := ⟨.returnStmt value, none⟩
private def choiceType : Ty := .sum .word (.sum .word .word)
private def choice : Expr := ⟨choiceType, .inK 2 choiceType (lit "9"), none⟩
private def arm (index : Nat) (value : Expr) : Alt := {
  pat := {kind := .con (.inK index)}, binder := "payload", body := [ret value]
}
private def indexedArms : List Alt := [arm 0 (invoke "addBonus" [v "payload", lit "100"]),
  arm 1 (invoke "addBonus" [v "payload", lit "200"]), arm 2 (invoke "addBonus" [v "payload", lit "300"])]
private def indexedMatch : Stmt := ⟨.matchStmt choiceType choice indexedArms, none⟩
private def yes : Expr := ⟨.bool, .bool true, none⟩
private def wildcardArm : Alt := {pat := {kind := .wildcard}, binder := "payload", body := [ret (v "payload")]}
private def wordArms : List Alt := [
  {pat := {kind := .intLit "0x10"}, binder := "unused", body := [ret (lit "999")]}, wildcardArm]
private def faultArms : List Alt := [arm 0 (lit "100"), arm 1 (lit "200"), arm 2 (invoke "missingReturn")]

def addBonus : Function := {
  name := "addBonus", args := [{name := "value", ty := .word}, {name := "bonus", ty := .word}], ret := .word,
  body := [ret (invoke "primAddWord" [v "value", v "bonus"])]
}
def missingReturn : Function := {
  name := "missingReturn", args := [], ret := .word,
  body := [⟨.letDecl "marker" .word, none⟩, ⟨.assign (v "marker") (lit "17"), none⟩]
}
def indexedLoop : Function := {
  name := "indexedLoop", args := [], ret := .word,
  body := [⟨.forLoop [] yes [ret (lit "999")] [indexedMatch], none⟩, ret (lit "888")]
}
def wordWildcard : Function := {
  name := "wordWildcard", args := [], ret := .word,
  body := [⟨.matchStmt .word (lit "17") wordArms, none⟩, ret (lit "888")]
}
def selectedFault : Function := {
  name := "selectedFault", args := [], ret := .word,
  body := [⟨.matchStmt choiceType choice faultArms, none⟩, ret (lit "888")]
}
def scrutineeFault : Function := {
  name := "scrutineeFault", args := [], ret := .word,
  body := [⟨.matchStmt .word (invoke "missingReturn") [wildcardArm], none⟩, ret (lit "888")]
}
def program : Program := {
  entryPoints := ["indexedLoop", "wordWildcard", "selectedFault", "scrutineeFault"],
  functions := [addBonus, missingReturn, indexedLoop, wordWildcard, selectedFault, scrutineeFault], objects := []
}

private theorem literal_eligible (text : String) : RecursiveExpression program.functions (lit text) := .word _ _ _
private theorem variable_eligible (name : String) : RecursiveExpression program.functions (v name) := .var _ _ _
private theorem choice_eligible : RecursiveExpression program.functions choice := .inK (literal_eligible _) _ _ _ _
private theorem add_eligible (text : String) : RecursiveExpression program.functions
    (invoke "addBonus" [v "payload", lit text]) := by
  apply RecursiveExpression.named (function := addBonus) rfl
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact variable_eligible _
  · exact literal_eligible _
private theorem missing_eligible : RecursiveExpression program.functions (invoke "missingReturn") := by
  apply RecursiveExpression.named (function := missingReturn) rfl
  intro argument member
  cases member

theorem program_eligible : RecursiveProgram program.functions := by
  intro function member
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [addBonus, missingReturn, indexedLoop, wordWildcard, selectedFault, scrutineeFault,
    indexedMatch, indexedArms, wordArms, faultArms, wildcardArm, arm, ret, ExecutableStatement,
    List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, true_and, and_true]
  · apply RecursiveExpression.builtin (operation := .binary .add) rfl (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact variable_eligible _
  · exact literal_eligible _
  · exact ⟨⟨.bool _ _ _, literal_eligible _, choice_eligible, add_eligible _, add_eligible _, add_eligible _⟩,
      literal_eligible _⟩
  · exact ⟨⟨literal_eligible _, literal_eligible _, variable_eligible _⟩, literal_eligible _⟩
  · exact ⟨⟨choice_eligible, literal_eligible _, literal_eligible _, missing_eligible⟩, literal_eligible _⟩
  · exact ⟨⟨missing_eligible, variable_eligible _⟩, literal_eligible _⟩

private def sourceChoice : Semantics.Value := .inr (.inr (.word (word 9)))
private def successHeap : Semantics.Heap := [.word (word 9), .word (word 9), .word (word 300)]
private def faultHeap : Semantics.Heap := [.word (word 9), .word (word 17)]
private def state {σ : Type} (external : σ) (heap : Semantics.Heap) : Semantics.State σ := ⟨heap, external⟩

private theorem read {σ : Type} (effects : Semantics.ExternalSemantics σ)
    {environment : Semantics.Environment} {initial : Semantics.State σ} {name : String} {value : Semantics.Value}
    (found : Semantics.readResult environment initial name = .value value) :
    Semantics.EvalExpr program.functions effects environment (v name) initial (.value value) initial := by
  simpa only [found] using (Semantics.EvalExpr.var (functions := program.functions) (effects := effects)
    (env := environment) (state := initial) (expression := v name) rfl)

private theorem choice_source {σ : Type} (effects : Semantics.ExternalSemantics σ)
    (environment : Semantics.Environment) (initial : Semantics.State σ) :
    Semantics.EvalExpr program.functions effects environment choice initial (.value sourceChoice) initial := by
  have payload : Semantics.EvalExpr program.functions effects environment (lit "9") initial
      (.value (.word (word 9))) initial := .word (text := "9") rfl
  have injected := Semantics.EvalExpr.inK (expression := choice) (index := 2) (target := choiceType) rfl payload
  simpa [Semantics.Result.bind, Semantics.injectionResult, Semantics.inject?, Semantics.injectShape?,
    Semantics.shape, choiceType, sourceChoice] using injected

theorem add_source {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ) :
    Semantics.EvalFunction program.functions effects addBonus [.word (word 9), .word (word 300)]
      (state external [.word (word 9)]) (.value (.word (word 309))) (state external successHeap) := by
  apply Semantics.EvalFunction.body (control := .returned (.word (word 309))) rfl
  apply Semantics.EvalStatements.stop
  · intros; intro same; cases same
  · apply Semantics.EvalStmt.returned rfl
    apply Semantics.EvalExpr.call (values := [.word (word 9), .word (word 300)])
      (middle := state external successHeap) rfl
    · exact .cons (read effects rfl) (.cons (read effects rfl) .nil)
    · exact .primitive (by rfl) rfl
  · intro same; cases same

theorem missing_return_source {σ : Type} (effects : Semantics.ExternalSemantics σ) (initial : Semantics.State σ) :
    Semantics.EvalFunction program.functions effects missingReturn [] initial
      (.fault (.language (word 4))) {initial with heap := initial.heap ++ [.word (word 17)]} := by
  apply Semantics.EvalFunction.body (control := .fallthrough) rfl
  apply Semantics.EvalStatements.declare (name := "marker") (type := .word) (value := .word (word 0)) rfl rfl
  apply Semantics.EvalStatements.next (middle := {initial with heap := initial.heap ++ [.word (word 17)]})
  · intros; intro same; cases same
  · apply Semantics.EvalStmt.assign (value := .word (word 17)) rfl (.word (text := "17") rfl)
    simp [Semantics.assignResult, Semantics.place?, Semantics.lookupLocation, Semantics.updateProduct?,
      Semantics.write?, Semantics.allocate, v]
  · exact .nil

private theorem missing_call {σ : Type} (effects : Semantics.ExternalSemantics σ)
    (environment : Semantics.Environment) (initial : Semantics.State σ) :
    Semantics.EvalExpr program.functions effects environment (invoke "missingReturn") initial
      (.fault (.language (word 4))) {initial with heap := initial.heap ++ [.word (word 17)]} :=
  .call rfl .nil (.function (function := missingReturn) (by rfl) (missing_return_source effects initial))

private theorem indexed_source {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ) :
    Semantics.EvalStmt program.functions effects [] indexedMatch ⟨[], external⟩
      (.returned (.word (word 309))) (state external successHeap) := by
  apply Semantics.EvalStmt.matchStmt rfl (choice_source effects [] _)
  apply Semantics.EvalAlternatives.next (by rfl)
  apply Semantics.EvalAlternatives.next (by rfl)
  apply Semantics.EvalAlternatives.matched (payload := .word (word 9)) (by rfl)
  apply Semantics.EvalStatements.stop
  · intros; intro same; cases same
  · apply Semantics.EvalStmt.returned rfl
    apply Semantics.EvalExpr.call (values := [.word (word 9), .word (word 300)])
      (middle := state external [.word (word 9)]) rfl
    · exact .cons (read effects rfl) (.cons (.word (text := "300") rfl) .nil)
    · exact .function (function := addBonus) rfl (add_source effects external)
  · intro same; cases same

theorem indexed_loop_source {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ) :
    Semantics.EvalFunction program.functions effects indexedLoop [] ⟨[], external⟩
      (.value (.word (word 309))) (state external successHeap) := by
  apply Semantics.EvalFunction.body (control := .returned (.word (word 309))) rfl
  apply Semantics.EvalStatements.stop
  · intros; intro same; cases same
  · apply Semantics.EvalStmt.forLoop rfl
    apply Semantics.EvalLoop.bodyStop (value := .bool true) (.bool rfl) rfl
    · apply Semantics.EvalStatements.stop
      · intros; intro same; cases same
      · exact indexed_source effects external
      · intro same; cases same
    · exact Or.inl ⟨_, rfl⟩
  · intro same; cases same

theorem word_wildcard_source {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ) :
    Semantics.EvalFunction program.functions effects wordWildcard [] ⟨[], external⟩
      (.value (.word (word 17))) (state external [.word (word 17)]) := by
  apply Semantics.EvalFunction.body (control := .returned (.word (word 17))) rfl
  apply Semantics.EvalStatements.stop
  · intros; intro same; cases same
  · apply Semantics.EvalStmt.matchStmt (value := .word (word 17)) rfl (.word (text := "17") rfl)
    apply Semantics.EvalAlternatives.next (by rfl)
    apply Semantics.EvalAlternatives.matched (payload := .word (word 17)) rfl
    apply Semantics.EvalStatements.stop
    · intros; intro same; cases same
    · exact .returned rfl (read effects rfl)
    · intro same; cases same
  · intro same; cases same

theorem selected_fault_source {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ) :
    Semantics.EvalFunction program.functions effects selectedFault [] ⟨[], external⟩
      (.fault (.language (word 4))) (state external faultHeap) := by
  apply Semantics.EvalFunction.body (control := .fault (.language (word 4))) rfl
  apply Semantics.EvalStatements.stop
  · intros; intro same; cases same
  · apply Semantics.EvalStmt.matchStmt rfl (choice_source effects [] _)
    apply Semantics.EvalAlternatives.next (by rfl)
    apply Semantics.EvalAlternatives.next (by rfl)
    apply Semantics.EvalAlternatives.matched (payload := .word (word 9)) (by rfl)
    apply Semantics.EvalStatements.stop
    · intros; intro same; cases same
    · exact .returnFault rfl (missing_call effects _ _)
    · intro same; cases same
  · intro same; cases same

theorem scrutinee_fault_source {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ) :
    Semantics.EvalFunction program.functions effects scrutineeFault [] ⟨[], external⟩
      (.fault (.language (word 4))) (state external [.word (word 17)]) := by
  apply Semantics.EvalFunction.body (control := .fault (.language (word 4))) rfl
  apply Semantics.EvalStatements.stop
  · intros; intro same; cases same
  · exact .matchFault rfl (missing_call effects _ _)
  · intro same; cases same

def PublicResult (prepared : ScalarExecution.Prepared) (expected : Core.Value) (heap : Semantics.Heap) : Prop :=
  ∃ world finalStore required,
    HeapRel world heap finalStore ∧
    ∀ fuel additional last, ScalarExecution.Resumes (ScalarExecution.run prepared fuel) additional last →
      (last = .done expected finalStore ↔ required ≤ fuel + additional) ∧
      ((∃ checkpoint, last = .outOfFuel checkpoint) ↔ fuel + additional < required)

private theorem public_fixture {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ)
    {entry : String} {function : Function} {heap : Semantics.Heap}
    {sourceResult : Semantics.Result Semantics.Value} {expected : Core.Value}
    (selected : program.functions.find? (·.name == entry) = some function)
    (shape : function.args = [] ∧ function.ret = .word)
    (source : Semantics.EvalFunction program.functions effects function [] ⟨[], external⟩
      sourceResult (state external heap))
    (target : ResultRel .word sourceResult expected)
    {prepared : ScalarExecution.Prepared}
    (accepted : ScalarExecution.prepare program entry [] 96 = .ok prepared) :
    PublicResult prepared expected heap := by
  have types : prepared.compiled.parameters = [] ∧ prepared.compiled.result = .word := by
    obtain ⟨compiled, argument, checked, _, rfl⟩ := ScalarExecution.prepare_components accepted
    obtain ⟨own, allocated, assembled, rfl⟩ := StatementCorrespondence.compile_components checked
    obtain ⟨signatures, codes, sourceFunction, code, index, _, sourceSelected, signatureCompiled, _⟩ :=
      assemble_selection assembled
    have same := Option.some.inj (selected.symm.trans sourceSelected)
    subst sourceFunction
    obtain ⟨arity, resultLowered⟩ := StatementCorrespondence.signature_components signatureCompiled
    rw [shape.1] at arity
    rw [shape.2] at resultLowered
    have resultSame : own.result = .word := by
      simpa only [lowerType, Pure.pure, Except.pure, Except.ok.injEq] using resultLowered.symm
    exact ⟨List.eq_nil_of_length_eq_zero arity.symm, resultSame⟩
  obtain ⟨sourceFunction, sources, sourceSelected, inputs, execute⟩ :=
    prepare_recursive_program_resumes accepted program_eligible external (effects := effects)
  have same := Option.some.inj (selected.symm.trans sourceSelected)
  subst sourceFunction
  rw [types.1] at inputs
  cases inputs
  obtain ⟨world, actual, finalStore, required, related, heapRelated, completed⟩ := execute _ _ source
  rw [types.2] at related
  have same : actual = expected := by
    cases related <;> cases target
    · congr 1
      exact ValueRel.functional ‹_› ‹_›
    · rfl
  subst actual
  exact ⟨world, finalStore, required, heapRelated, completed⟩

theorem indexed_loop_public {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ)
    {prepared : ScalarExecution.Prepared}
    (accepted : ScalarExecution.prepare program "indexedLoop" [] 96 = .ok prepared) :
    PublicResult prepared (.inRight .word (.word (word 309))) successHeap :=
  public_fixture effects external (function := indexedLoop) rfl ⟨rfl, rfl⟩
    (indexed_loop_source effects external) (.value (.word _)) accepted

theorem word_wildcard_public {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ)
    {prepared : ScalarExecution.Prepared}
    (accepted : ScalarExecution.prepare program "wordWildcard" [] 96 = .ok prepared) :
    PublicResult prepared (.inRight .word (.word (word 17))) [.word (word 17)] :=
  public_fixture effects external (function := wordWildcard) rfl ⟨rfl, rfl⟩
    (word_wildcard_source effects external) (.value (.word _)) accepted

theorem selected_fault_public {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ)
    {prepared : ScalarExecution.Prepared}
    (accepted : ScalarExecution.prepare program "selectedFault" [] 96 = .ok prepared) :
    PublicResult prepared (.inLeft .word (.word (word 4))) faultHeap :=
  public_fixture effects external (function := selectedFault) rfl ⟨rfl, rfl⟩
    (selected_fault_source effects external) (.language _) accepted

theorem scrutinee_fault_public {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ)
    {prepared : ScalarExecution.Prepared}
    (accepted : ScalarExecution.prepare program "scrutineeFault" [] 96 = .ok prepared) :
    PublicResult prepared (.inLeft .word (.word (word 4))) [.word (word 17)] :=
  public_fixture effects external (function := scrutineeFault) rfl ⟨rfl, rfl⟩
    (scrutinee_fault_source effects external) (.language _) accepted

private def check (entry : String) (expected : Core.Value) (heap : Semantics.Heap) (loopCells : Nat) : IO Unit := do
  let prepared ← match ScalarExecution.prepare program entry [] 96 with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError s!"match correspondence: {entry} preparation failed: {reprStr error}")
  let checkpoint ← match ScalarExecution.run prepared 0 with
    | .outOfFuel checkpoint => pure checkpoint
    | result => throw (IO.userError s!"match correspondence: {entry} zero fuel completed: {reprStr result}")
  let checkpoint ← match ScalarExecution.resume checkpoint 17 with
    | .outOfFuel checkpoint => pure checkpoint
    | result => throw (IO.userError s!"match correspondence: {entry} short resume completed: {reprStr result}")
  match ScalarExecution.resume checkpoint 100000 with
  | .done actual store =>
      unless actual == expected do throw (IO.userError s!"match correspondence: {entry} wrong result")
      unless store.length == program.functions.length + loopCells + heap.length do
        throw (IO.userError s!"match correspondence: {entry} wrong allocation count")
      let sourceCells := store.filterMap fun cell => match cell with
        | .inRight .unit (.word value) => some (Semantics.Value.word value)
        | _ => none
      unless sourceCells == heap do throw (IO.userError s!"match correspondence: {entry} wrong source heap")
  | result => throw (IO.userError s!"match correspondence: {entry} resume failed: {reprStr result}")

def run : IO Unit := do
  check "indexedLoop" (.inRight .word (.word (word 309))) successHeap 1
  check "wordWildcard" (.inRight .word (.word (word 17))) [.word (word 17)] 0
  check "selectedFault" (.inLeft .word (.word (word 4))) faultHeap 0
  check "scrutineeFault" (.inLeft .word (.word (word 4))) [.word (word 17)] 0

end Tests.RustHullMatchCorrespondence
end

section
-- leanmerge: from Solcore.Test.RustHullProductCorrespondence
/-! Nested product updates are checked from independent Hull evaluation through
actual compilation and public execution. A successful right-hand call changes
only the selected leaf; a failing call keeps the original product and its own
preceding allocations. -/
set_option autoImplicit false
namespace Tests.RustHullProductCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence PureCallCorrespondence

private def word (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def productType : Ty := .product .word (.product .word .word)
private def product : Expr := ⟨productType, .var "p", none⟩
private def first : Expr := ⟨.word, .fst product, none⟩
private def tail : Expr := ⟨.product .word .word, .snd product, none⟩
private def second : Expr := ⟨.word, .fst tail, none⟩
private def third : Expr := ⟨.word, .snd tail, none⟩
private def v (name : String) : Expr := ⟨.word, .var name, none⟩
private def lit (text : String) : Expr := ⟨.word, .word text, none⟩
private def invoke (name : String) (args : List Expr := []) : Expr := ⟨.word, .call name args, none⟩
private def assign (place value : Expr) : Stmt := ⟨.assign place value, none⟩
private def ret (value : Expr) : Stmt := ⟨.returnStmt value, none⟩
private def initialProduct : Expr := ⟨productType,
  .pair (lit "1") ⟨.product .word .word, .pair (lit "2") (lit "3"), none⟩, none⟩
private def weighted : Expr := invoke "primAddWord"
  [invoke "mulWord" [first, lit "100"], invoke "primAddWord" [invoke "mulWord" [second, lit "10"], third]]
private def setup : List Stmt := [⟨.letDecl "p" productType, none⟩, assign product initialProduct]

def inc : Function := {
  name := "inc", args := [{name := "value", ty := .word}], ret := .word,
  body := [ret (invoke "primAddWord" [v "value", lit "1"])]
}
def missingReturn : Function := {
  name := "missingReturn", args := [], ret := .word,
  body := [⟨.letDecl "marker" .word, none⟩, assign (v "marker") (lit "17")]
}
def productUpdate : Function := {
  name := "productUpdate", args := [], ret := .word,
  body := setup ++ [assign second (invoke "inc" [lit "6"]), ret weighted]
}
def productFault : Function := {
  name := "productFault", args := [], ret := .word,
  body := setup ++ [assign second (invoke "missingReturn"), assign first (lit "999"), ret weighted]
}
def program : Program := {
  entryPoints := ["productUpdate", "productFault"],
  functions := [inc, missingReturn, productUpdate, productFault], objects := []
}

private theorem literal_eligible (text : String) : RecursiveExpression program.functions (lit text) := .word _ _ _
private theorem initial_eligible : RecursiveExpression program.functions initialProduct :=
  .pair (literal_eligible _) (.pair (literal_eligible _) (literal_eligible _) _ _) _ _
private theorem builtin_eligible {name : String} {left right : Expr} {operation : PureBuiltin}
    (classified : pureBuiltin? name = some operation)
    (absent : program.functions.find? (·.name == name) = none)
    (lhs : RecursiveExpression program.functions left) (rhs : RecursiveExpression program.functions right) :
    RecursiveExpression program.functions (invoke name [left, right]) := by
  apply RecursiveExpression.builtin classified absent
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact lhs
  · exact rhs
private theorem weighted_eligible : RecursiveExpression program.functions weighted := by
  apply builtin_eligible (operation := .binary .add) rfl (by rfl)
  · exact builtin_eligible (operation := .binary .mul) rfl (by rfl) (.fst (.var _ _ _) _ _) (literal_eligible _)
  · apply builtin_eligible (operation := .binary .add) rfl (by rfl)
    · exact builtin_eligible (operation := .binary .mul) rfl (by rfl)
        (.fst (.snd (.var _ _ _) _ _) _ _) (literal_eligible _)
    · exact .snd (.snd (.var _ _ _) _ _) _ _

theorem program_eligible : RecursiveProgram program.functions := by
  intro function member
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals simp only [inc, missingReturn, productUpdate, productFault, setup, List.cons_append, List.nil_append,
    ret, assign, ExecutableStatement, List.forall_mem_cons, List.not_mem_nil,
    false_implies, implies_true, true_and, and_true]
  · exact builtin_eligible (operation := .binary .add) rfl (by rfl) (.var _ _ _) (literal_eligible _)
  · exact literal_eligible _
  · refine ⟨initial_eligible, ?_, weighted_eligible⟩
    apply RecursiveExpression.named (function := inc) rfl
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    subst argument
    exact literal_eligible _
  · refine ⟨initial_eligible, ?_, literal_eligible _, weighted_eligible⟩
    apply RecursiveExpression.named (function := missingReturn) rfl
    intro argument member
    cases member

private def sourceProduct (middle : Nat) : Semantics.Value :=
  .pair (.word (word 1)) (.pair (.word (word middle)) (.word (word 3)))
private def sourceHeap : Semantics.Heap := [sourceProduct 7, .word (word 6)]
private def faultHeap : Semantics.Heap := [sourceProduct 2, .word (word 17)]
private def env : Semantics.Environment := [("p", 0)]
private def state {σ : Type} (external : σ) (heap : Semantics.Heap) : Semantics.State σ := ⟨heap, external⟩

private theorem initial_source {σ : Type} (effects : Semantics.ExternalSemantics σ)
    (environment : Semantics.Environment) (initial : Semantics.State σ) :
    Semantics.EvalExpr program.functions effects environment initialProduct initial (.value (sourceProduct 2)) initial :=
  .pair rfl (.word (text := "1") rfl) (.pair rfl (.word (text := "2") rfl) (.word (text := "3") rfl))

theorem inc_source {σ : Type} (effects : Semantics.ExternalSemantics σ) (initial : Semantics.State σ) :
    Semantics.EvalFunction program.functions effects inc [.word (word 6)] initial
      (.value (.word (word 7))) {initial with heap := initial.heap ++ [.word (word 6)]} := by
  apply Semantics.EvalFunction.body (control := .returned (.word (word 7))) rfl
  apply Semantics.EvalStatements.stop
  · intros; intro same; cases same
  · apply Semantics.EvalStmt.returned rfl
    apply Semantics.EvalExpr.call (values := [.word (word 6), .word (word 1)])
      (middle := {initial with heap := initial.heap ++ [.word (word 6)]}) rfl
    · refine .cons (middle := {initial with heap := initial.heap ++ [.word (word 6)]})
        ?_ (.cons (.word (text := "1") rfl) .nil)
      have read := Semantics.EvalExpr.var (functions := program.functions) (effects := effects)
          (env := [("value", initial.heap.length)])
          (state := {initial with heap := initial.heap ++ [.word (word 6)]}) (expression := v "value") rfl
      simpa [Semantics.readResult, Semantics.lookupLocation] using read
    · exact .primitive (by rfl) rfl
  · intro same; cases same

theorem missing_return_source {σ : Type} (effects : Semantics.ExternalSemantics σ) (initial : Semantics.State σ) :
    Semantics.EvalFunction program.functions effects missingReturn [] initial
      (.fault (.language (word 4))) {initial with heap := initial.heap ++ [.word (word 17)]} := by
  apply Semantics.EvalFunction.body (control := .fallthrough) rfl
  apply Semantics.EvalStatements.declare (name := "marker") (type := .word) (value := .word (word 0)) rfl rfl
  apply Semantics.EvalStatements.next (middle := {initial with heap := initial.heap ++ [.word (word 17)]})
  · intros; intro same; cases same
  · apply Semantics.EvalStmt.assign (value := .word (word 17)) rfl (.word (text := "17") rfl)
    simp [Semantics.assignResult, Semantics.place?, Semantics.lookupLocation, Semantics.updateProduct?,
      Semantics.write?, Semantics.allocate, v]
  · exact .nil

private theorem weighted_source {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ) :
    Semantics.EvalExpr program.functions effects env weighted (state external sourceHeap)
      (.value (.word (word 173))) (state external sourceHeap) := by
  have read : Semantics.EvalExpr program.functions effects env product (state external sourceHeap)
      (.value (sourceProduct 7)) (state external sourceHeap) := by
    have read := Semantics.EvalExpr.var (functions := program.functions) (effects := effects)
      (env := env) (state := state external sourceHeap) (expression := product) rfl
    simpa [Semantics.readResult, Semantics.lookupLocation, env, state, sourceHeap] using read
  have lhs : Semantics.EvalExpr program.functions effects env first (state external sourceHeap)
      (.value (.word (word 1))) (state external sourceHeap) := .fst rfl read
  have mid : Semantics.EvalExpr program.functions effects env second (state external sourceHeap)
      (.value (.word (word 7))) (state external sourceHeap) := .fst rfl (.snd rfl read)
  have rhs : Semantics.EvalExpr program.functions effects env third (state external sourceHeap)
      (.value (.word (word 3))) (state external sourceHeap) := .snd rfl (.snd rfl read)
  apply Semantics.EvalExpr.call (values := [.word (word 100), .word (word 73)]) rfl
  · apply Semantics.EvalExprs.cons (value := .word (word 100)) (values := .value [.word (word 73)])
    · apply Semantics.EvalExpr.call (values := [.word (word 1), .word (word 100)]) rfl
      · exact .cons lhs (.cons (.word (text := "100") rfl) .nil)
      · exact .primitive (by rfl) rfl
    · apply Semantics.EvalExprs.cons (value := .word (word 73)) (values := .value [])
      · apply Semantics.EvalExpr.call (values := [.word (word 70), .word (word 3)]) rfl
        · apply Semantics.EvalExprs.cons (value := .word (word 70)) (values := .value [.word (word 3)])
          · apply Semantics.EvalExpr.call (values := [.word (word 7), .word (word 10)]) rfl
            · exact .cons mid (.cons (.word (text := "10") rfl) .nil)
            · exact .primitive (by rfl) rfl
          · exact .cons rhs .nil
        · exact .primitive (by rfl) rfl
      · exact .nil
  · exact .primitive (by rfl) rfl

private theorem with_setup {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ)
    {statements : List Stmt} {final : Semantics.State σ} {control : Semantics.Control}
    (continued : Semantics.EvalStatements program.functions effects env statements
      (state external [sourceProduct 2]) control final) :
    Semantics.EvalStatements program.functions effects [] (setup ++ statements) ⟨[], external⟩ control final := by
  apply Semantics.EvalStatements.declare (name := "p") (type := productType)
    (value := .pair (.word (word 0)) (.pair (.word (word 0)) (.word (word 0)))) rfl rfl
  apply Semantics.EvalStatements.next (middle := state external [sourceProduct 2])
  · intros; intro same; cases same
  · apply Semantics.EvalStmt.assign (value := sourceProduct 2) rfl (initial_source effects _ _)
    simp [Semantics.assignResult, Semantics.place?, Semantics.lookupLocation, Semantics.updateProduct?,
      Semantics.write?, Semantics.allocate, product, state]
  · exact continued

theorem product_update_source {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ) :
    Semantics.EvalFunction program.functions effects productUpdate [] ⟨[], external⟩
      (.value (.word (word 173))) (state external sourceHeap) := by
  apply Semantics.EvalFunction.body (control := .returned (.word (word 173))) rfl
  apply with_setup effects external
  apply Semantics.EvalStatements.next (middle := state external sourceHeap)
  · intros; intro same; cases same
  · apply Semantics.EvalStmt.assign (value := .word (word 7)) rfl
    · apply Semantics.EvalExpr.call (values := [.word (word 6)]) rfl (.cons (.word (text := "6") rfl) .nil)
      exact .function (function := inc) rfl (inc_source effects _)
    · simp [Semantics.assignResult, Semantics.place?, Semantics.lookupLocation, Semantics.updateProduct?,
        Semantics.write?, second, tail, product, state, env, sourceHeap, sourceProduct]
  · apply Semantics.EvalStatements.stop
    · intros; intro same; cases same
    · exact .returned rfl (weighted_source effects external)
    · intro same; cases same

theorem product_fault_source {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ) :
    Semantics.EvalFunction program.functions effects productFault [] ⟨[], external⟩
      (.fault (.language (word 4))) (state external faultHeap) := by
  apply Semantics.EvalFunction.body (control := .fault (.language (word 4))) rfl
  apply with_setup effects external
  apply Semantics.EvalStatements.stop
  · intros; intro same; cases same
  · apply Semantics.EvalStmt.assignFault rfl
    apply Semantics.EvalExpr.call rfl .nil
    exact .function (function := missingReturn) (by rfl) (missing_return_source effects _)
  · intro same; cases same

/-- Exact final value and source heap for every genuine public resumption chain. -/
def PublicResult (prepared : ScalarExecution.Prepared) (expected : Core.Value) (heap : Semantics.Heap) : Prop :=
  ∃ world finalStore required,
    HeapRel world heap finalStore ∧
    ∀ fuel additional last, ScalarExecution.Resumes (ScalarExecution.run prepared fuel) additional last →
      (last = .done expected finalStore ↔ required ≤ fuel + additional) ∧
      ((∃ checkpoint, last = .outOfFuel checkpoint) ↔ fuel + additional < required)

private theorem public_fixture {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ)
    {entry : String} {function : Function} {heap : Semantics.Heap}
    {sourceResult : Semantics.Result Semantics.Value} {expected : Core.Value}
    (selected : program.functions.find? (·.name == entry) = some function)
    (shape : function.args = [] ∧ function.ret = .word)
    (source : Semantics.EvalFunction program.functions effects function [] ⟨[], external⟩
      sourceResult (state external heap))
    (target : ResultRel .word sourceResult expected)
    {prepared : ScalarExecution.Prepared}
    (accepted : ScalarExecution.prepare program entry [] 96 = .ok prepared) :
    PublicResult prepared expected heap := by
  have types : prepared.compiled.parameters = [] ∧ prepared.compiled.result = .word := by
    obtain ⟨compiled, argument, checked, _, rfl⟩ := ScalarExecution.prepare_components accepted
    obtain ⟨own, allocated, assembled, rfl⟩ := StatementCorrespondence.compile_components checked
    obtain ⟨signatures, codes, sourceFunction, code, index, _, sourceSelected, signatureCompiled, _⟩ :=
      assemble_selection assembled
    have same := Option.some.inj (selected.symm.trans sourceSelected)
    subst sourceFunction
    obtain ⟨arity, resultLowered⟩ := StatementCorrespondence.signature_components signatureCompiled
    rw [shape.1] at arity
    rw [shape.2] at resultLowered
    have resultSame : own.result = .word := by
      simpa only [lowerType, Pure.pure, Except.pure, Except.ok.injEq] using resultLowered.symm
    exact ⟨List.eq_nil_of_length_eq_zero arity.symm, resultSame⟩
  obtain ⟨sourceFunction, sources, sourceSelected, inputs, execute⟩ :=
    prepare_recursive_program_resumes accepted program_eligible external (effects := effects)
  have same := Option.some.inj (selected.symm.trans sourceSelected)
  subst sourceFunction
  rw [types.1] at inputs
  cases inputs
  obtain ⟨world, actual, finalStore, required, related, heapRelated, completed⟩ :=
    execute _ _ source
  rw [types.2] at related
  have same : actual = expected := by
    cases related <;> cases target
    · congr 1
      exact ValueRel.functional ‹_› ‹_›
    · rfl
  subst actual
  exact ⟨world, finalStore, required, heapRelated, completed⟩

theorem product_update_public {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ)
    {prepared : ScalarExecution.Prepared}
    (accepted : ScalarExecution.prepare program "productUpdate" [] 96 = .ok prepared) :
    PublicResult prepared (.inRight .word (.word (word 173))) sourceHeap :=
  public_fixture effects external (function := productUpdate) rfl ⟨rfl, rfl⟩
    (product_update_source effects external) (.value (.word _)) accepted

theorem product_fault_public {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ)
    {prepared : ScalarExecution.Prepared}
    (accepted : ScalarExecution.prepare program "productFault" [] 96 = .ok prepared) :
    PublicResult prepared (.inLeft .word (.word (word 4))) faultHeap :=
  public_fixture effects external (function := productFault) rfl ⟨rfl, rfl⟩
    (product_fault_source effects external) (.language _) accepted

private def check (entry : String) (expected : Core.Value) (sourceCells : Core.Store) : IO Unit := do
  let prepared ← match ScalarExecution.prepare program entry [] 96 with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError s!"product correspondence: {entry} preparation failed: {reprStr error}")
  let checkpoint ← match ScalarExecution.run prepared 0 with
    | .outOfFuel checkpoint => pure checkpoint
    | result => throw (IO.userError s!"product correspondence: {entry} zero fuel completed: {reprStr result}")
  let checkpoint ← match ScalarExecution.resume checkpoint 17 with
    | .outOfFuel checkpoint => pure checkpoint
    | result => throw (IO.userError s!"product correspondence: {entry} short resume completed: {reprStr result}")
  match ScalarExecution.resume checkpoint 100000 with
  | .done actual store =>
      unless actual == expected do throw (IO.userError s!"product correspondence: {entry} wrong result")
      unless store.length == program.functions.length + sourceCells.length do
        throw (IO.userError s!"product correspondence: {entry} wrong allocation count")
      unless store.drop program.functions.length == sourceCells do
        throw (IO.userError s!"product correspondence: {entry} wrong source heap")
  | result => throw (IO.userError s!"product correspondence: {entry} resume failed: {reprStr result}")

def run : IO Unit := do
  check "productUpdate" (.inRight .word (.word (word 173)))
    [.inRight .unit (.pair (.word (word 1)) (.pair (.word (word 7)) (.word (word 3)))), .inRight .unit (.word (word 6))]
  check "productFault" (.inLeft .word (.word (word 4)))
    [.inRight .unit (.pair (.word (word 1)) (.pair (.word (word 2)) (.word (word 3)))), .inRight .unit (.word (word 17))]

end Tests.RustHullProductCorrespondence
end

section
-- leanmerge: from Solcore.Test.RustHullPureCorrespondence
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
end

section
-- leanmerge: from Solcore.Test.RustHullRankedCorrespondence
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
end

section
-- leanmerge: from Solcore.Test.RustHullRecursiveCorrespondence
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
  simp only [ExecutableStatement]
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
    simp only [ExecutableStatement]
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
end

section
-- leanmerge: from Solcore.Test.RustHullScalarExecution
set_option autoImplicit false
namespace Tests.RustHullScalarExecution
open Solcore Solcore.Frontend.RustHull

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def get {α : Type} (label : String) : LowerM α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def expectInput (type : Core.Ty) (input : String) (expected : Core.Expr) : IO Unit := do
  let actual ← get s!"input {input}" (ScalarExecution.parseInput type input)
  require (actual == expected) s!"input {input}: incorrect parsed value"
private def expectError {α : Type} (label message : String) (result : LowerM α) : IO Unit :=
  match result with
  | .error error => require (error.message == message) s!"{label}: wrong error {error.message}"
  | .ok _ => throw (IO.userError s!"{label}: invalid input was accepted")
private def reference (name : String) (type : Ty) : Expr := ⟨type, .var name, none⟩
private def pair (left right : Expr) : Expr := ⟨.product left.ty right.ty, .pair left right, none⟩
private def unit : Expr := ⟨.unit, .unit, none⟩
private def returned (value : Expr) : Stmt := ⟨.returnStmt value, none⟩
private def program (function : Function) : Program :=
  {functions := [function], entryPoints := [function.name], objects := []}
private def mixed : Program :=
  let value := pair (reference "w" .word)
    (pair (reference "b" .bool) (pair (reference "u" .unit) (reference "s" (.sum .unit .unit))))
  program {
    name := "mixed"
    args := [⟨"w", .word, none⟩, ⟨"b", .bool, none⟩, ⟨"u", .unit, none⟩, ⟨"s", .sum .unit .unit, none⟩]
    ret := value.ty
    body := [returned value]}
private def prepare (program : Program) (entry : String) (inputs : List String) : IO ScalarExecution.Prepared :=
  match ScalarExecution.prepare program entry inputs with
  | .ok prepared => pure prepared
  | .error error => throw (IO.userError s!"preparation: {reprStr error}")
private def expectRun (label : String) (actual : Core.StatefulRunResult) (expected : Core.Value) : IO Unit :=
  match actual with
  | .done value _ => require (value == expected) s!"{label}: wrong result {reprStr value}"
  | other => throw (IO.userError s!"{label}: {reprStr other}")
private def resumeChunks : Nat → Core.StatefulRunResult → IO Core.StatefulRunResult
  | 0, _ => throw (IO.userError "scalar resume budget exhausted")
  | fuel + 1, result => match result with
      | .outOfFuel state => resumeChunks fuel (ScalarExecution.resume state 17)
      | _ => pure result

def run : IO Unit := do
  for text in ["42", "0x2a", "0X2A", "00042", toString (Core.wordModulus + 42)] do
    expectInput .word text (.word (word 42))
  expectInput .bool "true" (.bool true)
  expectInput .bool "false" (.bool false)
  expectInput (.sum .unit .unit) "true" (.inRight .unit .unit)
  expectInput (.sum .unit .unit) "false" (.inLeft .unit .unit)
  expectInput .unit "unit" .unit
  for type in [Core.Ty.bool, .sum .unit .unit] do
    for input in ["True", "FALSE", "1", "0", " true", ""] do
      expectError "Boolean spelling" "Boolean input must be true or false" (ScalarExecution.parseInput type input)
  expectError "unit spelling" "Unit input must be unit" (ScalarExecution.parseInput .unit "()")
  for type in [Core.Ty.integer, .product .word .word, .function .unit .unit,
      .sum .word .unit, .sum .unit .bool, .cell .word, .namedData ⟨0⟩] do
    expectError "unsupported input layout" "CLI input supports Word, Bool and Unit"
      (ScalarExecution.parseInput type "0")
  for input in ["", "0x", "-1", "0xgg", "1 "] do
    match ScalarExecution.parseInput .word input with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError s!"invalid Word accepted: {input}")
  expectError "count before value parsing" "argument count mismatch"
    (ScalarExecution.parseArguments [.word, .word] ["invalid"])
  expectError "extra input before value parsing" "argument count mismatch"
    (ScalarExecution.parseArguments [.word] ["invalid", "42"])
  require ((← get "empty argument bundle" (ScalarExecution.parseArguments [] [])) == .unit)
    "zero arguments did not use unit"
  require ((← get "single argument bundle" (ScalarExecution.parseArguments [.word] ["42"])) == .word (word 42))
    "one argument acquired an extra pair"
  let prepared ← prepare mixed "mixed" ["0x2a", "true", "unit", "false"]
  let value := Core.Value.pair (.word (word 42)) (.pair (.bool true) (.pair .unit (.inLeft .unit .unit)))
  let expected := Core.Value.inRight .word value
  expectRun "mixed scalar preparation" (ScalarExecution.run prepared) expected
  let initial := ScalarExecution.run prepared 0
  match initial with
  | .outOfFuel _ => pure ()
  | _ => throw (IO.userError "zero-fuel scalar invocation did not suspend")
  expectRun "repeated scalar resumption" (← resumeChunks 1000 initial) expected
  let empty ← prepare (program {name := "unit", args := [], ret := .unit, body := [returned unit]}) "unit" []
  expectRun "zero-argument entry" (ScalarExecution.run empty) (.inRight .word .unit)
  let single ← prepare (program {
    name := "word"
    args := [⟨"w", .word, none⟩]
    ret := .word
    body := [returned (reference "w" .word)]}) "word" [toString (Core.wordModulus + 7)]
  expectRun "single Word modulo input" (ScalarExecution.run single) (.inRight .word (.word (word 7)))
  let missingReturn ← prepare (program {name := "missing", args := [], ret := .word, body := []}) "missing" []
  expectRun "language failure remains an explicit result" (ScalarExecution.run missingReturn)
    (.inLeft .word (.word (word 4)))
  match ScalarExecution.prepare mixed "absent" [] with
  | .error (.lowering _) => pure ()
  | _ => throw (IO.userError "missing entry did not retain lowering error stage")
  match ScalarExecution.prepare mixed "mixed" [] with
  | .error (.input error) => require (error.message == "argument count mismatch") "wrong input-stage error"
  | _ => throw (IO.userError "wrong count did not retain input error stage")
  let looping := program {
    name := "loop"
    args := []
    ret := .unit
    body := [⟨.expression ⟨.unit, .call "loop" [], none⟩, none⟩]}
  let looping ← prepare looping "loop" []
  match ScalarExecution.run looping 1000 with
  | .outOfFuel state =>
      match ScalarExecution.resume state 1000 with
      | .outOfFuel _ => pure ()
      | other => throw (IO.userError s!"recursive resumption: {reprStr other}")
  | other => throw (IO.userError s!"recursive execution: {reprStr other}")

end Tests.RustHullScalarExecution
end

section
-- leanmerge: from Solcore.Test.RustHullYul
set_option autoImplicit false

namespace Tests.RustHullYul

open Solcore
open Solcore.Frontend.RustHull

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {α : Type} : LowerM α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError error.message)
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def name (value : String) : YulName := ⟨value, none⟩
private def num (value : Nat) : YulExpr := ⟨.literal (.number (toString value)), none⟩
private def ref (value : String) : YulExpr := ⟨.ident (name value), none⟩
private def call (value : String) (args : List YulExpr) : YulExpr := ⟨.call (name value) args, none⟩
private def stmt (value : YulStmtKind) : YulStmt := ⟨value, none⟩
private def set (target : String) (value : YulExpr) : YulStmt := stmt (.assign [name target] value)
private def decl (target : String) (value : Option YulExpr := none) : YulStmt :=
  stmt (.letDecl [name target] value)
private def add (left right : YulExpr) : YulExpr := call "add" [left, right]
private def function (value : String) (parameters returns : List String)
    (body : List YulStmt) : YulStmt :=
  stmt (.functionDef (name value) (parameters.map name) (returns.map name) body)
private def outer : Scope := [⟨some "x", .word, true⟩]

private def check (label : String) (body : List YulStmt) (expected : Nat)
    (initial : Nat := 0) : IO Unit := do
  let lowered ← get (YulLowering.lowerStatements 1000 outer .word body)
  let returned ← get (outer.read "x")
  let program : Core.Program := {
    resultType := Core.LanguageResult.resultType .word
    body := .letE (Core.OptionalCell.allocateInitialized .word (.word (word initial)))
      (Core.LocalControl.finish .word (Core.LocalLoop.toControl .word lowered (word 2)) returned.expression)
  }
  require program.check s!"Yul {label}: generated Core code is ill-typed"
  let actual := program.run 10000
  require (actual == .done (.inRight .word (.word (word expected))))
    s!"Yul {label}: expected {expected}, got {reprStr actual}"

private def rejected (body : List YulStmt) (scope : Scope := outer) : Bool :=
  match YulLowering.lowerStatements 1000 scope .word body with
  | .error _ => true
  | .ok _ => false

private def checkStorageFunctions : IO Unit := do
  let slots : List (String × Core.Ty × Core.Expr) := [
    ("world", AccountState.type, AccountState.literal [({address := word 1}, 1)]),
    ("worldComplete", .bool, .bool false), ("address", .word, .word (word 1)),
    ("isStatic", .bool, .bool false), ("exit", .word, .word (word 0)),
    ("returnOffset", .word, .word (word 0)), ("returnSize", .word, .word (word 0)),
    ("memorySize", .word, .word (word 0))]
  let scope : Scope := (slots.reverse.map fun (name, type, _) =>
    ⟨some (Effects.slotName name), type, false⟩) ++ outer
  let body := [set "x" (call "sub" [call "tick" [], call "tick" []]),
    set "x" (add (call "mul" [ref "x", num 10]) (call "sload" [num 0])),
    function "tick" [] ["r"] [set "r" (call "sload" [num 0]),
      stmt (.expression (call "sstore" [num 0, add (ref "r") (num 1)]))]]
  let lowered ← get (YulLowering.lowerStatements 1000 scope .word body)
  let returned ← get (scope.read "x")
  let program : Core.Program := {
    dataDefinitions := AccountState.definitions
    resultType := Core.LanguageResult.resultType .word
    body := .letE (Core.OptionalCell.allocateInitialized .word (.word (word 0)))
      (slots.foldr (fun (_, type, initial) body => .letE (.newCell type initial) body)
        (Core.LocalControl.finish .word (Core.LocalLoop.toControl .word lowered (word 2)) returned.expression))
  }
  require program.check "Yul function storage effects generated ill-typed Core"
  require (program.run 100000 == .done (.inRight .word (.word (word 12))))
    "Yul functions lost runtime slots or evaluated effectful arguments in the wrong order"

def run : IO Unit := do
  check "zero initialization and Word Boolean" [decl "y", set "x" (add (ref "y")
    ⟨.literal (.bool true), none⟩)] 1
  check "lexical block shadowing" [decl "y", stmt (.block [decl "y" (some (num 9)),
    set "x" (ref "y")]), set "x" (add (ref "x") (ref "y"))] 9
  check "initializer resolves outer binding" [stmt (.block [
    decl "x" (some (add (ref "x") (num 1))),
    set "x" (add (ref "x") (num 1))])] 7 7
  check "nonzero condition" [stmt (.ifThen (num 256) [set "x" (num 3)]),
    stmt (.ifThen (num 0) [set "x" (num 99)])] 3
  check "loop init scope, continue and break" [
    stmt (.forLoop [decl "i" (some (num 0))]
      (call "lt" [ref "i", num 5]) [set "i" (add (ref "i") (num 1))] [
        stmt (.ifThen (call "eq" [ref "i", num 2]) [stmt .continueStmt]),
        stmt (.ifThen (call "eq" [ref "i", num 4]) [stmt .breakStmt]),
        set "x" (add (ref "x") (ref "i"))]),
    set "x" (add (ref "x") (num 10))] 14
  check "nested loops consume their own break" [
    stmt (.forLoop [decl "i" (some (num 0))]
      (call "lt" [ref "i", num 3]) [set "i" (add (ref "i") (num 1))] [
        stmt (.forLoop [] (num 1) [] [set "x" (add (ref "x") (num 1)), stmt .breakStmt])])] 3
  check "switch selected branch" [stmt (.switch (num 3) [
    ⟨.number "1", [set "x" (num 99)], none⟩,
    ⟨.number "3", [decl "y" (some (num 5)), set "x" (add (ref "x") (ref "y"))], none⟩]
    (some [set "x" (num 8)]))] 5
  check "switch default" [stmt (.switch (num 4) [
    ⟨.number "1", [set "x" (num 99)], none⟩] (some [set "x" (num 8)]))] 8
  check "switch omitted default" [stmt (.switch (num 4) [
    ⟨.number "1", [set "x" (num 99)], none⟩] none)] 2 2
  check "pop expression statement" [stmt (.expression (call "pop" [num 13])), set "x" (num 5)] 5
  check "hexadecimal literal" [set "x" ⟨.literal (.hex "0x2a"), none⟩] 42
  check "string packs bytes left aligned" [set "x" (call "byte" [num 0,
    ⟨.literal (.string "\"A\\n\""), none⟩])] 65
  check "string escapes" [set "x" (call "byte" [num 1,
    ⟨.literal (.string "\"A\\n\""), none⟩])] 10

  let missing ← get (YulLowering.lowerExpression 50 outer (call "add" [num 4, ref "x"]))
  let uninitialized : Core.Program := {
    resultType := Core.LanguageResult.resultType .word
    body := .letE (Core.OptionalCell.allocate .word) missing.expression
  }
  require (uninitialized.check && uninitialized.run 1000 ==
    .done (.inLeft .word (.word (word 1)))) "Yul nested call swallowed a language failure"

  require (rejected [stmt (.expression (num 1))]) "unused Yul result was accepted"
  require (rejected [stmt (.expression (call "sstore" [num 0, num 1]))])
    "unsupported storage effect was accepted"
  check "multiple zero locals" [stmt (.letDecl [name "a", name "b"] none),
    set "x" (add (ref "a") (ref "b"))] 0
  check "hoisted zero return slot" [set "x" (call "f" []), function "f" [] ["r"] []] 0 9
  check "hoisted builtin shadow after break" [stmt (.forLoop [] (num 1) [] [
    set "x" (call "add" [num 1, num 2]), stmt .breakStmt,
    function "add" ["a", "b"] ["r"] []])] 0
  check "zero-result function" [stmt (.expression (call "f" [])), set "x" (num 7),
    function "f" [] [] []] 7
  check "leave preserves return values" [set "x" (call "f" [num 8]),
    function "f" ["a"] ["r"] [set "r" (ref "a"), stmt .leave, set "r" (num 99)]] 8
  check "leave exits loops and function" [set "x" (call "f" []),
    function "f" [] ["r"] [stmt (.forLoop [] (num 1) [] [set "r" (num 3), stmt .leave]),
      set "r" (num 99)]] 3
  check "multiple default return slots" [stmt (.letDecl [name "a", name "b", name "c"]
    (some (call "f" []))), set "x" (add (ref "a") (add (ref "b") (ref "c"))),
    function "f" [] ["r", "s", "t"] []] 0
  check "parallel multiple assignment" [decl "a" (some (num 3)), decl "b" (some (num 7)),
    stmt (.assign [name "a", name "b"] (call "swap" [ref "a", ref "b"])),
    set "x" (add (call "mul" [ref "a", num 10]) (ref "b")),
    function "swap" ["a", "b"] ["c", "d"] [set "c" (ref "b"), set "d" (ref "a")]] 73
  check "multiple initialized locals" [stmt (.letDecl [name "a", name "b"] (some (call "pair" []))),
    set "x" (add (call "mul" [ref "a", num 10]) (ref "b")),
    function "pair" [] ["a", "b"] [set "a" (num 2), set "b" (num 9)]] 29
  check "function and value namespaces" [decl "add" (some (num 7)),
    set "x" (call "mul" [ref "add", call "add" [num 9, num 3]]),
    function "add" ["a", "b"] ["r"] [set "r" (call "sub" [ref "a", ref "b"])]] 42
  check "local function shadows host builtin" [set "x" (call "sload" [num 0]),
    function "sload" ["a"] ["r"] [set "r" (num 7)]] 7
  check "function lexical shadowing" [function "f" [] ["r"] [set "r" (num 1)],
    stmt (.block [set "x" (call "f" []), function "f" [] ["r"] [set "r" (num 2)]]),
    set "x" (add (ref "x") (call "f" []))] 3
  check "mutual recursion" [set "x" (add (call "even" [num 6]) (call "odd" [num 7])),
    function "even" ["n"] ["r"] [
      stmt (.ifThen (call "iszero" [ref "n"]) [set "r" (num 1), stmt .leave]),
      set "r" (call "odd" [call "sub" [ref "n", num 1]])],
    function "odd" ["n"] ["r"] [
      stmt (.ifThen (call "iszero" [ref "n"]) [stmt .leave]),
      set "r" (call "even" [call "sub" [ref "n", num 1]])]] 2
  check "function in for initializer" [stmt (.forLoop [decl "i",
    function "next" ["a"] ["r"] [set "r" (add (ref "a") (num 1))]]
    (call "lt" [ref "i", num 3]) [set "i" (call "next" [ref "i"])]
    [set "x" (add (ref "x") (num 1))])] 3
  require (rejected [function "f" [] ["r"] [set "r" (ref "x")]])
    "Yul function captured an enclosing Hull local"
  require (rejected [decl "y", function "f" [] ["r"] [set "r" (ref "y")]])
    "Yul function captured an enclosing Yul local"
  require (rejected [function "outer" ["a"] ["r"] [
    function "inner" [] ["r"] [set "r" (ref "a")]]])
    "nested Yul function captured an enclosing parameter"
  require (rejected [function "f" [] [] [], function "f" [] [] []])
    "duplicate Yul function declarations were accepted"
  require (rejected [function "f" ["a"] ["a"] []])
    "duplicate Yul parameter/return slots were accepted"
  require (rejected [decl (Effects.slotName "callvalue")] &&
    rejected [set (Effects.slotName "callvalue") (num 1)] &&
    rejected [set "x" (ref (Effects.slotName "callvalue"))])
    "inline Yul accessed a reserved runtime binding"
  require (rejected [set "x" (call "f" []), function "f" ["a"] ["r"] []])
    "Yul function call with wrong argument count was accepted"
  require (rejected [stmt (.letDecl [name "a", name "b"] (some (num 1)))])
    "Yul declaration with wrong result count was accepted"
  require (rejected [stmt (.forLoop [stmt .breakStmt] (num 0) [] [])] &&
    rejected [stmt (.forLoop [] (num 0) [stmt .continueStmt] [])])
    "Yul loop initializer or post accepted a loop transfer"
  require (rejected [function "f" [] [] [stmt (.forLoop [stmt .leave, stmt .breakStmt]
    (num 0) [] [])]]) "unreachable malformed Yul loop transfer was accepted"
  require (rejected [stmt (.forLoop [] (num 1) [] [function "f" [] [] [stmt .breakStmt]])])
    "a Yul function inherited an enclosing loop target"
  require (rejected [stmt .leave] && rejected [stmt .breakStmt] && rejected [stmt .continueStmt])
    "escaped Yul transfer was accepted"
  require (rejected [set "x" (num 1)] [⟨some "x", .bool, true⟩])
    "Yul assigned to a nonword Hull local"
  require (rejected [set "x" (ref "flag")] [⟨some "x", .word, true⟩, ⟨some "flag", .bool, true⟩])
    "Yul read a nonword Hull local"
  require (rejected [stmt (.block [decl "hidden"]), set "x" (ref "hidden")])
    "Yul block declaration leaked"
  require (rejected [stmt (.forLoop [decl "i"] (num 0) [] []), set "x" (ref "i")])
    "Yul initializer declaration leaked"
  require (rejected [stmt (.forLoop [decl "i"] (num 0) [set "x" (ref "bodyLocal")]
    [decl "bodyLocal"])]) "Yul body declarations leaked into post"
  require (rejected [stmt (.switch (num 0) [⟨.number "1", [], none⟩, ⟨.hex "0x1", [], none⟩] none)])
    "duplicate Yul switch labels were accepted"
  require (rejected [set "x" ⟨.literal (.string "\"invalid\\r\""), none⟩])
    "invalid Yul string escape was accepted"
  require (rejected [set "x" ⟨.literal (.string "\"12345678901234567890123456789012345\""), none⟩])
    "oversized Yul UTF8 string was accepted"
  checkStorageFunctions

end Tests.RustHullYul
end

section
-- leanmerge: from Solcore.Test.RustHullYulArithmeticCorrespondence
/-! The inline Yul word primitives `add`, `sub`, `lt`, `gt`, `eq` and `iszero`
reach their actual `RustYulPrimitives` code through the call-mode public
theorem. The block computes `x := add(40, 2)` and `y := sub(x, 2)`, stores `x`
under `if lt(y, x)`, skips the body of `if gt(y, x)`, stores `iszero(sub(0, 0))`
under `if eq(x, 42)`, and returns both words under
`if iszero(add(sub(0, 1), 1))`, which holds because `sub(0, 1)` wraps to
2^256 - 1. The independent source follows `YulSemantics`. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.RustHullYulArithmeticCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence

private abbrev w := Core.Word.ofNatModulo
private def number (text : String) : YulExpr := ⟨.literal (.number text), none⟩
private def reading (text : String) : YulExpr := ⟨.ident ⟨text, none⟩, none⟩
private def builtin (text : String) (arguments : List YulExpr) : YulExpr := ⟨.call ⟨text, none⟩ arguments, none⟩
private def perform (expression : YulExpr) : YulStmt := ⟨.expression expression, none⟩
private def declare (text : String) (value : YulExpr) : YulStmt := ⟨.letDecl [⟨text, none⟩] (some value), none⟩
private def when (condition : YulExpr) (body : List YulStmt) : YulStmt := ⟨.ifThen condition body, none⟩

/-- `let x := add(40, 2) let y := sub(x, 2) if lt(y, x) { mstore(0, x) }
if gt(y, x) { mstore(0, 7) } if eq(x, 42) { mstore(32, iszero(sub(0, 0))) }
if iszero(add(sub(0, 1), 1)) { return(0, 64) } mstore(0, 9)` -/
def arithmeticBlock : List YulStmt :=
  [declare "x" (builtin "add" [number "40", number "2"]),
   declare "y" (builtin "sub" [reading "x", number "2"]),
   when (builtin "lt" [reading "y", reading "x"]) [perform (builtin "mstore" [number "0", reading "x"])],
   when (builtin "gt" [reading "y", reading "x"]) [perform (builtin "mstore" [number "0", number "7"])],
   when (builtin "eq" [reading "x", number "42"])
     [perform (builtin "mstore" [number "32", builtin "iszero" [builtin "sub" [number "0", number "0"]]])],
   when (builtin "iszero" [builtin "add" [builtin "sub" [number "0", number "1"], number "1"]])
     [perform (builtin "return" [number "0", number "64"])],
   perform (builtin "mstore" [number "0", number "9"])]

def rootBytes : List UInt8 := [0]
def code : CodeBlock := {stmts := [⟨.assembly arithmeticBlock, none⟩], functions := []}
def program : Program := {entryPoints := [], functions := [], objects := [.object "Assembler" code []]}
def functions : List Function := [AccountRuntime.frameFunction code]
def effects : Semantics.ExternalSemantics RuntimeCallModeSemantics.State :=
  ChildFrameModeSemantics.effectsAt [] {} 1 (some rootBytes)
def context : Contract.Context := {}

abbrev SourceState := Semantics.State RuntimeCallModeSemantics.State
def initial (object : Contract.CompiledObject) : SourceState :=
  ⟨[], ContractCallCorrespondence.contextInitialState (some rootBytes) object (Contract.normalizeContext context)⟩

/-- The independent effects of the block's statements. -/
def stored (offset value : Core.Word) (state : SourceState) : SourceState :=
  YulSemantics.withFrame state {YulSemantics.frame state with
    memory := (MemorySemantics.mstore (YulSemantics.frame state).memory offset value).2}
def returned (offset length : Core.Word) (state : SourceState) : SourceState :=
  YulSemantics.withFrame state (TerminationSemantics.terminate (YulSemantics.frame state) 1 offset length).2
def allocated (value : Core.Word) (state : SourceState) : SourceState := (Semantics.allocate state (.word value)).2
def flag (holds : Prop) [Decidable holds] : Core.Word := if holds then w 1 else Core.Word.zero

def x : Core.Word := w 40 + w 2
def y : Core.Word := x - w 2
def zeroTest : Core.Word := flag (w 0 - w 0 = Core.Word.zero)
def finalState (object : Contract.CompiledObject) : SourceState :=
  returned (w 0) (w 64) (stored (w 32) zeroTest (stored (w 0) x (allocated y (allocated x (initial object)))))
def result : Semantics.Result Semantics.Value := .fault (.language Core.Word.maximum)
def halted : Semantics.Control := .fault (.language Core.Word.maximum)

private theorem block_run (object : Contract.CompiledObject) :
    YulSemantics.Run [] arithmeticBlock (initial object) halted (finalState object) :=
  YulSemantics.Run.letValue (YulSemantics.Eval.call (words := [w 2, w 40])
    (.cons (.literal (word := w 2) (by decide +kernel)) (.cons (.literal (word := w 40) (by decide +kernel)) .nil))
    .add)
  (YulSemantics.Run.letValue (YulSemantics.Eval.call (words := [w 2, x])
    (.cons (.literal (word := w 2) (by decide +kernel)) (.cons (YulSemantics.Eval.ident (word := x) rfl rfl) .nil))
    .sub)
  (YulSemantics.Run.compound (YulSemantics.Compound.ifTrue (YulSemantics.Eval.call (words := [x, y])
      (.cons (YulSemantics.Eval.ident (word := x) rfl rfl) (.cons (YulSemantics.Eval.ident (word := y) rfl rfl) .nil))
      .lt) (by decide)
    (YulSemantics.Run.expression (YulSemantics.Eval.call (words := [x, w 0])
      (.cons (YulSemantics.Eval.ident (word := x) rfl rfl) (.cons (.literal (word := w 0) (by decide +kernel)) .nil))
      .mstore) YulSemantics.Run.nil))
  (YulSemantics.Run.compound (YulSemantics.Compound.ifFalse (YulSemantics.Eval.call (words := [x, y])
      (.cons (YulSemantics.Eval.ident (word := x) rfl rfl) (.cons (YulSemantics.Eval.ident (word := y) rfl rfl) .nil))
      .gt))
  (YulSemantics.Run.compound (YulSemantics.Compound.ifTrue (YulSemantics.Eval.call (words := [w 42, x])
      (.cons (.literal (word := w 42) (by decide +kernel)) (.cons (YulSemantics.Eval.ident (word := x) rfl rfl) .nil))
      .eq) (by decide)
    (YulSemantics.Run.expression (YulSemantics.Eval.call (words := [zeroTest, w 32])
      (.cons (YulSemantics.Eval.call (words := [w 0 - w 0])
          (.cons (YulSemantics.Eval.call (words := [w 0, w 0])
            (.cons (.literal (word := w 0) (by decide +kernel)) (.cons (.literal (word := w 0) (by decide +kernel)) .nil))
            .sub) .nil) .iszero)
        (.cons (.literal (word := w 32) (by decide +kernel)) .nil))
      .mstore) YulSemantics.Run.nil))
  (YulSemantics.Run.compoundStop (YulSemantics.Compound.ifTrue (YulSemantics.Eval.call (words := [w 0 - w 1 + w 1])
      (.cons (YulSemantics.Eval.call (words := [w 1, w 0 - w 1])
        (.cons (.literal (word := w 1) (by decide +kernel))
          (.cons (YulSemantics.Eval.call (words := [w 1, w 0])
            (.cons (.literal (word := w 1) (by decide +kernel)) (.cons (.literal (word := w 0) (by decide +kernel)) .nil))
            .sub) .nil))
        .add) .nil)
      .iszero) (by decide)
    (YulSemantics.Run.expressionFault (YulSemantics.Eval.call (words := [w 64, w 0])
      (.cons (.literal (word := w 64) (by decide +kernel)) (.cons (.literal (word := w 0) (by decide +kernel)) .nil))
      .returned)))
    (by intro impossible; cases impossible))))))

theorem source (object : Contract.CompiledObject) :
    Semantics.EvalFunction functions effects (AccountRuntime.frameFunction code) [] (initial object) result
      (finalState object) := by
  apply Semantics.EvalFunction.body (control := .fault _) rfl
  exact .stop (by intros; intro impossible; cases impossible) (.assembly rfl (block_run object))
    (by intro impossible; cases impossible)

def usedNames : List String := ["mstore", "return"]

private theorem block_eligible {supported : String → Prop} (available : ∀ name ∈ usedNames, supported name) :
    YulFragment.Eligible supported arithmeticBlock := by
  refine ⟨⟨"mstore", available "mstore" (by simp [usedNames])⟩, ?_⟩
  simp only [arithmeticBlock, declare, perform, when, builtin, reading, number]
  repeat' (first
    | exact available _ (by simp [usedNames])
    | exact .inr (by decide)
    | constructor
    | simp only [List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true])

theorem eligible {supported : String → Prop} (available : ∀ name ∈ usedNames, supported name) :
    ExecutableProgram supported functions := by
  intro function member statement statementMember
  simp only [functions, List.mem_cons, List.not_mem_nil, or_false] at member
  subst function
  simp only [AccountRuntime.frameFunction, code, List.mem_cons, List.not_mem_nil, or_false] at statementMember
  subst statementMember
  simp only [ExecutableStatement]
  exact block_eligible available

private theorem names_supported : ∀ name ∈ usedNames, ContractCallModeCorrespondence.supported true name := by
  intro name member
  simp only [usedNames, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl ⟨.store, rfl⟩)))))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inr ⟨.returned, rfl⟩))))))

private theorem empty_connection : ModeChildCatalogExecutionCorrespondence.CatalogConnection [] [] [] := by
  intro address source selected
  simp [ChildFrameSemantics.select] at selected

private theorem empty_links (object : Contract.CompiledObject) :
    ContractCallModeCorrespondence.InitialContextLinks (some rootBytes) [] object context [] := by
  intro anchor member
  simp at member

/-- Public consumer of the call-mode theorem for the inline Yul word primitives
`add`, `sub`, `lt`, `gt`, `eq` and `iszero`, as values and as `if` conditions. -/
theorem public_resumes {object : Contract.CompiledObject}
    (accepted : Contract.compileObject program ["Assembler"] 64 (some rootBytes) [] = .ok object) :
    ∃ value, ContractCallModeCorrespondence.PublicMessageRel context result (finalState object).external value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate context) initialFuel limit)
          additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  exact ContractCallModeCorrespondence.compileObject_resumes_exact (height := 0) (code := code) (by rfl)
    accepted rfl (eligible names_supported) empty_connection (InitCatalogCorrespondence.InitCatalogConnection.empty rfl (by decide)) context rfl (empty_links object) (source object)

private def expected : List UInt8 := List.replicate 31 0 ++ [42] ++ List.replicate 31 0 ++ [1]

def run : IO Unit := do
  let object ← match Contract.compileObject program ["Assembler"] 64 (some rootBytes) [] with
    | .ok object => pure object
    | .error error => throw (IO.userError s!"Yul arithmetic correspondence: compile failed: {reprStr error}")
  let prepared := object.instantiate context
  let checkpoint ← match (Contract.runWithReceipt prepared 0).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"Yul arithmetic correspondence: zero fuel completed: {reprStr outcome}")
  for receipt in [Contract.runWithReceipt prepared 1000000, Contract.resumeWithReceipt checkpoint 1000000] do
    match receipt.outcome with
    | .returned bytes _ =>
        unless bytes == expected do
          throw (IO.userError s!"Yul arithmetic correspondence: wrong bytes: {reprStr bytes}")
    | outcome => throw (IO.userError s!"Yul arithmetic correspondence: unexpected outcome: {reprStr outcome}")

end Tests.RustHullYulArithmeticCorrespondence
end

section
-- leanmerge: from Solcore.Test.RustHullYulBlockCorrespondence
/-! Inline Yul blocks of several statements reach the actual Yul lowering
through the call-mode public theorem: `let` with and without a value, an
assignment, variables, nested builtin calls, and a Hull local the block assigns
and reads. In the ordered scenario the second `mstore` evaluates `msize()`
before `mload(32)` expands memory, so the block returns the word 32; the
opposite argument order would return 64. In the Hull-local scenario the block
assigns 42 to the Hull local `x`, stores it and returns it. The independent
source follows `YulSemantics`. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.RustHullYulBlockCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence

inductive Scenario where
  | ordered | hullLocal
  deriving DecidableEq, Repr

private abbrev w := Core.Word.ofNatModulo
private def number (text : String) : YulExpr := ⟨.literal (.number text), none⟩
private def reading (text : String) : YulExpr := ⟨.ident ⟨text, none⟩, none⟩
private def builtin (text : String) (arguments : List YulExpr) : YulExpr := ⟨.call ⟨text, none⟩ arguments, none⟩
private def perform (expression : YulExpr) : YulStmt := ⟨.expression expression, none⟩
private def declare (text : String) (value : Option YulExpr) : YulStmt := ⟨.letDecl [⟨text, none⟩] value, none⟩
private def assign (text : String) (value : YulExpr) : YulStmt := ⟨.assign [⟨text, none⟩] value, none⟩

/-- `mstore(0, 7) mstore(mload(32), msize()) let r := mload(0) let z z := r
mstore(32, z) return(32, 32)` -/
def orderedBlock : List YulStmt :=
  [perform (builtin "mstore" [number "0", number "7"]),
   perform (builtin "mstore" [builtin "mload" [number "32"], builtin "msize" []]),
   declare "r" (some (builtin "mload" [number "0"])),
   declare "z" none,
   assign "z" (reading "r"),
   perform (builtin "mstore" [number "32", reading "z"]),
   perform (builtin "return" [number "32", number "32"])]

/-- `x := 42 mstore(0, x) return(0, 32)`, after the Hull declaration `let x : word`. -/
def localBlock : List YulStmt :=
  [assign "x" (number "42"),
   perform (builtin "mstore" [number "0", reading "x"]),
   perform (builtin "return" [number "0", number "32"])]

def rootBytes : List UInt8 := [0]
def statements : Scenario → List Stmt
  | .ordered => [⟨.assembly orderedBlock, none⟩]
  | .hullLocal => [⟨.letDecl "x" .word, none⟩, ⟨.assembly localBlock, none⟩]
def code (scenario : Scenario) : CodeBlock := {stmts := statements scenario, functions := []}
def program (scenario : Scenario) : Program :=
  {entryPoints := [], functions := [], objects := [.object "Assembler" (code scenario) []]}
def functions (scenario : Scenario) : List Function := [AccountRuntime.frameFunction (code scenario)]
def effects : Semantics.ExternalSemantics RuntimeCallModeSemantics.State :=
  ChildFrameModeSemantics.effectsAt [] {} 1 (some rootBytes)
def context : Contract.Context := {}

abbrev SourceState := Semantics.State RuntimeCallModeSemantics.State
def initial (object : Contract.CompiledObject) : SourceState :=
  ⟨[], ContractCallCorrespondence.contextInitialState (some rootBytes) object (Contract.normalizeContext context)⟩

/-- The independent effects of the fragment's statements. -/
def stored (offset value : Core.Word) (state : SourceState) : SourceState :=
  YulSemantics.withFrame state {YulSemantics.frame state with
    memory := (MemorySemantics.mstore (YulSemantics.frame state).memory offset value).2}
def touched (offset : Core.Word) (state : SourceState) : SourceState :=
  YulSemantics.withFrame state {YulSemantics.frame state with
    memory := (MemorySemantics.mload (YulSemantics.frame state).memory offset).2}
def loaded (offset : Core.Word) (state : SourceState) : Core.Word :=
  MemorySemantics.readWord (YulSemantics.frame state).memory.words offset
def size (state : SourceState) : Core.Word := (YulSemantics.frame state).memory.size
def returned (offset length : Core.Word) (state : SourceState) : SourceState :=
  YulSemantics.withFrame state (TerminationSemantics.terminate (YulSemantics.frame state) 1 offset length).2
def allocated (value : Core.Word) (state : SourceState) : SourceState := (Semantics.allocate state (.word value)).2
def assigned (location : Nat) (value : Core.Word) (state : SourceState) : SourceState :=
  {state with heap := state.heap.set location (.word value)}

/-- `mstore(mload(32), msize())` takes the size before `mload(32)` expands memory. -/
def orderedFirst (object : Contract.CompiledObject) : SourceState := stored (w 0) (w 7) (initial object)
def orderedSecond (object : Contract.CompiledObject) : SourceState :=
  stored (loaded (w 32) (orderedFirst object)) (size (orderedFirst object)) (touched (w 32) (orderedFirst object))
def orderedValue (object : Contract.CompiledObject) : Core.Word := loaded (w 0) (orderedSecond object)
def orderedLocals (object : Contract.CompiledObject) : SourceState :=
  allocated Core.Word.zero (allocated (orderedValue object) (touched (w 0) (orderedSecond object)))
def orderedFinal (object : Contract.CompiledObject) : SourceState :=
  returned (w 32) (w 32) (stored (w 32) (orderedValue object) (assigned 1 (orderedValue object) (orderedLocals object)))
def localFinal (object : Contract.CompiledObject) : SourceState :=
  returned (w 0) (w 32) (stored (w 0) (w 42) (assigned 0 (w 42) (allocated Core.Word.zero (initial object))))
def finalState (object : Contract.CompiledObject) : Scenario → SourceState
  | .ordered => orderedFinal object
  | .hullLocal => localFinal object
def result : Semantics.Result Semantics.Value := .fault (.language Core.Word.maximum)
def halted : Semantics.Control := .fault (.language Core.Word.maximum)

private theorem ordered_run (object : Contract.CompiledObject) :
    YulSemantics.Run [] orderedBlock (initial object) halted (orderedFinal object) :=
  YulSemantics.Run.expression (YulSemantics.Eval.call (words := [w 7, w 0])
    (.cons (.literal (word := w 7) (by decide +kernel)) (.cons (.literal (word := w 0) (by decide +kernel)) .nil))
    .mstore)
  (YulSemantics.Run.expression (YulSemantics.Eval.call
    (words := [size (orderedFirst object), loaded (w 32) (orderedFirst object)])
    (.cons (YulSemantics.Eval.call (words := []) .nil .msize)
      (.cons (YulSemantics.Eval.call (words := [w 32])
        (.cons (.literal (word := w 32) (by decide +kernel)) .nil) .mload) .nil))
    .mstore)
  (YulSemantics.Run.letValue (YulSemantics.Eval.call (words := [w 0])
    (.cons (.literal (word := w 0) (by decide +kernel)) .nil) .mload)
  (YulSemantics.Run.letZero
  (YulSemantics.Run.assign (YulSemantics.Eval.ident (word := orderedValue object) rfl rfl) rfl
  (YulSemantics.Run.expression (YulSemantics.Eval.call (words := [orderedValue object, w 32])
    (.cons (YulSemantics.Eval.ident (word := orderedValue object) rfl rfl)
      (.cons (.literal (word := w 32) (by decide +kernel)) .nil)) .mstore)
  (YulSemantics.Run.expressionFault (YulSemantics.Eval.call (words := [w 32, w 32])
    (.cons (.literal (word := w 32) (by decide +kernel)) (.cons (.literal (word := w 32) (by decide +kernel)) .nil))
    .returned)))))))

private theorem local_run (object : Contract.CompiledObject) :
    YulSemantics.Run [("x", 0)] localBlock (allocated Core.Word.zero (initial object)) halted (localFinal object) :=
  YulSemantics.Run.assign (.literal (word := w 42) (by decide +kernel)) rfl
  (YulSemantics.Run.expression (YulSemantics.Eval.call (words := [w 42, w 0])
    (.cons (YulSemantics.Eval.ident (word := w 42) rfl rfl) (.cons (.literal (word := w 0) (by decide +kernel)) .nil))
    .mstore)
  (YulSemantics.Run.expressionFault (YulSemantics.Eval.call (words := [w 32, w 0])
    (.cons (.literal (word := w 32) (by decide +kernel)) (.cons (.literal (word := w 0) (by decide +kernel)) .nil))
    .returned)))

theorem source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalFunction (functions scenario) effects (AccountRuntime.frameFunction (code scenario)) []
      (initial object) result (finalState object scenario) := by
  apply Semantics.EvalFunction.body (control := .fault _) rfl
  cases scenario
  · exact .stop (by intros; intro impossible; cases impossible) (.assembly rfl (ordered_run object))
      (by intro impossible; cases impossible)
  · exact .declare rfl rfl (.stop (by intros; intro impossible; cases impossible) (.assembly rfl (local_run object))
      (by intro impossible; cases impossible))

def usedNames : List String := ["mstore", "mload", "msize", "return"]

private theorem block_eligible {supported : String → Prop} (available : ∀ name ∈ usedNames, supported name)
    {body : List YulStmt} (known : body = orderedBlock ∨ body = localBlock) : YulFragment.Eligible supported body := by
  refine ⟨⟨"mstore", available "mstore" (by simp [usedNames])⟩, ?_⟩
  intro statement member
  rcases known with rfl | rfl
  · simp only [orderedBlock, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      repeat' constructor
      all_goals exact available _ (by simp [usedNames])
  · simp only [localBlock, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    all_goals
      repeat' constructor
      all_goals exact available _ (by simp [usedNames])

theorem eligible (scenario : Scenario) {supported : String → Prop}
    (available : ∀ name ∈ usedNames, supported name) :
    ExecutableProgram supported (functions scenario) := by
  intro function member statement statementMember
  simp only [functions, List.mem_cons, List.not_mem_nil, or_false] at member
  subst function
  cases scenario
  · simp only [AccountRuntime.frameFunction, code, statements, List.mem_cons, List.not_mem_nil, or_false] at statementMember
    subst statementMember
    simp only [ExecutableStatement]
    exact block_eligible available (.inl rfl)
  · simp only [AccountRuntime.frameFunction, code, statements, List.mem_cons, List.not_mem_nil, or_false] at statementMember
    rcases statementMember with rfl | rfl
    · simp only [ExecutableStatement]
    · simp only [ExecutableStatement]
      exact block_eligible available (.inr rfl)

private theorem names_supported : ∀ name ∈ usedNames, ContractCallModeCorrespondence.supported true name := by
  intro name member
  simp only [usedNames, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl ⟨.store, rfl⟩)))))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl ⟨.load, rfl⟩)))))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl ⟨.size, rfl⟩)))))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inr ⟨.returned, rfl⟩))))))

private theorem empty_connection : ModeChildCatalogExecutionCorrespondence.CatalogConnection [] [] [] := by
  intro address source selected
  simp [ChildFrameSemantics.select] at selected

private theorem empty_links (object : Contract.CompiledObject) :
    ContractCallModeCorrespondence.InitialContextLinks (some rootBytes) [] object context [] := by
  intro anchor member
  simp at member

/-- Public consumer of the call-mode theorem for inline Yul blocks of several
statements: Yul locals, an assignment, nested calls in Yul's right-to-left
argument order and a Hull local assigned and read by the block. -/
theorem public_resumes (scenario : Scenario) {object : Contract.CompiledObject}
    (accepted : Contract.compileObject (program scenario) ["Assembler"] 64 (some rootBytes) [] = .ok object) :
    ∃ value, ContractCallModeCorrespondence.PublicMessageRel context result
        (finalState object scenario).external value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate context) initialFuel limit)
          additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  exact ContractCallModeCorrespondence.compileObject_resumes_exact (height := 0) (code := code scenario) (by rfl)
    accepted rfl (eligible scenario names_supported) empty_connection (InitCatalogCorrespondence.InitCatalogConnection.empty rfl (by decide)) context rfl (empty_links object)
    (source object scenario)

private def expected : Scenario → List UInt8
  | .ordered => List.replicate 31 0 ++ [32]
  | .hullLocal => List.replicate 31 0 ++ [42]

private def check (scenario : Scenario) : IO Unit := do
  let object ← match Contract.compileObject (program scenario) ["Assembler"] 64 (some rootBytes) [] with
    | .ok object => pure object
    | .error error => throw (IO.userError s!"Yul block correspondence: compile failed: {reprStr error}")
  let prepared := object.instantiate context
  let checkpoint ← match (Contract.runWithReceipt prepared 0).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"Yul block correspondence: zero fuel completed: {reprStr outcome}")
  for receipt in [Contract.runWithReceipt prepared 1000000, Contract.resumeWithReceipt checkpoint 1000000] do
    match receipt.outcome with
    | .returned bytes _ =>
        unless bytes == expected scenario do
          throw (IO.userError s!"Yul block correspondence: wrong bytes for {reprStr scenario}: {reprStr bytes}")
    | outcome =>
        throw (IO.userError s!"Yul block correspondence: unexpected outcome for {reprStr scenario}: {reprStr outcome}")

def run : IO Unit := do
  for scenario in [Scenario.ordered, .hullLocal] do
    check scenario

end Tests.RustHullYulBlockCorrespondence
end

section
-- leanmerge: from Solcore.Test.RustHullYulControlCorrespondence
/-! Inline Yul `if`, nested blocks and `switch` reach the actual Yul lowering
through the call-mode public theorem. In the branching scenario an `if` on a
zero local skips its `return`, a nested block reads memory into a local of its
own and stores it under an `if`, and a last `if` returns the stored word 7
before a statement that is not reached. In the switching scenario a `switch` on
`mload(0)` skips the first case, runs the second with a local of its own, and a
second `switch` returns the word 20 from its default body. The independent
source follows `YulSemantics`. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.RustHullYulControlCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence

inductive Scenario where
  | branching | switching
  deriving DecidableEq, Repr

private abbrev w := Core.Word.ofNatModulo
private def number (text : String) : YulExpr := ⟨.literal (.number text), none⟩
private def reading (text : String) : YulExpr := ⟨.ident ⟨text, none⟩, none⟩
private def builtin (text : String) (arguments : List YulExpr) : YulExpr := ⟨.call ⟨text, none⟩ arguments, none⟩
private def perform (expression : YulExpr) : YulStmt := ⟨.expression expression, none⟩
private def declare (text : String) (value : YulExpr) : YulStmt := ⟨.letDecl [⟨text, none⟩] (some value), none⟩
private def nested (body : List YulStmt) : YulStmt := ⟨.block body, none⟩
private def when (condition : YulExpr) (body : List YulStmt) : YulStmt := ⟨.ifThen condition body, none⟩
private def choose (value : YulExpr) (cases : List (String × List YulStmt)) (defaultBody : List YulStmt) : YulStmt :=
  ⟨.switch value (cases.map fun (text, body) => ⟨.number text, body, none⟩) (some defaultBody), none⟩

/-- `let c := 0 if c { return(0, 32) } mstore(0, 7) { let inner := mload(0)
if 1 { mstore(32, inner) } } if 1 { return(32, 32) } mstore(32, 9)` -/
def branchingBlock : List YulStmt :=
  [declare "c" (number "0"),
   when (reading "c") [perform (builtin "return" [number "0", number "32"])],
   perform (builtin "mstore" [number "0", number "7"]),
   nested [declare "inner" (builtin "mload" [number "0"]),
     when (number "1") [perform (builtin "mstore" [number "32", reading "inner"])]],
   when (number "1") [perform (builtin "return" [number "32", number "32"])],
   perform (builtin "mstore" [number "32", number "9"])]

def switchCases : List (String × List YulStmt) :=
  [("1", [perform (builtin "mstore" [number "32", number "10"])]),
   ("2", [declare "v" (number "20"), perform (builtin "mstore" [number "32", reading "v"])])]

def exitCases : List (String × List YulStmt) := [("1", [perform (builtin "return" [number "0", number "32"])])]

/-- `mstore(0, 2) switch mload(0) case 1 { mstore(32, 10) } case 2 { let v := 20
mstore(32, v) } default { mstore(32, 30) } switch 5 case 1 { return(0, 32) }
default { return(32, 32) }` -/
def switchingBlock : List YulStmt :=
  [perform (builtin "mstore" [number "0", number "2"]),
   choose (builtin "mload" [number "0"]) switchCases [perform (builtin "mstore" [number "32", number "30"])],
   choose (number "5") exitCases [perform (builtin "return" [number "32", number "32"])]]

def body : Scenario → List YulStmt
  | .branching => branchingBlock
  | .switching => switchingBlock

def rootBytes : List UInt8 := [0]
def code (scenario : Scenario) : CodeBlock := {stmts := [⟨.assembly (body scenario), none⟩], functions := []}
def program (scenario : Scenario) : Program :=
  {entryPoints := [], functions := [], objects := [.object "Assembler" (code scenario) []]}
def functions (scenario : Scenario) : List Function := [AccountRuntime.frameFunction (code scenario)]
def effects : Semantics.ExternalSemantics RuntimeCallModeSemantics.State :=
  ChildFrameModeSemantics.effectsAt [] {} 1 (some rootBytes)
def context : Contract.Context := {}

abbrev SourceState := Semantics.State RuntimeCallModeSemantics.State
def initial (object : Contract.CompiledObject) : SourceState :=
  ⟨[], ContractCallCorrespondence.contextInitialState (some rootBytes) object (Contract.normalizeContext context)⟩

/-- The independent effects of the fragment's statements. -/
def stored (offset value : Core.Word) (state : SourceState) : SourceState :=
  YulSemantics.withFrame state {YulSemantics.frame state with
    memory := (MemorySemantics.mstore (YulSemantics.frame state).memory offset value).2}
def touched (offset : Core.Word) (state : SourceState) : SourceState :=
  YulSemantics.withFrame state {YulSemantics.frame state with
    memory := (MemorySemantics.mload (YulSemantics.frame state).memory offset).2}
def loaded (offset : Core.Word) (state : SourceState) : Core.Word :=
  MemorySemantics.readWord (YulSemantics.frame state).memory.words offset
def returned (offset length : Core.Word) (state : SourceState) : SourceState :=
  YulSemantics.withFrame state (TerminationSemantics.terminate (YulSemantics.frame state) 1 offset length).2
def allocated (value : Core.Word) (state : SourceState) : SourceState := (Semantics.allocate state (.word value)).2

/-- The nested block's local holds the word that `mstore(0, 7)` wrote. -/
def branchingWritten (object : Contract.CompiledObject) : SourceState :=
  stored (w 0) (w 7) (allocated (w 0) (initial object))
def branchingFinal (object : Contract.CompiledObject) : SourceState :=
  let inner := loaded (w 0) (branchingWritten object)
  returned (w 32) (w 32) (stored (w 32) inner (allocated inner (touched (w 0) (branchingWritten object))))
/-- The second case runs with the word that `mstore(0, 2)` wrote as scrutinee. -/
def switchingWritten (object : Contract.CompiledObject) : SourceState := stored (w 0) (w 2) (initial object)
def switchingFinal (object : Contract.CompiledObject) : SourceState :=
  returned (w 32) (w 32) (stored (w 32) (w 20) (allocated (w 20) (touched (w 0) (switchingWritten object))))
def finalState (object : Contract.CompiledObject) : Scenario → SourceState
  | .branching => branchingFinal object
  | .switching => switchingFinal object
def result : Semantics.Result Semantics.Value := .fault (.language Core.Word.maximum)
def halted : Semantics.Control := .fault (.language Core.Word.maximum)

private theorem branching_run (object : Contract.CompiledObject) :
    YulSemantics.Run [] branchingBlock (initial object) halted (branchingFinal object) :=
  YulSemantics.Run.letValue (.literal (word := w 0) (by decide +kernel))
  (YulSemantics.Run.compound (YulSemantics.Compound.ifFalse (YulSemantics.Eval.ident rfl rfl))
  (YulSemantics.Run.expression (YulSemantics.Eval.call (words := [w 7, w 0])
    (.cons (.literal (word := w 7) (by decide +kernel)) (.cons (.literal (word := w 0) (by decide +kernel)) .nil))
    .mstore)
  (YulSemantics.Run.compound (YulSemantics.Compound.block
    (YulSemantics.Run.letValue (YulSemantics.Eval.call (words := [w 0])
      (.cons (.literal (word := w 0) (by decide +kernel)) .nil) .mload)
    (YulSemantics.Run.compound (YulSemantics.Compound.ifTrue (.literal (word := w 1) (by decide +kernel))
        (by decide)
      (YulSemantics.Run.expression (YulSemantics.Eval.call
        (words := [loaded (w 0) (branchingWritten object), w 32])
        (.cons (YulSemantics.Eval.ident (word := loaded (w 0) (branchingWritten object)) rfl rfl)
          (.cons (.literal (word := w 32) (by decide +kernel)) .nil)) .mstore)
      YulSemantics.Run.nil))
    YulSemantics.Run.nil)))
  (YulSemantics.Run.compoundStop (YulSemantics.Compound.ifTrue (.literal (word := w 1) (by decide +kernel))
      (by decide)
    (YulSemantics.Run.expressionFault (YulSemantics.Eval.call (words := [w 32, w 32])
      (.cons (.literal (word := w 32) (by decide +kernel)) (.cons (.literal (word := w 32) (by decide +kernel)) .nil))
      .returned)))
    (by intro impossible; cases impossible)))))

private theorem second_selected (object : Contract.CompiledObject) :
    YulSemantics.select (loaded (w 0) (switchingWritten object))
      (switchCases.map fun (text, body) => ⟨.number text, body, none⟩) =
      some [declare "v" (number "20"), perform (builtin "mstore" [number "32", reading "v"])] := by
  have first : YulSemantics.literalWord? (.number "1") ≠ some (loaded (w 0) (switchingWritten object)) := by
    rw [show loaded (w 0) (switchingWritten object) = w 2 from rfl]
    decide +kernel
  have second : YulSemantics.literalWord? (.number "2") = some (loaded (w 0) (switchingWritten object)) := by
    rw [show loaded (w 0) (switchingWritten object) = w 2 from rfl]
    decide +kernel
  simp only [switchCases, List.map_cons, List.map_nil, YulSemantics.select, if_neg first, if_pos second]

private theorem exit_unselected :
    YulSemantics.select (w 5) (exitCases.map fun (text, body) => ⟨.number text, body, none⟩) = none := by
  have first : YulSemantics.literalWord? (.number "1") ≠ some (w 5) := by decide +kernel
  simp only [exitCases, List.map_cons, List.map_nil, YulSemantics.select, if_neg first]

private theorem switching_run (object : Contract.CompiledObject) :
    YulSemantics.Run [] switchingBlock (initial object) halted (switchingFinal object) :=
  YulSemantics.Run.expression (YulSemantics.Eval.call (words := [w 2, w 0])
    (.cons (.literal (word := w 2) (by decide +kernel)) (.cons (.literal (word := w 0) (by decide +kernel)) .nil))
    .mstore)
  (YulSemantics.Run.compound (YulSemantics.Compound.switchCase (YulSemantics.Eval.call (words := [w 0])
      (.cons (.literal (word := w 0) (by decide +kernel)) .nil) .mload)
    (second_selected object)
    (YulSemantics.Run.letValue (.literal (word := w 20) (by decide +kernel))
    (YulSemantics.Run.expression (YulSemantics.Eval.call (words := [w 20, w 32])
      (.cons (YulSemantics.Eval.ident (word := w 20) rfl rfl)
        (.cons (.literal (word := w 32) (by decide +kernel)) .nil)) .mstore)
    YulSemantics.Run.nil)))
  (YulSemantics.Run.compoundStop (YulSemantics.Compound.switchDefault (.literal (word := w 5) (by decide +kernel))
      exit_unselected
    (YulSemantics.Run.expressionFault (YulSemantics.Eval.call (words := [w 32, w 32])
      (.cons (.literal (word := w 32) (by decide +kernel)) (.cons (.literal (word := w 32) (by decide +kernel)) .nil))
      .returned)))
    (by intro impossible; cases impossible)))

theorem source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalFunction (functions scenario) effects (AccountRuntime.frameFunction (code scenario)) []
      (initial object) result (finalState object scenario) := by
  apply Semantics.EvalFunction.body (control := .fault _) rfl
  cases scenario
  · exact .stop (by intros; intro impossible; cases impossible) (.assembly rfl (branching_run object))
      (by intro impossible; cases impossible)
  · exact .stop (by intros; intro impossible; cases impossible) (.assembly rfl (switching_run object))
      (by intro impossible; cases impossible)

def usedNames : List String := ["mstore", "mload", "return"]

private theorem block_eligible {supported : String → Prop} (available : ∀ name ∈ usedNames, supported name)
    (scenario : Scenario) : YulFragment.Eligible supported (body scenario) := by
  refine ⟨⟨"mstore", available "mstore" (by simp [usedNames])⟩, ?_⟩
  cases scenario
  all_goals
    simp only [body, branchingBlock, switchingBlock, switchCases, exitCases, declare, perform, nested, when, choose,
      builtin, reading, number, List.map_cons, List.map_nil]
    repeat' (first
      | exact available _ (by simp [usedNames])
      | constructor
      | simp only [List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true, Option.getD_some,
          ne_eq, reduceCtorEq, not_false_eq_true])

theorem eligible (scenario : Scenario) {supported : String → Prop}
    (available : ∀ name ∈ usedNames, supported name) :
    ExecutableProgram supported (functions scenario) := by
  intro function member statement statementMember
  simp only [functions, List.mem_cons, List.not_mem_nil, or_false] at member
  subst function
  simp only [AccountRuntime.frameFunction, code, List.mem_cons, List.not_mem_nil, or_false] at statementMember
  subst statementMember
  simp only [ExecutableStatement]
  exact block_eligible available scenario

private theorem names_supported : ∀ name ∈ usedNames, ContractCallModeCorrespondence.supported true name := by
  intro name member
  simp only [usedNames, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl ⟨.store, rfl⟩)))))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl ⟨.load, rfl⟩)))))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inr ⟨.returned, rfl⟩))))))

private theorem empty_connection : ModeChildCatalogExecutionCorrespondence.CatalogConnection [] [] [] := by
  intro address source selected
  simp [ChildFrameSemantics.select] at selected

private theorem empty_links (object : Contract.CompiledObject) :
    ContractCallModeCorrespondence.InitialContextLinks (some rootBytes) [] object context [] := by
  intro anchor member
  simp at member

/-- Public consumer of the call-mode theorem for inline Yul `if`, nested blocks
and `switch`, including control that stops the statement list from a nested
body. -/
theorem public_resumes (scenario : Scenario) {object : Contract.CompiledObject}
    (accepted : Contract.compileObject (program scenario) ["Assembler"] 64 (some rootBytes) [] = .ok object) :
    ∃ value, ContractCallModeCorrespondence.PublicMessageRel context result
        (finalState object scenario).external value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate context) initialFuel limit)
          additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  exact ContractCallModeCorrespondence.compileObject_resumes_exact (height := 0) (code := code scenario) (by rfl)
    accepted rfl (eligible scenario names_supported) empty_connection (InitCatalogCorrespondence.InitCatalogConnection.empty rfl (by decide)) context rfl (empty_links object)
    (source object scenario)

private def expected : Scenario → List UInt8
  | .branching => List.replicate 31 0 ++ [7]
  | .switching => List.replicate 31 0 ++ [20]

private def check (scenario : Scenario) : IO Unit := do
  let object ← match Contract.compileObject (program scenario) ["Assembler"] 64 (some rootBytes) [] with
    | .ok object => pure object
    | .error error => throw (IO.userError s!"Yul control correspondence: compile failed: {reprStr error}")
  let prepared := object.instantiate context
  let checkpoint ← match (Contract.runWithReceipt prepared 0).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"Yul control correspondence: zero fuel completed: {reprStr outcome}")
  for receipt in [Contract.runWithReceipt prepared 1000000, Contract.resumeWithReceipt checkpoint 1000000] do
    match receipt.outcome with
    | .returned bytes _ =>
        unless bytes == expected scenario do
          throw (IO.userError s!"Yul control correspondence: wrong bytes for {reprStr scenario}: {reprStr bytes}")
    | outcome =>
        throw (IO.userError s!"Yul control correspondence: unexpected outcome for {reprStr scenario}: {reprStr outcome}")

def run : IO Unit := do
  for scenario in [Scenario.branching, .switching] do
    check scenario

end Tests.RustHullYulControlCorrespondence
end
