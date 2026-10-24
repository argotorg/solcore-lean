import Solcore.Frontend.RustHull.RecursiveProgramCorrespondence

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
      RecursiveStatement, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, true_and, and_true]
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
    execute _ _ source trivial
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
