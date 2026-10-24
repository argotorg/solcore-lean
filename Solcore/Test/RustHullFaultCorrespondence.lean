import Solcore.Frontend.RustHull.RecursiveProgramCorrespondence

/-! Fault regressions start with independent Hull execution derivations. They
retain allocations and writes before a fault, skip later computations, and
exercise the actual compiler and repeated public checkpoint resumption. -/
set_option autoImplicit false
namespace Tests.RustHullFaultCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence

private def word (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def reason : Core.Word := word 4
private def fault : Semantics.Fault := .language reason
private def v (name : String) : Expr := ⟨.word, .var name, none⟩
private def lit (text : String) : Expr := ⟨.word, .word text, none⟩
private def invoke (name : String) (args : List Expr := []) (type : Ty := .word) : Expr :=
  ⟨type, .call name args, none⟩
private def assign (name : String) (rhs : Expr) : Stmt := ⟨.assign (v name) rhs, none⟩
private def ret (value : Expr) : Stmt := ⟨.returnStmt value, none⟩
private def expr (value : Expr) : Stmt := ⟨.expression value, none⟩
private def decl (name : String) : Stmt := ⟨.letDecl name .word, none⟩
private def yes : Expr := ⟨.bool, .bool true, none⟩
private def loop (condition : Expr) (post body : List Stmt) : Stmt :=
  ⟨.forLoop [] condition post body, none⟩
private def missingBody : List Stmt := [decl "marker", assign "marker" (lit "17")]

def missingWord : Function := {name := "missingWord", args := [], ret := .word, body := missingBody}
def missingBool : Function := {name := "missingBool", args := [], ret := .bool, body := missingBody}
def touch : Function := {
  name := "touch", args := [{name := "value", ty := .word}], ret := .word, body := [ret (v "value")]
}
def combine : Function := {
  name := "combine", args := [{name := "first", ty := .word}, {name := "second", ty := .word}], ret := .word,
  body := [decl "calleeMarker", assign "calleeMarker" (lit "999"), ret (v "first")]
}
def namedFault : Function := {
  name := "namedFault", args := [], ret := .word, body := [ret (invoke "missingWord"), ret (lit "999")]
}
def argumentFault : Function := {
  name := "argumentFault", args := [], ret := .word,
  body := [ret (invoke "primAddWord" [invoke "missingWord", invoke "touch" [lit "999"]])]
}
def namedArgumentsFault : Function := {
  name := "namedArgumentsFault", args := [], ret := .word,
  body := [ret (invoke "combine" [invoke "touch" [lit "7"], invoke "missingWord"])]
}
private def pairValue : Expr := ⟨.product .word .word,
  .pair (invoke "touch" [lit "7"]) (invoke "missingWord"), none⟩
def pairFault : Function := {
  name := "pairFault", args := [], ret := .product .word .word, body := [ret pairValue]
}
private def setup : List Stmt := [decl "total", assign "total" (lit "7")]
private def afterFault : List Stmt := [assign "total" (lit "999"), ret (v "total")]
def assignmentFault : Function := {
  name := "assignmentFault", args := [], ret := .word,
  body := setup ++ [assign "total" (invoke "missingWord")] ++ afterFault
}
def conditionFault : Function := {
  name := "conditionFault", args := [], ret := .word,
  body := setup ++ [loop (invoke "missingBool" [] .bool)
    [assign "total" (lit "999")] [assign "total" (lit "999")]] ++ afterFault
}
def bodyFault : Function := {
  name := "bodyFault", args := [], ret := .word,
  body := setup ++ [loop yes [assign "total" (lit "999")]
    [assign "total" (lit "11"), expr (invoke "missingWord"), assign "total" (lit "999")]] ++ afterFault
}
def postFault : Function := {
  name := "postFault", args := [], ret := .word,
  body := setup ++ [loop yes
    [assign "total" (lit "13"), expr (invoke "missingWord"), assign "total" (lit "999")]
    [assign "total" (lit "11")]] ++ afterFault
}

def program : Program := {
  entryPoints := ["missingWord", "namedFault", "argumentFault", "namedArgumentsFault", "pairFault", "assignmentFault",
    "conditionFault", "bodyFault", "postFault"],
  functions := [missingWord, missingBool, touch, namedFault, argumentFault, pairFault,
    assignmentFault, conditionFault, bodyFault, postFault, combine, namedArgumentsFault], objects := []
}

private theorem literal_eligible (text : String) : RecursiveExpression program.functions (lit text) := .word _ _ _
private theorem variable_eligible (name : String) : RecursiveExpression program.functions (v name) := .var _ _ _
private theorem missing_word_eligible : RecursiveExpression program.functions (invoke "missingWord") := by
  apply RecursiveExpression.named (function := missingWord) rfl
  intro argument member
  cases member
private theorem missing_bool_eligible : RecursiveExpression program.functions (invoke "missingBool" [] .bool) := by
  apply RecursiveExpression.named (function := missingBool) rfl
  intro argument member
  cases member
private theorem touch_eligible (text : String) : RecursiveExpression program.functions (invoke "touch" [lit text]) := by
  apply RecursiveExpression.named (function := touch) rfl
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst argument
  exact literal_eligible _

theorem program_eligible : RecursiveProgram program.functions := by
  intro function member
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [missingWord, missingBool, touch, namedFault, argumentFault, pairFault, assignmentFault,
      conditionFault, bodyFault, postFault, combine, namedArgumentsFault, setup, afterFault, missingBody, List.cons_append, List.nil_append,
      ret, decl, assign, expr, v, loop, RecursiveStatement, List.forall_mem_cons,
      List.not_mem_nil, false_implies, implies_true, true_and, and_true]
  · exact literal_eligible _
  · exact literal_eligible _
  · exact variable_eligible _
  · exact ⟨missing_word_eligible, literal_eligible _⟩
  · apply RecursiveExpression.builtin (operation := .binary .add) rfl (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact missing_word_eligible
    · exact touch_eligible _
  · exact .pair (touch_eligible _) missing_word_eligible _ _
  · exact ⟨literal_eligible _, missing_word_eligible, literal_eligible _, variable_eligible _⟩
  · exact ⟨literal_eligible _, ⟨missing_bool_eligible, literal_eligible _, literal_eligible _⟩,
      literal_eligible _, variable_eligible _⟩
  · exact ⟨literal_eligible _, ⟨.bool _ _ _, literal_eligible _, literal_eligible _,
      missing_word_eligible, literal_eligible _⟩, literal_eligible _, variable_eligible _⟩
  · exact ⟨literal_eligible _, ⟨.bool _ _ _, ⟨literal_eligible _, missing_word_eligible,
      literal_eligible _⟩, literal_eligible _⟩, literal_eligible _, variable_eligible _⟩
  · exact ⟨literal_eligible _, variable_eligible _⟩
  · apply RecursiveExpression.named (function := combine) rfl
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact touch_eligible _
    · exact missing_word_eligible

private def pushed {σ : Type} (initial : Semantics.State σ) (value : Core.Word) : Semantics.State σ :=
  {initial with heap := initial.heap ++ [.word value]}

private theorem missing_body_source {σ : Type} (effects : Semantics.ExternalSemantics σ)
    (initial : Semantics.State σ) :
    Semantics.EvalStatements program.functions effects [] missingBody initial .fallthrough (pushed initial (word 17)) := by
  apply Semantics.EvalStatements.declare (name := "marker") (type := .word) (value := .word (word 0)) rfl rfl
  apply Semantics.EvalStatements.next (middle := pushed initial (word 17))
  · intros; intro same; cases same
  · apply Semantics.EvalStmt.assign (value := .word (word 17)) rfl (.word (text := "17") rfl)
    simp [Semantics.assignResult, Semantics.place?, Semantics.lookupLocation, Semantics.updateProduct?,
      Semantics.write?, Semantics.allocate, pushed, v]
  · exact .nil

theorem missing_word_source {σ : Type} (effects : Semantics.ExternalSemantics σ)
    (initial : Semantics.State σ) :
    Semantics.EvalFunction program.functions effects missingWord [] initial (.fault fault) (pushed initial (word 17)) := by
  apply Semantics.EvalFunction.body (control := .fallthrough) rfl
  exact missing_body_source effects initial

theorem missing_bool_source {σ : Type} (effects : Semantics.ExternalSemantics σ)
    (initial : Semantics.State σ) :
    Semantics.EvalFunction program.functions effects missingBool [] initial (.fault fault) (pushed initial (word 17)) := by
  apply Semantics.EvalFunction.body (control := .fallthrough) rfl
  exact missing_body_source effects initial

private theorem missing_word_call {σ : Type} (effects : Semantics.ExternalSemantics σ)
    (initial : Semantics.State σ) (environment : Semantics.Environment) :
    Semantics.EvalExpr program.functions effects environment (invoke "missingWord") initial
      (.fault fault) (pushed initial (word 17)) :=
  .call rfl .nil (.function (function := missingWord) rfl (missing_word_source effects initial))

private theorem missing_bool_call {σ : Type} (effects : Semantics.ExternalSemantics σ)
    (initial : Semantics.State σ) (environment : Semantics.Environment) :
    Semantics.EvalExpr program.functions effects environment (invoke "missingBool" [] .bool) initial
      (.fault fault) (pushed initial (word 17)) :=
  .call rfl .nil (.function (function := missingBool) (by rfl) (missing_bool_source effects initial))

private theorem touch_call {σ : Type} (effects : Semantics.ExternalSemantics σ)
    (initial : Semantics.State σ) (environment : Semantics.Environment) :
    Semantics.EvalExpr program.functions effects environment (invoke "touch" [lit "7"]) initial
      (.value (.word (word 7))) (pushed initial (word 7)) := by
  apply Semantics.EvalExpr.call (values := [.word (word 7)]) rfl (.cons (.word (text := "7") rfl) .nil)
  apply Semantics.EvalCall.function (function := touch) (by rfl)
  apply Semantics.EvalFunction.body (control := .returned (.word (word 7))) rfl
  apply Semantics.EvalStatements.stop
  · intros; intro same; cases same
  · apply Semantics.EvalStmt.returned rfl
    have read := Semantics.EvalExpr.var (functions := program.functions) (effects := effects)
      (env := [("value", initial.heap.length)]) (state := pushed initial (word 7)) (expression := v "value") rfl
    simpa [pushed, Semantics.readResult, Semantics.lookupLocation] using read
  · intro same; cases same

theorem named_fault_source {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ) :
    Semantics.EvalFunction program.functions effects namedFault [] ⟨[], external⟩
      (.fault fault) ⟨[.word (word 17)], external⟩ := by
  apply Semantics.EvalFunction.body (control := .fault fault) rfl
  apply Semantics.EvalStatements.stop
  · intros; intro same; cases same
  · exact .returnFault rfl (missing_word_call effects _ _)
  · intro same; cases same

theorem argument_fault_source {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ) :
    Semantics.EvalFunction program.functions effects argumentFault [] ⟨[], external⟩
      (.fault fault) ⟨[.word (word 17)], external⟩ := by
  apply Semantics.EvalFunction.body (control := .fault fault) rfl
  apply Semantics.EvalStatements.stop
  · intros; intro same; cases same
  · exact .returnFault rfl (.callFault rfl (.fault (missing_word_call effects _ _)))
  · intro same; cases same

theorem pair_fault_source {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ) :
    Semantics.EvalFunction program.functions effects pairFault [] ⟨[], external⟩
      (.fault fault) ⟨[.word (word 7), .word (word 17)], external⟩ := by
  apply Semantics.EvalFunction.body (control := .fault fault) rfl
  apply Semantics.EvalStatements.stop
  · intros; intro same; cases same
  · exact .returnFault rfl (.pair rfl (touch_call effects _ _) (missing_word_call effects _ _))
  · intro same; cases same

/-- Argument evaluation retains the first call's allocation and the later
fault's heap. The selected callee neither allocates parameters nor runs. -/
theorem named_arguments_fault_source {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ) :
    Semantics.EvalFunction program.functions effects namedArgumentsFault [] ⟨[], external⟩
      (.fault fault) ⟨[.word (word 7), .word (word 17)], external⟩ := by
  apply Semantics.EvalFunction.body (control := .fault fault) rfl
  apply Semantics.EvalStatements.stop
  · intros; intro same; cases same
  · exact .returnFault rfl (.callFault rfl
      (.cons (touch_call effects _ _) (.fault (missing_word_call effects _ _))))
  · intro same; cases same

private def state {σ : Type} (external : σ) (total : Nat) : Semantics.State σ := ⟨[.word (word total)], external⟩
private def env : Semantics.Environment := [("total", 0)]

private theorem write_total {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ)
    (before after : Nat) (text : String) (literal : Semantics.literalResult text = .value (.word (word after))) :
    Semantics.EvalStmt program.functions effects env (assign "total" (lit text)) (state external before)
      .fallthrough (state external after) := by
  apply Semantics.EvalStmt.assign (value := .word (word after)) rfl
  · simpa only [literal] using (Semantics.EvalExpr.word (functions := program.functions) (effects := effects)
      (env := env) (state := state external before) (expression := lit text) rfl)
  · simp [Semantics.assignResult, Semantics.place?, Semantics.lookupLocation,
      Semantics.updateProduct?, Semantics.write?, state, env, v]

private theorem with_setup {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ)
    {tail : List Stmt} {final : Semantics.State σ}
    (continued : Semantics.EvalStatements program.functions effects env tail (state external 7) (.fault fault) final) :
    Semantics.EvalStatements program.functions effects [] (setup ++ tail) ⟨[], external⟩ (.fault fault) final := by
  apply Semantics.EvalStatements.declare (name := "total") (type := .word) (value := .word (word 0)) rfl rfl
  apply Semantics.EvalStatements.next
  · intros; intro same; cases same
  · exact write_total effects external 0 7 "7" rfl
  · exact continued

theorem assignment_fault_source {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ) :
    Semantics.EvalFunction program.functions effects assignmentFault [] ⟨[], external⟩
      (.fault fault) ⟨[.word (word 7), .word (word 17)], external⟩ := by
  apply Semantics.EvalFunction.body (control := .fault fault) rfl
  apply with_setup effects external
  apply Semantics.EvalStatements.stop
  · intros; intro same; cases same
  · exact .assignFault rfl (missing_word_call effects _ _)
  · intro same; cases same

theorem condition_fault_source {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ) :
    Semantics.EvalFunction program.functions effects conditionFault [] ⟨[], external⟩
      (.fault fault) ⟨[.word (word 7), .word (word 17)], external⟩ := by
  apply Semantics.EvalFunction.body (control := .fault fault) rfl
  apply with_setup effects external
  apply Semantics.EvalStatements.stop
  · intros; intro same; cases same
  · exact .forLoop rfl (.conditionFault (missing_bool_call effects _ _))
  · intro same; cases same

theorem body_fault_source {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ) :
    Semantics.EvalFunction program.functions effects bodyFault [] ⟨[], external⟩
      (.fault fault) ⟨[.word (word 11), .word (word 17)], external⟩ := by
  apply Semantics.EvalFunction.body (control := .fault fault) rfl
  apply with_setup effects external
  apply Semantics.EvalStatements.stop
  · intros; intro same; cases same
  · apply Semantics.EvalStmt.forLoop rfl
    apply Semantics.EvalLoop.bodyStop (value := .bool true) (.bool rfl) rfl
    · apply Semantics.EvalStatements.next
      · intros; intro same; cases same
      · exact write_total effects external 7 11 "11" rfl
      · apply Semantics.EvalStatements.stop
        · intros; intro same; cases same
        · exact .expressionFault rfl (missing_word_call effects _ _)
        · intro same; cases same
    · exact Or.inr ⟨fault, rfl⟩
  · intro same; cases same

theorem post_fault_source {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ) :
    Semantics.EvalFunction program.functions effects postFault [] ⟨[], external⟩
      (.fault fault) ⟨[.word (word 13), .word (word 17)], external⟩ := by
  apply Semantics.EvalFunction.body (control := .fault fault) rfl
  apply with_setup effects external
  apply Semantics.EvalStatements.stop
  · intros; intro same; cases same
  · apply Semantics.EvalStmt.forLoop rfl
    apply Semantics.EvalLoop.postStop (value := .bool true) (bodyControl := .fallthrough) (.bool rfl) rfl
    · apply Semantics.EvalStatements.next
      · intros; intro same; cases same
      · exact write_total effects external 7 11 "11" rfl
      · exact .nil
    · exact Or.inl rfl
    · apply Semantics.EvalStatements.next
      · intros; intro same; cases same
      · exact write_total effects external 11 13 "13" rfl
      · apply Semantics.EvalStatements.stop
        · intros; intro same; cases same
        · exact .expressionFault rfl (missing_word_call effects _ _)
        · intro same; cases same
    · exact Or.inr ⟨fault, rfl⟩
  · intro same; cases same

/-- Every genuine checkpoint chain retains the exact source fault reason and
all allocations and writes preceding it. Insufficient fuel remains resumable. -/
def PublicFaultResult (prepared : ScalarExecution.Prepared) (heap : Semantics.Heap) : Prop :=
  ∃ world finalStore required,
    HeapRel world heap finalStore ∧
    ∀ fuel additional last, ScalarExecution.Resumes (ScalarExecution.run prepared fuel) additional last →
      (last = .done (.inLeft prepared.compiled.result (.word reason)) finalStore ↔ required ≤ fuel + additional) ∧
      ((∃ checkpoint, last = .outOfFuel checkpoint) ↔ fuel + additional < required)

private theorem public_fixture {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ)
    {entry : String} {function : Function} {heap : Semantics.Heap}
    (selected : program.functions.find? (·.name == entry) = some function)
    (arity : function.args = [])
    (source : Semantics.EvalFunction program.functions effects function [] ⟨[], external⟩
      (.fault fault) ⟨heap, external⟩)
    {prepared : ScalarExecution.Prepared}
    (accepted : ScalarExecution.prepare program entry [] 96 = .ok prepared) :
    PublicFaultResult prepared heap := by
  have parameters : prepared.compiled.parameters = [] := by
    obtain ⟨compiled, argument, checked, _, rfl⟩ := ScalarExecution.prepare_components accepted
    obtain ⟨own, allocated, assembled, rfl⟩ := StatementCorrespondence.compile_components checked
    obtain ⟨signatures, codes, sourceFunction, code, index, _, sourceSelected, signatureCompiled, _⟩ :=
      assemble_selection assembled
    have same := Option.some.inj (selected.symm.trans sourceSelected)
    subst sourceFunction
    obtain ⟨lengths, _⟩ := StatementCorrespondence.signature_components signatureCompiled
    rw [arity] at lengths
    exact List.eq_nil_of_length_eq_zero lengths.symm
  obtain ⟨sourceFunction, sources, sourceSelected, inputs, execute⟩ :=
    prepare_recursive_program_resumes accepted program_eligible external (effects := effects)
  have same := Option.some.inj (selected.symm.trans sourceSelected)
  subst sourceFunction
  rw [parameters] at inputs
  cases inputs
  obtain ⟨world, target, finalStore, required, related, heapRelated, completed⟩ :=
    execute _ _ source (by trivial)
  cases related
  exact ⟨world, finalStore, required, heapRelated, completed⟩

/-- The operational premise is actual public preparation; this theorem supplies
its independent missing-return execution rather than assuming it. -/
theorem missing_word_public {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ)
    {prepared : ScalarExecution.Prepared}
    (accepted : ScalarExecution.prepare program "missingWord" [] 96 = .ok prepared) :
    PublicFaultResult prepared [.word (word 17)] :=
  public_fixture effects external (function := missingWord) rfl rfl (missing_word_source effects _) accepted

theorem named_fault_public {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ)
    {prepared : ScalarExecution.Prepared}
    (accepted : ScalarExecution.prepare program "namedFault" [] 96 = .ok prepared) :
    PublicFaultResult prepared [.word (word 17)] :=
  public_fixture effects external (function := namedFault) rfl rfl (named_fault_source effects external) accepted

theorem argument_fault_public {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ)
    {prepared : ScalarExecution.Prepared}
    (accepted : ScalarExecution.prepare program "argumentFault" [] 96 = .ok prepared) :
    PublicFaultResult prepared [.word (word 17)] :=
  public_fixture effects external (function := argumentFault) rfl rfl (argument_fault_source effects external) accepted

theorem pair_fault_public {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ)
    {prepared : ScalarExecution.Prepared}
    (accepted : ScalarExecution.prepare program "pairFault" [] 96 = .ok prepared) :
    PublicFaultResult prepared [.word (word 7), .word (word 17)] :=
  public_fixture effects external (function := pairFault) rfl rfl (pair_fault_source effects external) accepted

theorem named_arguments_fault_public {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ)
    {prepared : ScalarExecution.Prepared}
    (accepted : ScalarExecution.prepare program "namedArgumentsFault" [] 96 = .ok prepared) :
    PublicFaultResult prepared [.word (word 7), .word (word 17)] :=
  public_fixture effects external (function := namedArgumentsFault) rfl rfl
    (named_arguments_fault_source effects external) accepted

theorem assignment_fault_public {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ)
    {prepared : ScalarExecution.Prepared}
    (accepted : ScalarExecution.prepare program "assignmentFault" [] 96 = .ok prepared) :
    PublicFaultResult prepared [.word (word 7), .word (word 17)] :=
  public_fixture effects external (function := assignmentFault) rfl rfl (assignment_fault_source effects external) accepted

theorem condition_fault_public {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ)
    {prepared : ScalarExecution.Prepared}
    (accepted : ScalarExecution.prepare program "conditionFault" [] 96 = .ok prepared) :
    PublicFaultResult prepared [.word (word 7), .word (word 17)] :=
  public_fixture effects external (function := conditionFault) rfl rfl (condition_fault_source effects external) accepted

theorem body_fault_public {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ)
    {prepared : ScalarExecution.Prepared}
    (accepted : ScalarExecution.prepare program "bodyFault" [] 96 = .ok prepared) :
    PublicFaultResult prepared [.word (word 11), .word (word 17)] :=
  public_fixture effects external (function := bodyFault) rfl rfl (body_fault_source effects external) accepted

theorem post_fault_public {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ)
    {prepared : ScalarExecution.Prepared}
    (accepted : ScalarExecution.prepare program "postFault" [] 96 = .ok prepared) :
    PublicFaultResult prepared [.word (word 13), .word (word 17)] :=
  public_fixture effects external (function := postFault) rfl rfl (post_fault_source effects external) accepted

private def check (entry : String) (heap : List Semantics.Value) (loopCells : Nat) : IO Unit := do
  let prepared ← match ScalarExecution.prepare program entry [] 96 with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError s!"fault correspondence: {entry} preparation failed: {reprStr error}")
  let checkpoint ← match ScalarExecution.run prepared 0 with
    | .outOfFuel checkpoint => pure checkpoint
    | result => throw (IO.userError s!"fault correspondence: {entry} zero fuel completed: {reprStr result}")
  let checkpoint ← match ScalarExecution.resume checkpoint 17 with
    | .outOfFuel checkpoint => pure checkpoint
    | result => throw (IO.userError s!"fault correspondence: {entry} short resume completed: {reprStr result}")
  match ScalarExecution.resume checkpoint 100000 with
  | .done (.inLeft _ (.word actual)) store =>
      unless actual == reason do throw (IO.userError s!"fault correspondence: {entry} wrong fault reason")
      unless store.length == program.functions.length + loopCells + heap.length do
        throw (IO.userError s!"fault correspondence: {entry} wrong allocation count")
      let sourceCells := store.filterMap fun cell => match cell with
        | .inRight .unit (.word value) => some (Semantics.Value.word value)
        | _ => none
      unless sourceCells == heap do throw (IO.userError s!"fault correspondence: {entry} wrong source heap")
  | result => throw (IO.userError s!"fault correspondence: {entry} resume failed: {reprStr result}")

def run : IO Unit := do
  check "missingWord" [.word (word 17)] 0
  check "namedFault" [.word (word 17)] 0
  check "argumentFault" [.word (word 17)] 0
  check "namedArgumentsFault" [.word (word 7), .word (word 17)] 0
  check "pairFault" [.word (word 7), .word (word 17)] 0
  check "assignmentFault" [.word (word 7), .word (word 17)] 0
  check "conditionFault" [.word (word 7), .word (word 17)] 1
  check "bodyFault" [.word (word 11), .word (word 17)] 1
  check "postFault" [.word (word 13), .word (word 17)] 1

end Tests.RustHullFaultCorrespondence
