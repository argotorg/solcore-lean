import Solcore.Frontend.RustHull.RecursiveProgramCorrespondence

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
