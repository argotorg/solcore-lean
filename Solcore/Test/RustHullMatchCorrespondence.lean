import Solcore.Frontend.RustHull.RecursiveProgramCorrespondence

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
    indexedMatch, indexedArms, wordArms, faultArms, wildcardArm, arm, ret, RecursiveStatement,
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
