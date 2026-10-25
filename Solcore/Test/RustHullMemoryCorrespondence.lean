import Solcore.Frontend.RustHull.ContractMemoryExecutionCorrespondence

/-! Independent memory computation and actual public contract execution agree
on unaligned word access and on a language fault after a completed write. -/
set_option autoImplicit false
set_option maxRecDepth 4096
namespace Tests.RustHullMemoryCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence

private def word (text : String) : Expr := ⟨.word, .word text, none⟩
private def call (name : String) (type : Ty) (arguments : List Expr) : Expr :=
  ⟨type, .call name arguments, none⟩
private def expression (value : Expr) : Stmt := ⟨.expression value, none⟩

def write : Expr := call "mstore" .unit [word "1", word "171"]
def read : Expr := call "mload" .word [word "1"]
def overflow : Expr := call "mload" .word [word "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"]
def code (fault : Bool) : CodeBlock := {
  stmts := [expression write, expression (if fault then overflow else read)]
  functions := []
}
def program (fault : Bool) : Program := {
  entryPoints := [], functions := [], objects := [.object "Memory" (code fault) []]
}
def initial : Semantics.State MemorySemantics.State := ⟨[], {}⟩
def written : Semantics.State MemorySemantics.State :=
  ⟨[], (MemorySemantics.mstore {} (Core.Word.ofNatModulo 1) (Core.Word.ofNatModulo 171)).2⟩

private theorem write_source (fault : Bool) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code fault)] MemorySemantics.effects [] write initial
      (.value .unit) written := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "1") rfl) (.cons (.word (text := "171") rfl) .nil)
  · exact .external (by rfl) rfl rfl

private theorem read_source :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code false)] MemorySemantics.effects [] read written
      (.value (.word (Core.Word.ofNatModulo 171))) written := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "1") rfl) .nil
  · exact .external (by rfl) rfl rfl

private theorem overflow_source :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code true)] MemorySemantics.effects [] overflow written
      (.fault (.language (Core.Word.ofNatModulo 6))) written := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff") rfl) .nil
  · exact .external (by rfl) rfl rfl

theorem source (fault : Bool) :
    Semantics.EvalFunction [AccountRuntime.frameFunction (code fault)] MemorySemantics.effects
      (AccountRuntime.frameFunction (code fault)) [] initial
      (if fault then .fault (.language (Core.Word.ofNatModulo 6)) else .value .unit) written := by
  cases fault with
  | false =>
      apply Semantics.EvalFunction.body (control := .fallthrough) rfl
      apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
        (.expression rfl (write_source false))
      exact .next (by intros; intro impossible; cases impossible) (.expression rfl read_source) .nil
  | true =>
      apply Semantics.EvalFunction.body (control := .fault (.language (Core.Word.ofNatModulo 6))) rfl
      apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
        (.expression rfl (write_source true))
      exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl overflow_source)
        (by intro impossible; cases impossible)

theorem eligible (fault : Bool) :
    ExecutableProgram MemoryEffectCorrespondence.supported [AccountRuntime.frameFunction (code fault)] := by
  intro function member statement statementMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst function
  simp only [AccountRuntime.frameFunction, code, List.mem_cons, List.not_mem_nil, or_false] at statementMember
  rcases statementMember with rfl | rfl
  all_goals simp only [expression, ExecutableStatement]
  · apply ExecutableExpression.external (name := "mstore") ⟨.store, rfl⟩ (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .word _ _ _
  · cases fault <;>
      apply ExecutableExpression.external (name := "mload") ⟨.load, rfl⟩ (by rfl)
    all_goals
      intro argument member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      subst argument
      exact .word _ _ _

/-- The concrete independent derivations reach every actual public checkpoint
chain, including a language fault after the completed unaligned write. -/
theorem public_resumes (fault : Bool) {prepared : Contract.Prepared}
    (accepted : Contract.prepare (program fault) ["Memory"] {} 64 = .ok prepared) :
    ∃ object, Contract.compileObject (program fault) ["Memory"] 64 none [] = .ok object ∧
      prepared = object.instantiate {} ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt prepared initialFuel limit) additional last →
        (last = Contract.finish limit
          (ContractMemoryCorrespondence.publicMessageValue object {}
            (if fault then .fault (.language (Core.Word.ofNatModulo 6)) else .value .unit)
            written.external) ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  exact ContractMemoryCorrespondence.prepare_resumes_exact
    (code := code fault) (by rfl) accepted (eligible fault) rfl (source fault)

private def check (fault : Bool) : IO Unit := do
  let prepared ← match Contract.prepare (program fault) ["Memory"] {} 64 with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError s!"memory correspondence: preparation failed: {reprStr error}")
  let checkpoint ← match (Contract.runWithReceipt prepared 0).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | result => throw (IO.userError s!"memory correspondence: zero fuel completed: {reprStr result}")
  let checkpoint ← match (Contract.resumeWithReceipt checkpoint 11).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | result => throw (IO.userError s!"memory correspondence: short resume completed: {reprStr result}")
  let receipt := Contract.resumeWithReceipt checkpoint 300000
  match fault, receipt.outcome with
  | false, .returned [] [] => pure ()
  | true, .languageFailure (.word reason) =>
      unless reason == Core.Word.ofNatModulo 6 do
        throw (IO.userError "memory correspondence: incorrect fault reason")
  | _, result => throw (IO.userError s!"memory correspondence: incorrect public outcome: {reprStr result}")
  match Core.runStateful 300000 (Core.State.initial prepared.expression) with
  | .done (.pair _ (.pair _ (.pair _ (.pair _ (.pair memory _))))) _ =>
      unless memory == Core.WordMapping.encode written.external.words do
        throw (IO.userError "memory correspondence: write was lost before snapshot or fault")
  | result => throw (IO.userError s!"memory correspondence: Core execution failed: {reprStr result}")

def run : IO Unit := do
  check false
  check true

end Tests.RustHullMemoryCorrespondence
