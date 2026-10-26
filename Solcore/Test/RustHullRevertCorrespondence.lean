import Solcore.Frontend.RustHull.ContractCallModeExecutionCorrespondence
import Solcore.Frontend.RustHull.ContractCallModeSupported

/-! Hull's explicit revert reaches the actual lowering, memory write and revert
termination through the call-mode public theorem. Each scenario reverts with a
message of at most one EVM word: a short message, an empty one, a full word of
32 bytes, and a short message written over an earlier word at offset zero. The
independent source stores the left-aligned message word and reverts with
exactly the message bytes. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.RustHullRevertCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence

inductive Scenario where
  | short | empty | full | overwrite
  deriving DecidableEq, Repr

private abbrev w := Core.Word.ofNatModulo
private def word (text : String) : Expr := ⟨.word, .word text, none⟩
private def call (type : Ty) (name : String) (arguments : List Expr) : Expr := ⟨type, .call name arguments, none⟩
private def expression (value : Expr) : Stmt := ⟨.expression value, none⟩

def rootBytes : List UInt8 := [0]
def message : Scenario → String
  | .short => "boom"
  | .empty => ""
  | .full => "abcdefghijklmnopqrstuvwxyz012345"
  | .overwrite => "ok"
def reverting (scenario : Scenario) : Stmt := ⟨.revert (message scenario), none⟩
/-- A word of ones written before the revert in the overwrite scenario. -/
def seed : Stmt := expression (call .unit "mstore" [word "0",
  word "115792089237316195423570985008687907853269984665640564039457584007913129639935"])
def code (scenario : Scenario) : CodeBlock := {
  stmts := (if scenario = .overwrite then [seed] else []) ++ [reverting scenario], functions := []}
def program (scenario : Scenario) : Program :=
  {entryPoints := [], functions := [], objects := [.object "Reverter" (code scenario) []]}
def functions (scenario : Scenario) : List Function := [AccountRuntime.frameFunction (code scenario)]
def effects : Semantics.ExternalSemantics RuntimeCallModeSemantics.State :=
  ChildFrameModeSemantics.effectsAt [] 1 (some rootBytes)
def context : Contract.Context := {}

abbrev SourceState := Semantics.State RuntimeCallModeSemantics.State
def frame (state : SourceState) := state.external.runtime.runtime.runtime.runtime.runtime
def withMemory (state : SourceState) (memory : MemorySemantics.State) : SourceState :=
  ⟨[], {state.external with runtime := (RuntimeReturnDataEffectsSemantics.withRuntime state.external.runtime
    {frame state with memory := memory})}⟩
def initial (object : Contract.CompiledObject) : SourceState :=
  ⟨[], ContractCallCorrespondence.contextInitialState (some rootBytes) object (Contract.normalizeContext context)⟩
def seeded (object : Contract.CompiledObject) : SourceState :=
  withMemory (initial object)
    (MemorySemantics.mstore (frame (initial object)).memory (w 0) (w (Core.wordModulus - 1))).2
def beforeRevert (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  if scenario = .overwrite then seeded object else initial object

/-- The independent effect of the revert: the message word at offset zero and
the revert registers over the message bytes. -/
def stored (state : SourceState) (scenario : Scenario) : MemorySemantics.State :=
  (MemorySemantics.mstore (frame state).memory Core.Word.zero (RevertSemantics.messageWord (message scenario))).2
def halted (state : SourceState) (scenario : Scenario) : RuntimeEffectsSemantics.State :=
  (TerminationSemantics.terminate {frame state with memory := stored state scenario} 2 Core.Word.zero
    (RevertSemantics.messageLength (message scenario))).2
def finalState (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  let state := beforeRevert object scenario
  {state with external := {state.external with
    runtime := RuntimeReturnDataEffectsSemantics.withRuntime state.external.runtime (halted state scenario)}}
def result : Semantics.Result Semantics.Value := .fault (.language Core.Word.maximum)

private theorem fits (scenario : Scenario) : (message scenario).toUTF8.size ≤ 32 := by
  cases scenario <;> decide +kernel

private theorem revert_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalStmt (functions scenario) effects [] (reverting scenario) (beforeRevert object scenario)
      (.fault (.language Core.Word.maximum)) (finalState object scenario) := by
  cases scenario
  all_goals
    apply Semantics.EvalStmt.revert rfl
    exact RevertSemantics.Reverted.reverted (fits _) rfl rfl

private theorem seed_source (object : Contract.CompiledObject) :
    Semantics.EvalStmt (functions .overwrite) effects [] seed (initial object) .fallthrough (seeded object) := by
  apply Semantics.EvalStmt.expression rfl
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "0") rfl)
      (.cons (.word (text := "115792089237316195423570985008687907853269984665640564039457584007913129639935") rfl) .nil)
  · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

theorem source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalFunction (functions scenario) effects (AccountRuntime.frameFunction (code scenario)) []
      (initial object) result (finalState object scenario) := by
  apply Semantics.EvalFunction.body (control := .fault _) rfl
  cases scenario
  case overwrite =>
    apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (seed_source object)
    exact .stop (by intros; intro impossible; cases impossible) (revert_source object .overwrite)
      (by intro impossible; cases impossible)
  all_goals
    exact .stop (by intros; intro impossible; cases impossible) (revert_source object _)
      (by intro impossible; cases impossible)

def usedNames : List String := ["mstore", "revert"]

theorem eligible (scenario : Scenario) {supported : String → Prop}
    (available : ∀ name ∈ usedNames, supported name) :
    ExecutableProgram supported (functions scenario) := by
  intro function member statement statementMember
  simp only [functions, List.mem_cons, List.not_mem_nil, or_false] at member
  subst function
  have revertAvailable : supported "revert" := available _ (by simp [usedNames])
  cases scenario <;>
    simp only [AccountRuntime.frameFunction, code, reverting, seed, if_true, if_false, reduceCtorEq,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at statementMember
  all_goals try (subst statement; simpa only [ExecutableStatement] using revertAvailable)
  rcases statementMember with rfl | rfl
  · simp only [expression, ExecutableStatement]
    apply ExecutableExpression.external (name := "mstore") (available _ (by simp [usedNames])) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .word _ _ _
  · simpa only [ExecutableStatement] using revertAvailable

private theorem names_supported : ∀ name ∈ usedNames, ContractCallModeCorrespondence.supported true name := by
  intro name member
  simp only [usedNames, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl ⟨.store, rfl⟩)))))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inr ⟨.reverted, rfl⟩))))))

private theorem empty_connection : ModeChildCatalogExecutionCorrespondence.CatalogConnection [] [] [] := by
  intro address source selected
  simp [ChildFrameSemantics.select] at selected

private theorem empty_links (object : Contract.CompiledObject) :
    ContractCallModeCorrespondence.InitialContextLinks (some rootBytes) [] object context [] := by
  intro anchor member
  simp at member

/-- Public consumer of the call-mode theorem for Hull's explicit revert: short,
empty and full-word messages, and a message over an earlier memory word. -/
theorem public_resumes (scenario : Scenario) {object : Contract.CompiledObject}
    (accepted : Contract.compileObject (program scenario) ["Reverter"] 64 (some rootBytes) [] = .ok object) :
    ∃ value, ContractCallModeCorrespondence.PublicMessageRel context result
        (finalState object scenario).external value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate context) initialFuel limit)
          additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  exact ContractCallModeCorrespondence.compileObject_resumes_exact (height := 0) (code := code scenario) (by rfl)
    accepted rfl (eligible scenario names_supported) empty_connection context rfl (empty_links object)
    (source object scenario)

private def check (scenario : Scenario) : IO Unit := do
  let object ← match Contract.compileObject (program scenario) ["Reverter"] 64 (some rootBytes) [] with
    | .ok object => pure object
    | .error error => throw (IO.userError s!"revert correspondence: compile failed: {reprStr error}")
  let prepared := object.instantiate context
  let checkpoint ← match (Contract.runWithReceipt prepared 0).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"revert correspondence: zero fuel completed: {reprStr outcome}")
  for receipt in [Contract.runWithReceipt prepared 1000000, Contract.resumeWithReceipt checkpoint 1000000] do
    match receipt.outcome with
    | .reverted bytes =>
        unless bytes == (message scenario).toUTF8.toList do
          throw (IO.userError s!"revert correspondence: wrong bytes for {reprStr scenario}: {reprStr bytes}")
    | outcome =>
        throw (IO.userError s!"revert correspondence: unexpected outcome for {reprStr scenario}: {reprStr outcome}")

def run : IO Unit := do
  for scenario in [Scenario.short, .empty, .full, .overwrite] do
    check scenario

end Tests.RustHullRevertCorrespondence
