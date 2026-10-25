import Solcore.Frontend.RustHull.ContractCopyExecutionCorrespondence
import Solcore.Test.RustHullMemoryCopyDerivations

/-! Calldata copying and both overlap directions preserve a retained source.
The independent derivation reaches public return or overflow after repeated
resumption, including an empty range at the largest address. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.RustHullMemoryCopyCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence
open RustHullMemoryCopyDerivations (calldata calldataWords first right left)

inductive Scenario where | returned | empty | destinationOverflow | sourceOverflow
  deriving DecidableEq, Repr

private def word (text : String) : Expr := ⟨.word, .word text, none⟩
private def call (name : String) (arguments : List Expr) : Expr := ⟨.unit, .call name arguments, none⟩
private def expression (value : Expr) : Stmt := ⟨.expression value, none⟩
private def maximum := "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
def calldataCopy : Expr := call "calldatacopy" [word "1", word "0", word "33"]
def copyRight : Expr := call "mcopy" [word "2", word "1", word "33"]
def copyLeft : Expr := call "mcopy" [word "0", word "2", word "33"]
def returnBytes : Expr := call "return" [word "0", word "33"]
def lastCopy : Scenario → Expr
  | .returned => call "mcopy" [word "0", word "0", word "0"]
  | .empty => call "mcopy" [word maximum, word maximum, word "0"]
  | .destinationOverflow => call "mcopy" [word maximum, word "0", word "1"]
  | .sourceOverflow => call "mcopy" [word "96", word maximum, word "1"]
def code (scenario : Scenario) : CodeBlock := {
  stmts := [expression calldataCopy, expression copyRight, expression copyLeft,
    expression (lastCopy scenario), expression returnBytes]
  functions := []
}
def program (scenario : Scenario) : Program := {
  entryPoints := [], functions := [], objects := [.object "Copy" (code scenario) []]
}
def context : Contract.Context := {calldata := calldata}
def initial (object : Contract.CompiledObject) : Semantics.State RuntimeCopyEffectsSemantics.State :=
  ⟨[], ContractCopyCorrespondence.contextInitialState object (Contract.normalizeContext context)⟩
def copied (object : Contract.CompiledObject) (memory : MemorySemantics.State) : Semantics.State RuntimeCopyEffectsSemantics.State :=
  ⟨[], RuntimeCopyEffectsSemantics.withMemory (initial object).external memory⟩
def succeeds : Scenario → Bool
  | .returned | .empty => true
  | _ => false

def finalState (object : Contract.CompiledObject) (scenario : Scenario) : Semantics.State RuntimeCopyEffectsSemantics.State :=
  if succeeds scenario then
    ⟨[], RuntimeFullEffectsSemantics.withRuntime (copied object left).external
      (TerminationSemantics.terminate (copied object left).external.runtime.runtime 1
        Core.Word.zero (Core.Word.ofNatModulo 33)).2⟩
  else copied object left

def reason (scenario : Scenario) : Core.Word :=
  if succeeds scenario then Core.Word.maximum else Core.Word.ofNatModulo 6

def result (scenario : Scenario) : Semantics.Result Semantics.Value := .fault (.language (reason scenario))

private theorem calldata_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] RuntimeCopyEffectsSemantics.effects [] calldataCopy
      (initial object) (.value .unit) (copied object first) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "1") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "33") rfl) .nil))
  · exact .external (by rfl) rfl (.copy (.calldata RustHullMemoryCopyDerivations.from_calldata))

private theorem right_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] RuntimeCopyEffectsSemantics.effects [] copyRight
      (copied object first) (.value .unit) (copied object right) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "2") rfl) (.cons (.word (text := "1") rfl) (.cons (.word (text := "33") rfl) .nil))
  · exact .external (by rfl) rfl (.copy (.move RustHullMemoryCopyDerivations.overlap_right))

private theorem left_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] RuntimeCopyEffectsSemantics.effects [] copyLeft
      (copied object right) (.value .unit) (copied object left) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "0") rfl) (.cons (.word (text := "2") rfl) (.cons (.word (text := "33") rfl) .nil))
  · exact .external (by rfl) rfl (.copy (.move RustHullMemoryCopyDerivations.overlap_left))

private theorem last_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] RuntimeCopyEffectsSemantics.effects [] (lastCopy scenario)
      (copied object left)
      (if succeeds scenario then .value .unit else MemorySemantics.overflow) (copied object left) := by
  cases scenario
  case returned =>
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) .nil))
    · exact .external (by rfl) rfl (.copy (.move (.done (by rfl) (by rfl) (by rfl) (by rfl) (.empty _ _ _ _))))
  case empty =>
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := maximum) rfl) (.cons (.word (text := maximum) rfl) (.cons (.word (text := "0") rfl) .nil))
    · exact .external (by rfl) rfl (.copy (.move RustHullMemoryCopyDerivations.empty_maximum))
  case destinationOverflow =>
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := maximum) rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "1") rfl) .nil))
    · exact .external (by rfl) rfl (.copy (.move RustHullMemoryCopyDerivations.destination_overflow))
  case sourceOverflow =>
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := "96") rfl) (.cons (.word (text := maximum) rfl) (.cons (.word (text := "1") rfl) .nil))
    · exact .external (by rfl) rfl (.copy (.move RustHullMemoryCopyDerivations.source_overflow))

private theorem return_source (object : Contract.CompiledObject) (scenario : Scenario)
    (successful : succeeds scenario = true) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] RuntimeCopyEffectsSemantics.effects [] returnBytes
      (copied object left) (result scenario) (finalState object scenario) := by
  simp only [result, reason, finalState, successful, ↓reduceIte]
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "0") rfl) (.cons (.word (text := "33") rfl) .nil)
  · exact .external (by rfl) rfl (.runtime (.termination rfl))

theorem source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalFunction [AccountRuntime.frameFunction (code scenario)] RuntimeCopyEffectsSemantics.effects
      (AccountRuntime.frameFunction (code scenario)) [] (initial object) (result scenario) (finalState object scenario) := by
  apply Semantics.EvalFunction.body (control := .fault (.language (reason scenario))) rfl
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
    (.expression rfl (calldata_source object scenario))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
    (.expression rfl (right_source object scenario))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
    (.expression rfl (left_source object scenario))
  cases successful : succeeds scenario with
  | true =>
      have last := last_source object scenario
      simp only [successful, ↓reduceIte] at last
      apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl last)
      exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (return_source object scenario successful))
        (by intro impossible; cases impossible)
  | false =>
      have last := last_source object scenario
      simp only [successful, Bool.false_eq_true, ↓reduceIte] at last
      simp only [reason, finalState, successful, Bool.false_eq_true, ↓reduceIte]
      exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl last)
        (by intro impossible; cases impossible)

private theorem words_eligible {name : String} {texts : List String} (scenario : Scenario)
    (available : ContractCopyCorrespondence.supported name)
    (absent : [AccountRuntime.frameFunction (code scenario)].find? (·.name == name) = none) :
    ExecutableExpression ContractCopyCorrespondence.supported [AccountRuntime.frameFunction (code scenario)]
      (call name (texts.map word)) := by
  apply ExecutableExpression.external available absent
  intro argument member
  obtain ⟨text, _, rfl⟩ := List.mem_map.mp member
  exact .word _ _ _

private theorem last_eligible (scenario : Scenario) :
    ExecutableExpression ContractCopyCorrespondence.supported [AccountRuntime.frameFunction (code scenario)] (lastCopy scenario) := by
  cases scenario
  case returned => exact words_eligible (texts := ["0", "0", "0"]) .returned (Or.inr ⟨.move, rfl⟩) rfl
  case empty => exact words_eligible (texts := [maximum, maximum, "0"]) .empty (Or.inr ⟨.move, rfl⟩) rfl
  case destinationOverflow => exact words_eligible (texts := [maximum, "0", "1"]) .destinationOverflow (Or.inr ⟨.move, rfl⟩) rfl
  case sourceOverflow => exact words_eligible (texts := ["96", maximum, "1"]) .sourceOverflow (Or.inr ⟨.move, rfl⟩) rfl

theorem eligible (scenario : Scenario) :
    ExecutableProgram ContractCopyCorrespondence.supported [AccountRuntime.frameFunction (code scenario)] := by
  intro function member statement statementMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst function
  simp only [AccountRuntime.frameFunction, code, List.mem_cons, List.not_mem_nil, or_false] at statementMember
  rcases statementMember with rfl | rfl | rfl | rfl | rfl
  all_goals simp only [expression, ExecutableStatement]
  · exact words_eligible (texts := ["1", "0", "33"]) scenario (Or.inr ⟨.calldata, rfl⟩) rfl
  · exact words_eligible (texts := ["2", "1", "33"]) scenario (Or.inr ⟨.move, rfl⟩) rfl
  · exact words_eligible (texts := ["0", "2", "33"]) scenario (Or.inr ⟨.move, rfl⟩) rfl
  · exact last_eligible scenario
  · exact words_eligible (texts := ["0", "33"]) scenario (Or.inl (Or.inr ⟨.returned, rfl⟩)) rfl

theorem public_resumes (scenario : Scenario) {prepared : Contract.Prepared}
    (accepted : Contract.prepare (program scenario) ["Copy"] context 64 = .ok prepared) :
    ∃ object, Contract.compileObject (program scenario) ["Copy"] 64 none [] = .ok object ∧
      prepared = object.instantiate context ∧
      ∃ value, ContractCopyCorrespondence.PublicMessageRel context (result scenario) (finalState object scenario).external value ∧
        ∃ required, ∀ initialFuel additional limit last,
          Contract.ReceiptResumes limit (Contract.runWithReceipt prepared initialFuel limit) additional last →
          (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
          ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  obtain ⟨object, compiled, preparedEq, consume⟩ := ContractCopyCorrespondence.prepare_resumes_exact
    (code := code scenario) (by rfl) accepted (eligible scenario) rfl
  exact ⟨object, compiled, preparedEq, consume _ _ (source object scenario)⟩

private def check (scenario : Scenario) : IO Unit := do
  let object ← match Contract.compileObject (program scenario) ["Copy"] 64 with
    | .ok object => pure object
    | .error error => throw (IO.userError s!"copy correspondence: compile failed: {reprStr error}")
  let prepared := object.instantiate context
  let checkpoint ← match (Contract.runWithReceipt prepared 0).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | result => throw (IO.userError s!"copy correspondence: zero fuel completed: {reprStr result}")
  let checkpoint ← match (Contract.resumeWithReceipt checkpoint 17).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | result => throw (IO.userError s!"copy correspondence: short resume completed: {reprStr result}")
  let receipt := Contract.resumeWithReceipt checkpoint 1000000
  match succeeds scenario, receipt.outcome with
  | true, .returned bytes storage =>
      unless bytes == calldata ++ [0] && storage.isEmpty do
        throw (IO.userError "copy correspondence: copied bytes or empty storage differ")
  | false, .languageFailure (.word reason) =>
      unless reason == Core.Word.ofNatModulo 6 && receipt.world.isEmpty do
        throw (IO.userError "copy correspondence: overflow reason/export differs")
  | _, outcome => throw (IO.userError s!"copy correspondence: incorrect outcome: {reprStr outcome}")
  match Core.runStateful 1000000 (Core.State.initial prepared.expression) with
  | .done (.pair _ (.pair exit (.pair offset (.pair count (.pair memory _))))) _ =>
      let state := (finalState object scenario).external.runtime.runtime
      unless memory == Core.WordMapping.encode left.words && exit == .word state.storage.exit &&
          offset == .word state.storage.returnOffset && count == .word state.storage.returnSize do
        throw (IO.userError "copy correspondence: Core snapshot differs from independent copy")
  | outcome => throw (IO.userError s!"copy correspondence: Core failed: {reprStr outcome}")

def run : IO Unit := do
  for scenario in [Scenario.returned, .empty, .destinationOverflow, .sourceOverflow] do check scenario

end Tests.RustHullMemoryCopyCorrespondence
