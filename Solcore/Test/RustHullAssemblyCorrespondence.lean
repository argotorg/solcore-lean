import Solcore.Frontend.RustHull.ContractCallModeExecutionCorrespondence
import Solcore.Frontend.RustHull.ContractCallModeSupported

/-! Inline Yul blocks of one builtin call on two literal words reach the actual
Yul lowering, memory writes and terminations through the call-mode public
theorem. Each scenario writes memory in one block and ends the frame in a
second: an `mstore` returned as a word, an `mstore8` of a hexadecimal byte, an
`mstore` whose last byte is reverted, and an `mstore` of the literal `true`
whose last byte is returned. The independent source follows `YulSemantics`. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.RustHullAssemblyCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence

inductive Scenario where
  | stored | byte | reverted | flag
  deriving DecidableEq, Repr

private abbrev w := Core.Word.ofNatModulo
private def number (text : String) : YulExpr := ⟨.literal (.number text), none⟩
private def block (name : String) (first second : YulExpr) : Stmt :=
  ⟨.assembly [⟨.expression ⟨.call ⟨name, none⟩ [first, second], none⟩, none⟩], none⟩

def rootBytes : List UInt8 := [0]
def writing : Scenario → Stmt
  | .stored => block "mstore" (number "0") (number "42")
  | .byte => block "mstore8" (number "31") ⟨.literal (.hex "0xff"), none⟩
  | .reverted => block "mstore" (number "0") (number "7")
  | .flag => block "mstore" (number "0") ⟨.literal (.bool true), none⟩
def ending : Scenario → Stmt
  | .reverted => block "revert" (number "31") (number "1")
  | .flag => block "return" (number "31") (number "1")
  | _ => block "return" (number "0") (number "32")
def code (scenario : Scenario) : CodeBlock := {stmts := [writing scenario, ending scenario], functions := []}
def program (scenario : Scenario) : Program :=
  {entryPoints := [], functions := [], objects := [.object "Assembler" (code scenario) []]}
def functions (scenario : Scenario) : List Function := [AccountRuntime.frameFunction (code scenario)]
def effects : Semantics.ExternalSemantics RuntimeCallModeSemantics.State :=
  ChildFrameModeSemantics.effectsAt [] 1 (some rootBytes)
def context : Contract.Context := {}

abbrev SourceState := Semantics.State RuntimeCallModeSemantics.State
def frame (state : SourceState) := state.external.runtime.runtime.runtime.runtime.runtime
def withFrame (state : SourceState) (next : RuntimeEffectsSemantics.State) : SourceState :=
  {state with external := {state.external with
    runtime := (RuntimeReturnDataEffectsSemantics.withRuntime state.external.runtime next)}}
def initial (object : Contract.CompiledObject) : SourceState :=
  ⟨[], ContractCallCorrespondence.contextInitialState (some rootBytes) object (Contract.normalizeContext context)⟩

/-- The independent effect of each scenario's two blocks. -/
def write : Scenario → RuntimeEffectsSemantics.State → RuntimeEffectsSemantics.State
  | .stored, current => {current with memory := (MemorySemantics.mstore current.memory (w 0) (w 42)).2}
  | .byte, current => {current with memory := (MemorySemantics.mstore8 current.memory (w 31) (w 255)).2}
  | .reverted, current => {current with memory := (MemorySemantics.mstore current.memory (w 0) (w 7)).2}
  | .flag, current => {current with memory := (MemorySemantics.mstore current.memory (w 0) (w 1)).2}
def exit : Scenario → RuntimeEffectsSemantics.State → RuntimeEffectsSemantics.State
  | .reverted, current => (TerminationSemantics.terminate current 2 (w 31) (w 1)).2
  | .flag, current => (TerminationSemantics.terminate current 1 (w 31) (w 1)).2
  | _, current => (TerminationSemantics.terminate current 1 (w 0) (w 32)).2
def written (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  withFrame (initial object) (write scenario (frame (initial object)))
def finalState (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  withFrame (written object scenario) (exit scenario (frame (written object scenario)))
def result : Semantics.Result Semantics.Value := .fault (.language Core.Word.maximum)

private theorem write_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalStmt (functions scenario) effects [] (writing scenario) (initial object) .fallthrough
      (written object scenario) := by
  cases scenario
  · exact .assembly rfl ⟨_, .call (firstWord := w 0) (secondWord := w 42) (result := .value .unit)
      (by decide +kernel) (by decide +kernel) .mstore, rfl⟩
  · exact .assembly rfl ⟨_, .call (firstWord := w 31) (secondWord := w 255) (result := .value .unit)
      (by decide +kernel) (by decide +kernel) .mstore8, rfl⟩
  · exact .assembly rfl ⟨_, .call (firstWord := w 0) (secondWord := w 7) (result := .value .unit)
      (by decide +kernel) (by decide +kernel) .mstore, rfl⟩
  · exact .assembly rfl ⟨_, .call (firstWord := w 0) (secondWord := w 1) (result := .value .unit)
      (by decide +kernel) (by decide +kernel) .mstore, rfl⟩

private theorem exit_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalStmt (functions scenario) effects [] (ending scenario) (written object scenario)
      (.fault (.language Core.Word.maximum)) (finalState object scenario) := by
  cases scenario
  · exact .assembly rfl ⟨_, .call (firstWord := w 0) (secondWord := w 32)
      (result := .fault (.language Core.Word.maximum)) (by decide +kernel) (by decide +kernel) .returned, rfl⟩
  · exact .assembly rfl ⟨_, .call (firstWord := w 0) (secondWord := w 32)
      (result := .fault (.language Core.Word.maximum)) (by decide +kernel) (by decide +kernel) .returned, rfl⟩
  · exact .assembly rfl ⟨_, .call (firstWord := w 31) (secondWord := w 1)
      (result := .fault (.language Core.Word.maximum)) (by decide +kernel) (by decide +kernel) .reverted, rfl⟩
  · exact .assembly rfl ⟨_, .call (firstWord := w 31) (secondWord := w 1)
      (result := .fault (.language Core.Word.maximum)) (by decide +kernel) (by decide +kernel) .returned, rfl⟩

theorem source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalFunction (functions scenario) effects (AccountRuntime.frameFunction (code scenario)) []
      (initial object) result (finalState object scenario) := by
  apply Semantics.EvalFunction.body (control := .fault _) rfl
  cases scenario
  all_goals
    apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (write_source object _)
    exact .stop (by intros; intro impossible; cases impossible) (exit_source object _)
      (by intro impossible; cases impossible)

def usedNames : List String := ["mstore", "mstore8", "return", "revert"]

theorem eligible (scenario : Scenario) {supported : String → Prop}
    (available : ∀ name ∈ usedNames, supported name) :
    ExecutableProgram supported (functions scenario) := by
  intro function member statement statementMember
  simp only [functions, List.mem_cons, List.not_mem_nil, or_false] at member
  subst function
  simp only [AccountRuntime.frameFunction, code, List.mem_cons, List.not_mem_nil, or_false] at statementMember
  rcases statementMember with rfl | rfl
  all_goals
    cases scenario
    all_goals
      simp only [writing, ending, block, ExecutableStatement, YulFragment.Eligible]
      exact available _ (by simp [usedNames])

private theorem names_supported : ∀ name ∈ usedNames, ContractCallModeCorrespondence.supported true name := by
  intro name member
  simp only [usedNames, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl ⟨.store, rfl⟩)))))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl ⟨.store8, rfl⟩)))))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inr ⟨.returned, rfl⟩))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inr ⟨.reverted, rfl⟩))))))

private theorem empty_connection : ModeChildCatalogExecutionCorrespondence.CatalogConnection [] [] [] := by
  intro address source selected
  simp [ChildFrameSemantics.select] at selected

private theorem empty_links (object : Contract.CompiledObject) :
    ContractCallModeCorrespondence.InitialContextLinks (some rootBytes) [] object context [] := by
  intro anchor member
  simp at member

/-- Public consumer of the call-mode theorem for inline Yul: memory writes by
`mstore` and `mstore8` on number, hexadecimal and Boolean literals, followed by
`return` or `revert` blocks. -/
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
    accepted rfl (eligible scenario names_supported) empty_connection context rfl (empty_links object)
    (source object scenario)

private def expected : Scenario → List UInt8
  | .stored => List.replicate 31 0 ++ [42]
  | .byte => List.replicate 31 0 ++ [255]
  | .reverted => [7]
  | .flag => [1]

private def check (scenario : Scenario) : IO Unit := do
  let object ← match Contract.compileObject (program scenario) ["Assembler"] 64 (some rootBytes) [] with
    | .ok object => pure object
    | .error error => throw (IO.userError s!"assembly correspondence: compile failed: {reprStr error}")
  let prepared := object.instantiate context
  let checkpoint ← match (Contract.runWithReceipt prepared 0).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"assembly correspondence: zero fuel completed: {reprStr outcome}")
  for receipt in [Contract.runWithReceipt prepared 1000000, Contract.resumeWithReceipt checkpoint 1000000] do
    match scenario, receipt.outcome with
    | .reverted, .reverted bytes =>
        unless bytes == expected scenario do
          throw (IO.userError s!"assembly correspondence: wrong revert bytes: {reprStr bytes}")
    | .reverted, outcome =>
        throw (IO.userError s!"assembly correspondence: unexpected outcome for reverted: {reprStr outcome}")
    | _, .returned bytes _ =>
        unless bytes == expected scenario do
          throw (IO.userError s!"assembly correspondence: wrong bytes for {reprStr scenario}: {reprStr bytes}")
    | _, outcome =>
        throw (IO.userError s!"assembly correspondence: unexpected outcome for {reprStr scenario}: {reprStr outcome}")

def run : IO Unit := do
  for scenario in [Scenario.stored, .byte, .reverted, .flag] do
    check scenario

end Tests.RustHullAssemblyCorrespondence
