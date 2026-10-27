import Solcore.Frontend.RustHull.ContractCallModeExecutionCorrespondence
import Solcore.Frontend.RustHull.ContractCallModeSupported

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
