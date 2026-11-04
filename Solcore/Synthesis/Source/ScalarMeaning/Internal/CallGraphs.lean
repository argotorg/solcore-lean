import Solcore.Synthesis.Internal.Functions
import Solcore.Synthesis.Source.ScalarMeaning.Internal.Renderer
import Solcore.Synthesis.Internal.CallGraphs
import Solcore.Core.Primitive
import Solcore.Synthesis.Source.ScalarMeaning.Semantics

/-!
# Primitive and call-graph proofs

The raw primitive and call-graph renderers, and agreement of Core Word operations with EVM
operations.
-/

section
-- leanmerge: from Solcore.Synthesis.Source.ScalarMeaning.PrimitiveEquations
/-! Equations for the actual `PrimitiveRenderer.render`, stated with the
scalar source syntax and printer. They unfold the real implementation,
including its private helpers; nothing here re-implements it. Raw opcode
operands are copied into fresh `word` temporaries (snapshots) before the
call that uses them. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

open Solcore.Synthesis.Core (Target)
open Solcore.Synthesis.Source.ScalarRenderer (Rendered)

/-- The copy `let sc_v<n>: word = value;` that the primitive renderers take
of each raw opcode argument. -/
def snapshotOf (indent : Nat) (value : Rendered) : Rendered :=
  ⟨value.lines ++ Stmt.lines indent (.letDecl (temporary value.nextId) .word (.name value.value)),
    temporary value.nextId, value.nextId + 1⟩

/-- A fresh temporary of the target type, bound to `initializer` after
`lines`. -/
def resultOf (indent : Nat) (target : Target) (lines : List String) (next : Nat)
    (initializer : Expr) : Rendered :=
  ⟨lines ++ Stmt.lines indent (.letDecl (temporary next) (LocalType.ofTarget target) initializer),
    temporary next, next + 1⟩

/-- The `std.opcodes` aliases imported by the primitive emitters, as
`(opcode, alias)` pairs in import order. -/
def primitiveAliases : List (String × String) :=
  [("div", "sc_div"), ("mod", "sc_mod"), ("shl", "sc_shl"), ("shr", "sc_shr"),
    ("sar", "sc_sar"), ("sdiv", "sc_sdiv"), ("smod", "sc_smod"), ("sgt", "sc_sgt"),
    ("addmod", "sc_addmod"), ("mulmod", "sc_mulmod"), ("clz", "sc_clz"),
    ("byte", "sc_byte"), ("exp", "sc_exp"), ("signextend", "sc_signextend")]

/-- The source expression printed for an extended binary operation on the
names of its two operand snapshots. Shifts pass the shift first. -/
def primitiveBinary? : Solcore.Core.Wire.BinaryOp → Option (String → String → Expr)
  | .wordDiv => some fun left right => .call2 "sc_div" (.name left) (.name right)
  | .wordMod => some fun left right => .call2 "sc_mod" (.name left) (.name right)
  | .wordShl => some fun left right => .call2 "sc_shl" (.name right) (.name left)
  | .wordShr => some fun left right => .call2 "sc_shr" (.name right) (.name left)
  | .wordSar => some fun left right => .call2 "sc_sar" (.name right) (.name left)
  | .wordSdiv => some fun left right => .call2 "sc_sdiv" (.name left) (.name right)
  | .wordSmod => some fun left right => .call2 "sc_smod" (.name left) (.name right)
  | .wordSgt => some fun left right =>
      .call1 "tobool" (.call2 "sc_sgt" (.name left) (.name right))
  | .wordByte => some fun left right => .call2 "sc_byte" (.name left) (.name right)
  | .wordPow => some fun left right => .call2 "sc_exp" (.name left) (.name right)
  | .wordSignExtend => some fun left right =>
      .call2 "sc_signextend" (.name left) (.name right)
  | _ => none

def ternaryCallee : Solcore.Core.Wire.TernaryOp → String
  | .wordAddMod => "sc_addmod"
  | .wordMulMod => "sc_mulmod"

namespace PrimitiveEquations

theorem word (target : Target) (locals : List String) (indent first : Nat)
    (value : Solcore.Core.Word) :
    PrimitiveRenderer.render target locals indent first (.word value) =
      .ok ⟨Stmt.lines indent (.letDecl (temporary first) .word (.number value.val)),
        temporary first, first + 1⟩ := by
  simp only [PrimitiveRenderer.render]
  rfl

theorem bool (target : Target) (locals : List String) (indent first : Nat) (value : Bool) :
    PrimitiveRenderer.render target locals indent first (.bool value) =
      .ok ⟨Stmt.lines indent (.letDecl (temporary first) .bool (.bool value)),
        temporary first, first + 1⟩ := by
  simp only [PrimitiveRenderer.render]
  rfl

theorem var (target : Target) (locals : List String) (indent first index : Nat) :
    PrimitiveRenderer.render target locals indent first (.var index) =
      match locals[index]? with
      | some binding => .ok ⟨[], binding, first⟩
      | none => .error (.unboundLocal index) := by
  simp only [PrimitiveRenderer.render]
  cases locals[index]? <;> rfl

theorem letE (target : Target) (locals : List String) (indent first : Nat)
    (initializer body : Solcore.Core.Wire.Expr) :
    PrimitiveRenderer.render target locals indent first (.letE initializer body) =
      (PrimitiveRenderer.render .word locals indent first initializer).bind fun value =>
        (PrimitiveRenderer.render target (temporary value.nextId :: locals) indent
          (value.nextId + 1) body).bind fun rest =>
            .ok ⟨value.lines ++
                Stmt.lines indent (.letDecl (temporary value.nextId) .word (.name value.value)) ++
                rest.lines,
              rest.value, rest.nextId⟩ := by
  simp only [PrimitiveRenderer.render]
  rfl

theorem ifE (target : Target) (locals : List String) (indent first : Nat)
    (condition yes no : Solcore.Core.Wire.Expr) :
    PrimitiveRenderer.render target locals indent first (.ifE condition yes no) =
      (PrimitiveRenderer.render .bool locals indent first condition).bind fun tested =>
        (PrimitiveRenderer.render target locals (indent + 4) (tested.nextId + 1) yes).bind
          fun selected =>
            (PrimitiveRenderer.render target locals (indent + 4) selected.nextId no).bind
              fun fallback =>
                .ok ⟨tested.lines ++
                    [indentLine indent ("let " ++ temporary tested.nextId ++ ": " ++
                      (LocalType.ofTarget target).spelling ++ " = " ++ zeroText target ++ ";")] ++
                    [indentLine indent ("if (" ++ tested.value ++ ") {")] ++ selected.lines ++
                    [indentLine (indent + 4)
                        (temporary tested.nextId ++ " = " ++ selected.value ++ ";"),
                      indentLine indent "} else {"] ++
                    fallback.lines ++
                    [indentLine (indent + 4)
                        (temporary tested.nextId ++ " = " ++ fallback.value ++ ";"),
                      indentLine indent "}"],
                  temporary tested.nextId, fallback.nextId⟩ := by
  simp only [PrimitiveRenderer.render]
  cases target <;> rfl

theorem unary (target : Target) (locals : List String) (indent first : Nat)
    (op : Solcore.Core.Wire.UnaryOp) (sourceOp : UnaryOp) (operand : Solcore.Core.Wire.Expr)
    (selected : sourceUnary? op = some sourceOp) :
    PrimitiveRenderer.render target locals indent first (.unary op operand) =
      (PrimitiveRenderer.render (if op == .boolNot then .bool else .word) locals indent first
        operand).bind fun value =>
          .ok ⟨value.lines ++ Stmt.lines indent (.letDecl (temporary value.nextId)
              (LocalType.ofTarget target) (.unary sourceOp (.name value.value))),
            temporary value.nextId, value.nextId + 1⟩ := by
  cases op <;> simp only [sourceUnary?, reduceCtorEq, Option.some.injEq] at selected <;>
    subst selected <;> simp only [PrimitiveRenderer.render] <;> cases target <;> rfl

/-- `CLZ` snapshots its operand, then calls the raw opcode alias. -/
theorem clz (target : Target) (locals : List String) (indent first : Nat)
    (operand : Solcore.Core.Wire.Expr) :
    PrimitiveRenderer.render target locals indent first (.unary .wordClz operand) =
      (PrimitiveRenderer.render .word locals indent first operand).bind fun value =>
        .ok (resultOf indent target (snapshotOf indent value).lines (value.nextId + 1)
          (.call1 "sc_clz" (.name (temporary value.nextId)))) := by
  simp only [PrimitiveRenderer.render]
  cases target <;> rfl

theorem unary_unsupported (target : Target) (locals : List String) (indent first : Nat)
    (op : Solcore.Core.Wire.UnaryOp) (operand : Solcore.Core.Wire.Expr)
    (unsupported : PrimitiveRenderer.supportedUnary op = false) :
    PrimitiveRenderer.render target locals indent first (.unary op operand) =
      .error (.unsupportedUnary op) := by
  cases op <;> simp only [PrimitiveRenderer.supportedUnary, Source.supportedUnary,
    Bool.true_eq_false] at unsupported <;> rfl

theorem binary (target : Target) (locals : List String) (indent first : Nat)
    (op : Solcore.Core.Wire.BinaryOp) (sourceOp : BinaryOp) (left right : Solcore.Core.Wire.Expr)
    (selected : sourceBinary? op = some sourceOp) :
    PrimitiveRenderer.render target locals indent first (.binary op left right) =
      (PrimitiveRenderer.render .word locals indent first left).bind fun leftValue =>
        (PrimitiveRenderer.render .word locals indent leftValue.nextId right).bind
          fun rightValue =>
            .ok ⟨leftValue.lines ++ rightValue.lines ++
                Stmt.lines indent (.letDecl (temporary rightValue.nextId)
                  (LocalType.ofTarget target)
                  (.binary sourceOp (.name leftValue.value) (.name rightValue.value))),
              temporary rightValue.nextId, rightValue.nextId + 1⟩ := by
  cases op <;> simp only [sourceBinary?, reduceCtorEq, Option.some.injEq] at selected <;>
    subst selected <;> simp only [PrimitiveRenderer.render] <;> cases target <;> rfl

/-- Extended binary operations snapshot both operands, left to right, then
call the raw opcode alias. -/
theorem binary_primitive (target : Target) (locals : List String) (indent first : Nat)
    (op : Solcore.Core.Wire.BinaryOp) (build : String → String → Expr)
    (left right : Solcore.Core.Wire.Expr) (selected : primitiveBinary? op = some build) :
    PrimitiveRenderer.render target locals indent first (.binary op left right) =
      (PrimitiveRenderer.render .word locals indent first left).bind fun leftValue =>
        (PrimitiveRenderer.render .word locals indent (leftValue.nextId + 1) right).bind
          fun rightValue =>
            .ok (resultOf indent target
              ((snapshotOf indent leftValue).lines ++ (snapshotOf indent rightValue).lines)
              (rightValue.nextId + 1)
              (build (temporary leftValue.nextId) (temporary rightValue.nextId))) := by
  cases op <;> simp only [primitiveBinary?, reduceCtorEq, Option.some.injEq] at selected <;>
    subst selected <;> simp only [PrimitiveRenderer.render] <;> cases target <;> rfl

theorem binary_unsupported (target : Target) (locals : List String) (indent first : Nat)
    (op : Solcore.Core.Wire.BinaryOp) (left right : Solcore.Core.Wire.Expr)
    (unsupported : PrimitiveRenderer.supportedBinary op = false) :
    PrimitiveRenderer.render target locals indent first (.binary op left right) =
      .error (.unsupportedBinary op) := by
  cases op <;> simp only [PrimitiveRenderer.supportedBinary, Source.supportedBinary,
    Bool.true_eq_false] at unsupported <;> rfl

/-- `ADDMOD` and `MULMOD` snapshot all three operands, then call the raw
opcode alias. -/
theorem ternary (target : Target) (locals : List String) (indent first : Nat)
    (op : Solcore.Core.Wire.TernaryOp) (one two three : Solcore.Core.Wire.Expr) :
    PrimitiveRenderer.render target locals indent first (.ternary op one two three) =
      (PrimitiveRenderer.render .word locals indent first one).bind fun oneValue =>
        (PrimitiveRenderer.render .word locals indent (oneValue.nextId + 1) two).bind
          fun twoValue =>
            (PrimitiveRenderer.render .word locals indent (twoValue.nextId + 1) three).bind
              fun threeValue =>
                .ok (resultOf indent target
                  ((snapshotOf indent oneValue).lines ++ (snapshotOf indent twoValue).lines ++
                    (snapshotOf indent threeValue).lines)
                  (threeValue.nextId + 1)
                  (.call3 (ternaryCallee op) (.name (temporary oneValue.nextId))
                    (.name (temporary twoValue.nextId))
                    (.name (temporary threeValue.nextId)))) := by
  simp only [PrimitiveRenderer.render]
  cases op <;> cases target <;> rfl

end PrimitiveEquations

end Solcore.Synthesis.Source.ScalarMeaning
end

section
-- leanmerge: from Solcore.Synthesis.Source.ScalarMeaning.CallGraphEquations
/-! Equations for the actual `CallGraphRenderer.renderWithFunctions`, stated with
the scalar source syntax and printer. It prints raw opcode calls as the
primitive renderer does, and copies the argument of a helper call into a fresh
`word` temporary before the call. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

open Solcore.Synthesis.Core (Target)
open Solcore.Synthesis.Source.ScalarRenderer (Rendered)
open Solcore.Synthesis.Source.CallGraphRenderer (renderWithFunctions)

namespace CallGraphEquations

theorem word (functions : List String) (target : Target) (locals : List String) (indent first : Nat)
    (value : Solcore.Core.Word) :
    renderWithFunctions functions target locals indent first (.word value) =
      .ok ⟨Stmt.lines indent (.letDecl (temporary first) .word (.number value.val)),
        temporary first, first + 1⟩ := by
  simp only [CallGraphRenderer.renderWithFunctions]
  rfl

theorem bool (functions : List String) (target : Target) (locals : List String)
    (indent first : Nat) (value : Bool) :
    renderWithFunctions functions target locals indent first (.bool value) =
      .ok ⟨Stmt.lines indent (.letDecl (temporary first) .bool (.bool value)),
        temporary first, first + 1⟩ := by
  simp only [CallGraphRenderer.renderWithFunctions]
  rfl

theorem var (functions : List String) (target : Target) (locals : List String)
    (indent first index : Nat) :
    renderWithFunctions functions target locals indent first (.var index) =
      match locals[index]? with
      | some binding => .ok ⟨[], binding, first⟩
      | none => .error (.unboundLocal index) := by
  simp only [CallGraphRenderer.renderWithFunctions]
  cases locals[index]? <;> rfl

theorem letE (functions : List String) (target : Target) (locals : List String) (indent first : Nat)
    (initializer body : Solcore.Core.Wire.Expr) :
    renderWithFunctions functions target locals indent first (.letE initializer body) =
      (renderWithFunctions functions .word locals indent first initializer).bind fun value =>
        (renderWithFunctions functions target (temporary value.nextId :: locals) indent
          (value.nextId + 1) body).bind fun rest =>
            .ok ⟨value.lines ++
                Stmt.lines indent (.letDecl (temporary value.nextId) .word (.name value.value)) ++
                rest.lines,
              rest.value, rest.nextId⟩ := by
  simp only [CallGraphRenderer.renderWithFunctions]
  rfl

theorem ifE (functions : List String) (target : Target) (locals : List String) (indent first : Nat)
    (condition yes no : Solcore.Core.Wire.Expr) :
    renderWithFunctions functions target locals indent first (.ifE condition yes no) =
      (renderWithFunctions functions .bool locals indent first condition).bind fun tested =>
        (renderWithFunctions functions target locals (indent + 4) (tested.nextId + 1) yes).bind
          fun selected =>
            (renderWithFunctions functions target locals (indent + 4) selected.nextId no).bind
              fun fallback =>
                .ok ⟨tested.lines ++
                    [indentLine indent ("let " ++ temporary tested.nextId ++ ": " ++
                      (LocalType.ofTarget target).spelling ++ " = " ++ zeroText target ++ ";")] ++
                    [indentLine indent ("if (" ++ tested.value ++ ") {")] ++ selected.lines ++
                    [indentLine (indent + 4)
                        (temporary tested.nextId ++ " = " ++ selected.value ++ ";"),
                      indentLine indent "} else {"] ++
                    fallback.lines ++
                    [indentLine (indent + 4)
                        (temporary tested.nextId ++ " = " ++ fallback.value ++ ";"),
                      indentLine indent "}"],
                  temporary tested.nextId, fallback.nextId⟩ := by
  simp only [CallGraphRenderer.renderWithFunctions]
  cases target <;> rfl

theorem unary (functions : List String) (target : Target) (locals : List String)
    (indent first : Nat)
    (op : Solcore.Core.Wire.UnaryOp) (sourceOp : UnaryOp) (operand : Solcore.Core.Wire.Expr)
    (selected : sourceUnary? op = some sourceOp) :
    renderWithFunctions functions target locals indent first (.unary op operand) =
      (renderWithFunctions functions (if op == .boolNot then .bool else .word) locals indent first
        operand).bind fun value =>
          .ok ⟨value.lines ++ Stmt.lines indent (.letDecl (temporary value.nextId)
              (LocalType.ofTarget target) (.unary sourceOp (.name value.value))),
            temporary value.nextId, value.nextId + 1⟩ := by
  cases op <;> simp only [sourceUnary?, reduceCtorEq, Option.some.injEq] at selected <;>
    subst selected <;> simp only [CallGraphRenderer.renderWithFunctions] <;> cases target <;> rfl

/-- `CLZ` snapshots its operand, then calls the raw opcode alias. -/
theorem clz (functions : List String) (target : Target) (locals : List String) (indent first : Nat)
    (operand : Solcore.Core.Wire.Expr) :
    renderWithFunctions functions target locals indent first (.unary .wordClz operand) =
      (renderWithFunctions functions .word locals indent first operand).bind fun value =>
        .ok (resultOf indent target (snapshotOf indent value).lines (value.nextId + 1)
          (.call1 "sc_clz" (.name (temporary value.nextId)))) := by
  simp only [CallGraphRenderer.renderWithFunctions]
  cases target <;> rfl

theorem unary_unsupported (functions : List String) (target : Target) (locals : List String)
    (indent first : Nat)
    (op : Solcore.Core.Wire.UnaryOp) (operand : Solcore.Core.Wire.Expr)
    (unsupported : CallGraphRenderer.supportedUnary op = false) :
    renderWithFunctions functions target locals indent first (.unary op operand) =
      .error (.unsupportedUnary op) := by
  cases op <;> simp only [CallGraphRenderer.supportedUnary, PrimitiveRenderer.supportedUnary,
    Source.supportedUnary,
    Bool.true_eq_false] at unsupported <;> rfl

theorem binary (functions : List String) (target : Target) (locals : List String)
    (indent first : Nat)
    (op : Solcore.Core.Wire.BinaryOp) (sourceOp : BinaryOp) (left right : Solcore.Core.Wire.Expr)
    (selected : sourceBinary? op = some sourceOp) :
    renderWithFunctions functions target locals indent first (.binary op left right) =
      (renderWithFunctions functions .word locals indent first left).bind fun leftValue =>
        (renderWithFunctions functions .word locals indent leftValue.nextId right).bind
          fun rightValue =>
            .ok ⟨leftValue.lines ++ rightValue.lines ++
                Stmt.lines indent (.letDecl (temporary rightValue.nextId)
                  (LocalType.ofTarget target)
                  (.binary sourceOp (.name leftValue.value) (.name rightValue.value))),
              temporary rightValue.nextId, rightValue.nextId + 1⟩ := by
  cases op <;> simp only [sourceBinary?, reduceCtorEq, Option.some.injEq] at selected <;>
    subst selected <;> simp only [CallGraphRenderer.renderWithFunctions] <;> cases target <;> rfl

/-- Extended binary operations snapshot both operands, left to right, then
call the raw opcode alias. -/
theorem binary_primitive (functions : List String) (target : Target) (locals : List String)
    (indent first : Nat)
    (op : Solcore.Core.Wire.BinaryOp) (build : String → String → Expr)
    (left right : Solcore.Core.Wire.Expr) (selected : primitiveBinary? op = some build) :
    renderWithFunctions functions target locals indent first (.binary op left right) =
      (renderWithFunctions functions .word locals indent first left).bind fun leftValue =>
        (renderWithFunctions functions .word locals indent (leftValue.nextId + 1) right).bind
          fun rightValue =>
            .ok (resultOf indent target
              ((snapshotOf indent leftValue).lines ++ (snapshotOf indent rightValue).lines)
              (rightValue.nextId + 1)
              (build (temporary leftValue.nextId) (temporary rightValue.nextId))) := by
  cases op <;> simp only [primitiveBinary?, reduceCtorEq, Option.some.injEq] at selected <;>
    subst selected <;> simp only [CallGraphRenderer.renderWithFunctions] <;> cases target <;> rfl

theorem binary_unsupported (functions : List String) (target : Target) (locals : List String)
    (indent first : Nat)
    (op : Solcore.Core.Wire.BinaryOp) (left right : Solcore.Core.Wire.Expr)
    (unsupported : CallGraphRenderer.supportedBinary op = false) :
    renderWithFunctions functions target locals indent first (.binary op left right) =
      .error (.unsupportedBinary op) := by
  cases op <;> simp only [CallGraphRenderer.supportedBinary, PrimitiveRenderer.supportedBinary,
    Source.supportedBinary,
    Bool.true_eq_false] at unsupported <;> rfl

/-- `ADDMOD` and `MULMOD` snapshot all three operands, then call the raw
opcode alias. -/
theorem ternary (functions : List String) (target : Target) (locals : List String)
    (indent first : Nat)
    (op : Solcore.Core.Wire.TernaryOp) (one two three : Solcore.Core.Wire.Expr) :
    renderWithFunctions functions target locals indent first (.ternary op one two three) =
      (renderWithFunctions functions .word locals indent first one).bind fun oneValue =>
        (renderWithFunctions functions .word locals indent (oneValue.nextId + 1) two).bind
          fun twoValue =>
            (renderWithFunctions functions .word locals indent (twoValue.nextId + 1) three).bind
              fun threeValue =>
                .ok (resultOf indent target
                  ((snapshotOf indent oneValue).lines ++ (snapshotOf indent twoValue).lines ++
                    (snapshotOf indent threeValue).lines)
                  (threeValue.nextId + 1)
                  (.call3 (ternaryCallee op) (.name (temporary oneValue.nextId))
                    (.name (temporary twoValue.nextId))
                    (.name (temporary threeValue.nextId)))) := by
  simp only [CallGraphRenderer.renderWithFunctions]
  cases op <;> cases target <;> rfl

/-- A call to an earlier helper snapshots its argument, then calls the helper. -/
theorem apply_ok {functions : List String} {target : Target} {locals : List String}
    {indent first index : Nat} {argument : Solcore.Core.Wire.Expr} {rendered : Rendered}
    (equation : renderWithFunctions functions target locals indent first
      (.apply (.var index) argument) = .ok rendered) :
    target = .word ∧ locals.length ≤ index ∧ ∃ callee value,
      functions[index - locals.length]? = some callee ∧
      renderWithFunctions functions .word locals indent first argument =
        .ok value ∧
      rendered = resultOf indent .word (snapshotOf indent value).lines (value.nextId + 1)
        (.call1 callee (.name (temporary value.nextId))) := by
  cases target with
  | bool => cases equation
  | word =>
      by_cases below : index < locals.length
      · dsimp only [CallGraphRenderer.renderWithFunctions] at equation
        rw [if_pos below] at equation
        cases equation
      · cases found : functions[index - locals.length]? with
        | none =>
            dsimp only [CallGraphRenderer.renderWithFunctions] at equation
            rw [if_neg below, found] at equation
            cases equation
        | some callee =>
            dsimp only [CallGraphRenderer.renderWithFunctions] at equation
            rw [if_neg below, found] at equation
            obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
            exact ⟨rfl, Nat.le_of_not_lt below, callee, value, rfl, valueEquation,
              (Except.ok.inj equation).symm⟩

end CallGraphEquations
end Solcore.Synthesis.Source.ScalarMeaning
end

section
-- leanmerge: from Solcore.Synthesis.Source.ScalarMeaning.PrimitiveAgreement
/-! The Core Word operations reached only through raw `std.opcodes` aliases
agree with the independent EVM operations of the source semantics. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

theorem evm_div (left right : Solcore.Core.Word) :
    Evm.div left.val right.val = (left.udiv right).val := by
  unfold Evm.div Solcore.Core.Word.udiv
  split <;> simp_all [Solcore.Core.Word.zero]

theorem evm_mod (left right : Solcore.Core.Word) :
    Evm.mod left.val right.val = (left.umod right).val := by
  unfold Evm.mod Solcore.Core.Word.umod
  split <;> simp_all [Solcore.Core.Word.zero]

theorem evm_shl (shift value : Solcore.Core.Word) :
    Evm.shl shift.val value.val = (value.shiftLeft shift).val := by
  unfold Evm.shl Solcore.Core.Word.shiftLeft
  split
  · simp [Nat.shiftLeft_eq, Evm.modulus, Solcore.Core.wordModulus]
  · simp [Solcore.Core.Word.zero]

theorem evm_shr (shift value : Solcore.Core.Word) :
    Evm.shr shift.val value.val = (value.shiftRight shift).val := by
  unfold Evm.shr Solcore.Core.Word.shiftRight
  split
  · simp [Nat.shiftRight_eq_div_pow]
  · simp [Solcore.Core.Word.zero]

theorem evm_clz (value : Solcore.Core.Word) :
    Evm.clz value.val = value.clz.val := by
  unfold Evm.clz Solcore.Core.Word.clz
  split
  · simp only [Solcore.Core.Word.ofNatModulo, Solcore.Core.wordModulus]
  · simp only [Solcore.Core.Word.ofNatModulo, Solcore.Core.wordModulus]
    exact (Nat.mod_eq_of_lt (by omega)).symm

theorem evm_byte (index value : Solcore.Core.Word) :
    Evm.byte index.val value.val = (index.byteAt value).val := by
  unfold Evm.byte Solcore.Core.Word.byteAt
  split
  · simp only [Solcore.Core.Word.ofNatModulo, Solcore.Core.wordModulus]
    rw [Nat.pow_mul]
    exact (Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))).symm
  · simp [Solcore.Core.Word.zero]

theorem evm_addmod (left right divisor : Solcore.Core.Word) :
    Evm.addmod left.val right.val divisor.val = (left.addMod right divisor).val := by
  unfold Evm.addmod Solcore.Core.Word.addMod
  split
  · simp [Solcore.Core.Word.zero]
  · have bound := divisor.isLt
    simp only [Solcore.Core.Word.ofNatModulo]
    exact (Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by omega)) bound)).symm

theorem evm_mulmod (left right divisor : Solcore.Core.Word) :
    Evm.mulmod left.val right.val divisor.val = (left.mulMod right divisor).val := by
  unfold Evm.mulmod Solcore.Core.Word.mulMod
  split
  · simp [Solcore.Core.Word.zero]
  · have bound := divisor.isLt
    simp only [Solcore.Core.Word.ofNatModulo]
    exact (Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by omega)) bound)).symm

/-! ### Signed and exponent operations: EVM side -/

namespace Evm

theorem toSigned_of_lt (word : Nat) (small : word < 2 ^ 255) :
    toSigned word = (word : Int) := by
  rw [toSigned, if_pos small]

theorem toSigned_of_ge (word : Nat) (large : ¬ word < 2 ^ 255)
    (bound : word < 2 ^ 256) :
    toSigned word = Int.negSucc (2 ^ 256 - 1 - word) := by
  rw [toSigned, if_neg large, Int.negSucc_eq, modulus]
  omega

theorem ofSigned_cast (value : Nat) (bound : value < 2 ^ 256) :
    ofSigned (value : Int) = value := by
  rw [ofSigned, modulus]
  omega

theorem ofSigned_neg_cast (value : Nat) (bound : value < 2 ^ 256) :
    ofSigned (-(value : Int)) = (2 ^ 256 - value) % 2 ^ 256 := by
  rw [ofSigned, modulus]
  omega

theorem ofSigned_negSucc (value : Nat) (bound : value < 2 ^ 256) :
    ofSigned (Int.negSucc value) = 2 ^ 256 - 1 - value := by
  rw [ofSigned, modulus, Int.negSucc_eq]
  omega

theorem tdiv_cast_cast (a b : Nat) :
    Int.tdiv (a : Int) (b : Int) = ((a / b : Nat) : Int) := rfl

theorem tdiv_cast_negSucc (a b : Nat) :
    Int.tdiv (a : Int) (Int.negSucc b) = -((a / (b + 1) : Nat) : Int) := rfl

theorem tdiv_negSucc_cast (a b : Nat) :
    Int.tdiv (Int.negSucc a) (b : Int) = -(((a + 1) / b : Nat) : Int) := rfl

theorem tdiv_negSucc_negSucc (a b : Nat) :
    Int.tdiv (Int.negSucc a) (Int.negSucc b) = (((a + 1) / (b + 1) : Nat) : Int) := rfl

theorem tmod_cast_cast (a b : Nat) :
    Int.tmod (a : Int) (b : Int) = ((a % b : Nat) : Int) := rfl

theorem tmod_cast_negSucc (a b : Nat) :
    Int.tmod (a : Int) (Int.negSucc b) = ((a % (b + 1) : Nat) : Int) := rfl

theorem tmod_negSucc_cast (a b : Nat) :
    Int.tmod (Int.negSucc a) (b : Int) = -(((a + 1) % b : Nat) : Int) := rfl

theorem tmod_negSucc_negSucc (a b : Nat) :
    Int.tmod (Int.negSucc a) (Int.negSucc b) = -(((a + 1) % (b + 1) : Nat) : Int) := rfl

theorem cast_ediv_cast (a b : Nat) : (a : Int) / (b : Int) = ((a / b : Nat) : Int) := rfl

theorem negSucc_ediv_cast (a b : Nat) (positive : 0 < b) :
    Int.negSucc a / (b : Int) = Int.negSucc (a / b) := by
  obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
  rfl

theorem bne_false_false : (false != false) = false := rfl

theorem bne_false_true : (false != true) = true := rfl

theorem bne_true_false : (true != false) = true := rfl

theorem bne_true_true : (true != true) = false := rfl

theorem bnot_ite_beq_zero (condition : Prop) [Decidable condition] :
    (!((if condition then 1 else 0 : Nat) == 0)) = decide condition := by
  by_cases h : condition
  · rw [if_pos h, decide_eq_true h]
    rfl
  · rw [if_neg h, decide_eq_false h]
    rfl

end Evm

/-! ### Signed and exponent operations: Core side

Facts about the Core Word operations, kept outside the Core namespace. -/

namespace CoreWord

open Solcore.Core Solcore.Core.Word

theorem ofNatModulo_val (value : Nat) : (ofNatModulo value).val = value % 2 ^ 256 := rfl

theorem zero_val : zero.val = 0 := rfl

theorem maximum_val : maximum.val = 2 ^ 256 - 1 := rfl

theorem signedNegative_of_lt (value : Word) (small : value.val < 2 ^ 255) :
    value.signedNegative = false := by
  rw [signedNegative, decide_eq_false (Nat.not_le_of_lt small)]

theorem signedNegative_of_ge (value : Word) (large : ¬ value.val < 2 ^ 255) :
    value.signedNegative = true := by
  rw [signedNegative, decide_eq_true (Nat.le_of_not_lt large)]

theorem signedMagnitude_of_lt (value : Word) (small : value.val < 2 ^ 255) :
    value.signedMagnitude = value.val := by
  rw [signedMagnitude, signedNegative_of_lt value small, if_neg Bool.false_ne_true]

theorem signedMagnitude_of_ge (value : Word) (large : ¬ value.val < 2 ^ 255) :
    value.signedMagnitude = 2 ^ 256 - value.val := by
  rw [signedMagnitude, signedNegative_of_ge value large, if_pos rfl]
  rfl

theorem ofSignedMagnitude_false_val (magnitude : Nat) :
    (ofSignedMagnitude false magnitude).val = magnitude % 2 ^ 256 := rfl

theorem ofSignedMagnitude_true_val (magnitude : Nat) :
    (ofSignedMagnitude true magnitude).val = (2 ^ 256 - magnitude) % 2 ^ 256 := rfl

theorem shiftArithmeticRight_neg_val (value shift : Word) (small : shift.val < 256)
    (negative : ¬ value.val < 2 ^ 255) :
    (value.shiftArithmeticRight shift).val =
      (2 ^ 256 - 1 - (2 ^ 256 - 1 - value.val) / 2 ^ shift.val) % 2 ^ 256 := by
  rw [shiftArithmeticRight, if_pos small, if_neg negative]
  rfl

theorem signExtend_small_clear_val (index value : Word) (small : index.val < 32)
    (clear : value.val % 2 ^ (8 * (index.val + 1)) < 2 ^ (8 * (index.val + 1) - 1)) :
    (index.signExtend value).val = value.val % 2 ^ (8 * (index.val + 1)) % 2 ^ 256 := by
  rw [signExtend, if_pos small]
  dsimp only
  rw [if_pos clear]
  rfl

theorem signExtend_small_set_val (index value : Word) (small : index.val < 32)
    (set : ¬ value.val % 2 ^ (8 * (index.val + 1)) < 2 ^ (8 * (index.val + 1) - 1)) :
    (index.signExtend value).val =
      (2 ^ 256 - 2 ^ (8 * (index.val + 1)) + value.val % 2 ^ (8 * (index.val + 1))) %
        2 ^ 256 := by
  rw [signExtend, if_pos small]
  dsimp only
  rw [if_neg set]
  rfl

theorem signExtend_large (index value : Word) (large : ¬ index.val < 32) :
    index.signExtend value = value := by
  rw [signExtend, if_neg large]

theorem modularPowLoop_val (base accumulator exponent : Nat) :
    modularPowLoop base accumulator exponent = accumulator * base ^ exponent % 2 ^ 256 := by
  induction exponent using Nat.strongRecOn generalizing base accumulator with
  | ind exponent ih =>
    rw [modularPowLoop]
    have modulusEq : wordModulus = 2 ^ 256 := rfl
    by_cases zero : exponent = 0
    · rw [dif_pos zero, zero, Nat.pow_zero, Nat.mul_one, modulusEq]
    · rw [dif_neg zero]
      dsimp only
      rw [ih (exponent / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero zero) (by decide)),
        modulusEq]
      by_cases odd : exponent % 2 = 1
      · rw [if_pos odd, Nat.mul_mod, Nat.mod_mod, ← Nat.pow_mod, ← Nat.mul_mod,
          Nat.mul_pow]
        generalize split : exponent / 2 = half
        rw [(by omega : exponent = Nat.succ (half + half)), Nat.pow_succ base (half + half),
          Nat.pow_add base half half]
        ac_rfl
      · rw [if_neg odd, Nat.mul_mod, Nat.mod_mod, ← Nat.pow_mod, ← Nat.mul_mod,
          Nat.mul_pow]
        generalize split : exponent / 2 = half
        rw [(by omega : exponent = half + half), Nat.pow_add base half half]

end CoreWord

/-! ### Signed and exponent operations: agreement -/

open Solcore.Core in
theorem evm_sdiv (left right : Word) : Evm.sdiv left.val right.val = (left.sdiv right).val := by
  have leftBound : left.val < 2 ^ 256 := left.isLt
  have rightBound : right.val < 2 ^ 256 := right.isLt
  by_cases zero : right.val = 0
  · rw [Evm.sdiv, if_pos zero, Word.sdiv, if_pos zero, CoreWord.zero_val]
  · rw [Evm.sdiv, if_neg zero, Word.sdiv, if_neg zero]
    by_cases leftSmall : left.val < 2 ^ 255 <;> by_cases rightSmall : right.val < 2 ^ 255
    · rw [Evm.toSigned_of_lt _ leftSmall, Evm.toSigned_of_lt _ rightSmall, Evm.tdiv_cast_cast,
        Evm.ofSigned_cast _ (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) leftBound),
        CoreWord.signedNegative_of_lt _ leftSmall, CoreWord.signedNegative_of_lt _ rightSmall,
        CoreWord.signedMagnitude_of_lt _ leftSmall, CoreWord.signedMagnitude_of_lt _ rightSmall,
        Evm.bne_false_false, CoreWord.ofSignedMagnitude_false_val,
        Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) leftBound)]
    · rw [Evm.toSigned_of_lt _ leftSmall, Evm.toSigned_of_ge _ rightSmall rightBound,
        Evm.tdiv_cast_negSucc,
        (by omega : 2 ^ 256 - 1 - right.val + 1 = 2 ^ 256 - right.val),
        Evm.ofSigned_neg_cast _ (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) leftBound),
        CoreWord.signedNegative_of_lt _ leftSmall, CoreWord.signedNegative_of_ge _ rightSmall,
        CoreWord.signedMagnitude_of_lt _ leftSmall, CoreWord.signedMagnitude_of_ge _ rightSmall,
        Evm.bne_false_true, CoreWord.ofSignedMagnitude_true_val]
    · rw [Evm.toSigned_of_ge _ leftSmall leftBound, Evm.toSigned_of_lt _ rightSmall,
        Evm.tdiv_negSucc_cast,
        (by omega : 2 ^ 256 - 1 - left.val + 1 = 2 ^ 256 - left.val),
        Evm.ofSigned_neg_cast ((2 ^ 256 - left.val) / right.val)
          (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)),
        CoreWord.signedNegative_of_ge _ leftSmall, CoreWord.signedNegative_of_lt _ rightSmall,
        CoreWord.signedMagnitude_of_ge _ leftSmall, CoreWord.signedMagnitude_of_lt _ rightSmall,
        Evm.bne_true_false, CoreWord.ofSignedMagnitude_true_val]
    · rw [Evm.toSigned_of_ge _ leftSmall leftBound, Evm.toSigned_of_ge _ rightSmall rightBound,
        Evm.tdiv_negSucc_negSucc,
        (by omega : 2 ^ 256 - 1 - left.val + 1 = 2 ^ 256 - left.val),
        (by omega : 2 ^ 256 - 1 - right.val + 1 = 2 ^ 256 - right.val),
        Evm.ofSigned_cast ((2 ^ 256 - left.val) / (2 ^ 256 - right.val))
          (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)),
        CoreWord.signedNegative_of_ge _ leftSmall, CoreWord.signedNegative_of_ge _ rightSmall,
        CoreWord.signedMagnitude_of_ge _ leftSmall, CoreWord.signedMagnitude_of_ge _ rightSmall,
        Evm.bne_true_true, CoreWord.ofSignedMagnitude_false_val,
        Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _)
          (by omega : 2 ^ 256 - left.val < 2 ^ 256))]

open Solcore.Core in
theorem evm_smod (left right : Word) : Evm.smod left.val right.val = (left.smod right).val := by
  have leftBound : left.val < 2 ^ 256 := left.isLt
  have rightBound : right.val < 2 ^ 256 := right.isLt
  by_cases zero : right.val = 0
  · rw [Evm.smod, if_pos zero, Word.smod, if_pos zero, CoreWord.zero_val]
  · rw [Evm.smod, if_neg zero, Word.smod, if_neg zero]
    by_cases leftSmall : left.val < 2 ^ 255 <;> by_cases rightSmall : right.val < 2 ^ 255
    · rw [Evm.toSigned_of_lt _ leftSmall, Evm.toSigned_of_lt _ rightSmall, Evm.tmod_cast_cast,
        Evm.ofSigned_cast _ (Nat.lt_of_le_of_lt (Nat.mod_le _ _) leftBound),
        CoreWord.signedNegative_of_lt _ leftSmall, CoreWord.signedMagnitude_of_lt _ leftSmall,
        CoreWord.signedMagnitude_of_lt _ rightSmall, CoreWord.ofSignedMagnitude_false_val,
        Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) leftBound)]
    · rw [Evm.toSigned_of_lt _ leftSmall, Evm.toSigned_of_ge _ rightSmall rightBound,
        Evm.tmod_cast_negSucc,
        (by omega : 2 ^ 256 - 1 - right.val + 1 = 2 ^ 256 - right.val),
        Evm.ofSigned_cast _ (Nat.lt_of_le_of_lt (Nat.mod_le _ _) leftBound),
        CoreWord.signedNegative_of_lt _ leftSmall, CoreWord.signedMagnitude_of_lt _ leftSmall,
        CoreWord.signedMagnitude_of_ge _ rightSmall, CoreWord.ofSignedMagnitude_false_val,
        Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) leftBound)]
    · rw [Evm.toSigned_of_ge _ leftSmall leftBound, Evm.toSigned_of_lt _ rightSmall,
        Evm.tmod_negSucc_cast,
        (by omega : 2 ^ 256 - 1 - left.val + 1 = 2 ^ 256 - left.val),
        Evm.ofSigned_neg_cast ((2 ^ 256 - left.val) % right.val)
          (Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by omega)),
        CoreWord.signedNegative_of_ge _ leftSmall, CoreWord.signedMagnitude_of_ge _ leftSmall,
        CoreWord.signedMagnitude_of_lt _ rightSmall, CoreWord.ofSignedMagnitude_true_val]
    · rw [Evm.toSigned_of_ge _ leftSmall leftBound, Evm.toSigned_of_ge _ rightSmall rightBound,
        Evm.tmod_negSucc_negSucc,
        (by omega : 2 ^ 256 - 1 - left.val + 1 = 2 ^ 256 - left.val),
        (by omega : 2 ^ 256 - 1 - right.val + 1 = 2 ^ 256 - right.val),
        Evm.ofSigned_neg_cast ((2 ^ 256 - left.val) % (2 ^ 256 - right.val))
          (Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by omega)),
        CoreWord.signedNegative_of_ge _ leftSmall, CoreWord.signedMagnitude_of_ge _ leftSmall,
        CoreWord.signedMagnitude_of_ge _ rightSmall, CoreWord.ofSignedMagnitude_true_val]

open Solcore.Core in
theorem evm_sgt (left right : Word) :
    (!(Evm.sgt left.val right.val == 0)) = left.signedGt right := by
  have leftBound : left.val < 2 ^ 256 := left.isLt
  have rightBound : right.val < 2 ^ 256 := right.isLt
  rw [Evm.sgt, Evm.bnot_ite_beq_zero, Word.signedGt]
  by_cases leftSmall : left.val < 2 ^ 255 <;> by_cases rightSmall : right.val < 2 ^ 255
  · rw [Evm.toSigned_of_lt _ leftSmall, Evm.toSigned_of_lt _ rightSmall, if_pos leftSmall,
      if_pos rightSmall, decide_eq_decide]
    exact Int.ofNat_lt
  · rw [Evm.toSigned_of_lt _ leftSmall, Evm.toSigned_of_ge _ rightSmall rightBound,
      if_pos leftSmall, if_neg rightSmall, decide_eq_true_eq, Int.negSucc_eq]
    omega
  · rw [Evm.toSigned_of_ge _ leftSmall leftBound, Evm.toSigned_of_lt _ rightSmall,
      if_neg leftSmall, if_pos rightSmall, decide_eq_false_iff_not, Int.negSucc_eq]
    omega
  · rw [Evm.toSigned_of_ge _ leftSmall leftBound, Evm.toSigned_of_ge _ rightSmall rightBound,
      if_neg leftSmall, if_neg rightSmall, decide_eq_decide, Int.negSucc_eq, Int.negSucc_eq,
      gt_iff_lt, Fin.lt_def]
    constructor <;> intro h <;> omega

open Solcore.Core in
theorem evm_sar (value shift : Word) :
    Evm.sar shift.val value.val = (value.shiftArithmeticRight shift).val := by
  have valueBound : value.val < 2 ^ 256 := value.isLt
  by_cases small : shift.val < 256
  · by_cases nonnegative : value.val < 2 ^ 255
    · rw [Evm.sar, if_pos small, Evm.toSigned_of_lt _ nonnegative, Evm.cast_ediv_cast,
        Evm.ofSigned_cast _ (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) valueBound),
        Word.shiftArithmeticRight, if_pos small, if_pos nonnegative, CoreWord.ofNatModulo_val,
        Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) valueBound)]
    · rw [Evm.sar, if_pos small, Evm.toSigned_of_ge _ nonnegative valueBound,
        Evm.negSucc_ediv_cast _ _ (Nat.two_pow_pos _),
        Evm.ofSigned_negSucc ((2 ^ 256 - 1 - value.val) / 2 ^ shift.val)
          (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)),
        CoreWord.shiftArithmeticRight_neg_val value shift small nonnegative,
        Nat.mod_eq_of_lt
          (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (by omega : 2 ^ 256 - 1 < 2 ^ 256))]
  · by_cases nonnegative : value.val < 2 ^ 255
    · rw [Evm.sar, if_neg small, Evm.toSigned_of_lt _ nonnegative,
        if_neg (by omega : ¬ ((value.val : Nat) : Int) < 0),
        Word.shiftArithmeticRight, if_neg small, if_pos nonnegative, CoreWord.zero_val]
    · rw [Evm.sar, if_neg small, Evm.toSigned_of_ge _ nonnegative valueBound,
        if_pos (Int.negSucc_lt_zero _),
        Word.shiftArithmeticRight, if_neg small, if_neg nonnegative, CoreWord.maximum_val,
        Evm.modulus]

open Solcore.Core in
theorem evm_signextend (index value : Word) :
    Evm.signextend index.val value.val = (index.signExtend value).val := by
  have valueBound : value.val < 2 ^ 256 := value.isLt
  by_cases small : index.val < 31
  · have small32 : index.val < 32 := by omega
    have widthLe : 2 ^ (8 * (index.val + 1)) ≤ 2 ^ 248 :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have lowLt : value.val % 2 ^ (8 * (index.val + 1)) < 2 ^ (8 * (index.val + 1)) :=
      Nat.mod_lt _ (Nat.two_pow_pos _)
    rw [Evm.signextend, if_pos small]
    dsimp only
    by_cases clear : value.val % 2 ^ (8 * (index.val + 1)) < 2 ^ (8 * (index.val + 1) - 1)
    · rw [if_pos clear, CoreWord.signExtend_small_clear_val index value small32 clear,
        Nat.mod_eq_of_lt (by omega : value.val % 2 ^ (8 * (index.val + 1)) < 2 ^ 256)]
    · rw [if_neg clear, CoreWord.signExtend_small_set_val index value small32 clear, Evm.modulus]
      omega
  · by_cases small32 : index.val < 32
    · have index31 : index.val = 31 := by omega
      rw [Evm.signextend, if_neg small, Word.signExtend, if_pos small32]
      dsimp only
      rw [index31, (rfl : 8 * (31 + 1) = 256), (rfl : 256 - 1 = 255),
        Nat.mod_eq_of_lt valueBound]
      by_cases nonnegative : value.val < 2 ^ 255
      · rw [if_pos nonnegative, CoreWord.ofNatModulo_val, Nat.mod_eq_of_lt valueBound]
      · rw [if_neg nonnegative, CoreWord.ofNatModulo_val]
        have modulusEq : wordModulus = 2 ^ 256 := rfl
        omega
    · rw [Evm.signextend, if_neg small, CoreWord.signExtend_large index value small32]

theorem powMod_spec (base exponent : Nat) :
    Evm.powMod base exponent = base ^ exponent % Evm.modulus := by
  induction exponent using Nat.strongRecOn with
  | ind exponent ih =>
    rw [Evm.powMod]
    by_cases zero : exponent = 0
    · rw [dif_pos zero, zero, Nat.pow_zero]
    · rw [dif_neg zero]
      dsimp only
      rw [ih (exponent / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero zero) (by decide))]
      by_cases even : exponent % 2 = 0
      · rw [if_pos even, ← Nat.mul_mod, ← Nat.pow_add,
          (by omega : exponent / 2 + exponent / 2 = exponent)]
      · rw [if_neg even,
          ← Nat.mul_mod (base ^ (exponent / 2)) (base ^ (exponent / 2)) Evm.modulus,
          ← Nat.mul_mod, ← Nat.pow_add, ← Nat.pow_succ,
          (by omega : (exponent / 2 + exponent / 2).succ = exponent)]

open Solcore.Core in
theorem evm_exp (base exponent : Word) :
    Evm.exp base.val exponent.val = (base.pow exponent).val := by
  rw [Evm.exp, powMod_spec, Word.pow, CoreWord.ofNatModulo_val, CoreWord.modularPowLoop_val,
    Nat.one_mul, Nat.mod_mod]
  rfl

end Solcore.Synthesis.Source.ScalarMeaning
end

section
-- leanmerge: from Solcore.Synthesis.Source.ScalarMeaning.PrimitivePreservation
/-! Simulation lemmas for raw `std.opcodes` calls, generic over a renderer
that copies each opcode operand into a fresh `word` temporary first, and their
instance for the actual `PrimitiveRenderer.render`. The call context must
resolve every primitive alias to its opcode and `tobool` to the standard
library function; `PrimitiveContext` states exactly that. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

open Solcore.Synthesis.Core (Target functionAcceptsAt)
open Solcore.Synthesis.Source.ScalarRenderer (Rendered)

section Generic

variable {render : RenderFn} {admits : Context → Prop} {called : List String}

/-- A snapshot of a rendered Word operand is another rendering of it. -/
theorem snapshot_spec {expression : CoreExpr} {functions locals : List String}
    {indent first : Nat} {value : Rendered}
    (spec : RenderSpec admits called expression .word functions locals indent first value) :
    RenderSpec admits called expression .word functions locals indent first
      (snapshotOf indent value) := by
  obtain ⟨statements, lines, le, valueClassified, names, simulates⟩ := spec
  unfold RenderSpec snapshotOf
  dsimp only
  refine ⟨statements ++ [.letDecl (temporary value.nextId) .word (.name value.value)], ?_,
    by omega, Or.inr (allocated_temporary le (Nat.lt_succ_self _)), ?_, ?_⟩
  · simp only [Stmt.listLines_append, lines, Stmt.listLines, List.append_nil]
  · intro name mem
    simp only [Stmt.listIdentifiers_append, List.mem_append, Stmt.listIdentifiers,
      Stmt.identifiers, Expr.identifiers, List.append_nil, List.mem_cons,
      List.not_mem_nil, or_false] at mem
    rcases mem with mem | same | same
    · exact named_mono (names name mem) (Nat.le_refl _) (by omega)
    · exact named_allocated ⟨value.nextId, same, le, by omega⟩
    · subst same
      exact named_of_classified valueClassified (Nat.le_refl _) (by omega)
  · refine result_simulates (target := .word) (fun context environment store scope outer
      admitted agree lengthOk functionsOk => ?_) le
    obtain ⟨core, source, scope₁, outer₁, added₁, evaluates, represents, exec, lookup, keeps,
      shape, scopeNames, added⟩ :=
      simulates context environment store scope outer admitted agree lengthOk functionsOk
    exact ⟨core, source, scope₁, outer₁, added₁, evaluates, represents, exec, lookup, keeps,
      shape, scopeNames, added⟩

/-- A unary operation printed as one fresh temporary bound to `initializer`,
which reads the operand's value name. -/
theorem unaryResult_spec {op : Solcore.Core.Wire.UnaryOp} {operand : CoreExpr}
    {operandTarget target : Target} {functions locals : List String} {indent first : Nat}
    {value : Rendered} {initializer : Expr}
    (spec : RenderSpec admits called operand operandTarget functions locals indent first value)
    (initializerNames : ∀ name ∈ initializer.identifiers, name = value.value ∨ name ∈ called)
    (agree : ∀ (context : Context) (frames : Frames) (core : CoreValue) (source : Value),
      admits context → frames.lookup value.value = some source →
      Represents operandTarget core source →
      ∃ coreResult sourceResult,
        Solcore.Core.UnaryOp.apply op.toCore core = some coreResult ∧
        initializer.eval context frames = some sourceResult ∧
        Represents target coreResult sourceResult) :
    RenderSpec admits called (.unary op operand) target functions locals indent first
      (resultOf indent target value.lines value.nextId initializer) := by
  obtain ⟨statements, lines, le, valueClassified, names, simulates⟩ := spec
  unfold RenderSpec resultOf
  dsimp only
  refine ⟨statements ++ [.letDecl (temporary value.nextId) (LocalType.ofTarget target)
      initializer], ?_, by omega, Or.inr (allocated_temporary le (Nat.lt_succ_self _)), ?_, ?_⟩
  · simp only [Stmt.listLines_append, lines, Stmt.listLines, List.append_nil]
  · intro name mem
    simp only [Stmt.listIdentifiers_append, List.mem_append, Stmt.listIdentifiers,
      Stmt.identifiers, List.append_nil, List.mem_cons] at mem
    rcases mem with mem | same | mem
    · exact named_mono (names name mem) (Nat.le_refl _) (by omega)
    · exact named_allocated ⟨value.nextId, same, le, by omega⟩
    · rcases initializerNames name mem with same | mem
      · subst same
        exact named_of_classified valueClassified (Nat.le_refl _) (by omega)
      · exact Or.inr (Or.inr (Or.inr mem))
  · refine result_simulates (fun context environment store scope outer admitted agreeLocals
      lengthOk functionsOk => ?_) le
    obtain ⟨core, source, scope₁, outer₁, added₁, evaluates, represents, exec, lookup, keeps,
      shape, scopeNames, added⟩ :=
      simulates context environment store scope outer admitted agreeLocals lengthOk functionsOk
    obtain ⟨coreResult, sourceResult, coreApply, initialized, resultRepresents⟩ :=
      agree context _ core source admitted lookup represents
    refine ⟨coreResult, sourceResult, scope₁, outer₁, added₁, ?_, resultRepresents, exec,
      initialized, keeps, shape, scopeNames, added⟩
    simp only [Solcore.Core.Wire.Expr.toCore]
    exact .unary evaluates coreApply

/-- A binary operation printed as one fresh temporary bound to `initializer`,
which reads the two operands' value names. -/
theorem binaryResult_spec {op : Solcore.Core.Wire.BinaryOp} {left right : CoreExpr}
    {target : Target} {functions locals : List String} {indent first : Nat}
    {leftValue rightValue : Rendered} {initializer : Expr}
    (fresh : ∀ name ∈ locals, OlderThan first name)
    (leftSpec : RenderSpec admits called left .word functions locals indent first leftValue)
    (rightSpec : RenderSpec admits called right .word functions locals indent leftValue.nextId
      rightValue)
    (initializerNames : ∀ name ∈ initializer.identifiers,
      name = leftValue.value ∨ name = rightValue.value ∨ name ∈ called)
    (agree : ∀ (context : Context) (frames : Frames) (leftWord rightWord : Solcore.Core.Word),
      admits context → frames.lookup leftValue.value = some (.word leftWord.val) →
      frames.lookup rightValue.value = some (.word rightWord.val) →
      ∃ coreResult sourceResult,
        Solcore.Core.BinaryOp.apply op.toCore (.word leftWord) (.word rightWord) =
          some coreResult ∧
        initializer.eval context frames = some sourceResult ∧
        Represents target coreResult sourceResult) :
    RenderSpec admits called (.binary op left right) target functions locals indent first
      (resultOf indent target (leftValue.lines ++ rightValue.lines) rightValue.nextId
        initializer) := by
  obtain ⟨leftStatements, leftLines, leftLe, leftValueName, leftNames, leftSimulates⟩ :=
    leftSpec
  obtain ⟨rightStatements, rightLines, rightLe, rightValueName, rightNames, rightSimulates⟩ :=
    rightSpec
  unfold RenderSpec resultOf
  dsimp only
  refine ⟨leftStatements ++ rightStatements ++ [.letDecl (temporary rightValue.nextId)
      (LocalType.ofTarget target) initializer], ?_, by omega,
    Or.inr (allocated_temporary (by omega) (Nat.lt_succ_self _)), ?_, ?_⟩
  · simp only [Stmt.listLines_append, leftLines, rightLines, Stmt.listLines, List.append_nil]
  · intro name mem
    simp only [Stmt.listIdentifiers_append, List.mem_append, Stmt.listIdentifiers,
      Stmt.identifiers, List.append_nil, List.mem_cons] at mem
    rcases mem with (mem | mem) | same | mem
    · exact named_mono (leftNames name mem) (Nat.le_refl _) (by omega)
    · exact named_mono (rightNames name mem) leftLe (by omega)
    · exact named_allocated ⟨rightValue.nextId, same, by omega, by omega⟩
    · rcases initializerNames name mem with same | same | mem
      · subst same
        exact named_of_classified leftValueName (Nat.le_refl _) (by omega)
      · subst same
        exact named_of_classified rightValueName leftLe (by omega)
      · exact Or.inr (Or.inr (Or.inr mem))
  · refine result_simulates (fun context environment store scope outer admitted agreeLocals
      lengthOk functionsOk => ?_) (by omega)
    obtain ⟨leftCore, leftSource, scope₁, outer₁, added₁, leftEvaluates, leftRepresents,
      leftExec, leftLookup, leftKeeps, leftShape, leftScope, leftAdded⟩ :=
      leftSimulates context environment store scope outer admitted agreeLocals lengthOk
        functionsOk
    have rightAgree : LocalsAgree (scope₁ :: outer₁) locals environment :=
      agreeLocals.transfer fun name mem =>
        leftKeeps name (not_allocated_of_older (fresh name mem) (Nat.le_refl first))
    obtain ⟨rightCore, rightSource, scope₂, outer₂, added₂, rightEvaluates, rightRepresents,
      rightExec, rightLookup, rightKeeps, rightShape, rightScope, rightAdded⟩ :=
      rightSimulates context environment store scope₁ outer₁ admitted rightAgree lengthOk
        functionsOk
    obtain ⟨leftWord, rfl, rfl⟩ := leftRepresents
    obtain ⟨rightWord, rfl, rfl⟩ := rightRepresents
    have leftSurvives :
        Frames.lookup (scope₂ :: outer₂) leftValue.value = some (.word leftWord.val) := by
      rw [rightKeeps _ (value_not_reallocated fresh leftLe leftValueName)]
      exact leftLookup
    obtain ⟨coreResult, sourceResult, coreApply, initialized, resultRepresents⟩ :=
      agree context _ leftWord rightWord admitted leftSurvives rightLookup
    refine ⟨coreResult, sourceResult, scope₂, outer₂, added₂ ++ added₁, ?_, resultRepresents,
      ?_, initialized, ?_, rightShape.trans leftShape, ?_, ?_⟩
    · simp only [Solcore.Core.Wire.Expr.toCore]
      exact .binary leftEvaluates rightEvaluates coreApply
    · rw [Stmt.execList_append, leftExec]
      simpa using rightExec
    · intro name notAllocated
      rw [rightKeeps name fun allocated =>
          notAllocated (allocated_mono allocated leftLe (Nat.le_refl _)),
        leftKeeps name fun allocated =>
          notAllocated (allocated_mono allocated (Nat.le_refl _) rightLe)]
    · rw [rightScope, leftScope]
      simp
    · intro name mem
      rcases List.mem_append.mp mem with mem | mem
      · exact allocated_mono (rightAdded name mem) leftLe (Nat.le_refl _)
      · exact allocated_mono (leftAdded name mem) (Nat.le_refl _) rightLe

/-- A ternary operation printed as one fresh temporary bound to
`initializer`, which reads the three operands' value names. -/
theorem ternaryResult_spec {op : Solcore.Core.Wire.TernaryOp} {one two three : CoreExpr}
    {target : Target} {functions locals : List String} {indent first : Nat}
    {oneValue twoValue threeValue : Rendered} {initializer : Expr}
    (fresh : ∀ name ∈ locals, OlderThan first name)
    (oneSpec : RenderSpec admits called one .word functions locals indent first oneValue)
    (twoSpec : RenderSpec admits called two .word functions locals indent oneValue.nextId
      twoValue)
    (threeSpec : RenderSpec admits called three .word functions locals indent twoValue.nextId
      threeValue)
    (initializerNames : ∀ name ∈ initializer.identifiers,
      name = oneValue.value ∨ name = twoValue.value ∨ name = threeValue.value ∨ name ∈ called)
    (agree : ∀ (context : Context) (frames : Frames)
      (oneWord twoWord threeWord : Solcore.Core.Word),
      admits context → frames.lookup oneValue.value = some (.word oneWord.val) →
      frames.lookup twoValue.value = some (.word twoWord.val) →
      frames.lookup threeValue.value = some (.word threeWord.val) →
      ∃ coreResult sourceResult,
        Solcore.Core.TernaryOp.apply op.toCore (.word oneWord) (.word twoWord)
          (.word threeWord) = some coreResult ∧
        initializer.eval context frames = some sourceResult ∧
        Represents target coreResult sourceResult) :
    RenderSpec admits called (.ternary op one two three) target functions locals indent first
      (resultOf indent target (oneValue.lines ++ twoValue.lines ++ threeValue.lines)
        threeValue.nextId initializer) := by
  obtain ⟨oneStatements, oneLines, oneLe, oneName, oneNames, oneSimulates⟩ := oneSpec
  obtain ⟨twoStatements, twoLines, twoLe, twoName, twoNames, twoSimulates⟩ := twoSpec
  obtain ⟨threeStatements, threeLines, threeLe, threeName, threeNames, threeSimulates⟩ :=
    threeSpec
  unfold RenderSpec resultOf
  dsimp only
  refine ⟨oneStatements ++ twoStatements ++ threeStatements ++
      [.letDecl (temporary threeValue.nextId) (LocalType.ofTarget target) initializer], ?_,
    by omega, Or.inr (allocated_temporary (by omega) (Nat.lt_succ_self _)), ?_, ?_⟩
  · simp only [Stmt.listLines_append, oneLines, twoLines, threeLines, Stmt.listLines,
      List.append_nil]
  · intro name mem
    simp only [Stmt.listIdentifiers_append, List.mem_append, Stmt.listIdentifiers,
      Stmt.identifiers, List.append_nil, List.mem_cons] at mem
    rcases mem with ((mem | mem) | mem) | same | mem
    · exact named_mono (oneNames name mem) (Nat.le_refl _) (by omega)
    · exact named_mono (twoNames name mem) oneLe (by omega)
    · exact named_mono (threeNames name mem) (by omega) (by omega)
    · exact named_allocated ⟨threeValue.nextId, same, by omega, by omega⟩
    · rcases initializerNames name mem with same | same | same | mem
      · subst same
        exact named_of_classified oneName (Nat.le_refl _) (by omega)
      · subst same
        exact named_of_classified twoName oneLe (by omega)
      · subst same
        exact named_of_classified threeName (by omega) (by omega)
      · exact Or.inr (Or.inr (Or.inr mem))
  · refine result_simulates (fun context environment store scope outer admitted agreeLocals
      lengthOk functionsOk => ?_) (by omega)
    obtain ⟨oneCore, oneSource, scope₁, outer₁, added₁, oneEvaluates, oneRepresents,
      oneExec, oneLookup, oneKeeps, oneShape, oneScope, oneAdded⟩ :=
      oneSimulates context environment store scope outer admitted agreeLocals lengthOk
        functionsOk
    have twoAgree : LocalsAgree (scope₁ :: outer₁) locals environment :=
      agreeLocals.transfer fun name mem =>
        oneKeeps name (not_allocated_of_older (fresh name mem) (Nat.le_refl first))
    obtain ⟨twoCore, twoSource, scope₂, outer₂, added₂, twoEvaluates, twoRepresents,
      twoExec, twoLookup, twoKeeps, twoShape, twoScope, twoAdded⟩ :=
      twoSimulates context environment store scope₁ outer₁ admitted twoAgree lengthOk
        functionsOk
    have threeAgree : LocalsAgree (scope₂ :: outer₂) locals environment :=
      twoAgree.transfer fun name mem =>
        twoKeeps name (not_allocated_of_older (fresh name mem) oneLe)
    obtain ⟨threeCore, threeSource, scope₃, outer₃, added₃, threeEvaluates, threeRepresents,
      threeExec, threeLookup, threeKeeps, threeShape, threeScope, threeAdded⟩ :=
      threeSimulates context environment store scope₂ outer₂ admitted threeAgree lengthOk
        functionsOk
    obtain ⟨oneWord, rfl, rfl⟩ := oneRepresents
    obtain ⟨twoWord, rfl, rfl⟩ := twoRepresents
    obtain ⟨threeWord, rfl, rfl⟩ := threeRepresents
    have oneSurvives :
        Frames.lookup (scope₃ :: outer₃) oneValue.value = some (.word oneWord.val) := by
      rw [threeKeeps _ (value_not_reallocated fresh (by omega)
          (classified_mono oneName (Nat.le_refl _) twoLe)),
        twoKeeps _ (value_not_reallocated fresh oneLe oneName)]
      exact oneLookup
    have twoSurvives :
        Frames.lookup (scope₃ :: outer₃) twoValue.value = some (.word twoWord.val) := by
      rw [threeKeeps _ (value_not_reallocated (fun name mem => older_mono (fresh name mem) oneLe)
        twoLe twoName)]
      exact twoLookup
    obtain ⟨coreResult, sourceResult, coreApply, initialized, resultRepresents⟩ :=
      agree context _ oneWord twoWord threeWord admitted oneSurvives twoSurvives threeLookup
    refine ⟨coreResult, sourceResult, scope₃, outer₃, added₃ ++ added₂ ++ added₁, ?_,
      resultRepresents, ?_, initialized, ?_, threeShape.trans (twoShape.trans oneShape), ?_, ?_⟩
    · simp only [Solcore.Core.Wire.Expr.toCore]
      exact .ternary oneEvaluates twoEvaluates threeEvaluates coreApply
    · rw [Stmt.execList_append, Stmt.execList_append, oneExec]
      simpa [twoExec] using threeExec
    · intro name notAllocated
      rw [threeKeeps name fun allocated =>
          notAllocated (allocated_mono allocated (by omega) (Nat.le_refl _)),
        twoKeeps name fun allocated =>
          notAllocated (allocated_mono allocated oneLe (by omega)),
        oneKeeps name fun allocated =>
          notAllocated (allocated_mono allocated (Nat.le_refl _) (by omega))]
    · rw [threeScope, twoScope, oneScope]
      simp
    · intro name mem
      simp only [List.mem_append] at mem
      rcases mem with (mem | mem) | mem
      · exact allocated_mono (threeAdded name mem) (by omega) (Nat.le_refl _)
      · exact allocated_mono (twoAdded name mem) oneLe (by omega)
      · exact allocated_mono (oneAdded name mem) (Nat.le_refl _) (by omega)

/-! ### How a renderer prints raw opcode calls -/

def ClzInversion (render : RenderFn) : Prop :=
  ∀ (functions : List String) (target : Target) (locals : List String) (indent first : Nat)
    (operand : CoreExpr) (rendered : Rendered),
    render functions target locals indent first (.unary .wordClz operand) = .ok rendered →
    ∃ value, render functions .word locals indent first operand = .ok value ∧
      rendered = resultOf indent target (snapshotOf indent value).lines (value.nextId + 1)
        (.call1 "sc_clz" (.name (temporary value.nextId)))

def PrimitiveBinaryInversion (render : RenderFn) : Prop :=
  ∀ (functions : List String) (target : Target) (locals : List String) (indent first : Nat)
    (op : Solcore.Core.Wire.BinaryOp) (build : String → String → Expr) (left right : CoreExpr)
    (rendered : Rendered),
    primitiveBinary? op = some build →
    render functions target locals indent first (.binary op left right) = .ok rendered →
    ∃ leftValue rightValue, render functions .word locals indent first left = .ok leftValue ∧
      render functions .word locals indent (leftValue.nextId + 1) right = .ok rightValue ∧
      rendered = resultOf indent target
        ((snapshotOf indent leftValue).lines ++ (snapshotOf indent rightValue).lines)
        (rightValue.nextId + 1) (build (temporary leftValue.nextId) (temporary rightValue.nextId))

def TernaryInversion (render : RenderFn) : Prop :=
  ∀ (functions : List String) (target : Target) (locals : List String) (indent first : Nat)
    (op : Solcore.Core.Wire.TernaryOp) (one two three : CoreExpr) (rendered : Rendered),
    render functions target locals indent first (.ternary op one two three) = .ok rendered →
    ∃ oneValue twoValue threeValue,
      render functions .word locals indent first one = .ok oneValue ∧
      render functions .word locals indent (oneValue.nextId + 1) two = .ok twoValue ∧
      render functions .word locals indent (twoValue.nextId + 1) three = .ok threeValue ∧
      rendered = resultOf indent target
        ((snapshotOf indent oneValue).lines ++ (snapshotOf indent twoValue).lines ++
          (snapshotOf indent threeValue).lines)
        (threeValue.nextId + 1)
        (.call3 (ternaryCallee op) (.name (temporary oneValue.nextId))
          (.name (temporary twoValue.nextId)) (.name (temporary threeValue.nextId)))

theorem snapshot_le {expression : CoreExpr} {functions locals : List String}
    {indent first : Nat} {value : Rendered}
    (spec : RenderSpec admits called expression .word functions locals indent first
      (snapshotOf indent value)) : first ≤ value.nextId + 1 := by
  obtain ⟨_, _, le, _⟩ := spec
  exact le

theorem renderIH_clz (inversion : ClzInversion render) (calls : "sc_clz" ∈ called)
    (reaches : ∀ context, admits context → ∀ arguments,
      context.call "sc_clz" arguments = opcodeMeaning "clz" arguments)
    {operand : CoreExpr} (operandIH : RenderIH render admits called operand) :
    RenderIH render admits called (.unary .wordClz operand) := by
  intro functions depth prior target locals indent first rendered accepted equation fresh
  simp only [functionAcceptsAt, Target.unaryResult, Target.unaryOperand, Bool.and_eq_true,
    target_beq_iff] at accepted
  obtain ⟨rfl, operandAccepted⟩ := accepted
  obtain ⟨value, valueEquation, rfl⟩ :=
    inversion functions .word locals indent first operand rendered equation
  refine unaryResult_spec (op := .wordClz) (snapshot_spec (operandIH functions depth prior .word
    locals indent first value operandAccepted valueEquation fresh)) ?_ ?_
  · intro name mem
    simp only [Expr.identifiers, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with same | same
    · exact Or.inr (same ▸ calls)
    · exact Or.inl same
  · intro context frames core source admitted lookup represents
    obtain ⟨word, rfl, rfl⟩ := represents
    refine ⟨.word word.clz, .word (Evm.clz word.val), rfl, ?_, word.clz, rfl, by rw [evm_clz]⟩
    simp only [snapshotOf] at lookup
    simp [Expr.eval, lookup, reaches context admitted, opcodeMeaning]

theorem acceptsAt_primitiveBinary {depth prior : Nat} {target : Target}
    {op : Solcore.Core.Wire.BinaryOp} {build : String → String → Expr} {left right : CoreExpr}
    (selected : primitiveBinary? op = some build)
    (accepted : functionAcceptsAt depth prior target (.binary op left right) = true) :
    target = Target.binaryResult op ∧ functionAcceptsAt depth prior .word left = true ∧
      functionAcceptsAt depth prior .word right = true := by
  cases op <;> simp only [primitiveBinary?, reduceCtorEq] at selected <;>
    simp only [functionAcceptsAt, Bool.and_eq_true, target_beq_iff] at accepted <;>
    exact ⟨accepted.1.1, accepted.1.2, accepted.2⟩

theorem renderIH_primitiveBinary (inversion : PrimitiveBinaryInversion render)
    {op : Solcore.Core.Wire.BinaryOp} {build : String → String → Expr}
    (selected : primitiveBinary? op = some build)
    (buildNames : ∀ leftName rightName, ∀ name ∈ (build leftName rightName).identifiers,
      name = leftName ∨ name = rightName ∨ name ∈ called)
    (agree : ∀ (context : Context) (frames : Frames) (leftName rightName : String)
      (left right : Solcore.Core.Word), admits context →
      frames.lookup leftName = some (.word left.val) →
      frames.lookup rightName = some (.word right.val) →
      ∃ coreResult sourceResult,
        Solcore.Core.BinaryOp.apply op.toCore (.word left) (.word right) = some coreResult ∧
        (build leftName rightName).eval context frames = some sourceResult ∧
        Represents (Target.binaryResult op) coreResult sourceResult)
    {left right : CoreExpr} (leftIH : RenderIH render admits called left)
    (rightIH : RenderIH render admits called right) :
    RenderIH render admits called (.binary op left right) := by
  intro functions depth prior target locals indent first rendered accepted equation fresh
  obtain ⟨targetEq, leftAccepted, rightAccepted⟩ := acceptsAt_primitiveBinary selected accepted
  subst targetEq
  obtain ⟨leftValue, rightValue, leftEquation, rightEquation, rfl⟩ :=
    inversion functions _ locals indent first op build left right rendered selected equation
  have leftSpec := snapshot_spec (leftIH functions depth prior .word locals indent first
    leftValue leftAccepted leftEquation fresh)
  have rightSpec := snapshot_spec (rightIH functions depth prior .word locals indent
    (leftValue.nextId + 1) rightValue rightAccepted rightEquation
    (fun name mem => older_mono (fresh name mem) (snapshot_le leftSpec)))
  exact binaryResult_spec fresh leftSpec rightSpec
    (buildNames (temporary leftValue.nextId) (temporary rightValue.nextId))
    (fun context frames leftWord rightWord admitted leftLookup rightLookup =>
      agree context frames _ _ leftWord rightWord admitted leftLookup rightLookup)

theorem renderIH_ternary (inversion : TernaryInversion render)
    {op : Solcore.Core.Wire.TernaryOp} (calls : ternaryCallee op ∈ called)
    (agree : ∀ (context : Context) (frames : Frames) (oneName twoName threeName : String)
      (one two three : Solcore.Core.Word), admits context →
      frames.lookup oneName = some (.word one.val) →
      frames.lookup twoName = some (.word two.val) →
      frames.lookup threeName = some (.word three.val) →
      ∃ coreResult sourceResult,
        Solcore.Core.TernaryOp.apply op.toCore (.word one) (.word two) (.word three) =
          some coreResult ∧
        (Expr.call3 (ternaryCallee op) (.name oneName) (.name twoName) (.name threeName)).eval
          context frames = some sourceResult ∧
        Represents .word coreResult sourceResult)
    {one two three : CoreExpr} (oneIH : RenderIH render admits called one)
    (twoIH : RenderIH render admits called two) (threeIH : RenderIH render admits called three) :
    RenderIH render admits called (.ternary op one two three) := by
  intro functions depth prior target locals indent first rendered accepted equation fresh
  simp only [functionAcceptsAt, Bool.and_eq_true, target_beq_iff] at accepted
  obtain ⟨⟨⟨rfl, oneAccepted⟩, twoAccepted⟩, threeAccepted⟩ := accepted
  obtain ⟨oneValue, twoValue, threeValue, oneEquation, twoEquation, threeEquation, rfl⟩ :=
    inversion functions .word locals indent first op one two three rendered equation
  have oneSpec := snapshot_spec (oneIH functions depth prior .word locals indent first
    oneValue oneAccepted oneEquation fresh)
  have twoSpec := snapshot_spec (twoIH functions depth prior .word locals indent
    (oneValue.nextId + 1) twoValue twoAccepted twoEquation
    (fun name mem => older_mono (fresh name mem) (snapshot_le oneSpec)))
  have threeSpec := snapshot_spec (threeIH functions depth prior .word locals indent
    (twoValue.nextId + 1) threeValue threeAccepted threeEquation
    (fun name mem => older_mono (fresh name mem)
      (Nat.le_trans (snapshot_le oneSpec) (snapshot_le twoSpec))))
  refine ternaryResult_spec fresh oneSpec twoSpec threeSpec ?_
    (fun context frames oneWord twoWord threeWord admitted oneLookup twoLookup threeLookup =>
      agree context frames _ _ _ oneWord twoWord threeWord admitted oneLookup twoLookup
        threeLookup)
  intro name mem
  simp only [Expr.identifiers, List.mem_cons, List.mem_append, List.not_mem_nil,
    or_false] at mem
  rcases mem with same | (same | same) | same
  · exact Or.inr (Or.inr (Or.inr (same ▸ calls)))
  · exact Or.inl same
  · exact Or.inr (Or.inl same)
  · exact Or.inr (Or.inr (Or.inl same))

end Generic

/-! ### The actual primitive renderer -/

/-- The primitive renderer with the helper list of the shared signature,
which it does not use. -/
def primitiveRender (_ : List String) (target : Target) (locals : List String)
    (indent first : Nat) (expression : CoreExpr) : Except EmitError Rendered :=
  PrimitiveRenderer.render target locals indent first expression

theorem primitive_word : WordInversion primitiveRender := by
  intro functions target locals indent first value rendered equation
  rw [primitiveRender, PrimitiveEquations.word] at equation
  exact (Except.ok.inj equation).symm

theorem primitive_bool : BoolInversion primitiveRender := by
  intro functions target locals indent first value rendered equation
  rw [primitiveRender, PrimitiveEquations.bool] at equation
  exact (Except.ok.inj equation).symm

theorem primitive_var : VarInversion primitiveRender := by
  intro functions target locals indent first index rendered equation
  rw [primitiveRender, PrimitiveEquations.var] at equation
  cases found : locals[index]? with
  | none =>
      rw [found] at equation
      cases equation
  | some binding =>
      rw [found] at equation
      exact ⟨binding, rfl, (Except.ok.inj equation).symm⟩

theorem primitive_letE : LetInversion primitiveRender := by
  intro functions target locals indent first initializer body rendered equation
  rw [primitiveRender, PrimitiveEquations.letE] at equation
  obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨rest, restEquation, equation⟩ := except_bind_eq_ok equation
  exact ⟨value, rest, valueEquation, restEquation, (Except.ok.inj equation).symm⟩

theorem primitive_ifE : IfInversion primitiveRender := by
  intro functions target locals indent first condition yes no rendered equation
  rw [primitiveRender, PrimitiveEquations.ifE] at equation
  obtain ⟨tested, testedEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨selected, selectedEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨fallback, fallbackEquation, equation⟩ := except_bind_eq_ok equation
  exact ⟨tested, selected, fallback, testedEquation, selectedEquation, fallbackEquation,
    (Except.ok.inj equation).symm⟩

theorem primitive_unary : UnaryInversion primitiveRender := by
  intro functions target locals indent first op sourceOp operand rendered selected equation
  rw [primitiveRender, PrimitiveEquations.unary target locals indent first op sourceOp operand
    selected] at equation
  obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
  exact ⟨value, valueEquation, (Except.ok.inj equation).symm⟩

theorem primitive_binary : BinaryInversion primitiveRender := by
  intro functions target locals indent first op sourceOp left right rendered selected equation
  rw [primitiveRender, PrimitiveEquations.binary target locals indent first op sourceOp left
    right selected] at equation
  obtain ⟨leftValue, leftEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨rightValue, rightEquation, equation⟩ := except_bind_eq_ok equation
  exact ⟨leftValue, rightValue, leftEquation, rightEquation, (Except.ok.inj equation).symm⟩

theorem primitive_clz : ClzInversion primitiveRender := by
  intro functions target locals indent first operand rendered equation
  rw [primitiveRender, PrimitiveEquations.clz] at equation
  obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
  exact ⟨value, valueEquation, (Except.ok.inj equation).symm⟩

theorem primitive_primitiveBinary : PrimitiveBinaryInversion primitiveRender := by
  intro functions target locals indent first op build left right rendered selected equation
  rw [primitiveRender, PrimitiveEquations.binary_primitive target locals indent first op build
    left right selected] at equation
  obtain ⟨leftValue, leftEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨rightValue, rightEquation, equation⟩ := except_bind_eq_ok equation
  exact ⟨leftValue, rightValue, leftEquation, rightEquation, (Except.ok.inj equation).symm⟩

theorem primitive_ternary : TernaryInversion primitiveRender := by
  intro functions target locals indent first op one two three rendered equation
  rw [primitiveRender, PrimitiveEquations.ternary] at equation
  obtain ⟨oneValue, oneEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨twoValue, twoEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨threeValue, threeEquation, equation⟩ := except_bind_eq_ok equation
  exact ⟨oneValue, twoValue, threeValue, oneEquation, twoEquation, threeEquation,
    (Except.ok.inj equation).symm⟩

/-! ### Calls reaching the raw opcodes -/

/-- A call context in which every primitive alias reaches its `std.opcodes`
instruction and `tobool` is the standard library function. -/
def PrimitiveContext (context : Context) : Prop :=
  (∀ alias ∈ primitiveAliases, ∀ arguments,
      context.call alias.2 arguments = opcodeMeaning alias.1 arguments) ∧
    ∀ arguments, context.call "tobool" arguments = builtinMeaning "tobool" arguments

/-- The callees the primitive renderers print. -/
def primitiveCallees : List String := "tobool" :: primitiveAliases.map Prod.snd

theorem PrimitiveContext.reaches {context : Context} (admitted : PrimitiveContext context)
    {opcode alias : String} (mem : (opcode, alias) ∈ primitiveAliases)
    (arguments : List Value) : context.call alias arguments = opcodeMeaning opcode arguments :=
  admitted.1 (opcode, alias) mem arguments

theorem primitiveBinary_agree {op : Solcore.Core.Wire.BinaryOp}
    {build : String → String → Expr} (selected : primitiveBinary? op = some build)
    (context : Context) (frames : Frames) (leftName rightName : String)
    (left right : Solcore.Core.Word) (admitted : PrimitiveContext context)
    (leftLookup : frames.lookup leftName = some (.word left.val))
    (rightLookup : frames.lookup rightName = some (.word right.val)) :
    ∃ coreResult sourceResult,
      Solcore.Core.BinaryOp.apply op.toCore (.word left) (.word right) = some coreResult ∧
      (build leftName rightName).eval context frames = some sourceResult ∧
      Represents (Target.binaryResult op) coreResult sourceResult := by
  cases op <;> simp only [primitiveBinary?, reduceCtorEq, Option.some.injEq] at selected <;>
    subst selected
  case wordDiv =>
    refine ⟨.word (left.udiv right), .word (Evm.div left.val right.val), rfl, ?_,
      left.udiv right, rfl, by rw [evm_div]⟩
    simp [Expr.eval, leftLookup, rightLookup,
      admitted.reaches (opcode := "div") (alias := "sc_div") (by decide), opcodeMeaning]
  case wordMod =>
    refine ⟨.word (left.umod right), .word (Evm.mod left.val right.val), rfl, ?_,
      left.umod right, rfl, by rw [evm_mod]⟩
    simp [Expr.eval, leftLookup, rightLookup,
      admitted.reaches (opcode := "mod") (alias := "sc_mod") (by decide), opcodeMeaning]
  case wordShl =>
    refine ⟨.word (left.shiftLeft right), .word (Evm.shl right.val left.val), rfl, ?_,
      left.shiftLeft right, rfl, by rw [evm_shl]⟩
    simp [Expr.eval, leftLookup, rightLookup,
      admitted.reaches (opcode := "shl") (alias := "sc_shl") (by decide), opcodeMeaning]
  case wordShr =>
    refine ⟨.word (left.shiftRight right), .word (Evm.shr right.val left.val), rfl, ?_,
      left.shiftRight right, rfl, by rw [evm_shr]⟩
    simp [Expr.eval, leftLookup, rightLookup,
      admitted.reaches (opcode := "shr") (alias := "sc_shr") (by decide), opcodeMeaning]
  case wordSar =>
    refine ⟨.word (left.shiftArithmeticRight right), .word (Evm.sar right.val left.val), rfl,
      ?_, left.shiftArithmeticRight right, rfl, by rw [evm_sar]⟩
    simp [Expr.eval, leftLookup, rightLookup,
      admitted.reaches (opcode := "sar") (alias := "sc_sar") (by decide), opcodeMeaning]
  case wordSdiv =>
    refine ⟨.word (left.sdiv right), .word (Evm.sdiv left.val right.val), rfl, ?_,
      left.sdiv right, rfl, by rw [evm_sdiv]⟩
    simp [Expr.eval, leftLookup, rightLookup,
      admitted.reaches (opcode := "sdiv") (alias := "sc_sdiv") (by decide), opcodeMeaning]
  case wordSmod =>
    refine ⟨.word (left.smod right), .word (Evm.smod left.val right.val), rfl, ?_,
      left.smod right, rfl, by rw [evm_smod]⟩
    simp [Expr.eval, leftLookup, rightLookup,
      admitted.reaches (opcode := "smod") (alias := "sc_smod") (by decide), opcodeMeaning]
  case wordSgt =>
    refine ⟨.bool (left.signedGt right), .bool (toBool (Evm.sgt left.val right.val)), rfl, ?_,
      left.signedGt right, rfl, congrArg Value.bool (evm_sgt left right)⟩
    simp [Expr.eval, leftLookup, rightLookup,
      admitted.reaches (opcode := "sgt") (alias := "sc_sgt") (by decide), opcodeMeaning,
      admitted.2, builtinMeaning]
  case wordByte =>
    refine ⟨.word (left.byteAt right), .word (Evm.byte left.val right.val), rfl, ?_,
      left.byteAt right, rfl, by rw [evm_byte]⟩
    simp [Expr.eval, leftLookup, rightLookup,
      admitted.reaches (opcode := "byte") (alias := "sc_byte") (by decide), opcodeMeaning]
  case wordPow =>
    refine ⟨.word (left.pow right), .word (Evm.exp left.val right.val), rfl, ?_,
      left.pow right, rfl, by rw [evm_exp]⟩
    simp [Expr.eval, leftLookup, rightLookup,
      admitted.reaches (opcode := "exp") (alias := "sc_exp") (by decide), opcodeMeaning]
  case wordSignExtend =>
    refine ⟨.word (left.signExtend right), .word (Evm.signextend left.val right.val), rfl, ?_,
      left.signExtend right, rfl, by rw [evm_signextend]⟩
    simp [Expr.eval, leftLookup, rightLookup,
      admitted.reaches (opcode := "signextend") (alias := "sc_signextend") (by decide),
      opcodeMeaning]

theorem ternary_agree (op : Solcore.Core.Wire.TernaryOp) (context : Context)
    (frames : Frames) (oneName twoName threeName : String) (one two three : Solcore.Core.Word)
    (admitted : PrimitiveContext context)
    (oneLookup : frames.lookup oneName = some (.word one.val))
    (twoLookup : frames.lookup twoName = some (.word two.val))
    (threeLookup : frames.lookup threeName = some (.word three.val)) :
    ∃ coreResult sourceResult,
      Solcore.Core.TernaryOp.apply op.toCore (.word one) (.word two) (.word three) =
        some coreResult ∧
      (Expr.call3 (ternaryCallee op) (.name oneName) (.name twoName) (.name threeName)).eval
        context frames = some sourceResult ∧
      Represents .word coreResult sourceResult := by
  cases op
  case wordAddMod =>
    refine ⟨.word (one.addMod two three), .word (Evm.addmod one.val two.val three.val), rfl, ?_,
      one.addMod two three, rfl, by rw [evm_addmod]⟩
    simp [Expr.eval, oneLookup, twoLookup, threeLookup, ternaryCallee,
      admitted.reaches (opcode := "addmod") (alias := "sc_addmod") (by decide), opcodeMeaning]
  case wordMulMod =>
    refine ⟨.word (one.mulMod two three), .word (Evm.mulmod one.val two.val three.val), rfl, ?_,
      one.mulMod two three, rfl, by rw [evm_mulmod]⟩
    simp [Expr.eval, oneLookup, twoLookup, threeLookup, ternaryCallee,
      admitted.reaches (opcode := "mulmod") (alias := "sc_mulmod") (by decide), opcodeMeaning]

theorem primitiveBinary_names {op : Solcore.Core.Wire.BinaryOp}
    {build : String → String → Expr} (selected : primitiveBinary? op = some build)
    (leftName rightName : String) :
    ∀ name ∈ (build leftName rightName).identifiers,
      name = leftName ∨ name = rightName ∨ name ∈ primitiveCallees := by
  intro name mem
  cases op <;> simp only [primitiveBinary?, reduceCtorEq, Option.some.injEq] at selected <;>
    subst selected <;>
    simp only [Expr.identifiers, List.mem_cons, List.mem_append, List.not_mem_nil,
      or_false] at mem <;>
    rcases mem with rfl | rfl | rfl | rfl <;> simp [primitiveCallees, primitiveAliases]

theorem primitive_unary_spec {op : Solcore.Core.Wire.UnaryOp} {operand : CoreExpr}
    (operandIH : RenderIH primitiveRender PrimitiveContext primitiveCallees operand) :
    RenderIH primitiveRender PrimitiveContext primitiveCallees (.unary op operand) := by
  cases selected : sourceUnary? op with
  | some _ => exact renderIH_unary primitive_unary selected operandIH
  | none =>
      cases op
      case boolNot => simp [sourceUnary?] at selected
      case wordNot => simp [sourceUnary?] at selected
      case wordClz =>
        exact renderIH_clz primitive_clz (by decide)
          (fun _ admitted => admitted.reaches (by decide)) operandIH
      all_goals
        refine renderIH_error _ fun functions target locals indent first rendered equation => ?_
        rw [primitiveRender, PrimitiveEquations.unary_unsupported _ _ _ _ _ _ rfl] at equation
        cases equation

theorem primitive_binary_spec {op : Solcore.Core.Wire.BinaryOp} {left right : CoreExpr}
    (leftIH : RenderIH primitiveRender PrimitiveContext primitiveCallees left)
    (rightIH : RenderIH primitiveRender PrimitiveContext primitiveCallees right) :
    RenderIH primitiveRender PrimitiveContext primitiveCallees (.binary op left right) := by
  cases selected : sourceBinary? op with
  | some _ => exact renderIH_binary primitive_binary selected leftIH rightIH
  | none =>
      cases extended : primitiveBinary? op with
      | some build =>
          exact renderIH_primitiveBinary primitive_primitiveBinary extended
            (primitiveBinary_names extended)
            (fun context frames leftName rightName leftWord rightWord admitted =>
              primitiveBinary_agree extended context frames leftName rightName leftWord
                rightWord admitted)
            leftIH rightIH
      | none =>
          refine renderIH_error _ fun functions target locals indent first rendered equation => ?_
          have unsupported : PrimitiveRenderer.supportedBinary op = false := by
            cases op <;> simp_all [sourceBinary?, primitiveBinary?,
              PrimitiveRenderer.supportedBinary, Source.supportedBinary]
          rw [primitiveRender, PrimitiveEquations.binary_unsupported _ _ _ _ _ _ _ unsupported]
            at equation
          cases equation

/-- Every admitted expression that the actual primitive renderer accepts
satisfies its rendering specification in every primitive call context. -/
theorem primitive_render_spec :
    (expression : CoreExpr) →
      RenderIH primitiveRender PrimitiveContext primitiveCallees expression
  | .word value => renderIH_word primitive_word value
  | .bool value => renderIH_bool primitive_bool value
  | .var index => renderIH_var primitive_var index
  | .letE initializer body =>
      renderIH_letE primitive_letE (primitive_render_spec initializer)
        (primitive_render_spec body)
  | .ifE condition yes no =>
      renderIH_ifE primitive_ifE (primitive_render_spec condition) (primitive_render_spec yes)
        (primitive_render_spec no)
  | .unary _ operand => primitive_unary_spec (primitive_render_spec operand)
  | .binary _ left right =>
      primitive_binary_spec (primitive_render_spec left) (primitive_render_spec right)
  | .ternary op one two three =>
      renderIH_ternary primitive_ternary (by cases op <;> decide)
        (fun context frames oneName twoName threeName oneWord twoWord threeWord admitted =>
          ternary_agree op context frames oneName twoName threeName oneWord twoWord threeWord
            admitted)
        (primitive_render_spec one) (primitive_render_spec two) (primitive_render_spec three)
  | .apply _ _ =>
      renderIH_error _ fun _ _ _ _ _ _ equation => by
        rw [primitiveRender] at equation
        cases equation
  | .unit => renderIH_rejected _ fun _ _ _ => rfl
  | .integer _ => renderIH_rejected _ fun _ _ _ => rfl
  | .pair _ _ => renderIH_rejected _ fun _ _ _ => rfl
  | .first _ => renderIH_rejected _ fun _ _ _ => rfl
  | .second _ => renderIH_rejected _ fun _ _ _ => rfl
  | .lambda _ _ _ => renderIH_rejected _ fun _ _ _ => rfl
  | .inLeft _ _ => renderIH_rejected _ fun _ _ _ => rfl
  | .inRight _ _ => renderIH_rejected _ fun _ _ _ => rfl
  | .caseE _ _ _ => renderIH_rejected _ fun _ _ _ => rfl
  | .newCell _ _ => renderIH_rejected _ fun _ _ _ => rfl
  | .loadCell _ => renderIH_rejected _ fun _ _ _ => rfl
  | .storeCell _ _ => renderIH_rejected _ fun _ _ _ => rfl
  | .construct _ _ => renderIH_rejected _ fun _ _ _ => rfl
  | .matchData _ _ _ _ => renderIH_rejected _ fun _ _ _ => rfl

end Solcore.Synthesis.Source.ScalarMeaning
end

section
-- leanmerge: from Solcore.Synthesis.Source.ScalarMeaning.CallGraphPreservation
/-! Simulation lemmas for helper calls whose argument is copied into a fresh
temporary first, and their instance, together with the shared and raw opcode
cases, for the actual `CallGraphRenderer.renderWithFunctions`. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

open Solcore.Synthesis.Core (Target functionAcceptsAt)
open Solcore.Synthesis.Source.ScalarRenderer (Rendered)

section Generic

variable {render : RenderFn} {admits : Context → Prop} {called : List String}

/-- A call to an earlier helper printed as one fresh `word` temporary bound to
`callee(value)`: the argument value is passed to the helper's denotation in
the call context, as Core applies its closure. -/
theorem applyResult_spec {index : Nat} {argument : CoreExpr} {functions locals : List String}
    {indent first : Nat} {value : Rendered} {callee : String}
    (outside : locals.length ≤ index) (found : functions[index - locals.length]? = some callee)
    (spec : RenderSpec admits called argument .word functions locals indent first value) :
    RenderSpec admits called (.apply (.var index) argument) .word functions locals indent first
      (resultOf indent .word value.lines value.nextId (.call1 callee (.name value.value))) := by
  obtain ⟨statements, lines, le, valueClassified, names, simulates⟩ := spec
  unfold RenderSpec resultOf
  dsimp only
  refine ⟨statements ++ [.letDecl (temporary value.nextId) (LocalType.ofTarget .word)
      (.call1 callee (.name value.value))], ?_, by omega,
    Or.inr (allocated_temporary le (Nat.lt_succ_self _)), ?_, ?_⟩
  · simp only [Stmt.listLines_append, lines, Stmt.listLines, List.append_nil]
  · intro name mem
    simp only [Stmt.listIdentifiers_append, List.mem_append, Stmt.listIdentifiers,
      Stmt.identifiers, Expr.identifiers, List.append_nil, List.mem_cons,
      List.not_mem_nil, or_false] at mem
    rcases mem with mem | same | same | same
    · exact named_mono (names name mem) (Nat.le_refl _) (by omega)
    · exact named_allocated ⟨value.nextId, same, le, by omega⟩
    · subst same
      exact Or.inr (Or.inl (List.mem_of_getElem? found))
    · subst same
      exact named_of_classified valueClassified (Nat.le_refl _) (by omega)
  · refine result_simulates (target := .word) (fun context environment store scope outer
      admitted agree lengthOk functionsOk => ?_) le
    obtain ⟨argumentCore, argumentSource, scope₁, outer₁, added₁, argumentEvaluates,
      argumentRepresents, argumentExec, argumentLookup, argumentKeeps, argumentShape,
      argumentScope, argumentAdded⟩ :=
      simulates context environment store scope outer admitted agree lengthOk functionsOk
    obtain ⟨word, rfl, rfl⟩ := argumentRepresents
    obtain ⟨parameterType, resultType, body, captured, closureFound, behaves⟩ :=
      functionsOk (index - locals.length) callee found
    obtain ⟨result, bodyEvaluates, callResult⟩ := behaves word store
    have closureAt : environment[index]? =
        some (.closure parameterType resultType body captured) := by
      rw [List.getElem?_drop] at closureFound
      have position : locals.length + (index - locals.length) = index := by omega
      rwa [position] at closureFound
    refine ⟨.word result, .word result.val, scope₁, outer₁, added₁, ?_, ⟨result, rfl, rfl⟩,
      argumentExec, ?_, argumentKeeps, argumentShape, argumentScope, argumentAdded⟩
    · simp only [Solcore.Core.Wire.Expr.toCore]
      exact .apply (.var closureAt) argumentEvaluates bodyEvaluates
    · simp [Expr.eval, argumentLookup, callResult]

/-- A direct call to an earlier helper whose argument is copied first. -/
def SnapshotApplyInversion (render : RenderFn) : Prop :=
  ∀ (functions : List String) (target : Target) (locals : List String) (indent first index : Nat)
    (argument : CoreExpr) (rendered : Rendered),
    render functions target locals indent first (.apply (.var index) argument) = .ok rendered →
    target = .word ∧ locals.length ≤ index ∧ ∃ callee value,
      functions[index - locals.length]? = some callee ∧
      render functions .word locals indent first argument = .ok value ∧
      rendered = resultOf indent .word (snapshotOf indent value).lines (value.nextId + 1)
        (.call1 callee (.name (temporary value.nextId)))

theorem renderIH_snapshotApply (inversion : SnapshotApplyInversion render) {index : Nat}
    {argument : CoreExpr} (argumentIH : RenderIH render admits called argument) :
    RenderIH render admits called (.apply (.var index) argument) := by
  intro functions depth prior target locals indent first rendered accepted equation fresh
  simp only [functionAcceptsAt, Bool.and_eq_true] at accepted
  obtain ⟨_, argumentAccepted⟩ := accepted
  obtain ⟨rfl, outside, callee, value, found, valueEquation, rfl⟩ :=
    inversion functions target locals indent first index argument rendered equation
  exact applyResult_spec outside found (snapshot_spec (argumentIH functions depth prior .word
    locals indent first value argumentAccepted valueEquation fresh))

end Generic

/-! ### The actual call-graph renderer -/

theorem callGraph_word : WordInversion CallGraphRenderer.renderWithFunctions := by
  intro functions target locals indent first value rendered equation
  rw [CallGraphEquations.word] at equation
  exact (Except.ok.inj equation).symm

theorem callGraph_bool : BoolInversion CallGraphRenderer.renderWithFunctions := by
  intro functions target locals indent first value rendered equation
  rw [CallGraphEquations.bool] at equation
  exact (Except.ok.inj equation).symm

theorem callGraph_var : VarInversion CallGraphRenderer.renderWithFunctions := by
  intro functions target locals indent first index rendered equation
  rw [CallGraphEquations.var] at equation
  cases found : locals[index]? with
  | none =>
      rw [found] at equation
      cases equation
  | some binding =>
      rw [found] at equation
      exact ⟨binding, rfl, (Except.ok.inj equation).symm⟩

theorem callGraph_letE : LetInversion CallGraphRenderer.renderWithFunctions := by
  intro functions target locals indent first initializer body rendered equation
  rw [CallGraphEquations.letE] at equation
  obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨rest, restEquation, equation⟩ := except_bind_eq_ok equation
  exact ⟨value, rest, valueEquation, restEquation, (Except.ok.inj equation).symm⟩

theorem callGraph_ifE : IfInversion CallGraphRenderer.renderWithFunctions := by
  intro functions target locals indent first condition yes no rendered equation
  rw [CallGraphEquations.ifE] at equation
  obtain ⟨tested, testedEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨selected, selectedEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨fallback, fallbackEquation, equation⟩ := except_bind_eq_ok equation
  exact ⟨tested, selected, fallback, testedEquation, selectedEquation, fallbackEquation,
    (Except.ok.inj equation).symm⟩

theorem callGraph_unary : UnaryInversion CallGraphRenderer.renderWithFunctions := by
  intro functions target locals indent first op sourceOp operand rendered selected equation
  rw [CallGraphEquations.unary functions target locals indent first op sourceOp operand
    selected] at equation
  obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
  exact ⟨value, valueEquation, (Except.ok.inj equation).symm⟩

theorem callGraph_binary : BinaryInversion CallGraphRenderer.renderWithFunctions := by
  intro functions target locals indent first op sourceOp left right rendered selected equation
  rw [CallGraphEquations.binary functions target locals indent first op sourceOp left right
    selected] at equation
  obtain ⟨leftValue, leftEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨rightValue, rightEquation, equation⟩ := except_bind_eq_ok equation
  exact ⟨leftValue, rightValue, leftEquation, rightEquation, (Except.ok.inj equation).symm⟩

theorem callGraph_clz : ClzInversion CallGraphRenderer.renderWithFunctions := by
  intro functions target locals indent first operand rendered equation
  rw [CallGraphEquations.clz] at equation
  obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
  exact ⟨value, valueEquation, (Except.ok.inj equation).symm⟩

theorem callGraph_primitiveBinary :
    PrimitiveBinaryInversion CallGraphRenderer.renderWithFunctions := by
  intro functions target locals indent first op build left right rendered selected equation
  rw [CallGraphEquations.binary_primitive functions target locals indent first op build left
    right selected] at equation
  obtain ⟨leftValue, leftEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨rightValue, rightEquation, equation⟩ := except_bind_eq_ok equation
  exact ⟨leftValue, rightValue, leftEquation, rightEquation, (Except.ok.inj equation).symm⟩

theorem callGraph_ternary : TernaryInversion CallGraphRenderer.renderWithFunctions := by
  intro functions target locals indent first op one two three rendered equation
  rw [CallGraphEquations.ternary] at equation
  obtain ⟨oneValue, oneEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨twoValue, twoEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨threeValue, threeEquation, equation⟩ := except_bind_eq_ok equation
  exact ⟨oneValue, twoValue, threeValue, oneEquation, twoEquation, threeEquation,
    (Except.ok.inj equation).symm⟩

theorem callGraph_apply : SnapshotApplyInversion CallGraphRenderer.renderWithFunctions :=
  fun _ _ _ _ _ _ _ _ equation => CallGraphEquations.apply_ok equation

theorem callGraph_unary_spec {op : Solcore.Core.Wire.UnaryOp} {operand : CoreExpr}
    (operandIH : RenderIH CallGraphRenderer.renderWithFunctions PrimitiveContext primitiveCallees
      operand) :
    RenderIH CallGraphRenderer.renderWithFunctions PrimitiveContext primitiveCallees
      (.unary op operand) := by
  cases selected : sourceUnary? op with
  | some _ => exact renderIH_unary callGraph_unary selected operandIH
  | none =>
      cases op
      case boolNot => simp [sourceUnary?] at selected
      case wordNot => simp [sourceUnary?] at selected
      case wordClz =>
        exact renderIH_clz callGraph_clz (by decide)
          (fun _ admitted => admitted.reaches (by decide)) operandIH
      all_goals
        refine renderIH_error _ fun functions target locals indent first rendered equation => ?_
        rw [CallGraphEquations.unary_unsupported _ _ _ _ _ _ _ rfl] at equation
        cases equation

theorem callGraph_binary_spec {op : Solcore.Core.Wire.BinaryOp} {left right : CoreExpr}
    (leftIH : RenderIH CallGraphRenderer.renderWithFunctions PrimitiveContext primitiveCallees
      left)
    (rightIH : RenderIH CallGraphRenderer.renderWithFunctions PrimitiveContext primitiveCallees
      right) :
    RenderIH CallGraphRenderer.renderWithFunctions PrimitiveContext primitiveCallees
      (.binary op left right) := by
  cases selected : sourceBinary? op with
  | some _ => exact renderIH_binary callGraph_binary selected leftIH rightIH
  | none =>
      cases extended : primitiveBinary? op with
      | some build =>
          exact renderIH_primitiveBinary callGraph_primitiveBinary extended
            (primitiveBinary_names extended)
            (fun context frames leftName rightName leftWord rightWord admitted =>
              primitiveBinary_agree extended context frames leftName rightName leftWord
                rightWord admitted)
            leftIH rightIH
      | none =>
          refine renderIH_error _ fun functions target locals indent first rendered equation => ?_
          have unsupported : CallGraphRenderer.supportedBinary op = false := by
            cases op <;> simp_all [sourceBinary?, primitiveBinary?,
              CallGraphRenderer.supportedBinary, PrimitiveRenderer.supportedBinary,
              Source.supportedBinary]
          rw [CallGraphEquations.binary_unsupported _ _ _ _ _ _ _ _ unsupported] at equation
          cases equation

/-- Every admitted expression that the actual call-graph renderer accepts
satisfies its rendering specification in every primitive call context, with
or without earlier helpers. -/
theorem callGraph_render_spec :
    (expression : CoreExpr) →
      RenderIH CallGraphRenderer.renderWithFunctions PrimitiveContext primitiveCallees expression
  | .word value => renderIH_word callGraph_word value
  | .bool value => renderIH_bool callGraph_bool value
  | .var index => renderIH_var callGraph_var index
  | .letE initializer body =>
      renderIH_letE callGraph_letE (callGraph_render_spec initializer)
        (callGraph_render_spec body)
  | .ifE condition yes no =>
      renderIH_ifE callGraph_ifE (callGraph_render_spec condition) (callGraph_render_spec yes)
        (callGraph_render_spec no)
  | .unary _ operand => callGraph_unary_spec (callGraph_render_spec operand)
  | .binary _ left right =>
      callGraph_binary_spec (callGraph_render_spec left) (callGraph_render_spec right)
  | .ternary op one two three =>
      renderIH_ternary callGraph_ternary (by cases op <;> decide)
        (fun context frames oneName twoName threeName oneWord twoWord threeWord admitted =>
          ternary_agree op context frames oneName twoName threeName oneWord twoWord threeWord
            admitted)
        (callGraph_render_spec one) (callGraph_render_spec two) (callGraph_render_spec three)
  | .apply (.var _) argument =>
      renderIH_snapshotApply callGraph_apply (callGraph_render_spec argument)
  | .apply (.word _) _ | .apply (.bool _) _ | .apply .unit _ | .apply (.integer _) _
  | .apply (.pair _ _) _ | .apply (.first _) _ | .apply (.second _) _
  | .apply (.lambda _ _ _) _ | .apply (.apply _ _) _ | .apply (.inLeft _ _) _
  | .apply (.inRight _ _) _ | .apply (.caseE _ _ _) _ | .apply (.newCell _ _) _
  | .apply (.loadCell _) _ | .apply (.storeCell _ _) _ | .apply (.construct _ _) _
  | .apply (.matchData _ _ _ _) _ | .apply (.unary _ _) _ | .apply (.binary _ _ _) _
  | .apply (.ternary _ _ _ _) _ | .apply (.letE _ _) _ | .apply (.ifE _ _ _) _ =>
      renderIH_rejected _ fun _ _ _ => rfl
  | .unit => renderIH_rejected _ fun _ _ _ => rfl
  | .integer _ => renderIH_rejected _ fun _ _ _ => rfl
  | .pair _ _ => renderIH_rejected _ fun _ _ _ => rfl
  | .first _ => renderIH_rejected _ fun _ _ _ => rfl
  | .second _ => renderIH_rejected _ fun _ _ _ => rfl
  | .lambda _ _ _ => renderIH_rejected _ fun _ _ _ => rfl
  | .inLeft _ _ => renderIH_rejected _ fun _ _ _ => rfl
  | .inRight _ _ => renderIH_rejected _ fun _ _ _ => rfl
  | .caseE _ _ _ => renderIH_rejected _ fun _ _ _ => rfl
  | .newCell _ _ => renderIH_rejected _ fun _ _ _ => rfl
  | .loadCell _ => renderIH_rejected _ fun _ _ _ => rfl
  | .storeCell _ _ => renderIH_rejected _ fun _ _ _ => rfl
  | .construct _ _ => renderIH_rejected _ fun _ _ _ => rfl
  | .matchData _ _ _ _ => renderIH_rejected _ fun _ _ _ => rfl

end Solcore.Synthesis.Source.ScalarMeaning
end
