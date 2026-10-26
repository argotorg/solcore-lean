import Solcore.Synthesis.Source.PrimitiveRenderer
import Solcore.Synthesis.Source.ScalarMeaning.RendererEquations

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
