import Solcore.Core.Wire.V3.Host

/-! The checker-sealed, syntax-independent Word fragment used for synthesis. -/

set_option autoImplicit false

namespace Solcore.Synthesis.CoreV3

open Solcore.Core.Wire

/-- The two expression types generated inside the initial synthesis fragment. -/
inductive Target where
  | word
  | bool
  deriving Repr, BEq, DecidableEq

namespace Target

def toWireTy : Target → V3.Ty
  | .word => .word
  | .bool => .bool

def unaryOperand : V3.UnaryOp → Target
  | .boolNot => .bool
  | .wordNot
  | .wordClz => .word

def unaryResult : V3.UnaryOp → Target
  | .boolNot => .bool
  | .wordNot
  | .wordClz => .word

def binaryResult : V3.BinaryOp → Target
  | .wordEq
  | .wordGt
  | .wordSgt => .bool
  | .wordAdd
  | .wordSub
  | .wordMul
  | .wordDiv
  | .wordMod
  | .wordAnd
  | .wordOr
  | .wordXor
  | .wordShl
  | .wordShr
  | .wordByte
  | .wordSar
  | .wordPow
  | .wordSignExtend
  | .wordSdiv
  | .wordSmod => .word

end Target

/-- Recognize the deliberately small, intrinsically typed synthesis fragment.

`localWordDepth` counts Word-valued `let` binders. A variable is accepted only
when it points inside that local prefix; frozen Wire host bindings are therefore
never admitted into this fragment. -/
def acceptsAt (localWordDepth : Nat) (target : Target) : V3.Expr → Bool
  | .word _ => target == .word
  | .bool _ => target == .bool
  | .var index => target == .word && decide (index < localWordDepth)
  | .letE initializer body =>
      acceptsAt localWordDepth .word initializer &&
        acceptsAt (localWordDepth + 1) target body
  | .ifE condition thenBranch elseBranch =>
      acceptsAt localWordDepth .bool condition &&
        acceptsAt localWordDepth target thenBranch &&
        acceptsAt localWordDepth target elseBranch
  | .unary op operand =>
      target == Target.unaryResult op &&
        acceptsAt localWordDepth (Target.unaryOperand op) operand
  | .binary op left right =>
      target == Target.binaryResult op &&
        acceptsAt localWordDepth .word left &&
        acceptsAt localWordDepth .word right
  | .ternary _ first second third =>
      target == .word &&
        acceptsAt localWordDepth .word first &&
        acceptsAt localWordDepth .word second &&
        acceptsAt localWordDepth .word third
  | _ => false

/-- Recognize a closed expression at the root of the synthesis fragment. -/
def accepts (target : Target) (expression : V3.Expr) : Bool :=
  acceptsAt 0 target expression

/-- Every syntactic or primitive feature whose generation is tracked. -/
inductive Feature where
  | wordLiteral
  | local
  | boolLiteral
  | letE
  | ifE
  | unary (op : V3.UnaryOp)
  | binary (op : V3.BinaryOp)
  | ternary (op : V3.TernaryOp)
  deriving Repr, BEq, DecidableEq

/-- The frozen unary operator catalog for this generator version. -/
def unaryOps : Array V3.UnaryOp :=
  #[.boolNot, .wordNot, .wordClz]

/-- The frozen binary operator catalog for this generator version. -/
def binaryOps : Array V3.BinaryOp :=
  #[.wordAdd, .wordSub, .wordMul, .wordDiv, .wordMod,
    .wordEq, .wordGt, .wordSgt, .wordAnd, .wordOr, .wordXor,
    .wordShl, .wordShr, .wordByte, .wordSar, .wordPow,
    .wordSignExtend, .wordSdiv, .wordSmod]

/-- The frozen ternary operator catalog for this generator version. -/
def ternaryOps : Array V3.TernaryOp :=
  #[.wordAddMod, .wordMulMod]

namespace Feature

/-- The complete, stable feature catalog used by corpus coverage checks. -/
def catalog : Array Feature :=
  #[.wordLiteral, .local, .boolLiteral, .letE, .ifE] ++
    unaryOps.map Feature.unary ++
    binaryOps.map Feature.binary ++
    ternaryOps.map Feature.ternary

end Feature

/-- List feature occurrences in deterministic preorder.

The classifier is intended for expressions already accepted by `acceptsAt`.
Unsupported constructors contribute no synthesis feature. -/
def features : V3.Expr → List Feature
  | .word _ => [.wordLiteral]
  | .bool _ => [.boolLiteral]
  | .var _ => [.local]
  | .letE initializer body =>
      .letE :: features initializer ++ features body
  | .ifE condition thenBranch elseBranch =>
      .ifE :: features condition ++ features thenBranch ++ features elseBranch
  | .unary op operand =>
      .unary op :: features operand
  | .binary op left right =>
      .binary op :: features left ++ features right
  | .ternary op first second third =>
      .ternary op :: features first ++ features second ++ features third
  | _ => []

/-- A Wire v3 Word program admitted by both the checker and the synthesis
fragment boundary. The private constructor prevents forged evidence. -/
structure CheckedWordProgram where private mk ::
  program : V3.Program
  checked : program.check = true
  resultType_eq : program.resultType = .word
  dataDefinitions_eq : program.dataDefinitions = []
  fragment : accepts .word program.body = true

namespace CheckedWordProgram

/-- The sole admission path for externally supplied Wire v3 programs. -/
def ofProgram? (program : V3.Program) : Option CheckedWordProgram :=
  if checked : program.check = true then
    if resultTypeEq : program.resultType = .word then
      if dataDefinitionsEq : program.dataDefinitions = [] then
        if fragment : accepts .word program.body = true then
          some ⟨program, checked, resultTypeEq, dataDefinitionsEq, fragment⟩
        else
          none
      else
        none
    else
      none
  else
    none

/-- Checker admission projects to the frozen Wire v3 declarative contract. -/
theorem wellTyped (code : CheckedWordProgram) : code.program.WellTyped :=
  V3.Program.check_full_sound code.checked

end CheckedWordProgram

end Solcore.Synthesis.CoreV3
