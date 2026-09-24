import Solcore.Core.Wire.Host

/-! The checker-sealed, syntax-independent Word fragment used for synthesis. -/

set_option autoImplicit false

namespace Solcore.Synthesis.Core

open Solcore.Core.Wire

/-- The two expression types generated inside the initial synthesis fragment. -/
inductive Target where
  | word
  | bool
  deriving Repr, BEq, DecidableEq

namespace Target

def toWireTy : Target → Ty
  | .word => .word
  | .bool => .bool

def unaryOperand : UnaryOp → Target
  | .boolNot => .bool
  | .wordNot
  | .wordClz => .word

def unaryResult : UnaryOp → Target
  | .boolNot => .bool
  | .wordNot
  | .wordClz => .word

def binaryResult : BinaryOp → Target
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
when it points inside that local prefix; Wire host bindings are therefore
never admitted into this fragment. -/
def acceptsAt (localWordDepth : Nat) (target : Target) : Expr → Bool
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
def accepts (target : Target) (expression : Expr) : Bool :=
  acceptsAt 0 target expression

/-- Every syntactic or primitive feature whose generation is tracked. -/
inductive Feature where
  | wordLiteral
  | local
  | boolLiteral
  | letE
  | ifE
  | unary (op : UnaryOp)
  | binary (op : BinaryOp)
  | ternary (op : TernaryOp)
  deriving Repr, BEq, DecidableEq

/-- The fixed unary operator catalog for this generator. -/
def unaryOps : Array UnaryOp :=
  #[.boolNot, .wordNot, .wordClz]

/-- The fixed binary operator catalog for this generator. -/
def binaryOps : Array BinaryOp :=
  #[.wordAdd, .wordSub, .wordMul, .wordDiv, .wordMod,
    .wordEq, .wordGt, .wordSgt, .wordAnd, .wordOr, .wordXor,
    .wordShl, .wordShr, .wordByte, .wordSar, .wordPow,
    .wordSignExtend, .wordSdiv, .wordSmod]

/-- The fixed ternary operator catalog for this generator. -/
def ternaryOps : Array TernaryOp :=
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
def features : Expr → List Feature
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

/-- A Wire Word program admitted by both the checker and the synthesis
fragment boundary. The private constructor prevents forged evidence. -/
structure CheckedWordProgram where private mk ::
  program : Program
  checked : program.check = true
  resultType_eq : program.resultType = .word
  dataDefinitions_eq : program.dataDefinitions = []
  fragment : accepts .word program.body = true

namespace CheckedWordProgram

/-- The sole admission path for externally supplied Wire programs. -/
def ofProgram? (program : Program) : Option CheckedWordProgram :=
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

/-- Checker admission projects to the Wire declarative contract. -/
theorem wellTyped (code : CheckedWordProgram) : code.program.WellTyped :=
  Program.check_full_sound code.checked

end CheckedWordProgram

end Solcore.Synthesis.Core
