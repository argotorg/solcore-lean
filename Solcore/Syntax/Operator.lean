import Solcore.Syntax.Type

set_option autoImplicit false

namespace Solcore.Syntax

/-- Prefix operators accepted by canonical Core expressions. -/
inductive UnaryOp where
  | logicalNot
  | bitNot
  deriving Repr, BEq, DecidableEq

namespace UnaryOp

def symbol : UnaryOp → Symbol
  | .logicalNot => .bang
  | .bitNot => .tilde

end UnaryOp

/-- Infix operators accepted by canonical Core expressions. -/
inductive BinaryOp where
  | multiply
  | divide
  | modulo
  | add
  | subtract
  | bitAnd
  | bitXor
  | bitOr
  | less
  | greater
  | lessEqual
  | greaterEqual
  | equal
  | notEqual
  | logicalAnd
  | logicalOr
  deriving Repr, BEq, DecidableEq

namespace BinaryOp

/-- Larger values bind more tightly. -/
def precedence : BinaryOp → Nat
  | .multiply | .divide | .modulo => 8
  | .add | .subtract => 7
  | .bitAnd => 6
  | .bitXor => 5
  | .bitOr => 4
  | .less | .greater | .lessEqual | .greaterEqual => 3
  | .equal | .notEqual => 2
  | .logicalAnd => 1
  | .logicalOr => 0

/-- Relational and equality chains are deliberately non-associative. -/
def isNonAssociative : BinaryOp → Bool
  | .less | .greater | .lessEqual | .greaterEqual | .equal | .notEqual => true
  | _ => false

def symbol : BinaryOp → Symbol
  | .multiply => .star
  | .divide => .slash
  | .modulo => .percent
  | .add => .plus
  | .subtract => .minus
  | .bitAnd => .amp
  | .bitXor => .caret
  | .bitOr => .pipe
  | .less => .less
  | .greater => .greater
  | .lessEqual => .lessEqual
  | .greaterEqual => .greaterEqual
  | .equal => .equalEqual
  | .notEqual => .notEqual
  | .logicalAnd => .logicalAnd
  | .logicalOr => .logicalOr

end BinaryOp

/-- Assignment spellings that consume a right-hand expression. -/
inductive ValueAssignOp where
  | equal
  | add
  | subtract
  | multiply
  | divide
  | modulo
  | bitAnd
  | bitXor
  | bitOr
  deriving Repr, BEq, DecidableEq

namespace ValueAssignOp

def symbol : ValueAssignOp → Symbol
  | .equal => .equal
  | .add => .plusEqual
  | .subtract => .minusEqual
  | .multiply => .starEqual
  | .divide => .slashEqual
  | .modulo => .percentEqual
  | .bitAnd => .ampEqual
  | .bitXor => .caretEqual
  | .bitOr => .pipeEqual

end ValueAssignOp

end Solcore.Syntax
