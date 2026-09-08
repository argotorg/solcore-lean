import Solcore.Resolved.Expr

/-! Uniform renaming of resolved local identities. Both references and let
binders are renamed; literal values and selected primitives remain unchanged.
This operation does not rename source spellings or allocate fresh identities. -/

set_option autoImplicit false

namespace Solcore.Resolved

def LocalScope.mapIds {α : Type} (mapping : LocalId → LocalId)
    (scope : LocalScope α) : LocalScope α :=
  scope.map (fun entry => (mapping entry.1, entry.2))

def Expr.renameIds (mapping : LocalId → LocalId) : Expr → Expr
  | .unit => .unit
  | .bool value => .bool value
  | .word value => .word value
  | .var id => .var (mapping id)
  | .unary op operand => .unary op (operand.renameIds mapping)
  | .binary op left right => .binary op (left.renameIds mapping) (right.renameIds mapping)
  | .letE binder value body =>
      .letE (mapping binder) (value.renameIds mapping) (body.renameIds mapping)
  | .ifE condition thenBranch elseBranch =>
      .ifE (condition.renameIds mapping) (thenBranch.renameIds mapping) (elseBranch.renameIds mapping)

end Solcore.Resolved
