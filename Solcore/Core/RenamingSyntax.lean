import Solcore.Core.Primitive

set_option autoImplicit false

namespace Solcore.Core

abbrev Renaming := Nat → Nat

namespace Renaming

def id : Renaming := fun index => index

def comp (outer inner : Renaming) : Renaming :=
  fun index => outer (inner index)

def lift (mapping : Renaming) : Renaming
  | 0 => 0
  | index + 1 => mapping index + 1

def insertion (cutoff : Nat) : Renaming :=
  fun index => if cutoff ≤ index then index + 1 else index

@[simp] theorem lift_id : lift id = id := by
  funext index
  cases index <;> rfl

@[simp] theorem lift_comp (outer inner : Renaming) :
    lift (comp outer inner) = comp (lift outer) (lift inner) := by
  funext index
  cases index <;> rfl

@[simp] theorem lift_insertion (cutoff : Nat) :
    lift (insertion cutoff) = insertion (cutoff + 1) := by
  funext index
  cases index with
  | zero => simp [lift, insertion]
  | succ index =>
      by_cases shifted : cutoff ≤ index <;>
        simp [lift, insertion, Nat.succ_le_succ_iff, shifted]

@[simp] theorem lift_comp_insertion_zero (mapping : Renaming) :
    comp mapping.lift (insertion 0) = comp (insertion 0) mapping := by
  funext index
  simp [comp, lift, insertion]

end Renaming

mutual

  def Expr.rename (expr : Expr) (mapping : Renaming) : Expr :=
    match expr with
    | .unit => .unit
    | .bool value => .bool value
    | .word value => .word value
    | .var index => .var (mapping index)
    | .pair left right => .pair (left.rename mapping) (right.rename mapping)
    | .first operand => .first (operand.rename mapping)
    | .second operand => .second (operand.rename mapping)
    | .lambda parameterType resultType body =>
        .lambda parameterType resultType (body.rename mapping.lift)
    | .apply function argument =>
        .apply (function.rename mapping) (argument.rename mapping)
    | .inLeft rightType payload => .inLeft rightType (payload.rename mapping)
    | .inRight leftType payload => .inRight leftType (payload.rename mapping)
    | .caseE scrutinee leftBranch rightBranch =>
        .caseE
          (scrutinee.rename mapping)
          (leftBranch.rename mapping.lift)
          (rightBranch.rename mapping.lift)
    | .newCell elementType initializer =>
        .newCell elementType (initializer.rename mapping)
    | .loadCell reference => .loadCell (reference.rename mapping)
    | .storeCell reference value =>
        .storeCell (reference.rename mapping) (value.rename mapping)
    | .construct constructor payload =>
        .construct constructor (payload.rename mapping)
    | .matchData dataType resultType scrutinee branches =>
        .matchData dataType resultType
          (scrutinee.rename mapping)
          (Expr.renameList branches mapping.lift)
    | .unary op operand => .unary op (operand.rename mapping)
    | .binary op left right =>
        .binary op (left.rename mapping) (right.rename mapping)
    | .ternary op firstExpr secondExpr thirdExpr =>
        .ternary op (firstExpr.rename mapping) (secondExpr.rename mapping)
          (thirdExpr.rename mapping)
    | .letE value body =>
        .letE (value.rename mapping) (body.rename mapping.lift)
    | .ifE condition thenBranch elseBranch =>
        .ifE
          (condition.rename mapping)
          (thenBranch.rename mapping)
          (elseBranch.rename mapping)

  def Expr.renameList (expressions : List Expr) (mapping : Renaming) : List Expr :=
    match expressions with
    | [] => []
    | expression :: rest =>
        expression.rename mapping :: Expr.renameList rest mapping

end

mutual

  @[simp] theorem Expr.rename_id : ∀ expr : Expr, expr.rename Renaming.id = expr
    | .unit | .bool _ | .word _ | .var _ => rfl
    | .pair left right
    | .apply left right
    | .storeCell left right
    | .binary _ left right
    | .letE left right => by simp [Expr.rename, Expr.rename_id left, Expr.rename_id right]
    | .first operand
    | .second operand
    | .loadCell operand
    | .unary _ operand => by simp [Expr.rename, Expr.rename_id operand]
    | .lambda _ _ body => by simp [Expr.rename, Expr.rename_id body]
    | .inLeft _ payload
    | .inRight _ payload
    | .newCell _ payload
    | .construct _ payload => by simp [Expr.rename, Expr.rename_id payload]
    | .caseE scrutinee leftBranch rightBranch
    | .ifE scrutinee leftBranch rightBranch => by
        simp [Expr.rename, Expr.rename_id scrutinee, Expr.rename_id leftBranch,
          Expr.rename_id rightBranch]
    | .ternary _ firstExpr secondExpr thirdExpr => by
        simp [Expr.rename, Expr.rename_id firstExpr, Expr.rename_id secondExpr,
          Expr.rename_id thirdExpr]
    | .matchData _ _ scrutinee branches => by
        simp [Expr.rename, Expr.rename_id scrutinee, Expr.renameList_id branches]

  @[simp] theorem Expr.renameList_id : ∀ expressions : List Expr,
      Expr.renameList expressions Renaming.id = expressions
    | [] => rfl
    | expression :: rest => by
        simp [Expr.renameList, Expr.rename_id expression, Expr.renameList_id rest]

end

mutual

  theorem Expr.rename_comp : ∀ (expr : Expr) (outer inner : Renaming),
      (expr.rename inner).rename outer = expr.rename (outer.comp inner)
    | .unit, _, _ | .bool _, _, _ | .word _, _, _ | .var _, _, _ => rfl
    | .pair left right, outer, inner
    | .apply left right, outer, inner
    | .storeCell left right, outer, inner
    | .binary _ left right, outer, inner
    | .letE left right, outer, inner => by
        simp [Expr.rename, Expr.rename_comp left, Expr.rename_comp right]
    | .first operand, outer, inner
    | .second operand, outer, inner
    | .loadCell operand, outer, inner
    | .unary _ operand, outer, inner => by
        simp [Expr.rename, Expr.rename_comp operand]
    | .lambda _ _ body, outer, inner => by
        simp [Expr.rename, Expr.rename_comp body]
    | .inLeft _ payload, outer, inner
    | .inRight _ payload, outer, inner
    | .newCell _ payload, outer, inner
    | .construct _ payload, outer, inner => by
        simp [Expr.rename, Expr.rename_comp payload]
    | .caseE scrutinee leftBranch rightBranch, outer, inner
    | .ifE scrutinee leftBranch rightBranch, outer, inner => by
        simp [Expr.rename, Expr.rename_comp scrutinee,
          Expr.rename_comp leftBranch, Expr.rename_comp rightBranch]
    | .ternary _ firstExpr secondExpr thirdExpr, outer, inner => by
        simp [Expr.rename, Expr.rename_comp firstExpr, Expr.rename_comp secondExpr,
          Expr.rename_comp thirdExpr]
    | .matchData _ _ scrutinee branches, outer, inner => by
        simp [Expr.rename, Expr.rename_comp scrutinee,
          Expr.renameList_comp branches]

  theorem Expr.renameList_comp : ∀
      (expressions : List Expr) (outer inner : Renaming),
      Expr.renameList (Expr.renameList expressions inner) outer =
        Expr.renameList expressions (outer.comp inner)
    | [], _, _ => rfl
    | expression :: rest, outer, inner => by
        simp [Expr.renameList, Expr.rename_comp expression,
          Expr.renameList_comp rest]

end


mutual

  @[simp] theorem Expr.rename_insertion : ∀ (expr : Expr) (cutoff : Nat),
      expr.rename (Renaming.insertion cutoff) = expr.weakenAt cutoff
    | .unit, _ => by simp [Expr.rename, Expr.weakenAt]
    | .bool _, _ => by simp [Expr.rename, Expr.weakenAt]
    | .word _, _ => by simp [Expr.rename, Expr.weakenAt]
    | .var index, cutoff => by
        by_cases shifted : cutoff ≤ index <;>
          simp [Expr.rename, Expr.weakenAt, Renaming.insertion, shifted]
    | .pair left right, cutoff
    | .apply left right, cutoff
    | .storeCell left right, cutoff
    | .binary _ left right, cutoff
    | .letE left right, cutoff => by
        simp [Expr.rename, Expr.weakenAt, Expr.rename_insertion left,
          Expr.rename_insertion right]
    | .first operand, cutoff
    | .second operand, cutoff
    | .loadCell operand, cutoff
    | .unary _ operand, cutoff => by
        simp [Expr.rename, Expr.weakenAt, Expr.rename_insertion operand]
    | .lambda _ _ body, cutoff => by
        simp [Expr.rename, Expr.weakenAt, Expr.rename_insertion body]
    | .inLeft _ payload, cutoff
    | .inRight _ payload, cutoff
    | .newCell _ payload, cutoff
    | .construct _ payload, cutoff => by
        simp [Expr.rename, Expr.weakenAt, Expr.rename_insertion payload]
    | .caseE scrutinee leftBranch rightBranch, cutoff
    | .ifE scrutinee leftBranch rightBranch, cutoff => by
        simp [Expr.rename, Expr.weakenAt, Expr.rename_insertion scrutinee,
          Expr.rename_insertion leftBranch, Expr.rename_insertion rightBranch]
    | .ternary _ firstExpr secondExpr thirdExpr, cutoff => by
        simp [Expr.rename, Expr.weakenAt, Expr.rename_insertion firstExpr,
          Expr.rename_insertion secondExpr, Expr.rename_insertion thirdExpr]
    | .matchData _ _ scrutinee branches, cutoff => by
        simp [Expr.rename, Expr.weakenAt, Expr.rename_insertion scrutinee,
          Expr.renameList_insertion branches]

  theorem Expr.renameList_insertion : ∀
      (expressions : List Expr) (cutoff : Nat),
      Expr.renameList expressions (Renaming.insertion cutoff) =
        expressions.map fun expression => expression.weakenAt cutoff
    | [], _ => rfl
    | expression :: rest, cutoff => by
        simp [Expr.renameList, Expr.rename_insertion expression,
          Expr.renameList_insertion rest]

end

end Solcore.Core
