import Solcore.TypeSystem.Substitution

set_option autoImplicit false

namespace Solcore.TypeSystem

structure Constraint where
  left : Ty
  right : Ty
  deriving Repr, DecidableEq

namespace Constraint

def apply (substitution : Substitution) (constraint : Constraint) : Constraint :=
  { left := substitution.apply constraint.left
    right := substitution.apply constraint.right }

end Constraint

namespace Unification

inductive Error where
  | occursCheck (metavariable : TypeVarId) (type : Ty)
  | mismatch (left right : Ty)
  | exhausted
  deriving Repr, DecidableEq

private def loop : Nat → Substitution → List Constraint → Except Error Substitution
  | 0, _, _ => .error .exhausted
  | fuel + 1, substitution, constraints =>
      match constraints with
      | [] => .ok substitution
      | constraint :: rest =>
          let left := substitution.apply constraint.left
          let right := substitution.apply constraint.right
          if left = right then
            loop fuel substitution rest
          else
            match left, right with
            | .variable metavariable, type
            | type, .variable metavariable =>
                if type.containsVariable metavariable then
                  .error (.occursCheck metavariable type)
                else
                  let binding : Substitution := [(metavariable, type)]
                  loop fuel (binding.compose substitution) rest
            | .application leftFunction leftArgument,
                .application rightFunction rightArgument
            | .function leftFunction leftArgument,
                .function rightFunction rightArgument
            | .product leftFunction leftArgument,
                .product rightFunction rightArgument
            | .mapping leftFunction leftArgument,
                .mapping rightFunction rightArgument =>
                  loop fuel substitution
                    ({ left := leftFunction, right := rightFunction } ::
                     { left := leftArgument, right := rightArgument } :: rest)
            | .proxy leftInner, .proxy rightInner
            | .comptime leftInner, .comptime rightInner =>
                loop fuel substitution ({ left := leftInner, right := rightInner } :: rest)
            | _, _ => .error (.mismatch left right)

def constraintSize (constraint : Constraint) : Nat :=
  constraint.left.size + constraint.right.size

/-- A bounded polynomial budget; pathological expansion reports `exhausted`. -/
def defaultFuel (constraints : List Constraint) : Nat :=
  let scale := constraints.foldl
    (fun size constraint => size + constraintSize constraint) (constraints.length + 1)
  scale * scale

def unifyWithFuel (fuel : Nat) (constraints : List Constraint) :
    Except Error Substitution :=
  loop fuel [] constraints

@[simp]
theorem unifyWithFuel_empty (fuel : Nat) :
    unifyWithFuel (fuel + 1) [] = .ok [] := by
  simp [unifyWithFuel, loop]

@[simp]
theorem unifyWithFuel_reflexive (fuel : Nat) (type : Ty) :
    unifyWithFuel (fuel + 2) [{ left := type, right := type }] = .ok [] := by
  simp [unifyWithFuel, loop]

@[simp]
theorem unifyWithFuel_variable_constructor (fuel : Nat) (metavariable : TypeVarId)
    (constructor : TypeConstructorId) :
    unifyWithFuel (fuel + 2)
      [{ left := .variable metavariable, right := .constructor constructor }] =
        .ok [(metavariable, .constructor constructor)] := by
  simp [unifyWithFuel, loop, Substitution.compose, Substitution.apply,
    Substitution.lookup?, Ty.containsVariable, Ty.freeVariables]

/-- First-order unification with an occurs check. -/
def unify (constraints : List Constraint) : Except Error Substitution :=
  unifyWithFuel (defaultFuel constraints) constraints

def unifyTypes (left right : Ty) : Except Error Substitution :=
  unify [{ left, right }]

end Unification

end Solcore.TypeSystem
