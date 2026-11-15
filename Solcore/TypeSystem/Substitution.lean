import Solcore.TypeSystem.Type

/-!
# Substitutions

`TypeSystem.Substitution` maps flexible variables to types. `TypeSystem.Substitution.apply` applies
one and `TypeSystem.Substitution.compose` composes two.
-/

set_option autoImplicit false

namespace Solcore.TypeSystem

/-- Ordered substitutions for flexible metavariables.  First match wins. -/
abbrev Substitution := List (TypeVarId × Ty)

namespace Substitution

def empty : Substitution := []

def lookup? : Substitution → TypeVarId → Option Ty
  | [], _ => none
  | (candidate, replacement) :: rest, metavariable =>
      if candidate = metavariable then some replacement else lookup? rest metavariable

/-- Simultaneous capture-free substitution.  Rigid parameters are untouched. -/
def apply (substitution : Substitution) : Ty → Ty
  | .variable metavariable =>
      substitution.lookup? metavariable |>.getD (.variable metavariable)
  | .parameter parameter => .parameter parameter
  | .constructor constructor => .constructor constructor
  | .application function argument =>
      .application (apply substitution function) (apply substitution argument)
  | .function parameter result =>
      .function (apply substitution parameter) (apply substitution result)
  | .product left right =>
      .product (apply substitution left) (apply substitution right)
  | .mapping key value =>
      .mapping (apply substitution key) (apply substitution value)
  | .proxy inner => .proxy (apply substitution inner)
  | .comptime inner => .comptime (apply substitution inner)
  | .error => .error

def erase (substitution : Substitution) (metavariable : TypeVarId) : Substitution :=
  substitution.filter fun entry => entry.1 != metavariable

def without (substitution : Substitution) (variables : List TypeVarId) : Substitution :=
  variables.foldl erase substitution

/--
`compose newer older` has the effect of applying `older` and then `newer`.
The result is kept closed enough for the substitutions produced by unification.
-/
def compose (newer older : Substitution) : Substitution :=
  let oldDomain := older.map Prod.fst
  let updatedOld := older.map fun entry => (entry.1, apply newer entry.2)
  updatedOld ++ newer.filter fun entry => !(entry.1 ∈ oldDomain)

def domain (substitution : Substitution) : List TypeVarId :=
  substitution.map Prod.fst

end Substitution

/-- Ordered replacement of rigid source parameters when a declaration is used. -/
abbrev ParameterSubstitution := List (TypeParameterId × Ty)

namespace ParameterSubstitution

def lookup? : ParameterSubstitution → TypeParameterId → Option Ty
  | [], _ => none
  | (candidate, replacement) :: rest, parameter =>
      if candidate = parameter then some replacement else lookup? rest parameter

/-- Instantiate rigid parameters; flexible inference variables are untouched. -/
def apply (substitution : ParameterSubstitution) : Ty → Ty
  | .variable metavariable => .variable metavariable
  | .parameter parameter =>
      substitution.lookup? parameter |>.getD (.parameter parameter)
  | .constructor constructor => .constructor constructor
  | .application function argument =>
      .application (apply substitution function) (apply substitution argument)
  | .function parameter result =>
      .function (apply substitution parameter) (apply substitution result)
  | .product left right =>
      .product (apply substitution left) (apply substitution right)
  | .mapping key value =>
      .mapping (apply substitution key) (apply substitution value)
  | .proxy inner => .proxy (apply substitution inner)
  | .comptime inner => .comptime (apply substitution inner)
  | .error => .error

end ParameterSubstitution

/-- A flexible substitution keeps an element that a memory array admits. -/
theorem Substitution.arrayElementAllowed_apply (substitution : Substitution) {element : Ty}
    (allowed : element.arrayElementAllowed = true) :
    (substitution.apply element).arrayElementAllowed = true := by
  unfold Ty.arrayElementAllowed at allowed
  split at allowed <;> first | rfl | cases allowed

/-- A rigid substitution keeps an element that a memory array admits. -/
theorem ParameterSubstitution.arrayElementAllowed_apply (substitution : ParameterSubstitution)
    {element : Ty} (allowed : element.arrayElementAllowed = true) :
    (substitution.apply element).arrayElementAllowed = true := by
  unfold Ty.arrayElementAllowed at allowed
  split at allowed <;> first | rfl | cases allowed

/-- A flexible substitution keeps a base that a slice admits. -/
theorem Substitution.arraySliceBaseAllowed_apply (substitution : Substitution) {base : Ty}
    (allowed : base.arraySliceBaseAllowed = true) :
    (substitution.apply base).arraySliceBaseAllowed = true := by
  unfold Ty.arraySliceBaseAllowed at allowed
  split at allowed <;> first | rfl | cases allowed

/-- A rigid substitution keeps a base that a slice admits. -/
theorem ParameterSubstitution.arraySliceBaseAllowed_apply (substitution : ParameterSubstitution)
    {base : Ty} (allowed : base.arraySliceBaseAllowed = true) :
    (substitution.apply base).arraySliceBaseAllowed = true := by
  unfold Ty.arraySliceBaseAllowed at allowed
  split at allowed <;> first | rfl | cases allowed

end Solcore.TypeSystem
