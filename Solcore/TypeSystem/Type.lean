import Solcore.Resolved.Identity

/-! A small source-level type language.

`Core.Ty` remains the concrete runtime type language.  This language lives in
front of it and distinguishes flexible inference variables from rigid source
generic parameters. -/

set_option autoImplicit false

namespace Solcore.TypeSystem

/-- A flexible metavariable allocated by type inference. -/
structure TypeVarId where
  index : Nat
  deriving Repr, DecidableEq

/-- A rigid generic parameter owned by one resolved declaration. -/
structure TypeParameterId where
  owner : Resolved.DeclarationId
  index : Nat
  deriving Repr, DecidableEq

/-- Built-ins which do not need declaration identities in the first slice. -/
inductive BuiltinType where
  | unit
  | bool
  | word
  | integer
  deriving Repr, DecidableEq

/-- The stable identity at the head of a type application. -/
inductive TypeConstructorId where
  | builtin (type : BuiltinType)
  | declaration (id : Resolved.DeclarationId)
  deriving Repr, DecidableEq

/--
Semantic source types.  `variable` is flexible; `parameter` is rigid.
Nominal arguments are represented by left-associated `application` nodes.
-/
inductive Ty where
  | variable (id : TypeVarId)
  | parameter (id : TypeParameterId)
  | constructor (id : TypeConstructorId)
  | application (function argument : Ty)
  | function (parameter result : Ty)
  | product (left right : Ty)
  | mapping (key value : Ty)
  | proxy (inner : Ty)
  | comptime (inner : Ty)
  | error
  deriving Repr, DecidableEq

/-- Syntactic occurrence of one rigid declaration parameter in a type.
This low-level predicate is independent of substitution lookup and can be
shared by frontend collectors and declarative source semantics. -/
def TypeParameterOccurs (parameter : TypeParameterId) : Ty → Prop
  | .parameter candidate => candidate = parameter
  | .application function argument
  | .function function argument
  | .product function argument
  | .mapping function argument =>
      TypeParameterOccurs parameter function ∨
        TypeParameterOccurs parameter argument
  | .proxy inner
  | .comptime inner => TypeParameterOccurs parameter inner
  | .variable _
  | .constructor _
  | .error => False

namespace Ty

def unit : Ty := .constructor (.builtin .unit)

def bool : Ty := .constructor (.builtin .bool)

def word : Ty := .constructor (.builtin .word)

/-- The arbitrary-precision source integer type.  It is staged and therefore
does not by itself acquire a `Core.Ty` projection. -/
def integer : Ty := .constructor (.builtin .integer)

/-- Left-associated type application. -/
def applyMany (head : Ty) (arguments : List Ty) : Ty :=
  arguments.foldl Ty.application head

/-- A nominal declaration applied to zero or more type arguments. -/
def nominal (declaration : Resolved.DeclarationId) (arguments : List Ty := []) : Ty :=
  applyMany (.constructor (.declaration declaration)) arguments

/-- Right-associated products, with the conventional zero/singleton cases. -/
def productMany : List Ty → Ty
  | [] => unit
  | [type] => type
  | type :: types => .product type (productMany types)

private def insertVariable (variables : List TypeVarId) (metavariable : TypeVarId) :
    List TypeVarId :=
  if metavariable ∈ variables then variables else variables ++ [metavariable]

private def unionVariables (left right : List TypeVarId) : List TypeVarId :=
  right.foldl insertVariable left

/-- Flexible variables occurring in a type, in stable left-to-right order. -/
def freeVariables : Ty → List TypeVarId
  | .variable metavariable => [metavariable]
  | .parameter _
  | .constructor _
  | .error => []
  | .application leftPart rightPart
  | .function leftPart rightPart
  | .product leftPart rightPart
  | .mapping leftPart rightPart =>
      unionVariables leftPart.freeVariables rightPart.freeVariables
  | .proxy inner
  | .comptime inner => inner.freeVariables

private theorem insertVariable_nodup
    {variables : List TypeVarId} (metavariable : TypeVarId)
    (nodup : variables.Nodup) :
    (insertVariable variables metavariable).Nodup := by
  unfold insertVariable
  by_cases present : metavariable ∈ variables
  · rw [if_pos present]
    exact nodup
  · rw [if_neg present, List.nodup_append]
    refine ⟨nodup, by simp, ?_⟩
    intro candidate member
    simp only [List.mem_singleton]
    intro other other_eq same
    subst other
    exact present (same ▸ member)

private theorem unionVariables_nodup
    (right : List TypeVarId) {left : List TypeVarId}
    (nodup : left.Nodup) :
    (unionVariables left right).Nodup := by
  unfold unionVariables
  induction right generalizing left with
  | nil => exact nodup
  | cons head tail induction =>
      exact induction (insertVariable_nodup head nodup)

/-- The stable flexible-variable ledger of every source type contains each
metavariable at most once. -/
theorem freeVariables_nodup (type : Ty) : type.freeVariables.Nodup := by
  induction type with
  | «variable» | «parameter» | constructor | error => simp [freeVariables]
  | application left right leftInduction _
  | function left right leftInduction _
  | product left right leftInduction _
  | mapping left right leftInduction _ =>
      exact unionVariables_nodup right.freeVariables leftInduction
  | proxy inner induction
  | comptime inner induction => exact induction

/-- Every flexible variable in a type lies below the allocator bound. -/
def VariablesBelow (next : Nat) (type : Ty) : Prop :=
  ∀ metavariable, metavariable ∈ type.freeVariables →
    metavariable.index < next

/-- A type remains allocator-bounded when the bound grows. -/
theorem VariablesBelow.weaken
    {type : Ty} {lower upper : Nat}
    (below : VariablesBelow lower type) (bound : lower ≤ upper) :
    VariablesBelow upper type := by
  intro metavariable member
  exact Nat.lt_of_lt_of_le (below metavariable member) bound

private theorem mem_unionVariables_iff (metavariable : TypeVarId)
    (left right : List TypeVarId) :
    metavariable ∈ unionVariables left right ↔
      metavariable ∈ left ∨ metavariable ∈ right := by
  induction right generalizing left with
  | nil => simp [unionVariables]
  | cons head tail induction =>
      change metavariable ∈ unionVariables
          (if head ∈ left then left else left ++ [head]) tail ↔
        metavariable ∈ left ∨ metavariable ∈ head :: tail
      rw [induction]
      by_cases present : head ∈ left
      · simp only [if_pos present, List.mem_cons]
        constructor
        · rintro (member | member)
          · exact Or.inl member
          · exact Or.inr (Or.inr member)
        · rintro (member | same | member)
          · exact Or.inl member
          · exact Or.inl (by simpa [same] using present)
          · exact Or.inr member
      · simp [present, or_assoc]

@[simp] theorem mem_freeVariables_application_iff
    (metavariable : TypeVarId) (function argument : Ty) :
    metavariable ∈ (Ty.application function argument).freeVariables ↔
      metavariable ∈ function.freeVariables ∨
        metavariable ∈ argument.freeVariables := by
  exact mem_unionVariables_iff metavariable _ _

@[simp] theorem mem_freeVariables_function_iff
    (metavariable : TypeVarId) (parameter result : Ty) :
    metavariable ∈ (Ty.function parameter result).freeVariables ↔
      metavariable ∈ parameter.freeVariables ∨
        metavariable ∈ result.freeVariables := by
  exact mem_unionVariables_iff metavariable _ _

@[simp] theorem mem_freeVariables_product_iff
    (metavariable : TypeVarId) (left right : Ty) :
    metavariable ∈ (Ty.product left right).freeVariables ↔
      metavariable ∈ left.freeVariables ∨
        metavariable ∈ right.freeVariables := by
  exact mem_unionVariables_iff metavariable _ _

@[simp] theorem mem_freeVariables_mapping_iff
    (metavariable : TypeVarId) (key value : Ty) :
    metavariable ∈ (Ty.mapping key value).freeVariables ↔
      metavariable ∈ key.freeVariables ∨
        metavariable ∈ value.freeVariables := by
  exact mem_unionVariables_iff metavariable _ _

@[simp] theorem variablesBelow_variable_iff
    (next : Nat) (metavariable : TypeVarId) :
    VariablesBelow next (.variable metavariable) ↔
      metavariable.index < next := by
  simp [VariablesBelow, freeVariables]

@[simp] theorem variablesBelow_parameter
    (next : Nat) (parameter : TypeParameterId) :
    VariablesBelow next (.parameter parameter) := by
  simp [VariablesBelow, freeVariables]

@[simp] theorem variablesBelow_constructor
    (next : Nat) (constructor : TypeConstructorId) :
    VariablesBelow next (.constructor constructor) := by
  simp [VariablesBelow, freeVariables]

@[simp] theorem variablesBelow_application_iff
    (next : Nat) (function argument : Ty) :
    VariablesBelow next (.application function argument) ↔
      VariablesBelow next function ∧ VariablesBelow next argument := by
  constructor
  · intro below
    constructor
    · intro metavariable member
      exact below metavariable
        ((mem_freeVariables_application_iff metavariable function argument).mpr
          (Or.inl member))
    · intro metavariable member
      exact below metavariable
        ((mem_freeVariables_application_iff metavariable function argument).mpr
          (Or.inr member))
  · rintro ⟨functionBelow, argumentBelow⟩ metavariable member
    rw [mem_freeVariables_application_iff] at member
    exact member.elim (functionBelow metavariable) (argumentBelow metavariable)

@[simp] theorem variablesBelow_function_iff
    (next : Nat) (parameter result : Ty) :
    VariablesBelow next (.function parameter result) ↔
      VariablesBelow next parameter ∧ VariablesBelow next result := by
  constructor
  · intro below
    constructor
    · intro metavariable member
      exact below metavariable
        ((mem_freeVariables_function_iff metavariable parameter result).mpr
          (Or.inl member))
    · intro metavariable member
      exact below metavariable
        ((mem_freeVariables_function_iff metavariable parameter result).mpr
          (Or.inr member))
  · rintro ⟨parameterBelow, resultBelow⟩ metavariable member
    rw [mem_freeVariables_function_iff] at member
    exact member.elim (parameterBelow metavariable) (resultBelow metavariable)

@[simp] theorem variablesBelow_product_iff
    (next : Nat) (left right : Ty) :
    VariablesBelow next (.product left right) ↔
      VariablesBelow next left ∧ VariablesBelow next right := by
  constructor
  · intro below
    constructor
    · intro metavariable member
      exact below metavariable
        ((mem_freeVariables_product_iff metavariable left right).mpr
          (Or.inl member))
    · intro metavariable member
      exact below metavariable
        ((mem_freeVariables_product_iff metavariable left right).mpr
          (Or.inr member))
  · rintro ⟨leftBelow, rightBelow⟩ metavariable member
    rw [mem_freeVariables_product_iff] at member
    exact member.elim (leftBelow metavariable) (rightBelow metavariable)

@[simp] theorem variablesBelow_mapping_iff
    (next : Nat) (key value : Ty) :
    VariablesBelow next (.mapping key value) ↔
      VariablesBelow next key ∧ VariablesBelow next value := by
  constructor
  · intro below
    constructor
    · intro metavariable member
      exact below metavariable
        ((mem_freeVariables_mapping_iff metavariable key value).mpr
          (Or.inl member))
    · intro metavariable member
      exact below metavariable
        ((mem_freeVariables_mapping_iff metavariable key value).mpr
          (Or.inr member))
  · rintro ⟨keyBelow, valueBelow⟩ metavariable member
    rw [mem_freeVariables_mapping_iff] at member
    exact member.elim (keyBelow metavariable) (valueBelow metavariable)

@[simp] theorem variablesBelow_proxy_iff (next : Nat) (inner : Ty) :
    VariablesBelow next (.proxy inner) ↔ VariablesBelow next inner := by
  rfl

@[simp] theorem variablesBelow_comptime_iff (next : Nat) (inner : Ty) :
    VariablesBelow next (.comptime inner) ↔ VariablesBelow next inner := by
  rfl

@[simp] theorem variablesBelow_error (next : Nat) :
    VariablesBelow next .error := by
  simp [VariablesBelow, freeVariables]

/-- Whether a flexible metavariable occurs in a type. -/
def containsVariable (type : Ty) (metavariable : TypeVarId) : Bool :=
  type.freeVariables.contains metavariable

@[simp] theorem containsVariable_eq_false_iff
    (type : Ty) (metavariable : TypeVarId) :
    type.containsVariable metavariable = false ↔
      metavariable ∉ type.freeVariables := by
  simp [containsVariable]

/-- A fresh-variable lower bound strictly above every flexible variable. -/
def nextVariable (type : Ty) : Nat :=
  type.freeVariables.foldl (fun next metavariable => max next (metavariable.index + 1)) 0

private theorem foldl_nextVariable_mono
    (variables : List TypeVarId) (initial : Nat) :
    initial ≤ variables.foldl
      (fun next metavariable => max next (metavariable.index + 1)) initial := by
  induction variables generalizing initial with
  | nil => exact Nat.le_refl initial
  | cons metavariable variables induction =>
      exact Nat.le_trans (Nat.le_max_left initial (metavariable.index + 1))
        (induction (max initial (metavariable.index + 1)))

private theorem mem_index_lt_foldl_nextVariable
    (variables : List TypeVarId) (initial : Nat) {metavariable : TypeVarId}
    (member : metavariable ∈ variables) :
    metavariable.index < variables.foldl
      (fun next candidate => max next (candidate.index + 1)) initial := by
  induction variables generalizing initial with
  | nil => simp at member
  | cons head variables induction =>
      rw [List.foldl_cons]
      rcases List.mem_cons.mp member with same | member
      · subst head
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self metavariable.index)
          (foldl_nextVariable_mono variables
            (max initial (metavariable.index + 1)) |>
              Nat.le_trans (Nat.le_max_right initial
                (metavariable.index + 1)))
      · exact induction (max initial (head.index + 1)) member

/-- `nextVariable` is strictly above every flexible variable in the type. -/
theorem variablesBelow_nextVariable (type : Ty) :
    type.VariablesBelow type.nextVariable := by
  intro metavariable member
  exact mem_index_lt_foldl_nextVariable type.freeVariables 0 member

/-- Constructor-node size, used to choose a conservative unification budget. -/
def size : Ty → Nat
  | .variable _
  | .parameter _
  | .constructor _
  | .error => 1
  | .application left right
  | .function left right
  | .product left right
  | .mapping left right => left.size + right.size + 1
  | .proxy inner
  | .comptime inner => inner.size + 1

end Ty

end Solcore.TypeSystem
