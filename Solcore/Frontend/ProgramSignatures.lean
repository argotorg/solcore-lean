import Solcore.Frontend.ProgramTypeResolution
import Solcore.Frontend.ProgramInterfaces
import Solcore.Frontend.TraitResolution
import Solcore.TypeSystem.Scheme

/-!
# Program signatures

Source-connected function signatures and implementation rules, before any body is inferred. Main
declarations: `ProgramFunctionSignature`, `ProgramPredicate`, `ProgramSignatures`.
-/

/-!
Source-connected function signatures and implementation rules.

This layer deliberately stops before function-body inference.  It resolves the
types and trait predicates needed by that consumer, while keeping declaration
parameters rigid until a signature or implementation is instantiated.
-/

set_option autoImplicit false

namespace Solcore.Frontend

namespace BuiltinFunctionId

/-- Exact source spelling of one compiler-provided function. -/
def spelling : BuiltinFunctionId → String
  | .integerSub => "integerSub"
  | .wordFromInteger => "wordFromInteger"
  | .integerAdd => "integerAdd"
  | .integerEq => "integerEq"
  | .integerLt => "integerLt"
  | .integerMul => "integerMul"
  | .wordToInteger => "wordToInteger"
  | .fixedFromWord type => type.name
  | .fixedToWord _ => "Typedef.rep"
  | .wordIdentity => "Typedef"
  | .wordOpcode op => "std.opcodes." ++ op.name

/-- Whether a reference's name may denote the function: its spelling, or any name for an opcode,
which an import of `std.opcodes` binds, an alias among them, or upstream's `primAddWord`. -/
def namedBy (function : BuiltinFunctionId) (name : String) : Bool :=
  name == function.spelling || function.opcode?.isSome

/-- Exact compiler-function spellings remain pairwise distinct. -/
theorem all_spellings_nodup : (all.map spelling).Nodup := by
  simp [all, spelling, WordOpcode.all, WordOpcode.name]

/-- Fixed source parameter types of one compiler-provided function. -/
def parameterTypes : BuiltinFunctionId → List TypeSystem.Ty
  | .integerSub => [TypeSystem.Ty.integer, TypeSystem.Ty.integer]
  | .wordFromInteger => [TypeSystem.Ty.integer]
  | .integerAdd
  | .integerEq
  | .integerLt
  | .integerMul => [TypeSystem.Ty.integer, TypeSystem.Ty.integer]
  | .wordToInteger => [TypeSystem.Ty.word]
  | .fixedFromWord _ => [TypeSystem.Ty.word]
  | .fixedToWord type => [TypeSystem.Ty.fixed type]
  | .wordIdentity => [TypeSystem.Ty.word]
  | .wordOpcode op => List.replicate op.arity TypeSystem.Ty.word

/-- Fixed source result type of one compiler-provided function. -/
def returnType : BuiltinFunctionId → TypeSystem.Ty
  | .integerSub => TypeSystem.Ty.integer
  | .wordFromInteger => TypeSystem.Ty.word
  | .integerAdd => TypeSystem.Ty.integer
  | .integerEq
  | .integerLt => TypeSystem.Ty.bool
  | .integerMul => TypeSystem.Ty.integer
  | .wordToInteger => TypeSystem.Ty.integer
  | .fixedFromWord type => TypeSystem.Ty.fixed type
  | .fixedToWord _ | .wordIdentity | .wordOpcode _ => TypeSystem.Ty.word

/-- Exact monomorphic function type of one compiler-provided function. -/
def type (function : BuiltinFunctionId) : TypeSystem.Ty :=
  .function (TypeSystem.Ty.productMany function.parameterTypes)
    function.returnType

/-- The compiler-provided function has no rigid or flexible parameters. -/
def scheme (function : BuiltinFunctionId) : TypeSystem.Scheme :=
  .mono function.type

end BuiltinFunctionId

/-- Resolve the deliberately small exact bare compiler-function namespace: the
closures by their spelling, the opcode `add` by upstream's primitive name
`primAddWord`, then the conversions by their type's name. No other opcode has a
bare name. Like upstream's builtin terms, these come after the names a module
declares or imports, at both identifier sites (`builtinNamed?`). -/
def builtinFunctionNamed? (name : String) : Option BuiltinFunctionId :=
  match BuiltinFunctionId.all.find? fun function =>
      function.opcode?.isNone && function.spelling == name with
  | some function => some function
  | none =>
      if name = "primAddWord" then some (.wordOpcode .add)
      else (TypeSystem.FixedInteger.ofName? name).map .fixedFromWord

/-- The concrete trait-predicate representation used by whole-program source
checking. -/
abbrev ProgramPredicate :=
  TraitResolution.Predicate ProgramTraitId TypeSystem.Ty

/-- A source implementation after its trait and every type have resolved. -/
abbrev ProgramImplRule :=
  TraitResolution.ImplRule ProgramTraitId TypeSystem.Ty ProgramImplId

/-- A declaration type together with its source-level trait requirements.
`parameters` are rigid and are instantiated only when the declaration is used. -/
structure ConstrainedDeclarationScheme where
  parameters : List TypeSystem.TypeParameterId
  predicates : List ProgramPredicate
  body : TypeSystem.Ty
  deriving Repr, DecidableEq

/-- The result of consistently instantiating a constrained declaration. -/
structure InstantiatedConstrainedDeclaration where
  parameterSubstitution : TypeSystem.ParameterSubstitution
  predicates : List ProgramPredicate
  body : TypeSystem.Ty
  next : Nat
  deriving Repr, DecidableEq

namespace ProgramPredicate

/-- Replace rigid source parameters throughout one trait obligation. -/
def applyParameters (substitution : TypeSystem.ParameterSubstitution)
    (predicate : ProgramPredicate) : ProgramPredicate := {
  predicate with
  subject := substitution.apply predicate.subject
  arguments := predicate.arguments.map substitution.apply
}

end ProgramPredicate

namespace ConstrainedDeclarationScheme

private def freshParameterSubstitution :
    List TypeSystem.TypeParameterId → Nat →
      TypeSystem.ParameterSubstitution →
        TypeSystem.ParameterSubstitution × Nat
  | [], next, substitution => (substitution, next)
  | parameter :: parameters, next, substitution =>
      match substitution.lookup? parameter with
      | some _ => freshParameterSubstitution parameters next substitution
      | none =>
          freshParameterSubstitution parameters (next + 1)
            ((parameter, .variable ⟨next⟩) :: substitution)

private theorem freshParameterSubstitution_next_le
    (parameters : List TypeSystem.TypeParameterId) (next : Nat)
    (substitution : TypeSystem.ParameterSubstitution) :
    next ≤ (freshParameterSubstitution parameters next substitution).2 := by
  induction parameters generalizing next substitution with
  | nil => exact Nat.le_refl next
  | cons parameter parameters induction =>
      simp only [freshParameterSubstitution]
      split
      · exact induction next substitution
      · exact Nat.le_trans (Nat.le_succ next)
          (induction (next + 1)
            ((parameter, .variable ⟨next⟩) :: substitution))

private theorem freshParameterSubstitution_ranges_below
    (parameters : List TypeSystem.TypeParameterId) (next : Nat)
    (substitution : TypeSystem.ParameterSubstitution)
    (rangesBelow : ∀ {parameter replacement},
      (parameter, replacement) ∈ substitution →
        replacement.VariablesBelow next) :
    ∀ {parameter replacement},
      (parameter, replacement) ∈
          (freshParameterSubstitution parameters next substitution).1 →
        replacement.VariablesBelow
          (freshParameterSubstitution parameters next substitution).2 := by
  induction parameters generalizing next substitution with
  | nil => exact rangesBelow
  | cons parameter parameters induction =>
      cases found : substitution.lookup? parameter with
      | some existing =>
          simp only [freshParameterSubstitution, found]
          exact induction next substitution rangesBelow
      | none =>
          simp only [freshParameterSubstitution, found]
          apply induction (next + 1)
            ((parameter, .variable ⟨next⟩) :: substitution)
          intro candidate replacement member
          rcases List.mem_cons.mp member with same | member
          · cases same
            simp [TypeSystem.Ty.VariablesBelow,
              TypeSystem.Ty.freeVariables]
          · exact (rangesBelow member).weaken (Nat.le_succ next)

private theorem perm_append_cons {α : Type} (head : α) (left right : List α) :
    (left ++ head :: right).Perm (head :: left ++ right) := by
  induction left with
  | nil => simp
  | cons first rest induction =>
      exact (List.Perm.cons first induction).trans
        (List.Perm.swap head first (rest ++ right))

private theorem freshParameterSubstitution_domain_permutation
    (parameters : List TypeSystem.TypeParameterId) (next : Nat)
    (substitution : TypeSystem.ParameterSubstitution)
    (parametersUnique : parameters.Nodup)
    (substitutionUnique : (substitution.map Prod.fst).Nodup)
    (disjoint : ∀ parameter, parameter ∈ parameters →
      parameter ∉ substitution.map Prod.fst) :
    ((freshParameterSubstitution parameters next substitution).1.map Prod.fst).Perm
      (parameters ++ substitution.map Prod.fst) := by
  induction parameters generalizing next substitution with
  | nil => simp [freshParameterSubstitution]
  | cons parameter parameters induction =>
      simp only [List.nodup_cons] at parametersUnique
      rcases parametersUnique with ⟨parameterFresh, parametersUnique⟩
      have parameterAbsent : parameter ∉ substitution.map Prod.fst :=
        disjoint parameter (by simp)
      have lookupNone : substitution.lookup? parameter = none := by
        cases found : substitution.lookup? parameter with
        | none => rfl
        | some replacement =>
            have member :=
              TypeSystem.ParameterSubstitution.lookup?_eq_some_mem found
            exact False.elim (parameterAbsent
              (List.mem_map.mpr ⟨(parameter, replacement), member, rfl⟩))
      simp only [freshParameterSubstitution, lookupNone]
      have extendedUnique :
          (((parameter, TypeSystem.Ty.variable ⟨next⟩) :: substitution).map
              Prod.fst).Nodup := by
        simpa using And.intro parameterAbsent substitutionUnique
      have tailDisjoint : ∀ candidate, candidate ∈ parameters →
          candidate ∉
            (((parameter, TypeSystem.Ty.variable ⟨next⟩) :: substitution).map
              Prod.fst) := by
        intro candidate candidateMember
        intro member
        simp only [List.map_cons, List.mem_cons] at member
        rcases member with same | oldMember
        · exact parameterFresh (same.symm ▸ candidateMember)
        · exact disjoint candidate (by simp [candidateMember]) oldMember
      have result := induction (next + 1)
        ((parameter, TypeSystem.Ty.variable ⟨next⟩) :: substitution)
        parametersUnique extendedUnique tailDisjoint
      exact result.trans
        (perm_append_cons parameter parameters (substitution.map Prod.fst))

private theorem freshParameterSubstitution_range_is_variable
    (parameters : List TypeSystem.TypeParameterId) (next : Nat)
    (substitution : TypeSystem.ParameterSubstitution)
    (rangeIsVariable : ∀ parameter replacement,
      (parameter, replacement) ∈ substitution →
        ∃ metavariable, replacement = .variable metavariable) :
    ∀ parameter replacement,
      (parameter, replacement) ∈
          (freshParameterSubstitution parameters next substitution).1 →
        ∃ metavariable, replacement = .variable metavariable := by
  induction parameters generalizing next substitution with
  | nil =>
      simpa [freshParameterSubstitution] using rangeIsVariable
  | cons parameter parameters induction =>
      simp only [freshParameterSubstitution]
      split
      · exact induction next substitution rangeIsVariable
      · apply induction (next + 1)
          ((parameter, TypeSystem.Ty.variable ⟨next⟩) :: substitution)
        intro candidate replacement member
        rcases List.mem_cons.mp member with same | member
        · cases same
          exact ⟨⟨next⟩, rfl⟩
        · exact rangeIsVariable candidate replacement member

/-- Instantiate body and constraints with one shared fresh-variable mapping. -/
def instantiate (scheme : ConstrainedDeclarationScheme) (next : Nat) :
    InstantiatedConstrainedDeclaration :=
  let (substitution, next) :=
    freshParameterSubstitution scheme.parameters next []
  {
    parameterSubstitution := substitution
    predicates := scheme.predicates.map (ProgramPredicate.applyParameters substitution)
    body := substitution.apply scheme.body
    next
  }

/-- Constrained declaration instantiation never moves the fresh-variable
allocator backwards. -/
theorem instantiate_next_le
    (scheme : ConstrainedDeclarationScheme) (next : Nat) :
    next ≤ (scheme.instantiate next).next := by
  exact freshParameterSubstitution_next_le scheme.parameters next []

/-- Every rigid-parameter replacement generated by constrained declaration
instantiation lies below its returned allocator bound. -/
theorem instantiate_parameterSubstitution_range_variablesBelow
    (scheme : ConstrainedDeclarationScheme) (next : Nat) :
    ∀ {parameter replacement},
      (parameter, replacement) ∈
          (scheme.instantiate next).parameterSubstitution →
        replacement.VariablesBelow (scheme.instantiate next).next := by
  change ∀ {parameter replacement},
    (parameter, replacement) ∈
        (freshParameterSubstitution scheme.parameters next []).1 →
      replacement.VariablesBelow
        (freshParameterSubstitution scheme.parameters next []).2
  exact freshParameterSubstitution_ranges_below scheme.parameters next []
    (by simp)

/-- Instantiating a constrained declaration preserves flexible-variable
bounds, accounting for both pre-existing variables and freshly generated
rigid-parameter replacements. -/
theorem instantiate_body_variablesBelow
    (scheme : ConstrainedDeclarationScheme) (next : Nat)
    (bodyBelow : scheme.body.VariablesBelow next) :
    (scheme.instantiate next).body.VariablesBelow
      (scheme.instantiate next).next := by
  change
    ((freshParameterSubstitution scheme.parameters next []).1.apply
      scheme.body).VariablesBelow
        (freshParameterSubstitution scheme.parameters next []).2
  apply TypeSystem.ParameterSubstitution.apply_variables_below
  · exact freshParameterSubstitution_ranges_below scheme.parameters next []
      (by simp)
  · exact bodyBelow.weaken
      (freshParameterSubstitution_next_le scheme.parameters next [])

/-- A canonical constrained declaration instantiation covers every rigid
parameter exactly once.  Entry order is intentionally abstracted by
permutation because substitution lookup, rather than list order, is the
semantic interface. -/
theorem instantiate_parameterSubstitution_domain_permutation
    (scheme : ConstrainedDeclarationScheme) (next : Nat)
    (parametersUnique : scheme.parameters.Nodup) :
    ((scheme.instantiate next).parameterSubstitution.map Prod.fst).Perm
      scheme.parameters := by
  change
    ((freshParameterSubstitution scheme.parameters next []).1.map Prod.fst).Perm
      scheme.parameters
  simpa using freshParameterSubstitution_domain_permutation
    scheme.parameters next [] parametersUnique (by simp) (by simp)

/-- Every rigid-parameter replacement generated by declaration instantiation
is a fresh flexible metavariable.  Later unification may solve it, but the
initial shared substitution cannot contain recovery or malformed types. -/
theorem instantiate_parameterSubstitution_range_is_variable
    (scheme : ConstrainedDeclarationScheme) (next : Nat) :
    ∀ parameter replacement,
      (parameter, replacement) ∈
          (scheme.instantiate next).parameterSubstitution →
        ∃ metavariable, replacement = .variable metavariable := by
  change ∀ parameter replacement,
    (parameter, replacement) ∈
        (freshParameterSubstitution scheme.parameters next []).1 →
      ∃ metavariable, replacement = .variable metavariable
  exact freshParameterSubstitution_range_is_variable
    scheme.parameters next [] (by simp)

@[simp] theorem instantiate_predicates
    (scheme : ConstrainedDeclarationScheme) (next : Nat) :
    (scheme.instantiate next).predicates =
      scheme.predicates.map (ProgramPredicate.applyParameters
        (scheme.instantiate next).parameterSubstitution) := by
  rfl

@[simp] theorem instantiate_body
    (scheme : ConstrainedDeclarationScheme) (next : Nat) :
    (scheme.instantiate next).body =
      (scheme.instantiate next).parameterSubstitution.apply scheme.body := by
  rfl

end ConstrainedDeclarationScheme

/-- One named-function parameter after resolving its source type.  Staging is
kept independently from the ordinary semantic type so later consumers can
enforce the execution boundary without wrapping runtime values in `Ty.comptime`. -/
structure ProgramFunctionParameter where
  name : String
  type : TypeSystem.Ty
  comptime : Bool
  deriving Repr, BEq, DecidableEq

/-- A resolved top-level function signature plus its source body. -/
structure ProgramFunctionSignature where
  id : Resolved.DeclarationId
  name : String
  parameters : List ProgramFunctionParameter
  returnTypes : List TypeSystem.Ty
  returnComptime : Bool
  scheme : ConstrainedDeclarationScheme
  /-- The `where` predicates as written. `scheme.predicates` closes them under
  their superclasses: the body assumes the closure and its callers prove it,
  as upstream's local givens give their superclasses. These are the givens
  that upstream counts when two of them reach one goal. -/
  declaredPredicates : List ProgramPredicate := scheme.predicates
  source : Syntax.FunctionDecl
  deriving Repr

namespace ProgramFunctionSignature

/-- Source-order parameter names, retained as a compatibility projection. -/
def parameterNames (signature : ProgramFunctionSignature) : List String :=
  signature.parameters.map (·.name)

/-- Bare semantic parameter types, retained as a compatibility projection. -/
def parameterTypes (signature : ProgramFunctionSignature) : List TypeSystem.Ty :=
  signature.parameters.map (·.type)

/-- Source-order staging markers for the function parameters. -/
def parameterComptime (signature : ProgramFunctionSignature) : List Bool :=
  signature.parameters.map (·.comptime)

end ProgramFunctionSignature

/-- Stable identity of a trait method, kept distinct from every declaration and
implementation method identity. -/
structure ProgramTraitMethodId where
  trait : Resolved.DeclarationId
  methodIndex : Nat
  deriving Repr, BEq, DecidableEq

/-- Stable identity of an implementation method, kept distinct from the trait
method that it implements. -/
structure ProgramImplMethodId where
  implementation : Resolved.DeclarationId
  methodIndex : Nat
  deriving Repr, BEq, DecidableEq

/-- One resolved trait method.  The parameter types, result types, and method
predicates may mention the enclosing trait's rigid type parameters. -/
structure ProgramTraitMethodSignature where
  id : ProgramTraitMethodId
  name : String
  parameters : List ProgramFunctionParameter
  returnTypes : List TypeSystem.Ty
  returnComptime : Bool
  wherePredicates : List ProgramPredicate
  source : Syntax.TraitMethod
  /-- The `where` predicates as written. Once the catalog is built,
  `wherePredicates` closes them under their superclasses: what a caller proves,
  and so what an implementation method's body may assume. -/
  declaredWherePredicates : List ProgramPredicate := wherePredicates
  deriving Repr

namespace ProgramTraitMethodSignature

/-- Source-order parameter names, retained as a compatibility projection. -/
def parameterNames (signature : ProgramTraitMethodSignature) : List String :=
  signature.parameters.map (·.name)

/-- Bare semantic parameter types, retained as a compatibility projection. -/
def parameterTypes (signature : ProgramTraitMethodSignature) : List TypeSystem.Ty :=
  signature.parameters.map (·.type)

/-- Source-order staging markers for the trait method parameters. -/
def parameterComptime (signature : ProgramTraitMethodSignature) : List Bool :=
  signature.parameters.map (·.comptime)

end ProgramTraitMethodSignature

/-- One resolved implementation method and the trait method selected by its
name.  Its source body is retained for later runtime-evidence lowering. -/
structure ProgramImplMethodSignature where
  id : ProgramImplMethodId
  traitMethod : ProgramTraitMethodId
  name : String
  parameters : List ProgramFunctionParameter
  returnTypes : List TypeSystem.Ty
  returnComptime : Bool
  wherePredicates : List ProgramPredicate
  source : Syntax.ImplMethod
  /-- The `where` predicates as written. Once the catalog is built,
  `wherePredicates` adds their superclasses that a caller proves, as upstream
  projects them from their dictionaries. -/
  declaredWherePredicates : List ProgramPredicate := wherePredicates
  deriving Repr

namespace ProgramImplMethodSignature

/-- Source-order parameter names, retained as a compatibility projection. -/
def parameterNames (signature : ProgramImplMethodSignature) : List String :=
  signature.parameters.map (·.name)

/-- Bare semantic parameter types, retained as a compatibility projection. -/
def parameterTypes (signature : ProgramImplMethodSignature) : List TypeSystem.Ty :=
  signature.parameters.map (·.type)

/-- Source-order staging markers for the implementation method parameters. -/
def parameterComptime (signature : ProgramImplMethodSignature) : List Bool :=
  signature.parameters.map (·.comptime)

end ProgramImplMethodSignature

/-- Resolved signature catalog for one trait, preserving method source order. -/
structure ProgramTraitSignature where
  id : Resolved.DeclarationId
  name : String
  parameters : List TypeSystem.TypeParameterId
  wherePredicates : List ProgramPredicate
  methods : List ProgramTraitMethodSignature
  source : Syntax.TraitDecl
  deriving Repr

/-- A predicate's direct superclasses: its trait's own where predicates at the
predicate's arguments. -/
def superclassPredicatesIn (traits : List ProgramTraitSignature)
    (predicate : ProgramPredicate) : List ProgramPredicate :=
  match predicate.trait with
  | .declaration id =>
      match traits.find? fun trait => decide (trait.id = id) with
      | some trait => trait.wherePredicates.map
          (ProgramPredicate.applyParameters
            (trait.parameters.zip (predicate.subject :: predicate.arguments)))
      | none => []
  | .builtin _ => []

/-- The predicates and, transitively, their superclasses, in the order they are
first reached, within `fuel` rounds. -/
def closeUnderSuperclasses (traits : List ProgramTraitSignature) :
    Nat → List ProgramPredicate → List ProgramPredicate
  | 0, predicates => predicates
  | fuel + 1, predicates =>
      let added := ((predicates.flatMap (superclassPredicatesIn traits)).filter
        fun predicate => !predicates.contains predicate).eraseDups
      if added.isEmpty then predicates
      else closeUnderSuperclasses traits fuel (predicates ++ added)

/-- The closure of predicates under their superclasses, one round per trait and
one more. -/
def superclassClosure (traits : List ProgramTraitSignature)
    (predicates : List ProgramPredicate) : List ProgramPredicate :=
  closeUnderSuperclasses traits (traits.length + 1) predicates

theorem mem_closeUnderSuperclasses_of_mem {traits : List ProgramTraitSignature} :
    ∀ {fuel : Nat} {predicates : List ProgramPredicate} {predicate : ProgramPredicate},
      predicate ∈ predicates → predicate ∈ closeUnderSuperclasses traits fuel predicates
  | 0, _, _, member => member
  | fuel + 1, predicates, predicate, member => by
      simp only [closeUnderSuperclasses]
      split
      · exact member
      · exact mem_closeUnderSuperclasses_of_mem (List.mem_append_left _ member)

theorem mem_superclassClosure_of_mem {traits : List ProgramTraitSignature}
    {predicates : List ProgramPredicate} {predicate : ProgramPredicate}
    (member : predicate ∈ predicates) : predicate ∈ superclassClosure traits predicates :=
  mem_closeUnderSuperclasses_of_mem member

/-- Whether a predicate is in a list, by its decidable equality. -/
def predicateListed (predicates : List ProgramPredicate) (predicate : ProgramPredicate) :
    Bool :=
  predicates.any fun listed => decide (listed = predicate)

theorem mem_of_predicateListed {predicates : List ProgramPredicate}
    {predicate : ProgramPredicate} (listed : predicateListed predicates predicate = true) :
    predicate ∈ predicates := by
  obtain ⟨candidate, member, equal⟩ := List.any_eq_true.mp listed
  exact of_decide_eq_true equal ▸ member

namespace ProgramTraitMethodSignature

/-- Close the trait method's where predicates under their superclasses, keeping
them as written in `declaredWherePredicates`. A caller proves the closure, so
an implementation method's body may assume the superclasses of its own
predicates, as upstream projects them from their dictionaries. -/
def closeUnderSuperclasses (traits : List ProgramTraitSignature)
    (method : ProgramTraitMethodSignature) : ProgramTraitMethodSignature :=
  { method with wherePredicates := superclassClosure traits method.wherePredicates }

@[simp] theorem closeUnderSuperclasses_id (traits : List ProgramTraitSignature)
    (method : ProgramTraitMethodSignature) :
    (method.closeUnderSuperclasses traits).id = method.id := rfl

@[simp] theorem closeUnderSuperclasses_name (traits : List ProgramTraitSignature)
    (method : ProgramTraitMethodSignature) :
    (method.closeUnderSuperclasses traits).name = method.name := rfl

@[simp] theorem closeUnderSuperclasses_parameters (traits : List ProgramTraitSignature)
    (method : ProgramTraitMethodSignature) :
    (method.closeUnderSuperclasses traits).parameters = method.parameters := rfl

@[simp] theorem closeUnderSuperclasses_returnTypes (traits : List ProgramTraitSignature)
    (method : ProgramTraitMethodSignature) :
    (method.closeUnderSuperclasses traits).returnTypes = method.returnTypes := rfl

@[simp] theorem closeUnderSuperclasses_returnComptime (traits : List ProgramTraitSignature)
    (method : ProgramTraitMethodSignature) :
    (method.closeUnderSuperclasses traits).returnComptime = method.returnComptime := rfl

@[simp] theorem closeUnderSuperclasses_parameterTypes (traits : List ProgramTraitSignature)
    (method : ProgramTraitMethodSignature) :
    (method.closeUnderSuperclasses traits).parameterTypes = method.parameterTypes := rfl

@[simp] theorem closeUnderSuperclasses_parameterComptime
    (traits : List ProgramTraitSignature) (method : ProgramTraitMethodSignature) :
    (method.closeUnderSuperclasses traits).parameterComptime =
      method.parameterComptime := rfl

@[simp] theorem closeUnderSuperclasses_parameterNames (traits : List ProgramTraitSignature)
    (method : ProgramTraitMethodSignature) :
    (method.closeUnderSuperclasses traits).parameterNames = method.parameterNames := rfl

end ProgramTraitMethodSignature

namespace ProgramTraitSignature

/-- Close each of the trait's methods' where predicates under their
superclasses (`ProgramTraitMethodSignature.closeUnderSuperclasses`). -/
def closeMethodsUnderSuperclasses (traits : List ProgramTraitSignature)
    (trait : ProgramTraitSignature) : ProgramTraitSignature :=
  { trait with
    methods := trait.methods.map (ProgramTraitMethodSignature.closeUnderSuperclasses traits) }

@[simp] theorem closeMethodsUnderSuperclasses_id (traits : List ProgramTraitSignature)
    (trait : ProgramTraitSignature) :
    (trait.closeMethodsUnderSuperclasses traits).id = trait.id := rfl

@[simp] theorem closeMethodsUnderSuperclasses_name (traits : List ProgramTraitSignature)
    (trait : ProgramTraitSignature) :
    (trait.closeMethodsUnderSuperclasses traits).name = trait.name := rfl

@[simp] theorem closeMethodsUnderSuperclasses_parameters (traits : List ProgramTraitSignature)
    (trait : ProgramTraitSignature) :
    (trait.closeMethodsUnderSuperclasses traits).parameters = trait.parameters := rfl

@[simp] theorem closeMethodsUnderSuperclasses_wherePredicates
    (traits : List ProgramTraitSignature) (trait : ProgramTraitSignature) :
    (trait.closeMethodsUnderSuperclasses traits).wherePredicates = trait.wherePredicates := rfl

@[simp] theorem closeMethodsUnderSuperclasses_methods (traits : List ProgramTraitSignature)
    (trait : ProgramTraitSignature) :
    (trait.closeMethodsUnderSuperclasses traits).methods =
      trait.methods.map (ProgramTraitMethodSignature.closeUnderSuperclasses traits) := rfl

end ProgramTraitSignature

namespace ProgramImplMethodSignature

/-- Add to an implementation method's where predicates their superclasses among
`provided`, the predicates that its caller and its implementation's use sites
prove, keeping them as written in `declaredWherePredicates`. -/
def closeUnderSuperclasses (traits : List ProgramTraitSignature)
    (provided : List ProgramPredicate) (method : ProgramImplMethodSignature) :
    ProgramImplMethodSignature :=
  { method with
    wherePredicates := method.wherePredicates ++
      (superclassClosure traits method.wherePredicates).filter fun predicate =>
        !predicateListed method.wherePredicates predicate &&
          predicateListed provided predicate }

@[simp] theorem closeUnderSuperclasses_id (traits : List ProgramTraitSignature)
    (provided : List ProgramPredicate) (method : ProgramImplMethodSignature) :
    (method.closeUnderSuperclasses traits provided).id = method.id := rfl

@[simp] theorem closeUnderSuperclasses_traitMethod (traits : List ProgramTraitSignature)
    (provided : List ProgramPredicate) (method : ProgramImplMethodSignature) :
    (method.closeUnderSuperclasses traits provided).traitMethod = method.traitMethod := rfl

@[simp] theorem closeUnderSuperclasses_name (traits : List ProgramTraitSignature)
    (provided : List ProgramPredicate) (method : ProgramImplMethodSignature) :
    (method.closeUnderSuperclasses traits provided).name = method.name := rfl

@[simp] theorem closeUnderSuperclasses_parameters (traits : List ProgramTraitSignature)
    (provided : List ProgramPredicate) (method : ProgramImplMethodSignature) :
    (method.closeUnderSuperclasses traits provided).parameters = method.parameters := rfl

@[simp] theorem closeUnderSuperclasses_returnTypes (traits : List ProgramTraitSignature)
    (provided : List ProgramPredicate) (method : ProgramImplMethodSignature) :
    (method.closeUnderSuperclasses traits provided).returnTypes = method.returnTypes := rfl

@[simp] theorem closeUnderSuperclasses_returnComptime (traits : List ProgramTraitSignature)
    (provided : List ProgramPredicate) (method : ProgramImplMethodSignature) :
    (method.closeUnderSuperclasses traits provided).returnComptime =
      method.returnComptime := rfl

@[simp] theorem closeUnderSuperclasses_source (traits : List ProgramTraitSignature)
    (provided : List ProgramPredicate) (method : ProgramImplMethodSignature) :
    (method.closeUnderSuperclasses traits provided).source = method.source := rfl

@[simp] theorem closeUnderSuperclasses_parameterTypes (traits : List ProgramTraitSignature)
    (provided : List ProgramPredicate) (method : ProgramImplMethodSignature) :
    (method.closeUnderSuperclasses traits provided).parameterTypes =
      method.parameterTypes := rfl

@[simp] theorem closeUnderSuperclasses_parameterComptime
    (traits : List ProgramTraitSignature) (provided : List ProgramPredicate)
    (method : ProgramImplMethodSignature) :
    (method.closeUnderSuperclasses traits provided).parameterComptime =
      method.parameterComptime := rfl

@[simp] theorem closeUnderSuperclasses_parameterNames (traits : List ProgramTraitSignature)
    (provided : List ProgramPredicate) (method : ProgramImplMethodSignature) :
    (method.closeUnderSuperclasses traits provided).parameterNames =
      method.parameterNames := rfl

/-- Each predicate of the closed method is one of its own or one provided. -/
theorem mem_closeUnderSuperclasses {traits : List ProgramTraitSignature}
    {provided : List ProgramPredicate} {method : ProgramImplMethodSignature}
    {predicate : ProgramPredicate}
    (member : predicate ∈ (method.closeUnderSuperclasses traits provided).wherePredicates) :
    predicate ∈ method.wherePredicates ∨ predicate ∈ provided := by
  simp only [closeUnderSuperclasses] at member
  rcases List.mem_append.mp member with own | added
  · exact Or.inl own
  · have selected := (List.mem_filter.mp added).2
    simp only [Bool.and_eq_true] at selected
    exact Or.inr (mem_of_predicateListed selected.2)

end ProgramImplMethodSignature

/-- The declared givens that reach a goal, directly or through their
superclasses, each counted once. -/
def givensReaching (traits : List ProgramTraitSignature)
    (declared : List ProgramPredicate) (goal : ProgramPredicate) :
    List ProgramPredicate :=
  declared.eraseDups.filter fun given =>
    (superclassClosure traits [given]).contains goal

/-- Upstream's projection ambiguity (`SC0208`), the one place Lean tests it: a
goal that two different declared givens reach, directly or through their
superclasses, is ambiguous where it is used. Upstream ranks every answer rooted
at a local given alike, so a given that states the superclass is one more
candidate, while paths from one given and equal givens are one. -/
def reachedByTwoGivens (traits : List ProgramTraitSignature)
    (declared : List ProgramPredicate) (goal : ProgramPredicate) : Bool :=
  1 < (givensReaching traits declared goal).length

/-- Structural facts fixed by trait-method collection itself.  These do not
depend on the later declarative judgments for method types or predicates. -/
structure TraitSignatureStructuralWellFormed
    (signature : ProgramTraitSignature) : Prop where
  method_names_nodup :
    (signature.methods.map fun method => method.name).Nodup
  method_owners : ∀ method, method ∈ signature.methods →
    method.id.trait = signature.id
  method_positions : ∀ index : Fin signature.methods.length,
    (signature.methods.get index).id.methodIndex = index.val
  method_parameter_names_nodup : ∀ method,
    method ∈ signature.methods → method.parameterNames.Nodup

/-- Resolved signature catalog for one implementation, preserving method source
order and the parsed method bodies. -/
structure ProgramImplementationSignature where
  id : Resolved.DeclarationId
  /-- Whether the source declaration used the `default impl` marker. -/
  isDefault : Bool := false
  parameters : List TypeSystem.TypeParameterId
  head : ProgramPredicate
  wherePredicates : List ProgramPredicate
  /-- The `where` predicates as written. `wherePredicates` closes them under
  their superclasses: the premises that use sites prove and that method bodies
  assume. -/
  declaredWherePredicates : List ProgramPredicate := wherePredicates
  methods : List ProgramImplMethodSignature
  source : Syntax.ImplDecl
  deriving Repr

/-- Structural facts fixed by implementation-method collection itself.  Trait
method correspondence and the semantic formation of method types remain
separate obligations. -/
structure ImplementationSignatureStructuralWellFormed
    (signature : ProgramImplementationSignature) : Prop where
  method_names_nodup :
    (signature.methods.map fun method => method.name).Nodup
  method_owners : ∀ method, method ∈ signature.methods →
    method.id.implementation = signature.id
  method_positions : ∀ index : Fin signature.methods.length,
    (signature.methods.get index).id.methodIndex = index.val
  method_parameter_names_nodup : ∀ method,
    method ∈ signature.methods → method.parameterNames.Nodup

/-- Head-level checks fixed by implementation signature collection.  This
retains the exact trait entry selected by the collector so later semantic
proofs can recover arity, substitution, and method-catalog facts without
replaying name resolution. -/
structure ImplementationSignatureHeadValidated
    (traits : List ProgramTraitSignature)
    (signature : ProgramImplementationSignature) : Prop where
  parameters_in_head : ∀ parameter, parameter ∈ signature.parameters →
    parameter ∈ TypedTraitResolution.predicateParameters signature.head
  trait_catalog : ∃ trait ∈ traits,
    signature.head.trait = .declaration trait.id ∧
    let substitution : TypeSystem.ParameterSubstitution :=
      trait.parameters.zip
        (signature.head.subject :: signature.head.arguments)
    ∀ predicate, predicate ∈ trait.wherePredicates.map
      (ProgramPredicate.applyParameters substitution) →
      predicate ∈ signature.wherePredicates

/-- Method-to-trait correspondence fixed by required-method validation and
trait-method attachment.  Completeness is stated for the exact trait selected
while collecting the implementation; catalog-wide trait identity uniqueness
allows later semantic consumers to transport it to any equal-headed entry.
Each method's predicates are among its trait method's, instantiated at the
head, and the implementation's own. -/
structure ImplementationSignatureMethodCatalogValidated
    (traits : List ProgramTraitSignature)
    (signature : ProgramImplementationSignature) : Prop where
  trait_catalog : ∃ trait ∈ traits,
    signature.head.trait = .declaration trait.id ∧
    (∀ method, method ∈ signature.methods →
      ∃ traitMethod, traitMethod ∈ trait.methods ∧
        traitMethod.id = method.traitMethod ∧
        traitMethod.name = method.name ∧
        let substitution : TypeSystem.ParameterSubstitution :=
          trait.parameters.zip
            (signature.head.subject :: signature.head.arguments)
        method.parameterTypes =
          traitMethod.parameterTypes.map substitution.apply ∧
        method.returnTypes =
          traitMethod.returnTypes.map substitution.apply ∧
        method.parameterComptime = traitMethod.parameterComptime ∧
        method.returnComptime = traitMethod.returnComptime ∧
        ∀ predicate, predicate ∈ method.wherePredicates →
          predicate ∈ traitMethod.wherePredicates.map
            (ProgramPredicate.applyParameters substitution) ++
              signature.wherePredicates) ∧
    (∀ traitMethod, traitMethod ∈ trait.methods →
      ∃ method ∈ signature.methods, method.traitMethod = traitMethod.id)

private def TraitSignaturesStructurallyWellFormed
    (traits : List ProgramTraitSignature) : Prop :=
  ∀ signature, signature ∈ traits →
    TraitSignatureStructuralWellFormed signature

/-- Stable source identity of one constructor within an algebraic data
declaration.  Constructor order is semantic because Core data values retain
the same zero-based tag. -/
structure ProgramDataConstructorId where
  dataType : Resolved.DeclarationId
  constructorIndex : Nat
  deriving Repr, BEq, ReflBEq, LawfulBEq, DecidableEq

/-- One constructor after resolving every positional payload type in the
generic scope of its owning data declaration. -/
structure ProgramDataConstructorSignature where
  id : ProgramDataConstructorId
  name : String
  payloadTypes : List TypeSystem.Ty
  source : Syntax.EnumConstructor
  deriving Repr

/-- A resolved top-level algebraic data declaration.  `parameters` retain
declaration order and constructor order is preserved exactly from source. -/
structure ProgramDataSignature where
  id : Resolved.DeclarationId
  name : String
  parameters : List TypeSystem.TypeParameterId
  constructors : List ProgramDataConstructorSignature
  source : Syntax.EnumDecl
  deriving Repr

/-- Structural facts fixed by data-constructor collection itself.  These do
not depend on the later declarative judgment for constructor payload types. -/
structure DataSignatureStructuralWellFormed
    (signature : ProgramDataSignature) : Prop where
  constructor_names_nodup :
    (signature.constructors.map fun constructor => constructor.name).Nodup
  constructor_owners : ∀ constructor, constructor ∈ signature.constructors →
    constructor.id.dataType = signature.id
  constructor_positions : ∀ index : Fin signature.constructors.length,
    (signature.constructors.get index).id.constructorIndex = index.val

/-- A resolved top-level contract declaration. Contract members remain
separate from the data-constructor and pattern catalogs; this carrier records
only the declaration identity and its generic scope. -/
structure ProgramContractSignature where
  id : Resolved.DeclarationId
  name : String
  parameters : List TypeSystem.TypeParameterId
  source : Syntax.ContractDecl
  deriving Repr

namespace ProgramImplementationSignature

/-- Exact generic assumptions available while checking one implementation
method.  Trait predicates are instantiated at the implementation head before
the implementation- and method-level predicates are appended in source
semantic order. -/
def methodAssumptions
    (implementation : ProgramImplementationSignature)
    (trait : ProgramTraitSignature)
    (method : ProgramImplMethodSignature) : List ProgramPredicate :=
  let traitSubstitution : TypeSystem.ParameterSubstitution :=
    trait.parameters.zip
      (implementation.head.subject :: implementation.head.arguments)
  trait.wherePredicates.map
      (ProgramPredicate.applyParameters traitSubstitution) ++
    implementation.wherePredicates ++ method.wherePredicates

/-- Backward-compatible trait-search projection of an implementation catalog. -/
def implRule (implementation : ProgramImplementationSignature) :
    ProgramImplRule := {
  id := implementation.id
  head := implementation.head
  wherePredicates := implementation.wherePredicates
  isDefault := implementation.isDefault
}

/-- Present an implementation method to the existing function-body checker.
The implementation declaration owns every rigid parameter, while declaration-
and method-level predicates are assumptions for the synthetic function body. -/
def functionSignatureOfMethod
    (implementation : ProgramImplementationSignature)
    (method : ProgramImplMethodSignature) : ProgramFunctionSignature := {
  id := implementation.id
  name := method.name
  parameters := method.parameters
  returnTypes := method.returnTypes
  returnComptime := method.returnComptime
  scheme := {
    parameters := implementation.parameters
    predicates := implementation.wherePredicates ++ method.wherePredicates
    body := .function
      (TypeSystem.Ty.productMany method.parameterTypes)
      (TypeSystem.Ty.productMany method.returnTypes)
  }
  declaredPredicates := implementation.declaredWherePredicates ++ method.declaredWherePredicates
  source := method.source.value.declaration
}

/-- Present an implementation method to the ordinary body checker with the
same trait-, implementation-, and method-level assumptions used by the source
semantics. -/
def functionSignatureOfMethodWithTrait
    (implementation : ProgramImplementationSignature)
    (trait : ProgramTraitSignature)
    (method : ProgramImplMethodSignature) : ProgramFunctionSignature :=
  let signature := implementation.functionSignatureOfMethod method
  {
    signature with
    scheme := {
      signature.scheme with
      predicates := implementation.methodAssumptions trait method
    }
    declaredPredicates := implementation.declaredWherePredicates ++ method.declaredWherePredicates
  }

/-- The predicates that a caller proves for one of the implementation's
methods: its trait method's, closed under their superclasses
(`ProgramTraitMethodSignature.closeUnderSuperclasses`) and instantiated at the
head. The trait is the one with the head's identity and the trait method the
one with the method's name, each only when it is the only one. -/
def inheritedMethodPredicates (traits : List ProgramTraitSignature)
    (implementation : ProgramImplementationSignature)
    (method : ProgramImplMethodSignature) : List ProgramPredicate :=
  match traits.filter fun trait => decide (implementation.head.trait = .declaration trait.id) with
  | [trait] =>
      match trait.methods.filter fun traitMethod => traitMethod.name == method.name with
      | [traitMethod] => (superclassClosure traits traitMethod.wherePredicates).map
          (ProgramPredicate.applyParameters
            (trait.parameters.zip
              (implementation.head.subject :: implementation.head.arguments)))
      | _ => []
  | _ => []

/-- Close the implementation's conditions under their superclasses, and add to
each method's predicates their superclasses that its caller or the
implementation's use sites prove, keeping both as written in
`declaredWherePredicates`. -/
def closeUnderSuperclasses (traits : List ProgramTraitSignature)
    (implementation : ProgramImplementationSignature) :
    ProgramImplementationSignature :=
  let conditions := superclassClosure traits implementation.wherePredicates
  {
    implementation with
    wherePredicates := conditions
    declaredWherePredicates := implementation.declaredWherePredicates
    methods := implementation.methods.map fun method =>
      method.closeUnderSuperclasses traits
        (implementation.inheritedMethodPredicates traits method ++ conditions)
  }

@[simp] theorem closeUnderSuperclasses_id (traits : List ProgramTraitSignature)
    (implementation : ProgramImplementationSignature) :
    (implementation.closeUnderSuperclasses traits).id = implementation.id := rfl

@[simp] theorem closeUnderSuperclasses_head (traits : List ProgramTraitSignature)
    (implementation : ProgramImplementationSignature) :
    (implementation.closeUnderSuperclasses traits).head = implementation.head := rfl

@[simp] theorem closeUnderSuperclasses_parameters (traits : List ProgramTraitSignature)
    (implementation : ProgramImplementationSignature) :
    (implementation.closeUnderSuperclasses traits).parameters = implementation.parameters := rfl

@[simp] theorem closeUnderSuperclasses_methods (traits : List ProgramTraitSignature)
    (implementation : ProgramImplementationSignature) :
    (implementation.closeUnderSuperclasses traits).methods =
      implementation.methods.map fun method =>
        method.closeUnderSuperclasses traits
          (implementation.inheritedMethodPredicates traits method ++
            superclassClosure traits implementation.wherePredicates) := rfl

end ProgramImplementationSignature

/-- The closure keeps every condition, so the trait's restated where
predicates stay among them. -/
theorem ImplementationSignatureHeadValidated.closeUnderSuperclasses
    {traits catalog : List ProgramTraitSignature}
    {signature : ProgramImplementationSignature}
    (validated : ImplementationSignatureHeadValidated traits signature) :
    ImplementationSignatureHeadValidated traits
      (signature.closeUnderSuperclasses catalog) := by
  obtain ⟨parameters, trait, member, headTrait, required⟩ := validated
  exact ⟨parameters, trait, member, headTrait, fun predicate requiredMember =>
    mem_superclassClosure_of_mem (required predicate requiredMember)⟩

/-- Closing the traits' methods keeps their where predicates, so an
implementation's head stays validated against the closed catalog. -/
theorem ImplementationSignatureHeadValidated.closeTraits
    {traits catalog : List ProgramTraitSignature}
    {signature : ProgramImplementationSignature}
    (validated : ImplementationSignatureHeadValidated traits signature) :
    ImplementationSignatureHeadValidated
      (traits.map (ProgramTraitSignature.closeMethodsUnderSuperclasses catalog)) signature := by
  obtain ⟨parameters, trait, member, headTrait, required⟩ := validated
  exact ⟨parameters, trait.closeMethodsUnderSuperclasses catalog, List.mem_map_of_mem member,
    headTrait, required⟩

namespace ProgramFunctionSignature

/-- Close the function's predicates under their superclasses, keeping them as
written in `declaredPredicates`. -/
def closeUnderSuperclasses (traits : List ProgramTraitSignature)
    (signature : ProgramFunctionSignature) : ProgramFunctionSignature := {
  signature with
  scheme := {
    signature.scheme with
    predicates := superclassClosure traits signature.scheme.predicates
  }
  declaredPredicates := signature.scheme.predicates
}

@[simp] theorem closeUnderSuperclasses_id (traits : List ProgramTraitSignature)
    (signature : ProgramFunctionSignature) :
    (signature.closeUnderSuperclasses traits).id = signature.id := rfl

end ProgramFunctionSignature

/-- The declarations needed by source expression inference, trait search, and
later trait-evidence execution. `functions` and `implRules` remain source-only
catalog projections; `ProgramSignatures.resolutionRules` adds compiler rules. -/
structure ProgramSignatures where
  functions : List ProgramFunctionSignature
  implRules : List ProgramImplRule
  traits : List ProgramTraitSignature
  implementations : List ProgramImplementationSignature
  dataTypes : List ProgramDataSignature := []
  contracts : List ProgramContractSignature := []
  deriving Repr

/-- One declaration-owned rigid-parameter row has no duplicate identities,
retains its declaration owner, and uses the source position as its stable
zero-based index. -/
structure SignatureParametersWellFormed
    (owner : Resolved.DeclarationId)
    (parameters : List TypeSystem.TypeParameterId) : Prop where
  parameters_nodup : parameters.Nodup
  parameter_owners : ∀ parameter, parameter ∈ parameters →
    parameter.owner = owner
  parameter_positions : ∀ index : Fin parameters.length,
    (parameters.get index).index = index.val

/-- The declaration-owned rigid parameters of every declaration-backed
signature category satisfy the same canonical allocation contract. -/
structure ProgramSignatureParametersWellFormed
    (signatures : ProgramSignatures) : Prop where
  functions : ∀ signature, signature ∈ signatures.functions →
    SignatureParametersWellFormed signature.id signature.scheme.parameters
  dataTypes : ∀ signature, signature ∈ signatures.dataTypes →
    SignatureParametersWellFormed signature.id signature.parameters
  traits : ∀ signature, signature ∈ signatures.traits →
    SignatureParametersWellFormed signature.id signature.parameters
  implementations : ∀ signature, signature ∈ signatures.implementations →
    SignatureParametersWellFormed signature.id signature.parameters
  contracts : ∀ signature, signature ∈ signatures.contracts →
    SignatureParametersWellFormed signature.id signature.parameters

namespace ProgramSignatures

/-- The exact unary builtin `Int` obligation for a selected result type. -/
def builtinIntPredicate (subject : TypeSystem.Ty) : ProgramPredicate := {
  trait := .builtin .int
  subject
  arguments := []
}

/-- Primitive `Int<Word>` evidence.  Builtins are deliberately separate from
the source implementation catalog because they have no source declaration or
method body. -/
def builtinIntWordRule : ProgramImplRule := {
  id := .builtin .intWord
  head := builtinIntPredicate .word
  wherePredicates := []
}

/-- Primitive `Int<integer>` evidence retained for staged literal payloads. -/
def builtinIntIntegerRule : ProgramImplRule := {
  id := .builtin .intInteger
  head := builtinIntPredicate .integer
  wherePredicates := []
}

/-- Primitive `Int<uintN>` and `Int<intN>` evidence for the twelve fixed-width
integer types. -/
def builtinIntFixedRule (type : TypeSystem.FixedInteger) : ProgramImplRule := {
  id := .builtin (.intFixed type)
  head := builtinIntPredicate (.fixed type)
  wherePredicates := []
}

/-- Compiler-provided rules in stable resolution order. -/
def builtinResolutionRules : List ProgramImplRule :=
  [builtinIntWordRule, builtinIntIntegerRule] ++
    TypeSystem.FixedInteger.all.map builtinIntFixedRule

/-- The complete trait-resolution view.  Primitive rules precede source rules,
while `implRules` itself remains the source-only catalog projection. -/
def resolutionRules (signatures : ProgramSignatures) : List ProgramImplRule :=
  builtinResolutionRules ++ signatures.implRules

/-- Preserve every overload with an exact unqualified spelling. -/
def functionsNamed (signatures : ProgramSignatures)
    (name : String) : List ProgramFunctionSignature :=
  signatures.functions.filter fun signature => signature.name == name

/-- Preserve every overload with an exact spelling in one module. -/
def localFunctionsNamed (signatures : ProgramSignatures)
    (moduleId : Workspace.ModuleId) (name : String) :
    List ProgramFunctionSignature :=
  signatures.functions.filter fun signature =>
    decide (signature.id.moduleId = moduleId) && signature.name == name

/-- Look up one resolved trait catalog entry by declaration identity. -/
def trait? (signatures : ProgramSignatures)
    (id : Resolved.DeclarationId) : Option ProgramTraitSignature :=
  signatures.traits.find? fun trait => decide (trait.id = id)

/-- Look up one resolved implementation catalog entry by declaration identity. -/
def implementation? (signatures : ProgramSignatures)
    (id : Resolved.DeclarationId) : Option ProgramImplementationSignature :=
  signatures.implementations.find? fun implementation =>
    decide (implementation.id = id)

/-- Look up one trait method by its role-tagged stable identity. -/
def traitMethod? (signatures : ProgramSignatures)
    (id : ProgramTraitMethodId) : Option ProgramTraitMethodSignature := do
  let trait ← signatures.trait? id.trait
  trait.methods.find? fun method => decide (method.id = id)

/-- Look up one implementation method by its role-tagged stable identity. -/
def implMethod? (signatures : ProgramSignatures)
    (id : ProgramImplMethodId) : Option ProgramImplMethodSignature := do
  let implementation ← signatures.implementation? id.implementation
  implementation.methods.find? fun method => decide (method.id = id)

/-- Look up one algebraic data declaration by stable declaration identity. -/
def dataType? (signatures : ProgramSignatures)
    (id : Resolved.DeclarationId) : Option ProgramDataSignature :=
  signatures.dataTypes.find? fun dataType => decide (dataType.id = id)

/-- Look up one contract declaration by stable declaration identity. -/
def contract? (signatures : ProgramSignatures)
    (id : Resolved.DeclarationId) : Option ProgramContractSignature :=
  signatures.contracts.find? fun contract => decide (contract.id = id)

/-- Preserve source order when finding constructors with an exact spelling. -/
def constructorsNamed (signatures : ProgramSignatures)
    (name : String) : List ProgramDataConstructorSignature :=
  signatures.dataTypes.flatMap fun dataType =>
    dataType.constructors.filter fun constructor => constructor.name == name

/-- Recover the owning data declaration of one constructor identity. -/
def constructor? (signatures : ProgramSignatures)
    (id : ProgramDataConstructorId) : Option ProgramDataConstructorSignature := do
  let dataType ← signatures.dataType? id.dataType
  dataType.constructors.find? fun constructor => decide (constructor.id = id)

end ProgramSignatures

/-- Failures while turning cataloged declarations into typed signatures. -/
inductive ProgramSignatureError where
  | duplicateFunctionParameter
      (declaration : Resolved.DeclarationId)
      (name : String) (firstIndex duplicateIndex : Nat)
  | malformedFunctionParameter
      (declaration : Resolved.DeclarationId) (parameterIndex : Nat)
  | malformedType (declaration : Resolved.DeclarationId)
  | nestedComptimeReturn
      (declaration : Resolved.DeclarationId) (returnIndex : Nat)
  | comptimeReturnMustBeSingleton
      (declaration : Resolved.DeclarationId)
      (returnIndex returnCount : Nat)
  | unknownTrait
      (declaration : Resolved.DeclarationId) (name : String)
  | ambiguousTrait
      (declaration : Resolved.DeclarationId) (name : String)
      (candidates : List Resolved.DeclarationId)
  | traitArityMismatch
      (declaration trait : Resolved.DeclarationId)
      (expected actual : Nat)
  | importVisibility
      (declaration : Resolved.DeclarationId)
      (errors : List ProgramImportError)
  | typeResolution
      (declaration : Resolved.DeclarationId)
      (error : ProgramTypeResolutionError)
  | traitMethodLocalGenerics (method : ProgramTraitMethodId)
  | implMethodLocalGenerics (method : ProgramImplMethodId)
  | duplicateTraitMethod
      (trait : Resolved.DeclarationId) (name : String)
      (firstIndex duplicateIndex : Nat)
  | duplicateImplMethod
      (implementation : Resolved.DeclarationId) (name : String)
      (firstIndex duplicateIndex : Nat)
  | missingImplMethod
      (implementation : Resolved.DeclarationId)
      (method : ProgramTraitMethodId) (name : String)
  | extraImplMethod (method : ProgramImplMethodId) (name : String)
  | implMethodSignatureMismatch
      (method : ProgramImplMethodId) (traitMethod : ProgramTraitMethodId)
      (expectedParameters actualParameters : List TypeSystem.Ty)
      (expectedReturns actualReturns : List TypeSystem.Ty)
  | implMethodComptimeMismatch
      (method : ProgramImplMethodId) (traitMethod : ProgramTraitMethodId)
      (expectedParameters actualParameters : List Bool)
      (expectedReturn actualReturn : Bool)
  | implMethodUndeclaredPredicate
      (method : ProgramImplMethodId) (traitMethod : ProgramTraitMethodId)
      (predicate : ProgramPredicate)
  | traitCatalogUnavailable
      (implementation trait : Resolved.DeclarationId)
  | implementationParameterNotInHead
      (implementation : Resolved.DeclarationId)
      (parameter : TypeSystem.TypeParameterId)
  /-- A default implementation whose head overlaps an earlier default's of the
  same trait while one of the two has no where predicates (`SC0247`). -/
  | overlappingDefaultImplementation
      (implementation overlaps : Resolved.DeclarationId)
  /-- An ordinary implementation whose head overlaps one that its module sees of the same
  trait (`SC0218`). -/
  | overlappingImplementation
      (implementation overlaps : Resolved.DeclarationId)
  /-- An implementation away from its trait's module and from the module of the
  type at its subject's coherence head (`SC0246`). -/
  | orphanImplementation (implementation : Resolved.DeclarationId)
  /-- A default implementation whose subject, the trait's main argument, holds
  no type parameter (`SC0219`). -/
  | invalidDefaultImplementation (implementation : Resolved.DeclarationId)
  /-- An implementation whose trait's other arguments hold parameters that its
  subject does not, the coverage condition (`SC0212`). -/
  | coverageCondition (implementation : Resolved.DeclarationId)
      (undetermined : List TypeSystem.TypeParameterId)
  /-- An implementation with a declared condition no smaller than its head, the
  Patterson condition (`SC0213`). -/
  | pattersonCondition (implementation : Resolved.DeclarationId)
  /-- An implementation of a trait named `Shl` or `Shr` that declares `bshl` or `bshr`, at `word`
  or a fixed-width type, where Lean's shifts are builtins that never take it, even in generic
  code (`shiftImplementationErrors`). -/
  | shiftImplementationAtBuiltinType (implementation : Resolved.DeclarationId)
  | duplicateDataConstructor
      (dataType : Resolved.DeclarationId) (name : String)
      (firstIndex duplicateIndex : Nat)
  deriving Repr, DecidableEq

private def programSignatureErrorDeclaration :
    ProgramSignatureError → Resolved.DeclarationId
  | .duplicateFunctionParameter declaration _ _ _ => declaration
  | .malformedFunctionParameter declaration _ => declaration
  | .malformedType declaration => declaration
  | .nestedComptimeReturn declaration _ => declaration
  | .comptimeReturnMustBeSingleton declaration _ _ => declaration
  | .unknownTrait declaration _ => declaration
  | .ambiguousTrait declaration _ _ => declaration
  | .traitArityMismatch declaration _ _ _ => declaration
  | .importVisibility declaration _ => declaration
  | .typeResolution declaration _ => declaration
  | .traitMethodLocalGenerics method => method.trait
  | .implMethodLocalGenerics method => method.implementation
  | .duplicateTraitMethod trait _ _ _ => trait
  | .duplicateImplMethod implementation _ _ _ => implementation
  | .missingImplMethod implementation _ _ => implementation
  | .extraImplMethod method _ => method.implementation
  | .implMethodSignatureMismatch method _ _ _ _ _ => method.implementation
  | .implMethodComptimeMismatch method _ _ _ _ _ => method.implementation
  | .implMethodUndeclaredPredicate method _ _ => method.implementation
  | .traitCatalogUnavailable implementation _ => implementation
  | .implementationParameterNotInHead implementation _ => implementation
  | .overlappingDefaultImplementation implementation _ => implementation
  | .overlappingImplementation implementation _ => implementation
  | .orphanImplementation implementation => implementation
  | .invalidDefaultImplementation implementation => implementation
  | .coverageCondition implementation _ => implementation
  | .pattersonCondition implementation => implementation
  | .shiftImplementationAtBuiltinType implementation => implementation
  | .duplicateDataConstructor dataType _ _ _ => dataType

private def declarationParameters
    (declaration : ProgramDeclaration) : List TypeSystem.TypeParameterId :=
  declaration.genericParameters.zipIdx.map fun (_, index) =>
    { owner := declaration.id, index }

private theorem declarationParameters_wellFormed
    (declaration : ProgramDeclaration) :
    SignatureParametersWellFormed declaration.id
      (declarationParameters declaration) := by
  have indices :
      (declarationParameters declaration).map (fun parameter => parameter.index) =
        List.range declaration.genericParameters.length := by
    rw [declarationParameters, List.map_map]
    change List.map Prod.snd declaration.genericParameters.zipIdx = _
    rw [List.zipIdx_map_snd]
    exact List.range_eq_range'.symm
  have distinctIndices :
      (declarationParameters declaration).Pairwise
        (fun left right => left.index ≠ right.index) := by
    rw [← List.pairwise_map]
    rw [indices]
    exact List.nodup_range
  refine {
    parameters_nodup := distinctIndices.imp (fun distinct equal =>
      distinct (congrArg TypeSystem.TypeParameterId.index equal))
    parameter_owners := ?_
    parameter_positions := ?_
  }
  · intro parameter member
    simp only [declarationParameters, List.mem_map] at member
    obtain ⟨entry, _, rfl⟩ := member
    rfl
  · intro index
    rw [List.get_eq_getElem]
    simp [declarationParameters]

private def typeContainsError : TypeSystem.Ty → Bool
  | .error => true
  | .variable _
  | .parameter _
  | .constructor _ => false
  | .application left right
  | .function left right
  | .product left right
  | .mapping left right => typeContainsError left || typeContainsError right
  | .proxy inner
  | .comptime inner => typeContainsError inner

private def finishSignatureTypeResolution
    (declaration : ProgramDeclaration)
    (result : Except ProgramTypeResolutionError TypeSystem.Ty) :
    Except ProgramSignatureError TypeSystem.Ty :=
  match result with
  | .error error => .error (.typeResolution declaration.id error)
  | .ok type =>
      if typeContainsError type then
        .error (.malformedType declaration.id)
      else
        .ok type

private def resolveSignatureType
    (environment : ProgramEnvironment) (declaration : ProgramDeclaration)
    (scope : ProgramTypeScope) (source : Syntax.TypeExpr) :
    Except ProgramSignatureError TypeSystem.Ty :=
  finishSignatureTypeResolution declaration
    (resolveProgramTypeExpr environment scope source)

private def resolveSignatureAliasBody
    (environment : ProgramEnvironment) (declaration : ProgramDeclaration)
    (source : Syntax.TypeExpr) : Except ProgramSignatureError TypeSystem.Ty :=
  finishSignatureTypeResolution declaration
    (resolveProgramTypeAliasBody environment declaration source)

private def resolveSignatureTypes
    (environment : ProgramEnvironment) (declaration : ProgramDeclaration)
    (scope : ProgramTypeScope) : List Syntax.TypeExpr →
      Except ProgramSignatureError (List TypeSystem.Ty)
  | [] => .ok []
  | source :: rest => do
      let type ← resolveSignatureType environment declaration scope source
      let types ← resolveSignatureTypes environment declaration scope rest
      pure (type :: types)

private def dataConstructorsOfDeclaration
    (environment : ProgramEnvironment) (declaration : ProgramDeclaration)
    (scope : ProgramTypeScope) :
    List Syntax.EnumConstructor → Nat → List (String × Nat) →
      Except ProgramSignatureError (List ProgramDataConstructorSignature)
  | [], _, _ => pure []
  | source :: rest, index, seen => do
      let name := source.value.name.value
      match seen.find? fun previous => previous.1 == name with
      | some previous =>
          throw (.duplicateDataConstructor declaration.id name previous.2 index)
      | none =>
          let payloadSources := source.value.fields.map
            (fun fields => fields.elements) |>.getD []
          let payloadTypes ← resolveSignatureTypes environment declaration scope
            payloadSources
          let constructors ← dataConstructorsOfDeclaration environment
            declaration scope rest (index + 1) ((name, index) :: seen)
          pure ({
            id := { dataType := declaration.id, constructorIndex := index }
            name
            payloadTypes
            source
          } :: constructors)

/-- Successful constructor collection preserves the duplicate-name check and
the declaration-owned, source-order constructor identity allocation.  The
freshness clause is the induction invariant needed to relate the output to the
names already seen by its caller. -/
private theorem dataConstructorsOfDeclaration_success_structure
    {environment : ProgramEnvironment} {declaration : ProgramDeclaration}
    {scope : ProgramTypeScope} {sources : List Syntax.EnumConstructor}
    {index : Nat} {seen : List (String × Nat)}
    {constructors : List ProgramDataConstructorSignature}
    (success : dataConstructorsOfDeclaration environment declaration scope
      sources index seen = .ok constructors) :
    (constructors.map fun constructor => constructor.name).Nodup ∧
      (∀ name, name ∈ constructors.map (fun constructor => constructor.name) →
        ∀ previous, previous ∈ seen → name ≠ previous.1) ∧
      (∀ constructor, constructor ∈ constructors →
        constructor.id.dataType = declaration.id) ∧
      (∀ position : Fin constructors.length,
        (constructors.get position).id.constructorIndex =
          index + position.val) := by
  induction sources generalizing index seen constructors with
  | nil =>
      change Except.ok [] = Except.ok constructors at success
      injection success with constructorsEq
      subst constructors
      simp
  | cons source rest induction =>
      simp only [dataConstructorsOfDeclaration] at success
      cases duplicateEq : seen.find? fun previous =>
          previous.1 == source.value.name.value with
      | some previous => simp [duplicateEq] at success
      | none =>
          simp only [duplicateEq] at success
          cases payloadEq : resolveSignatureTypes environment declaration scope
              ((source.value.fields.map fun fields => fields.elements).getD []) with
          | error error => simp [payloadEq, bind, Except.bind] at success
          | ok payloadTypes =>
              simp only [payloadEq, bind, Except.bind] at success
              cases restEq : dataConstructorsOfDeclaration environment declaration
                  scope rest (index + 1)
                  ((source.value.name.value, index) :: seen) with
              | error error => simp [restEq] at success
              | ok restConstructors =>
                  simp only [restEq, pure, Pure.pure, Except.pure,
                    Except.ok.injEq] at success
                  subst constructors
                  have restStructure := induction restEq
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · simp only [List.map_cons, List.nodup_cons]
                    refine ⟨?_, restStructure.1⟩
                    intro member
                    exact (restStructure.2.1 source.value.name.value member
                      (source.value.name.value, index) (by simp)) rfl
                  · intro name member previous previousMember
                    simp only [List.map_cons, List.mem_cons] at member
                    rcases member with rfl | member
                    · intro equal
                      have rejected :=
                        (List.find?_eq_none.mp duplicateEq) previous previousMember
                      exact rejected (by simp [equal])
                    · exact restStructure.2.1 name member previous
                        (by simp [previousMember])
                  · intro constructor member
                    simp only [List.mem_cons] at member
                    rcases member with rfl | member
                    · rfl
                    · exact restStructure.2.2.1 constructor member
                  · intro position
                    refine Fin.cases ?_ (fun restPosition => ?_) position
                    · rfl
                    · change
                        (restConstructors.get restPosition).id.constructorIndex =
                          index + (restPosition.val + 1)
                      rw [restStructure.2.2.2 restPosition]
                      omega

private def dataSignatureOfDeclaration
    (environment : ProgramEnvironment) (declaration : ProgramDeclaration)
    (source : Syntax.EnumDecl) :
    Except ProgramSignatureError ProgramDataSignature := do
  let scope := ProgramTypeScope.ofDeclaration declaration
  match validateProgramTypeScope scope with
  | .error error => throw (.typeResolution declaration.id error)
  | .ok () => pure ()
  let constructors ← dataConstructorsOfDeclaration environment declaration
    scope source.value.constructors 0 []
  pure {
    id := declaration.id
    name := source.value.name.value
    parameters := declarationParameters declaration
    constructors
    source
  }

/-- Validate and retain one contract's declaration-local generic scope.
Contract members are intentionally not interpreted as data constructors. -/
private def contractSignatureOfDeclaration
    (declaration : ProgramDeclaration) (source : Syntax.ContractDecl) :
    Except ProgramSignatureError ProgramContractSignature := do
  let scope := ProgramTypeScope.ofDeclaration declaration
  match validateProgramTypeScope scope with
  | .error error => throw (.typeResolution declaration.id error)
  | .ok () => pure ()
  pure {
    id := declaration.id
    name := source.value.name.value
    parameters := declarationParameters declaration
    source
  }

private def firstTopLevelComptimeReturn? :
    List Syntax.TypeExpr → Nat → Option Nat
  | [], _ => none
  | source :: rest, index =>
      match source.value with
      | .comptime _ _ _ => some index
      | _ => firstTopLevelComptimeReturn? rest (index + 1)

/-- Resolve a named function's results while separating the source staging
marker from its ordinary semantic result type.  The current surface contract
admits the marker only around one result and deliberately rejects a second
outer marker instead of silently retaining `Ty.comptime` in the function type. -/
private def resolveFunctionReturns
    (environment : ProgramEnvironment) (declaration : ProgramDeclaration)
    (scope : ProgramTypeScope) (sources : List Syntax.TypeExpr) :
    Except ProgramSignatureError (List TypeSystem.Ty × Bool) := do
  match sources with
  | [source] =>
      match source.value with
      | .comptime _ _ inner =>
          match inner.value with
          | .comptime _ _ _ =>
              throw (.nestedComptimeReturn declaration.id 0)
          | _ =>
              let type ← resolveSignatureType environment declaration scope inner
              pure ([type], true)
      | _ =>
          let type ← resolveSignatureType environment declaration scope source
          pure ([type], false)
  | sources =>
      match firstTopLevelComptimeReturn? sources 0 with
      | some index =>
          throw (.comptimeReturnMustBeSingleton declaration.id index sources.length)
      | none =>
          let types ← resolveSignatureTypes environment declaration scope sources
          pure (types, false)

private def traitCandidates
    (environment : ProgramEnvironment) (declaration : ProgramDeclaration)
    (name : String) : Except ProgramSignatureError (List ProgramDeclaration) :=
  match environment.localTraitsNamed declaration.id.moduleId name with
  | localCandidates@(_ :: _) => .ok localCandidates
  | [] =>
      match buildProgramImports environment declaration.id.moduleId with
      | .error errors => .error (.importVisibility declaration.id errors)
      | .ok visibility => .ok (visibility.traitsNamed name)

private def resolveTrait
    (environment : ProgramEnvironment) (declaration : ProgramDeclaration)
    (name : String) (actualArity : Nat) :
    Except ProgramSignatureError Resolved.DeclarationId := do
  match ← traitCandidates environment declaration name with
  | [] => .error (.unknownTrait declaration.id name)
  | [trait] =>
      if trait.genericParameters.length = actualArity then
        .ok trait.id
      else
        .error (.traitArityMismatch declaration.id trait.id
          trait.genericParameters.length actualArity)
  | candidates =>
      .error (.ambiguousTrait declaration.id name (candidates.map (·.id)))

private def resolvePredicate
    (environment : ProgramEnvironment) (declaration : ProgramDeclaration)
    (scope : ProgramTypeScope) (source : Syntax.Predicate) :
    Except ProgramSignatureError ProgramPredicate := do
  let subject ← resolveSignatureType environment declaration scope source.subject
  let argumentSources := source.arguments.map
    (fun arguments => arguments.elements.toList) |>.getD []
  let arguments ← resolveSignatureTypes environment declaration scope argumentSources
  let trait ← resolveTrait environment declaration source.traitName.value
    (arguments.length + 1)
  pure { trait, subject, arguments }

private def resolveWhereClause
    (environment : ProgramEnvironment) (declaration : ProgramDeclaration)
    (scope : ProgramTypeScope) : Option Syntax.WhereClause →
      Except ProgramSignatureError (List ProgramPredicate)
  | none => .ok []
  | some clause =>
      let rec loop : List Syntax.Predicate →
          Except ProgramSignatureError (List ProgramPredicate)
        | [] => .ok []
        | source :: rest => do
            let predicate ← resolvePredicate environment declaration scope source
            let predicates ← loop rest
            pure (predicate :: predicates)
      loop clause.predicates.toList

private structure ResolvedFunctionParameters where
  parameters : List ProgramFunctionParameter

private def resolveFunctionParameters
    (environment : ProgramEnvironment) (declaration : ProgramDeclaration)
    (scope : ProgramTypeScope) :
    List Syntax.FunctionParameter → Nat → List (String × Nat) →
      Except ProgramSignatureError ResolvedFunctionParameters
  | [], _, _ => .ok { parameters := [] }
  | parameter :: rest, index, seen =>
      match parameter.value with
      | .error => .error (.malformedFunctionParameter declaration.id index)
      | .typed comptime name sourceType =>
          match seen.find? fun previous => previous.1 == name.value with
          | some previous =>
              .error (.duplicateFunctionParameter declaration.id name.value
                previous.2 index)
          | none => do
              let type ← resolveSignatureType environment declaration scope sourceType
              let resolvedRest ← resolveFunctionParameters environment declaration
                scope rest (index + 1) ((name.value, index) :: seen)
              pure {
                parameters := {
                  name := name.value
                  type
                  comptime := comptime.isSome
                } :: resolvedRest.parameters
              }

/-- Successful parameter resolution produces unique names and keeps every
newly resolved name distinct from the names already recorded by the caller. -/
private theorem resolveFunctionParameters_success_names
    {environment : ProgramEnvironment} {declaration : ProgramDeclaration}
    {scope : ProgramTypeScope} {sources : List Syntax.FunctionParameter}
    {index : Nat} {seen : List (String × Nat)}
    {resolved : ResolvedFunctionParameters}
    (success : resolveFunctionParameters environment declaration scope
      sources index seen = .ok resolved) :
    (resolved.parameters.map (·.name)).Nodup ∧
      ∀ name, name ∈ resolved.parameters.map (·.name) →
        ∀ previous, previous ∈ seen → name ≠ previous.1 := by
  induction sources generalizing index seen resolved with
  | nil =>
      simp only [resolveFunctionParameters, Except.ok.injEq] at success
      subst resolved
      simp
  | cons parameter rest induction =>
      cases valueEq : parameter.value with
      | error =>
          simp [resolveFunctionParameters, valueEq] at success
      | typed comptime name sourceType =>
          simp only [resolveFunctionParameters, valueEq] at success
          cases duplicateEq : seen.find? fun previous =>
              previous.1 == name.value with
          | some previous =>
              simp [duplicateEq] at success
          | none =>
              simp only [duplicateEq] at success
              cases typeEq : resolveSignatureType environment declaration scope
                  sourceType with
              | error error =>
                  simp [typeEq, bind, Except.bind] at success
              | ok type =>
                  simp only [typeEq, bind, Except.bind] at success
                  cases restEq : resolveFunctionParameters environment declaration
                      scope rest (index + 1) ((name.value, index) :: seen) with
                  | error error =>
                      simp [restEq] at success
                  | ok resolvedRest =>
                      simp only [restEq, pure, Pure.pure, Except.pure,
                        Except.ok.injEq] at success
                      subst resolved
                      have restProperties := induction restEq
                      constructor
                      · simp only [List.map_cons, List.nodup_cons]
                        refine ⟨?_, restProperties.1⟩
                        intro member
                        exact (restProperties.2 name.value member
                          (name.value, index) (by simp)) rfl
                      · intro candidate member previous previousMember
                        simp only [List.map_cons, List.mem_cons] at member
                        rcases member with rfl | member
                        · intro equal
                          have rejected :=
                            (List.find?_eq_none.mp duplicateEq) previous
                              previousMember
                          exact rejected (by simp [equal])
                        · exact restProperties.2 candidate member previous
                            (by simp [previousMember])

private def functionSignatureOfDeclaration
    (environment : ProgramEnvironment) (declaration : ProgramDeclaration)
    (source : Syntax.FunctionDecl) :
    Except ProgramSignatureError ProgramFunctionSignature := do
  let scope := ProgramTypeScope.ofDeclaration declaration
  match validateProgramTypeScope scope with
  | .error error => throw (.typeResolution declaration.id error)
  | .ok () => pure ()
  let signature := source.value.signature
  let parameters ← resolveFunctionParameters environment declaration scope
    signature.parameters.elements 0 []
  let returnSources := signature.returnsClause.map
    (fun clause => clause.types.elements) |>.getD []
  let (returnTypes, returnComptime) ← resolveFunctionReturns environment declaration
    scope returnSources
  let predicates ← resolveWhereClause environment declaration scope
    signature.whereClause
  let body := TypeSystem.Ty.function
    (TypeSystem.Ty.productMany (parameters.parameters.map (·.type)))
    (TypeSystem.Ty.productMany returnTypes)
  pure {
    id := declaration.id
    name := signature.name.value
    parameters := parameters.parameters
    returnTypes
    returnComptime
    scheme := {
      parameters := declarationParameters declaration
      predicates
      body
    }
    source
  }

private structure ResolvedMethodShape where
  parameters : List ProgramFunctionParameter
  returnTypes : List TypeSystem.Ty
  returnComptime : Bool
  wherePredicates : List ProgramPredicate

private def resolveMethodShape
    (environment : ProgramEnvironment) (declaration : ProgramDeclaration)
    (scope : ProgramTypeScope) (signature : Syntax.FunctionSignature) :
    Except ProgramSignatureError ResolvedMethodShape := do
  let parameters ← resolveFunctionParameters environment declaration scope
    signature.parameters.elements 0 []
  let returnSources := signature.returnsClause.map
    (fun clause => clause.types.elements) |>.getD []
  let (returnTypes, returnComptime) ← resolveFunctionReturns environment declaration
    scope returnSources
  let wherePredicates ← resolveWhereClause environment declaration scope
    signature.whereClause
  pure {
    parameters := parameters.parameters
    returnTypes
    returnComptime
    wherePredicates
  }

/-- Method-shape resolution reuses the ordinary function-parameter collector,
so a successful result retains its duplicate-name rejection. -/
private theorem resolveMethodShape_success_parameter_names_nodup
    {environment : ProgramEnvironment} {declaration : ProgramDeclaration}
    {scope : ProgramTypeScope} {source : Syntax.FunctionSignature}
    {shape : ResolvedMethodShape}
    (success : resolveMethodShape environment declaration scope source =
      .ok shape) :
    (shape.parameters.map fun parameter => parameter.name).Nodup := by
  simp only [resolveMethodShape] at success
  cases parametersEq : resolveFunctionParameters environment declaration scope
      source.parameters.elements 0 [] with
  | error error => simp [parametersEq, bind, Except.bind] at success
  | ok parameters =>
      have parameterNames :=
        (resolveFunctionParameters_success_names parametersEq).1
      simp only [parametersEq, bind, Except.bind] at success
      cases returnsEq : resolveFunctionReturns environment declaration scope
          ((source.returnsClause.map fun clause => clause.types.elements).getD []) with
      | error error => simp [returnsEq] at success
      | ok returns =>
          rcases returns with ⟨returnTypes, returnComptime⟩
          simp only [returnsEq] at success
          cases predicatesEq : resolveWhereClause environment declaration scope
              source.whereClause with
          | error error => simp [predicatesEq] at success
          | ok predicates =>
              simp only [predicatesEq, pure, Pure.pure, Except.pure,
                Except.ok.injEq] at success
              subst shape
              exact parameterNames

private def traitMethodsOfDeclaration
    (environment : ProgramEnvironment) (declaration : ProgramDeclaration)
    (scope : ProgramTypeScope) :
    List Syntax.TraitMethod → Nat → List (String × Nat) →
      Except ProgramSignatureError (List ProgramTraitMethodSignature)
  | [], _, _ => .ok []
  | source :: rest, index, seen => do
      let id : ProgramTraitMethodId := {
        trait := declaration.id
        methodIndex := index
      }
      let signature := source.value.signature
      if signature.genericParameters.isSome then
        throw (.traitMethodLocalGenerics id)
      let name := signature.name.value
      match seen.find? fun previous => previous.1 == name with
      | some previous =>
          throw (.duplicateTraitMethod declaration.id name previous.2 index)
      | none =>
          let shape ← resolveMethodShape environment declaration scope signature
          let methods ← traitMethodsOfDeclaration environment declaration scope
            rest (index + 1) ((name, index) :: seen)
          pure ({
            id
            name
            parameters := shape.parameters
            returnTypes := shape.returnTypes
            returnComptime := shape.returnComptime
            wherePredicates := shape.wherePredicates
            source
          } :: methods)

/-- Successful trait-method collection preserves duplicate-name rejection,
declaration ownership, source-order indices, and each method's local
parameter-name uniqueness.  The freshness clause is the induction invariant
relating newly collected names to the caller's `seen` ledger. -/
private theorem traitMethodsOfDeclaration_success_structure
    {environment : ProgramEnvironment} {declaration : ProgramDeclaration}
    {scope : ProgramTypeScope} {sources : List Syntax.TraitMethod}
    {index : Nat} {seen : List (String × Nat)}
    {methods : List ProgramTraitMethodSignature}
    (success : traitMethodsOfDeclaration environment declaration scope
      sources index seen = .ok methods) :
    (methods.map fun method => method.name).Nodup ∧
      (∀ name, name ∈ methods.map (fun method => method.name) →
        ∀ previous, previous ∈ seen → name ≠ previous.1) ∧
      (∀ method, method ∈ methods → method.id.trait = declaration.id) ∧
      (∀ position : Fin methods.length,
        (methods.get position).id.methodIndex = index + position.val) ∧
      (∀ method, method ∈ methods → method.parameterNames.Nodup) := by
  induction sources generalizing index seen methods with
  | nil =>
      change Except.ok [] = Except.ok methods at success
      injection success with methodsEq
      subst methods
      simp
  | cons source rest induction =>
      simp only [traitMethodsOfDeclaration] at success
      by_cases generics : source.value.signature.genericParameters.isSome
      · simp [generics, bind, Except.bind] at success
      · simp only [generics, Bool.false_eq_true, if_false] at success
        cases duplicateEq : seen.find? fun previous =>
            previous.1 == source.value.signature.name.value with
        | some previous => simp [duplicateEq] at success
        | none =>
            simp only [duplicateEq] at success
            cases shapeEq : resolveMethodShape environment declaration scope
                source.value.signature with
            | error error => simp [shapeEq, bind, Except.bind] at success
            | ok shape =>
                have parameterNames :=
                  resolveMethodShape_success_parameter_names_nodup shapeEq
                simp only [shapeEq, bind, Except.bind] at success
                cases restEq : traitMethodsOfDeclaration environment declaration
                    scope rest (index + 1)
                    ((source.value.signature.name.value, index) :: seen) with
                | error error => simp [restEq] at success
                | ok restMethods =>
                    simp only [restEq, pure, Pure.pure, Except.pure,
                      Except.ok.injEq] at success
                    subst methods
                    have restStructure := induction restEq
                    refine ⟨?_, ?_, ?_, ?_, ?_⟩
                    · simp only [List.map_cons, List.nodup_cons]
                      refine ⟨?_, restStructure.1⟩
                      intro member
                      exact (restStructure.2.1 source.value.signature.name.value
                        member (source.value.signature.name.value, index)
                        (by simp)) rfl
                    · intro name member previous previousMember
                      simp only [List.map_cons, List.mem_cons] at member
                      rcases member with rfl | member
                      · intro equal
                        have rejected :=
                          (List.find?_eq_none.mp duplicateEq) previous
                            previousMember
                        exact rejected (by simp [equal])
                      · exact restStructure.2.1 name member previous
                          (by simp [previousMember])
                    · intro method member
                      simp only [List.mem_cons] at member
                      rcases member with rfl | member
                      · rfl
                      · exact restStructure.2.2.1 method member
                    · intro position
                      refine Fin.cases ?_ (fun restPosition => ?_) position
                      · rfl
                      · change
                          (restMethods.get restPosition).id.methodIndex =
                            index + (restPosition.val + 1)
                        rw [restStructure.2.2.2.1 restPosition]
                        omega
                    · intro method member
                      simp only [List.mem_cons] at member
                      rcases member with rfl | member
                      · simpa [ProgramTraitMethodSignature.parameterNames]
                          using parameterNames
                      · exact restStructure.2.2.2.2 method member

private def traitSignatureOfDeclaration
    (environment : ProgramEnvironment) (declaration : ProgramDeclaration)
    (source : Syntax.TraitDecl) :
    Except ProgramSignatureError ProgramTraitSignature := do
  let scope := ProgramTypeScope.ofDeclaration declaration
  match validateProgramTypeScope scope with
  | .error error => throw (.typeResolution declaration.id error)
  | .ok () => pure ()
  let wherePredicates ← resolveWhereClause environment declaration scope
    source.value.whereClause
  let methods ← traitMethodsOfDeclaration environment declaration scope
    source.value.methods 0 []
  pure {
    id := declaration.id
    name := source.value.name.value
    parameters := declarationParameters declaration
    wherePredicates
    methods
    source
  }

private structure UnmatchedProgramImplMethod where
  id : ProgramImplMethodId
  name : String
  parameters : List ProgramFunctionParameter
  returnTypes : List TypeSystem.Ty
  returnComptime : Bool
  wherePredicates : List ProgramPredicate
  source : Syntax.ImplMethod

namespace UnmatchedProgramImplMethod

private def parameterNames
    (method : UnmatchedProgramImplMethod) : List String :=
  method.parameters.map (·.name)

private def parameterTypes
    (method : UnmatchedProgramImplMethod) : List TypeSystem.Ty :=
  method.parameters.map (·.type)

private def parameterComptime
    (method : UnmatchedProgramImplMethod) : List Bool :=
  method.parameters.map (·.comptime)

end UnmatchedProgramImplMethod

/-- The signature comparison performed before an implementation method is
attached to its selected trait method identity: an exact shape, and only
predicates that its callers or its implementation provide. -/
private structure UnmatchedImplMethodMatchesTrait
    (substitution : TypeSystem.ParameterSubstitution)
    (implementationPredicates : List ProgramPredicate)
    (traitMethod : ProgramTraitMethodSignature)
    (implMethod : UnmatchedProgramImplMethod) : Prop where
  name : traitMethod.name = implMethod.name
  parameter_types : implMethod.parameterTypes =
    traitMethod.parameterTypes.map substitution.apply
  return_types : implMethod.returnTypes =
    traitMethod.returnTypes.map substitution.apply
  parameter_comptime : implMethod.parameterComptime =
    traitMethod.parameterComptime
  return_comptime : implMethod.returnComptime = traitMethod.returnComptime
  predicates : ∀ predicate, predicate ∈ implMethod.wherePredicates →
    predicate ∈ traitMethod.wherePredicates.map
      (ProgramPredicate.applyParameters substitution) ++ implementationPredicates

/-- Two members of a list with duplicate-free projected keys and the same key
are the same retained value. -/
private theorem eq_of_mem_of_projected_nodup
    {value key : Type} (project : value → key)
    {values : List value} {left right : value}
    (unique : (values.map project).Nodup)
    (leftMember : left ∈ values) (rightMember : right ∈ values)
    (keysEqual : project left = project right) : left = right := by
  induction values generalizing left right with
  | nil => simp at leftMember
  | cons head tail induction =>
      simp only [List.map_cons, List.nodup_cons] at unique
      rcases unique with ⟨headAbsent, tailUnique⟩
      simp only [List.mem_cons] at leftMember rightMember
      rcases leftMember with rfl | leftMember
      · rcases rightMember with rfl | rightMember
        · rfl
        · exfalso
          apply headAbsent
          rw [keysEqual]
          exact List.mem_map.mpr ⟨right, rightMember, rfl⟩
      · rcases rightMember with rfl | rightMember
        · exfalso
          apply headAbsent
          rw [← keysEqual]
          exact List.mem_map.mpr ⟨left, leftMember, rfl⟩
        · exact induction tailUnique leftMember rightMember keysEqual

private structure UnmatchedImplMethodsStructural
    (owner : Resolved.DeclarationId) (index : Nat)
    (seen : List (String × Nat))
    (methods : List UnmatchedProgramImplMethod) : Prop where
  method_names_nodup : (methods.map fun method => method.name).Nodup
  method_names_fresh : ∀ name,
    name ∈ methods.map (fun method => method.name) →
      ∀ previous, previous ∈ seen → name ≠ previous.1
  method_owners : ∀ method, method ∈ methods →
    method.id.implementation = owner
  method_positions : ∀ position : Fin methods.length,
    (methods.get position).id.methodIndex = index + position.val
  method_parameter_names_nodup : ∀ method, method ∈ methods →
    method.parameterNames.Nodup

private structure ImplMethodsStructural
    (owner : Resolved.DeclarationId) (index : Nat)
    (methods : List ProgramImplMethodSignature) : Prop where
  method_names_nodup : (methods.map fun method => method.name).Nodup
  method_owners : ∀ method, method ∈ methods →
    method.id.implementation = owner
  method_positions : ∀ position : Fin methods.length,
    (methods.get position).id.methodIndex = index + position.val
  method_parameter_names_nodup : ∀ method, method ∈ methods →
    method.parameterNames.Nodup

private def unmatchedImplMethodsOfDeclaration
    (environment : ProgramEnvironment) (declaration : ProgramDeclaration)
    (scope : ProgramTypeScope) :
    List Syntax.ImplMethod → Nat → List (String × Nat) →
      Except ProgramSignatureError (List UnmatchedProgramImplMethod)
  | [], _, _ => .ok []
  | source :: rest, index, seen => do
      let id : ProgramImplMethodId := {
        implementation := declaration.id
        methodIndex := index
      }
      let signature := source.value.declaration.value.signature
      if signature.genericParameters.isSome then
        throw (.implMethodLocalGenerics id)
      let name := signature.name.value
      match seen.find? fun previous => previous.1 == name with
      | some previous =>
          throw (.duplicateImplMethod declaration.id name previous.2 index)
      | none =>
          let shape ← resolveMethodShape environment declaration scope signature
          let methods ← unmatchedImplMethodsOfDeclaration environment declaration
            scope rest (index + 1) ((name, index) :: seen)
          pure ({
            id
            name
            parameters := shape.parameters
            returnTypes := shape.returnTypes
            returnComptime := shape.returnComptime
            wherePredicates := shape.wherePredicates
            source
          } :: methods)

/-- Successful implementation-method collection preserves duplicate-name
rejection, declaration ownership, source-order indices, and each method's
duplicate-free parameter names. -/
private theorem unmatchedImplMethodsOfDeclaration_success_structure
    {environment : ProgramEnvironment} {declaration : ProgramDeclaration}
    {scope : ProgramTypeScope} {sources : List Syntax.ImplMethod}
    {index : Nat} {seen : List (String × Nat)}
    {methods : List UnmatchedProgramImplMethod}
    (success : unmatchedImplMethodsOfDeclaration environment declaration scope
      sources index seen = .ok methods) :
    UnmatchedImplMethodsStructural declaration.id index seen methods := by
  induction sources generalizing index seen methods with
  | nil =>
      change Except.ok [] = Except.ok methods at success
      injection success with methodsEq
      subst methods
      constructor <;> simp
  | cons source rest induction =>
      simp only [unmatchedImplMethodsOfDeclaration] at success
      by_cases generics :
          source.value.declaration.value.signature.genericParameters.isSome
      · simp [generics, bind, Except.bind] at success
      · simp only [generics, Bool.false_eq_true, if_false] at success
        cases duplicateEq : seen.find? fun previous =>
            previous.1 == source.value.declaration.value.signature.name.value with
        | some previous => simp [duplicateEq] at success
        | none =>
            simp only [duplicateEq] at success
            cases shapeEq : resolveMethodShape environment declaration scope
                source.value.declaration.value.signature with
            | error error => simp [shapeEq, bind, Except.bind] at success
            | ok shape =>
                have parameterNames :=
                  resolveMethodShape_success_parameter_names_nodup shapeEq
                simp only [shapeEq, bind, Except.bind] at success
                cases restEq : unmatchedImplMethodsOfDeclaration environment
                    declaration scope rest (index + 1)
                    ((source.value.declaration.value.signature.name.value, index) ::
                      seen) with
                | error error => simp [restEq] at success
                | ok restMethods =>
                    simp only [restEq, pure, Pure.pure, Except.pure,
                      Except.ok.injEq] at success
                    subst methods
                    have restStructure := induction restEq
                    refine {
                      method_names_nodup := ?_
                      method_names_fresh := ?_
                      method_owners := ?_
                      method_positions := ?_
                      method_parameter_names_nodup := ?_
                    }
                    · simp only [List.map_cons, List.nodup_cons]
                      refine ⟨?_, restStructure.method_names_nodup⟩
                      intro member
                      exact (restStructure.method_names_fresh
                        source.value.declaration.value.signature.name.value member
                        (source.value.declaration.value.signature.name.value, index)
                        (by simp)) rfl
                    · intro name member previous previousMember
                      simp only [List.map_cons, List.mem_cons] at member
                      rcases member with rfl | member
                      · intro equal
                        have rejected :=
                          (List.find?_eq_none.mp duplicateEq) previous
                            previousMember
                        exact rejected (by simp [equal])
                      · exact restStructure.method_names_fresh name member previous
                          (by simp [previousMember])
                    · intro method member
                      simp only [List.mem_cons] at member
                      rcases member with rfl | member
                      · rfl
                      · exact restStructure.method_owners method member
                    · intro position
                      refine Fin.cases ?_ (fun restPosition => ?_) position
                      · rfl
                      · change
                          (restMethods.get restPosition).id.methodIndex =
                            index + (restPosition.val + 1)
                        rw [restStructure.method_positions restPosition]
                        omega
                    · intro method member
                      simp only [List.mem_cons] at member
                      rcases member with rfl | member
                      · simpa [UnmatchedProgramImplMethod.parameterNames] using
                          parameterNames
                      · exact restStructure.method_parameter_names_nodup method
                          member

/-- Check a source-ordered list of required values against an available list,
returning the caller-provided error for the first missing value. -/
private def validateContained {value : Type} [DecidableEq value]
    (missing : value → ProgramSignatureError) (available : List value) :
    List value → Except ProgramSignatureError Unit
  | [] => .ok ()
  | value :: rest =>
      if value ∈ available then
        validateContained missing available rest
      else
        .error (missing value)

/-- Successful containment validation is an exact subset witness. -/
private theorem validateContained_success
    {value : Type} [DecidableEq value]
    {missing : value → ProgramSignatureError}
    {available required : List value}
    (success : validateContained missing available required = .ok ()) :
    ∀ candidate, candidate ∈ required → candidate ∈ available := by
  induction required with
  | nil => simp
  | cons head tail induction =>
      simp only [validateContained] at success
      by_cases member : head ∈ available
      · simp only [member, if_true] at success
        intro candidate candidateMember
        simp only [List.mem_cons] at candidateMember
        rcases candidateMember with rfl | candidateMember
        · exact member
        · exact induction success candidate candidateMember
      · simp [member] at success

/-- Each trait method needs one implementation method of the same
instantiated shape. Its predicates must be among those that are provided, as
upstream checks with `SC0249`: a caller proves the trait method's predicates,
instantiated at the head, and the implementation adds its own, which contain
the trait's instantiated where predicates. The rule is membership, so an
omitted, reordered, repeated or restated predicate is accepted, while one that
only follows from the provided predicates is refused. -/
private def validateRequiredImplMethods
    (implementation : Resolved.DeclarationId)
    (substitution : TypeSystem.ParameterSubstitution)
    (implementationPredicates : List ProgramPredicate) :
    List ProgramTraitMethodSignature → List UnmatchedProgramImplMethod →
      Except ProgramSignatureError Unit
  | [], _ => .ok ()
  | traitMethod :: rest, implMethods => do
      let some implMethod := implMethods.find? fun method =>
          method.name == traitMethod.name
        | throw (.missingImplMethod implementation traitMethod.id traitMethod.name)
      let expectedParameters :=
        traitMethod.parameterTypes.map substitution.apply
      let expectedReturns := traitMethod.returnTypes.map substitution.apply
      if expectedParameters = implMethod.parameterTypes &&
          expectedReturns = implMethod.returnTypes then
        if traitMethod.parameterComptime = implMethod.parameterComptime &&
            traitMethod.returnComptime = implMethod.returnComptime then
          validateContained
            (ProgramSignatureError.implMethodUndeclaredPredicate implMethod.id
              traitMethod.id)
            (traitMethod.wherePredicates.map
                (ProgramPredicate.applyParameters substitution) ++
              implementationPredicates)
            implMethod.wherePredicates
          validateRequiredImplMethods implementation substitution
            implementationPredicates rest implMethods
        else
          throw (.implMethodComptimeMismatch implMethod.id traitMethod.id
            traitMethod.parameterComptime implMethod.parameterComptime
            traitMethod.returnComptime implMethod.returnComptime)
      else
        throw (.implMethodSignatureMismatch implMethod.id traitMethod.id
          expectedParameters implMethod.parameterTypes
          expectedReturns implMethod.returnTypes)

/-- Successful required-method validation supplies one matching source
implementation method for every trait method. -/
private theorem validateRequiredImplMethods_success_matches
    {implementation : Resolved.DeclarationId}
    {substitution : TypeSystem.ParameterSubstitution}
    {implementationPredicates : List ProgramPredicate}
    {traitMethods : List ProgramTraitMethodSignature}
    {implMethods : List UnmatchedProgramImplMethod}
    (success : validateRequiredImplMethods implementation substitution
      implementationPredicates traitMethods implMethods = .ok ()) :
    ∀ traitMethod, traitMethod ∈ traitMethods →
      ∃ implMethod, implMethod ∈ implMethods ∧
        UnmatchedImplMethodMatchesTrait substitution implementationPredicates
          traitMethod implMethod := by
  induction traitMethods with
  | nil => simp
  | cons traitMethod rest induction =>
      simp only [validateRequiredImplMethods] at success
      cases foundEq : implMethods.find? fun method =>
          method.name == traitMethod.name with
      | none => simp [foundEq] at success
      | some implMethod =>
          simp only [foundEq] at success
          by_cases parameterTypesEq :
              traitMethod.parameterTypes.map substitution.apply =
                implMethod.parameterTypes
          · by_cases returnTypesEq :
                traitMethod.returnTypes.map substitution.apply =
                  implMethod.returnTypes
            · by_cases parameterComptimeEq :
                  traitMethod.parameterComptime = implMethod.parameterComptime
              · by_cases returnComptimeEq :
                    traitMethod.returnComptime = implMethod.returnComptime
                · cases containedEq : validateContained
                      (ProgramSignatureError.implMethodUndeclaredPredicate
                        implMethod.id traitMethod.id)
                      (traitMethod.wherePredicates.map
                          (ProgramPredicate.applyParameters substitution) ++
                        implementationPredicates)
                      implMethod.wherePredicates with
                  | error error =>
                      simp [parameterTypesEq, returnTypesEq,
                        parameterComptimeEq, returnComptimeEq, containedEq,
                        bind, Except.bind] at success
                  | ok checked =>
                    have restSuccess :
                        validateRequiredImplMethods implementation substitution
                            implementationPredicates rest implMethods = .ok () := by
                      simpa [parameterTypesEq, returnTypesEq,
                        parameterComptimeEq, returnComptimeEq, containedEq,
                        bind, Except.bind] using success
                    intro candidate member
                    simp only [List.mem_cons] at member
                    rcases member with rfl | member
                    · have implMember : implMethod ∈ implMethods :=
                        List.mem_of_find?_eq_some foundEq
                      have nameEq : implMethod.name = candidate.name := by
                        have accepted := List.find?_some foundEq
                        simpa using accepted
                      cases checked
                      exact ⟨implMethod, implMember, {
                        name := nameEq.symm
                        parameter_types := parameterTypesEq.symm
                        return_types := returnTypesEq.symm
                        parameter_comptime := parameterComptimeEq.symm
                        return_comptime := returnComptimeEq.symm
                        predicates := validateContained_success containedEq
                      }⟩
                    · exact induction restSuccess candidate member
                · simp [parameterTypesEq, returnTypesEq,
                    parameterComptimeEq, returnComptimeEq] at success
              · simp [parameterTypesEq, returnTypesEq, parameterComptimeEq]
                  at success
            · simp [parameterTypesEq, returnTypesEq] at success
          · simp [parameterTypesEq] at success

private def attachTraitMethods
    (traitMethods : List ProgramTraitMethodSignature) :
    List UnmatchedProgramImplMethod →
      Except ProgramSignatureError (List ProgramImplMethodSignature)
  | [] => .ok []
  | implMethod :: rest => do
      let some traitMethod := traitMethods.find? fun method =>
          method.name == implMethod.name
        | throw (.extraImplMethod implMethod.id implMethod.name)
      let methods ← attachTraitMethods traitMethods rest
      pure ({
        id := implMethod.id
        traitMethod := traitMethod.id
        name := implMethod.name
        parameters := implMethod.parameters
        returnTypes := implMethod.returnTypes
        returnComptime := implMethod.returnComptime
        wherePredicates := implMethod.wherePredicates
        source := implMethod.source
      } :: methods)

/-- One output method is the field-for-field attachment of a retained source
method to the trait method selected by its name. -/
private def AttachedImplMethod
    (traitMethods : List ProgramTraitMethodSignature)
    (unmatched : UnmatchedProgramImplMethod)
    (method : ProgramImplMethodSignature) : Prop :=
  ∃ traitMethod, traitMethod ∈ traitMethods ∧
    traitMethod.name = unmatched.name ∧
    method.id = unmatched.id ∧
    method.traitMethod = traitMethod.id ∧
    method.name = unmatched.name ∧
    method.parameters = unmatched.parameters ∧
    method.returnTypes = unmatched.returnTypes ∧
    method.returnComptime = unmatched.returnComptime ∧
    method.wherePredicates = unmatched.wherePredicates ∧
    method.source = unmatched.source

/-- Successful attachment is a bidirectional correspondence between input and
output method rows; no source method is dropped or duplicated. -/
private theorem attachTraitMethods_success_correspondence
    {traitMethods : List ProgramTraitMethodSignature}
    {unmatchedMethods : List UnmatchedProgramImplMethod}
    {methods : List ProgramImplMethodSignature}
    (success : attachTraitMethods traitMethods unmatchedMethods = .ok methods) :
    (∀ method, method ∈ methods →
      ∃ unmatched, unmatched ∈ unmatchedMethods ∧
        AttachedImplMethod traitMethods unmatched method) ∧
    (∀ unmatched, unmatched ∈ unmatchedMethods →
      ∃ method, method ∈ methods ∧
        AttachedImplMethod traitMethods unmatched method) := by
  induction unmatchedMethods generalizing methods with
  | nil =>
      change Except.ok [] = Except.ok methods at success
      injection success with methodsEq
      subst methods
      simp
  | cons implMethod rest induction =>
      simp only [attachTraitMethods] at success
      cases traitMethodEq : traitMethods.find? fun method =>
          method.name == implMethod.name with
      | none => simp [traitMethodEq] at success
      | some traitMethod =>
          simp only [traitMethodEq] at success
          cases restEq : attachTraitMethods traitMethods rest with
          | error error => simp [restEq, bind, Except.bind] at success
          | ok restMethods =>
              simp only [restEq, bind, Except.bind, pure, Pure.pure, Except.pure,
                Except.ok.injEq] at success
              subst methods
              have traitMember : traitMethod ∈ traitMethods :=
                List.mem_of_find?_eq_some traitMethodEq
              have traitName : traitMethod.name = implMethod.name := by
                have accepted := List.find?_some traitMethodEq
                simpa using accepted
              have restResult := induction restEq
              constructor
              · intro method member
                simp only [List.mem_cons] at member
                rcases member with rfl | member
                · refine ⟨implMethod, by simp, ?_⟩
                  exact ⟨traitMethod, traitMember, traitName, rfl, rfl, rfl,
                    rfl, rfl, rfl, rfl, rfl⟩
                · obtain ⟨unmatched, unmatchedMember, attached⟩ :=
                    restResult.1 method member
                  exact ⟨unmatched, by simp [unmatchedMember], attached⟩
              · intro unmatched member
                simp only [List.mem_cons] at member
                rcases member with rfl | member
                · let method : ProgramImplMethodSignature := {
                    id := unmatched.id
                    traitMethod := traitMethod.id
                    name := unmatched.name
                    parameters := unmatched.parameters
                    returnTypes := unmatched.returnTypes
                    returnComptime := unmatched.returnComptime
                    wherePredicates := unmatched.wherePredicates
                    source := unmatched.source
                  }
                  refine ⟨method, by simp [method], ?_⟩
                  exact ⟨traitMethod, traitMember, traitName, by simp [method]⟩
                · obtain ⟨method, methodMember, attached⟩ :=
                    restResult.2 unmatched member
                  exact ⟨method, by simp [methodMember], attached⟩

/-- Attaching trait identities does not change implementation-method order or
any of the structural projections established by source collection. -/
private theorem attachTraitMethods_success_structure
    {traitMethods : List ProgramTraitMethodSignature}
    {unmatchedMethods : List UnmatchedProgramImplMethod}
    {methods : List ProgramImplMethodSignature}
    {owner : Resolved.DeclarationId} {index : Nat}
    (success : attachTraitMethods traitMethods unmatchedMethods = .ok methods)
    (unmatched : UnmatchedImplMethodsStructural owner index [] unmatchedMethods) :
    ImplMethodsStructural owner index methods ∧
      methods.map (fun method => method.name) =
        unmatchedMethods.map (fun method => method.name) := by
  induction unmatchedMethods generalizing methods index with
  | nil =>
      change Except.ok [] = Except.ok methods at success
      injection success with methodsEq
      subst methods
      exact ⟨by constructor <;> simp, rfl⟩
  | cons implMethod rest induction =>
      simp only [attachTraitMethods] at success
      cases traitMethodEq : traitMethods.find? fun method =>
          method.name == implMethod.name with
      | none => simp [traitMethodEq] at success
      | some traitMethod =>
          simp only [traitMethodEq] at success
          cases restEq : attachTraitMethods traitMethods rest with
          | error error => simp [restEq, bind, Except.bind] at success
          | ok restMethods =>
              simp only [restEq, bind, Except.bind, pure, Pure.pure, Except.pure,
                Except.ok.injEq] at success
              subst methods
              have unmatchedNames := List.nodup_cons.mp unmatched.method_names_nodup
              have restUnmatched :
                  UnmatchedImplMethodsStructural owner (index + 1) [] rest := {
                method_names_nodup := unmatchedNames.2
                method_names_fresh := by
                  intro name member previous previousMember
                  simp at previousMember
                method_owners := by
                  intro method member
                  exact unmatched.method_owners method (by simp [member])
                method_positions := by
                  intro position
                  have positionEq := unmatched.method_positions position.succ
                  change (rest.get position).id.methodIndex =
                    index + (position.val + 1) at positionEq
                  omega
                method_parameter_names_nodup := by
                  intro method member
                  exact unmatched.method_parameter_names_nodup method
                    (by simp [member])
              }
              have restResult := induction restEq restUnmatched
              have restStructure := restResult.1
              refine ⟨{
                method_names_nodup := ?_
                method_owners := ?_
                method_positions := ?_
                method_parameter_names_nodup := ?_
              }, ?_⟩
              · simp only [List.map_cons, List.nodup_cons]
                refine ⟨?_, restStructure.method_names_nodup⟩
                intro member
                apply unmatchedNames.1
                rw [← restResult.2]
                exact member
              · intro method member
                simp only [List.mem_cons] at member
                rcases member with rfl | member
                · exact unmatched.method_owners implMethod (by simp)
                · exact restStructure.method_owners method member
              · intro position
                refine Fin.cases ?_ (fun restPosition => ?_) position
                · simpa using unmatched.method_positions (0 : Fin (implMethod :: rest).length)
                · change
                    (restMethods.get restPosition).id.methodIndex =
                      index + (restPosition.val + 1)
                  rw [restStructure.method_positions restPosition]
                  omega
              · intro method member
                simp only [List.mem_cons] at member
                rcases member with rfl | member
                · simpa [ProgramImplMethodSignature.parameterNames,
                    UnmatchedProgramImplMethod.parameterNames] using
                    unmatched.method_parameter_names_nodup implMethod (by simp)
                · exact restStructure.method_parameter_names_nodup method member
              · simp [restResult.2]

/-- Exact method correspondence and completeness for one selected trait after
required-method validation and identity attachment. Each method's predicates
are among its trait method's instantiated ones and the implementation's. -/
private structure ImplMethodCatalogMatchesTrait
    (substitution : TypeSystem.ParameterSubstitution)
    (implementationPredicates : List ProgramPredicate)
    (trait : ProgramTraitSignature)
    (resolvedMethods : List ProgramImplMethodSignature) : Prop where
  method_correspondence : ∀ method, method ∈ resolvedMethods →
    ∃ traitMethod, traitMethod ∈ trait.methods ∧
      traitMethod.id = method.traitMethod ∧
      traitMethod.name = method.name ∧
      method.parameterTypes =
        traitMethod.parameterTypes.map substitution.apply ∧
      method.returnTypes =
        traitMethod.returnTypes.map substitution.apply ∧
      method.parameterComptime = traitMethod.parameterComptime ∧
      method.returnComptime = traitMethod.returnComptime ∧
      ∀ predicate, predicate ∈ method.wherePredicates →
        predicate ∈ traitMethod.wherePredicates.map
          (ProgramPredicate.applyParameters substitution) ++
            implementationPredicates
  complete : ∀ traitMethod, traitMethod ∈ trait.methods →
    ∃ method ∈ resolvedMethods, method.traitMethod = traitMethod.id

/-- The two executable method passes jointly establish exact correspondence.
The two duplicate-name witnesses are essential: validation and attachment use
independent name lookups in opposite directions. -/
private theorem validatedAndAttachedImplMethods_matchTrait
    {implementation : Resolved.DeclarationId}
    {substitution : TypeSystem.ParameterSubstitution}
    {implementationPredicates : List ProgramPredicate}
    {trait : ProgramTraitSignature}
    {unmatchedMethods : List UnmatchedProgramImplMethod}
    {methods : List ProgramImplMethodSignature}
    (traitStructure : TraitSignatureStructuralWellFormed trait)
    (unmatchedStructure : UnmatchedImplMethodsStructural implementation 0 []
      unmatchedMethods)
    (validated : validateRequiredImplMethods implementation substitution
      implementationPredicates trait.methods unmatchedMethods = .ok ())
    (attached : attachTraitMethods trait.methods unmatchedMethods = .ok methods) :
    ImplMethodCatalogMatchesTrait substitution implementationPredicates trait
      methods := by
  have required := validateRequiredImplMethods_success_matches validated
  have correspondence := attachTraitMethods_success_correspondence attached
  constructor
  · intro method methodMember
    obtain ⟨unmatched, unmatchedMember, attachedMethod⟩ :=
      correspondence.1 method methodMember
    rcases attachedMethod with
      ⟨traitMethod, traitMethodMember, traitName, methodId, traitMethodId,
        methodName, methodParameters, methodReturns, methodReturnComptime,
        methodPredicates, methodSource⟩
    obtain ⟨validatedMethod, validatedMember, methodMatch⟩ :=
      required traitMethod traitMethodMember
    have validatedEq : validatedMethod = unmatched :=
      eq_of_mem_of_projected_nodup UnmatchedProgramImplMethod.name
        unmatchedStructure.method_names_nodup validatedMember unmatchedMember
        (methodMatch.name.symm.trans traitName)
    subst validatedMethod
    refine ⟨traitMethod, traitMethodMember, traitMethodId.symm,
      traitName.trans methodName.symm, ?_, ?_, ?_, ?_, ?_⟩
    · calc
        method.parameterTypes = unmatched.parameterTypes := by
          simp [ProgramImplMethodSignature.parameterTypes,
            UnmatchedProgramImplMethod.parameterTypes, methodParameters]
        _ = traitMethod.parameterTypes.map substitution.apply :=
          methodMatch.parameter_types
    · exact methodReturns.trans methodMatch.return_types
    · calc
        method.parameterComptime = unmatched.parameterComptime := by
          simp [ProgramImplMethodSignature.parameterComptime,
            UnmatchedProgramImplMethod.parameterComptime, methodParameters]
        _ = traitMethod.parameterComptime := methodMatch.parameter_comptime
    · exact methodReturnComptime.trans methodMatch.return_comptime
    · intro predicate member
      exact methodMatch.predicates predicate (methodPredicates ▸ member)
  · intro traitMethod traitMethodMember
    obtain ⟨unmatched, unmatchedMember, methodMatch⟩ :=
      required traitMethod traitMethodMember
    obtain ⟨method, methodMember, attachedMethod⟩ :=
      correspondence.2 unmatched unmatchedMember
    rcases attachedMethod with
      ⟨selected, selectedMember, selectedName, methodId, selectedId,
        methodName, methodParameters, methodReturns, methodReturnComptime,
        methodPredicates, methodSource⟩
    have selectedEq : selected = traitMethod :=
      eq_of_mem_of_projected_nodup ProgramTraitMethodSignature.name
        traitStructure.method_names_nodup selectedMember traitMethodMember
        (selectedName.trans methodMatch.name.symm)
    subst selected
    exact ⟨method, methodMember, selectedId⟩

/-- An implementation's conditions, then the trait's where predicates at its head
that they do not state: an implicit restatement, as upstream reads an impl's
superclasses. `SC0248` checks the implied ones where the implementation is
declared (`missingSuperclassErrors`). -/
def impliedConditions (conditions required : List ProgramPredicate) :
    List ProgramPredicate :=
  conditions ++ required.filter fun predicate =>
    !conditions.any fun condition => decide (condition = predicate)

theorem mem_impliedConditions_of_required {conditions required : List ProgramPredicate}
    {predicate : ProgramPredicate} (member : predicate ∈ required) :
    predicate ∈ impliedConditions conditions required := by
  unfold impliedConditions
  by_cases stated : predicate ∈ conditions
  · exact List.mem_append_left _ stated
  · refine List.mem_append_right _ (List.mem_filter.mpr ⟨member, ?_⟩)
    have unstated : (conditions.any fun condition => decide (condition = predicate)) = false := by
      rw [List.any_eq_false]
      intro condition conditionMember equal
      exact stated (of_decide_eq_true equal ▸ conditionMember)
    simp [unstated]

theorem mem_impliedConditions_of_mem {conditions required : List ProgramPredicate}
    {predicate : ProgramPredicate} (member : predicate ∈ conditions) :
    predicate ∈ impliedConditions conditions required :=
  List.mem_append_left _ member

private def implementationSignatureOfDeclaration
    (environment : ProgramEnvironment) (declaration : ProgramDeclaration)
    (traits : List ProgramTraitSignature) (source : Syntax.ImplDecl) :
    Except ProgramSignatureError ProgramImplementationSignature := do
  let scope := ProgramTypeScope.ofDeclaration declaration
  match validateProgramTypeScope scope with
  | .error error => throw (.typeResolution declaration.id error)
  | .ok () => pure ()
  let headTypes ← resolveSignatureTypes environment declaration scope
    source.value.headArguments.elements.toList
  let (subject, arguments) ← match headTypes with
    | [] => throw (.malformedType declaration.id)
    | subject :: arguments => pure (subject, arguments)
  let trait ← resolveTrait environment declaration
    source.value.traitName.value (arguments.length + 1)
  let parameters := declarationParameters declaration
  let head : ProgramPredicate := { trait, subject, arguments }
  let headParameters := TypedTraitResolution.predicateParameters head
  validateContained
    (ProgramSignatureError.implementationParameterNotInHead declaration.id)
    headParameters parameters
  let wherePredicates ← resolveWhereClause environment declaration scope
    source.value.whereClause
  let some traitSignature := traits.find? fun signature =>
      decide (signature.id = trait)
    | throw (.traitCatalogUnavailable declaration.id trait)
  let substitution : TypeSystem.ParameterSubstitution :=
    traitSignature.parameters.zip (subject :: arguments)
  let requiredPredicates := traitSignature.wherePredicates.map
    (ProgramPredicate.applyParameters substitution)
  let conditions := impliedConditions wherePredicates requiredPredicates
  let unmatchedMethods ← unmatchedImplMethodsOfDeclaration environment
    declaration scope source.value.methods 0 []
  validateRequiredImplMethods declaration.id substitution conditions
    traitSignature.methods unmatchedMethods
  let methods ← attachTraitMethods traitSignature.methods unmatchedMethods
  pure {
    id := declaration.id
    isDefault := source.value.defaultMarker.isSome
    parameters
    head
    wherePredicates := conditions
    declaredWherePredicates := wherePredicates
    methods
    source
  }

private def signatureItemOfDeclaration
    (environment : ProgramEnvironment) (traits : List ProgramTraitSignature)
    (declaration : ProgramDeclaration) :
    Except ProgramSignatureError
      (Option ProgramFunctionSignature ×
        Option ProgramImplementationSignature) :=
  match declaration.source.value with
  | .function source => do
      pure (some (← functionSignatureOfDeclaration environment declaration source), none)
  | .impl source => do
      pure (none, some (← implementationSignatureOfDeclaration environment
        declaration traits source))
  | _ => .ok (none, none)

private structure ProgramTraitBuildState where
  errors : List ProgramSignatureError := []
  traits : List ProgramTraitSignature := []
  failedTraits : List Resolved.DeclarationId := []

private def collectProgramTraits
    (environment : ProgramEnvironment) :
    List ProgramDeclaration → ProgramTraitBuildState → ProgramTraitBuildState
  | [], state => state
  | declaration :: rest, state =>
      let state :=
        match declaration.source.value with
        | .trait source =>
            match traitSignatureOfDeclaration environment declaration source with
            | .error error => {
                state with
                errors := state.errors ++ [error]
                failedTraits := state.failedTraits ++ [declaration.id]
              }
            | .ok signature => { state with traits := state.traits ++ [signature] }
        | _ => state
      collectProgramTraits environment rest state

private structure ProgramSignatureBuildState where
  errors : List ProgramSignatureError := []
  functions : List ProgramFunctionSignature := []
  implementations : List ProgramImplementationSignature := []
  dataTypes : List ProgramDataSignature := []
  contracts : List ProgramContractSignature := []

private def collectProgramSignatures
    (environment : ProgramEnvironment) (traits : List ProgramTraitSignature) :
    List ProgramDeclaration → ProgramSignatureBuildState →
      ProgramSignatureBuildState
  | [], state => state
  | declaration :: rest, state =>
      let state :=
        match declaration.source.value with
        | .typeAlias source =>
            match resolveSignatureAliasBody environment declaration
                source.value.value with
            | .error error => { state with errors := state.errors ++ [error] }
            | .ok _ => state
        | .enum source =>
            match dataSignatureOfDeclaration environment declaration source with
            | .error error => { state with errors := state.errors ++ [error] }
            | .ok dataType => {
                state with dataTypes := state.dataTypes ++ [dataType]
              }
        | .contract source =>
            match contractSignatureOfDeclaration declaration source with
            | .error error => { state with errors := state.errors ++ [error] }
            | .ok contract => {
                state with contracts := state.contracts ++ [contract]
              }
        | _ =>
            match signatureItemOfDeclaration environment traits declaration with
            | .error error => { state with errors := state.errors ++ [error] }
            | .ok (function?, implementation?) => {
                state with
                functions := state.functions ++ function?.toList
                implementations := state.implementations ++ implementation?.toList
              }
      collectProgramSignatures environment traits rest state

/-- Whether two implementation heads can describe one goal: their subjects, the
trait's main arguments, unify once both heads' parameters are fresh variables
apart. The trait's other arguments are not compared, as upstream's
`instance_heads_overlap` does not compare them. -/
private def implementationHeadsOverlap
    (first second : ProgramImplementationSignature) : Bool :=
  let left := TypedTraitResolution.freshenRuleFor first.implRule second.head
  let right := TypedTraitResolution.freshenRuleFor second.implRule left.head
  match TypeSystem.Unification.unifyTypes left.head.subject right.head.subject with
  | .ok _ => true
  | .error _ => false

/-- Upstream's `SC0247` (`4f22ddb0`): a default implementation whose head
overlaps an earlier default's of the same trait, when either of the two has no
where predicates, since a goal both decide is ambiguous and nothing tells them
apart. Defaults of the standard library and those of other libraries are
compared only among themselves. Lean's implementations are visible everywhere,
so each is compared with every earlier one. -/
private def overlappingDefaultErrors :
    List ProgramImplementationSignature → List ProgramImplementationSignature →
      List ProgramSignatureError
  | _, [] => []
  | earlier, implementation :: rest =>
      let standard (signature : ProgramImplementationSignature) : Bool :=
        signature.id.moduleId.library == Workspace.LibraryId.standard
      let overlapped := if implementation.isDefault then
          earlier.find? fun prior =>
            prior.isDefault && decide (prior.head.trait = implementation.head.trait) &&
              standard prior == standard implementation &&
              (prior.wherePredicates.isEmpty || implementation.wherePredicates.isEmpty) &&
              implementationHeadsOverlap implementation prior
        else none
      overlapped.toList.map (fun prior =>
          ProgramSignatureError.overlappingDefaultImplementation implementation.id prior.id) ++
        overlappingDefaultErrors (earlier ++ [implementation]) rest

/-- The modules whose implementations a module sees directly: those that its
imports and its re-exports name, as upstream's `file_instance_edges` reads
them. -/
private def moduleInstanceEdges (environment : ProgramEnvironment)
    (module : ProgramModule) : List Workspace.ModuleId :=
  module.source.items.flatMap fun item =>
    match item.value with
    | .importDecl declaration =>
        let path := match declaration.value with
          | .plain path => path
          | .namespace path _ => path
          | .wildcard path _ => path
          | .selected _ path _ => path
        (resolveProgramModulePath? environment module.id path).toList
    | .exportDecl declaration =>
        let paths : List Syntax.QualifiedName := match declaration.value with
          | .local items => items.elements.filterMap fun item =>
              match item.value with
              | .moduleWildcard path _ => some path
              | .name _ => none
          | .module path => [path]
          | .moduleAs path _ => [path]
          | .itemsFrom path _ => [path]
        paths.filterMap (resolveProgramExportPath? environment module.id)
    | _ => []

/-- The modules seen from `seen`: transitively, those that their imports and
re-exports name (`instance_import_modules`), within `fuel` rounds. -/
private def seenModules (edges : Workspace.ModuleId → List Workspace.ModuleId) :
    Nat → List Workspace.ModuleId → List Workspace.ModuleId
  | 0, seen => seen
  | fuel + 1, seen =>
      let added := ((seen.flatMap edges).filter fun id => !seen.contains id).eraseDups
      if added.isEmpty then seen else seenModules edges fuel (seen ++ added)

/-- Whether two ordinary heads of one trait overlap as upstream's `SC0218` reads them: their
subjects unify once both heads' parameters are apart (`implementationHeadsOverlap`). Lean's own
`Coerce`, a two-parameter trait of that name, is the one exception: its target is an input of the
coercion search, so its argument must unify as well. -/
private def ordinaryHeadsOverlap (traits : List ProgramTraitSignature)
    (first second : ProgramImplementationSignature) : Bool :=
  let conventionalCoerce := traits.any fun trait =>
    first.head.trait.declaration? == some trait.id && trait.name == "Coerce" &&
      trait.parameters.length == 2
  if conventionalCoerce then
    let left := TypedTraitResolution.freshenRuleFor first.implRule second.head
    let right := TypedTraitResolution.freshenRuleFor second.implRule left.head
    match TypeSystem.Unification.unifyTypes
        (.product left.head.subject (TypeSystem.Ty.productMany left.head.arguments))
        (.product right.head.subject (TypeSystem.Ty.productMany right.head.arguments)) with
    | .ok _ => true
    | .error _ => false
  else implementationHeadsOverlap first second

/-- Upstream's `SC0218` (`check_overlapping_instance`): an ordinary implementation whose head
overlaps an ordinary one of the same trait that its module sees. Those are the ones declared
before it in its module, and those of every module that it sees through its imports and
re-exports (`instance_import_modules`), as upstream compares them; defaults are left to `SC0247`.
Each is reported once, at the later head, and in an import cycle each module reports its own. -/
private def overlappingImplementationErrors (environment : ProgramEnvironment)
    (traits : List ProgramTraitSignature)
    (implementations : List ProgramImplementationSignature) :
    List ProgramSignatureError :=
  let edges (id : Workspace.ModuleId) : List Workspace.ModuleId :=
    match environment.modules.find? fun module => decide (module.id = id) with
    | some module => moduleInstanceEdges environment module
    | none => []
  let fuel := environment.modules.length + 1
  let indexed := (implementations.filter fun implementation => !implementation.isDefault).zipIdx
  indexed.filterMap fun (implementation, index) =>
    let module := implementation.id.moduleId
    let seen := (seenModules edges fuel [module]).filter fun id => !decide (id = module)
    let prior := indexed.filter fun (candidate, candidateIndex) =>
      decide (candidate.head.trait = implementation.head.trait) &&
        ((decide (candidate.id.moduleId = module) && decide (candidateIndex < index)) ||
          seen.contains candidate.id.moduleId)
    (prior.find? fun (candidate, _) => ordinaryHeadsOverlap traits implementation candidate).map
      fun (candidate, _) =>
        ProgramSignatureError.overlappingImplementation implementation.id candidate.id

/-- The declared type at a subject's coherence head: a nominal type's
declaration, after a product's first component, recursively. -/
private def coherenceTypeDeclaration? : TypeSystem.Ty → Option Resolved.DeclarationId
  | .product first _ => coherenceTypeDeclaration? first
  | .application function _ => coherenceTypeDeclaration? function
  | .constructor (.declaration id) => some id
  | _ => none

/-- Upstream's `SC0246` (`02456cee`, `282cb2c8`): an implementation must sit in
its trait's module or in the module of the type at its subject's coherence
head, or in a module that sees that module and is seen by it, so every module
that can state a goal sees every implementation that could decide it. A
standard library counts as one unit. -/
private def orphanImplementationErrors (environment : ProgramEnvironment)
    (implementations : List ProgramImplementationSignature) :
    List ProgramSignatureError :=
  let edges (id : Workspace.ModuleId) : List Workspace.ModuleId :=
    match environment.modules.find? fun module => decide (module.id = id) with
    | some module => moduleInstanceEdges environment module
    | none => []
  let fuel := environment.modules.length + 1
  let seen := environment.modules.map fun module =>
    (module.id, seenModules edges fuel [module.id])
  let sees (viewer target : Workspace.ModuleId) : Bool :=
    match seen.find? fun entry => decide (entry.1 = viewer) with
    | some entry => entry.2.contains target
    | none => false
  let nextTo (module owner : Workspace.ModuleId) : Bool :=
    decide (module = owner) || (sees module owner && sees owner module) ||
      (module.library == Workspace.LibraryId.standard &&
        owner.library == Workspace.LibraryId.standard)
  implementations.filterMap fun implementation =>
    let owners := implementation.head.trait.declaration?.toList ++
      (coherenceTypeDeclaration? implementation.head.subject).toList
    if owners.any fun owner => nextTo implementation.id.moduleId owner.moduleId then none
    else some (ProgramSignatureError.orphanImplementation implementation.id)

/-- A type's size as upstream's `Ty::measure` counts it for the Patterson
condition: one for a parameter or a constructor and one more for each part, with
`T[]` as std's `memory<DynArray<T>>`, a product as std's pair, and each of a
function type's parameters. Lean's function type holds its parameters as one
product, so `function(a, b)` and `function((a, b))` resolve alike, as do
`function()` and `function(())`. With `lower`, a product or `()` among a
function type's parameters (`inParameters`) counts as several parameters or
none, the least upstream can count; without it, as one tuple, the most. -/
def pattersonTypeMeasure (lower : Bool) : Bool → TypeSystem.Ty → Nat
  | true, .constructor (.builtin .unit) => if lower then 0 else 1
  | true, .product left right =>
      if lower then
        pattersonTypeMeasure lower false left + pattersonTypeMeasure lower true right
      else 1 + pattersonTypeMeasure lower false left + pattersonTypeMeasure lower false right
  | _, .constructor (.builtin .memoryArray) => 2
  | _, .parameter _ | _, .variable _ | _, .constructor _ | _, .error => 1
  | _, .application function argument =>
      pattersonTypeMeasure lower false function + pattersonTypeMeasure lower false argument
  | _, .function parameter result =>
      1 + pattersonTypeMeasure lower true parameter + pattersonTypeMeasure lower false result
  | _, .product left right | _, .mapping left right =>
      1 + pattersonTypeMeasure lower false left + pattersonTypeMeasure lower false right
  | _, .proxy inner | _, .comptime inner => 1 + pattersonTypeMeasure lower false inner

/-- A predicate's size, its subject's and its arguments', as upstream's
`Pred::measure` counts it. -/
def pattersonPredicateMeasure (lower : Bool) (predicate : ProgramPredicate) : Nat :=
  ((predicate.subject :: predicate.arguments).map (pattersonTypeMeasure lower false)).sum

/-- Whether a module's pragma `name` lifts a check for `trait`, the name its
implementation's head writes: with no items for every trait, and otherwise for
the traits it names, as upstream's `PragmaEscape` reads it. -/
private def pragmaLifts (environment : ProgramEnvironment) (module : Workspace.ModuleId)
    (name trait : String) : Bool :=
  match environment.modules.find? fun candidate => decide (candidate.id = module) with
  | none => false
  | some module => module.source.items.any fun item =>
      match item.value with
      | .pragmaDecl declaration =>
          declaration.value.name.value == name &&
            (declaration.value.items.isEmpty ||
              declaration.value.items.any fun named => named.value == trait)
      | _ => false

/-- Upstream's checks of an implementation's head and declared conditions
(`check_instance_soundness`), on the resolved types, so aliases are expanded:
- `SC0219`: a default implementation's subject, the trait's main argument, holds
  a type parameter;
- `SC0212`, the coverage condition: each parameter of the trait's other
  arguments occurs in the subject, unless the module's `no-coverage-condition`
  pragma lifts it for the trait;
- `SC0213`, the Patterson condition: each declared condition, without the
  trait's where predicates that it implies, is smaller than the head, unless the
  module's `no-patterson-condition` pragma lifts it for the trait. A condition
  is measured with the fewest parameters and the head with the most
  (`pattersonTypeMeasure`), so a function type there never refuses what
  upstream accepts. -/
private def implementationConditionErrors (environment : ProgramEnvironment)
    (implementations : List ProgramImplementationSignature) :
    List ProgramSignatureError :=
  implementations.flatMap fun implementation =>
    let head := implementation.head
    let lifts (pragma : String) : Bool :=
      pragmaLifts environment implementation.id.moduleId pragma
        implementation.source.value.traitName.value
    let subjectParameters :=
      TypedTraitResolution.predicateParameters { head with arguments := [] }
    let undetermined := (TypedTraitResolution.predicateParameters head).filter
      fun parameter => !subjectParameters.contains parameter
    let headMeasure := pattersonPredicateMeasure false head
    let tooLarge := implementation.declaredWherePredicates.any fun condition =>
      headMeasure ≤ pattersonPredicateMeasure true condition
    (if implementation.isDefault && subjectParameters.isEmpty then
        [ProgramSignatureError.invalidDefaultImplementation implementation.id]
      else []) ++
    (if !undetermined.isEmpty && !lifts "no-coverage-condition" then
        [ProgramSignatureError.coverageCondition implementation.id undetermined]
      else []) ++
    (if tooLarge && !lifts "no-patterson-condition" then
        [ProgramSignatureError.pattersonCondition implementation.id]
      else [])

/-- Lean's shifts are builtins at `word` and the twelve fixed-width types and never take a
program's trait, even in generic code, where upstream's `<<` and `>>` run `Shl.bshl` and
`Shr.bshr`. So an implementation of a trait named `Shl` or `Shr` that declares that method, at one
of those types, is refused where it is declared, the user's rule of 2026-11-23; one at a
program's own type stays, as Lean refuses a shift there. -/
private def shiftImplementationErrors (traits : List ProgramTraitSignature)
    (implementations : List ProgramImplementationSignature) : List ProgramSignatureError :=
  implementations.filterMap fun implementation =>
    let shiftTrait := traits.any fun trait =>
      decide (implementation.head.trait = ProgramTraitId.declaration trait.id) &&
        ((trait.name == "Shl" && trait.methods.any (·.name == "bshl")) ||
          (trait.name == "Shr" && trait.methods.any (·.name == "bshr")))
    let builtinSubject := match implementation.head.subject with
      | .constructor (.builtin .word) => true
      | .constructor (.builtin (.fixed _)) => true
      | _ => false
    if shiftTrait && builtinSubject then
      some (.shiftImplementationAtBuiltinType implementation.id)
    else none

/-- The closure keeps every condition and every method predicate, and adds to a
method only predicates that its closed trait method or the closed conditions
provide, so the method catalog stays validated against the closed traits. -/
theorem ImplementationSignatureMethodCatalogValidated.closeUnderSuperclasses
    {traits : List ProgramTraitSignature} {signature : ProgramImplementationSignature}
    (validated : ImplementationSignatureMethodCatalogValidated traits signature) :
    ImplementationSignatureMethodCatalogValidated
      (traits.map (ProgramTraitSignature.closeMethodsUnderSuperclasses traits))
      (signature.closeUnderSuperclasses traits) := by
  obtain ⟨trait, member, headTrait, methods, complete⟩ := validated
  refine ⟨trait.closeMethodsUnderSuperclasses traits, List.mem_map_of_mem member, headTrait,
    fun closedMethod closedMember => ?_, fun closedTraitMethod closedTraitMember => ?_⟩
  · simp only [ProgramImplementationSignature.closeUnderSuperclasses] at closedMember
    obtain ⟨method, methodMember, rfl⟩ := List.mem_map.mp closedMember
    obtain ⟨traitMethod, traitMember, idEq, nameEq, parameters, returns,
      parameterComptime, returnComptime, predicates⟩ := methods method methodMember
    refine ⟨traitMethod.closeUnderSuperclasses traits, ?_, by simpa using idEq,
      by simpa using nameEq, by simpa using parameters, by simpa using returns,
      by simpa using parameterComptime, by simpa using returnComptime,
      fun predicate predicateMember => ?_⟩
    · simpa using List.mem_map_of_mem traitMember
    · simp only [ProgramTraitSignature.closeMethodsUnderSuperclasses_parameters,
        ProgramTraitMethodSignature.closeUnderSuperclasses,
        ProgramImplementationSignature.closeUnderSuperclasses]
      rcases ProgramImplMethodSignature.mem_closeUnderSuperclasses predicateMember with
        own | provided
      · rcases List.mem_append.mp (predicates predicate own) with inherited | condition
        · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp inherited
          exact List.mem_append_left _
            (List.mem_map_of_mem (mem_superclassClosure_of_mem originalMember))
        · exact List.mem_append_right _ (mem_superclassClosure_of_mem condition)
      · rcases List.mem_append.mp provided with inherited | condition
        · refine List.mem_append_left _ ?_
          simp only [ProgramImplementationSignature.inheritedMethodPredicates] at inherited
          split at inherited
          · rename_i onlyTrait traitsEq
            have traitSelected : trait ∈ traits.filter fun candidate =>
                decide (signature.head.trait = .declaration candidate.id) :=
              List.mem_filter.mpr ⟨member, by simp [headTrait]⟩
            rw [traitsEq, List.mem_singleton] at traitSelected
            subst traitSelected
            split at inherited
            · rename_i onlyMethod methodsEq
              have methodSelected : traitMethod ∈ trait.methods.filter fun candidate =>
                  candidate.name == method.name :=
                List.mem_filter.mpr ⟨traitMember, by simp [nameEq]⟩
              rw [methodsEq, List.mem_singleton] at methodSelected
              subst methodSelected
              exact inherited
            · simp at inherited
          · simp at inherited
        · exact List.mem_append_right _ condition
  · simp only [ProgramTraitSignature.closeMethodsUnderSuperclasses_methods] at closedTraitMember
    obtain ⟨traitMethod, traitMember, rfl⟩ := List.mem_map.mp closedTraitMember
    obtain ⟨method, methodMember, idEq⟩ := complete traitMethod traitMember
    exact ⟨_, List.mem_map_of_mem methodMember, by simpa using idEq⟩

/-- Closing the traits' methods keeps every structural fact of the traits. -/
private theorem TraitSignatureStructuralWellFormed.closeMethods
    {catalog : List ProgramTraitSignature} {trait : ProgramTraitSignature}
    (structural : TraitSignatureStructuralWellFormed trait) :
    TraitSignatureStructuralWellFormed (trait.closeMethodsUnderSuperclasses catalog) := by
  obtain ⟨names, owners, positions, parameterNames⟩ := structural
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [List.map_map, Function.comp_def] using names
  · intro method member
    simp only [ProgramTraitSignature.closeMethodsUnderSuperclasses_methods] at member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    simpa using owners original originalMember
  · intro index
    have bound : index.val < trait.methods.length := by
      simpa using index.isLt
    rw [List.get_eq_getElem]
    simp only [ProgramTraitSignature.closeMethodsUnderSuperclasses_methods, List.getElem_map,
      ProgramTraitMethodSignature.closeUnderSuperclasses_id]
    simpa [List.get_eq_getElem] using positions ⟨index.val, bound⟩
  · intro method member
    simp only [ProgramTraitSignature.closeMethodsUnderSuperclasses_methods] at member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    simpa using parameterNames original originalMember

/-- Closing an implementation's methods keeps every structural fact of them. -/
private theorem ImplementationSignatureStructuralWellFormed.closeUnderSuperclasses
    {traits : List ProgramTraitSignature} {signature : ProgramImplementationSignature}
    (structural : ImplementationSignatureStructuralWellFormed signature) :
    ImplementationSignatureStructuralWellFormed (signature.closeUnderSuperclasses traits) := by
  obtain ⟨names, owners, positions, parameterNames⟩ := structural
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [List.map_map, Function.comp_def] using names
  · intro method member
    simp only [ProgramImplementationSignature.closeUnderSuperclasses_methods] at member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    simpa using owners original originalMember
  · intro index
    have bound : index.val < signature.methods.length := by
      simpa using index.isLt
    rw [List.get_eq_getElem]
    simp only [ProgramImplementationSignature.closeUnderSuperclasses_methods, List.getElem_map,
      ProgramImplMethodSignature.closeUnderSuperclasses_id]
    simpa [List.get_eq_getElem] using positions ⟨index.val, bound⟩
  · intro method member
    simp only [ProgramImplementationSignature.closeUnderSuperclasses_methods] at member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    simpa using parameterNames original originalMember

/-- Resolve every top-level function signature and implementation rule.
Independent declaration failures are accumulated in source order. -/
def buildProgramSignatures (environment : ProgramEnvironment) :
    Except (List ProgramSignatureError) ProgramSignatures :=
  let traitState := collectProgramTraits environment environment.declarations {}
  let state := collectProgramSignatures environment traitState.traits
    environment.declarations {}
  let nonCascadingErrors := state.errors.filter fun error =>
    match error with
    | .traitCatalogUnavailable _ trait => !(trait ∈ traitState.failedTraits)
    | _ => true
  let collectedErrors := traitState.errors ++ nonCascadingErrors ++
    overlappingDefaultErrors [] state.implementations ++
    overlappingImplementationErrors environment traitState.traits state.implementations ++
    orphanImplementationErrors environment state.implementations ++
    implementationConditionErrors environment state.implementations ++
    shiftImplementationErrors traitState.traits state.implementations
  let errors := environment.declarations.flatMap fun declaration =>
    collectedErrors.filter fun error =>
      decide (programSignatureErrorDeclaration error = declaration.id)
  if errors.isEmpty then
    let implementations := state.implementations.map
      (ProgramImplementationSignature.closeUnderSuperclasses traitState.traits)
    .ok {
      functions := state.functions.map
        (ProgramFunctionSignature.closeUnderSuperclasses traitState.traits)
      implRules := implementations.map (ProgramImplementationSignature.implRule)
      traits := traitState.traits.map
        (ProgramTraitSignature.closeMethodsUnderSuperclasses traitState.traits)
      implementations
      dataTypes := state.dataTypes
      contracts := state.contracts
    }
  else
    .error errors

/-! The identity projections below are deliberately proved next to the
private collectors which establish them.  Their public consequences live in
`ProgramSignaturesProperties`; no collector state is exposed as API. -/

private def isFunctionSignatureDeclaration
    (declaration : ProgramDeclaration) : Bool :=
  match declaration.source.value with
  | .function _ => true
  | _ => false

private def isDataSignatureDeclaration
    (declaration : ProgramDeclaration) : Bool :=
  match declaration.source.value with
  | .enum _ => true
  | _ => false

private def isTraitSignatureDeclaration
    (declaration : ProgramDeclaration) : Bool :=
  match declaration.source.value with
  | .trait _ => true
  | _ => false

private def isImplementationSignatureDeclaration
    (declaration : ProgramDeclaration) : Bool :=
  match declaration.source.value with
  | .impl _ => true
  | _ => false

private def isContractSignatureDeclaration
    (declaration : ProgramDeclaration) : Bool :=
  match declaration.source.value with
  | .contract _ => true
  | _ => false

private theorem traitSignatureOfDeclaration_success_header
    {environment : ProgramEnvironment} {declaration : ProgramDeclaration}
    {source : Syntax.TraitDecl} {signature : ProgramTraitSignature}
    (success : traitSignatureOfDeclaration environment declaration source =
      .ok signature) :
    signature.id = declaration.id ∧
      signature.parameters = declarationParameters declaration ∧
      TraitSignatureStructuralWellFormed signature := by
  cases scopeEq : validateProgramTypeScope
      (ProgramTypeScope.ofDeclaration declaration) with
  | error error =>
      simp only [traitSignatureOfDeclaration, scopeEq] at success
      change Except.error (ProgramSignatureError.typeResolution
          declaration.id error) =
        Except.ok signature at success
      cases success
  | ok scopeUnit =>
      cases scopeUnit
      simp only [traitSignatureOfDeclaration, scopeEq] at success
      cases predicatesEq : resolveWhereClause environment declaration
          (ProgramTypeScope.ofDeclaration declaration)
          source.value.whereClause with
      | error error =>
          simp only [predicatesEq] at success
          change Except.error error = Except.ok signature at success
          cases success
      | ok predicates =>
          simp only [predicatesEq] at success
          cases methodsEq : traitMethodsOfDeclaration environment declaration
              (ProgramTypeScope.ofDeclaration declaration)
              source.value.methods 0 [] with
          | error error =>
              simp only [methodsEq] at success
              change Except.error error = Except.ok signature at success
              cases success
          | ok methods =>
              have methodStructure :=
                traitMethodsOfDeclaration_success_structure methodsEq
              simp only [methodsEq] at success
              change Except.ok {
                id := declaration.id
                name := source.value.name.value
                parameters := declarationParameters declaration
                wherePredicates := predicates
                methods
                source
              } = Except.ok signature at success
              injection success with signatureEq
              subst signature
              refine ⟨rfl, rfl, ?_⟩
              exact {
                method_names_nodup := methodStructure.1
                method_owners := methodStructure.2.2.1
                method_positions := by
                  intro position
                  simpa using methodStructure.2.2.2.1 position
                method_parameter_names_nodup := methodStructure.2.2.2.2
              }

private theorem traitSignatureOfDeclaration_success_id
    {environment : ProgramEnvironment} {declaration : ProgramDeclaration}
    {source : Syntax.TraitDecl} {signature : ProgramTraitSignature}
    (success : traitSignatureOfDeclaration environment declaration source =
      .ok signature) :
    signature.id = declaration.id :=
  (traitSignatureOfDeclaration_success_header success).1

private theorem traitSignatureOfDeclaration_success_parameters
    {environment : ProgramEnvironment} {declaration : ProgramDeclaration}
    {source : Syntax.TraitDecl} {signature : ProgramTraitSignature}
    (success : traitSignatureOfDeclaration environment declaration source =
      .ok signature) :
    SignatureParametersWellFormed signature.id signature.parameters := by
  have header := traitSignatureOfDeclaration_success_header success
  rw [header.1, header.2.1]
  exact declarationParameters_wellFormed declaration

private theorem traitSignatureOfDeclaration_success_structure
    {environment : ProgramEnvironment} {declaration : ProgramDeclaration}
    {source : Syntax.TraitDecl} {signature : ProgramTraitSignature}
    (success : traitSignatureOfDeclaration environment declaration source =
      .ok signature) :
    TraitSignatureStructuralWellFormed signature :=
  (traitSignatureOfDeclaration_success_header success).2.2

private theorem functionSignatureOfDeclaration_success_header
    {environment : ProgramEnvironment} {declaration : ProgramDeclaration}
    {source : Syntax.FunctionDecl} {signature : ProgramFunctionSignature}
    (success : functionSignatureOfDeclaration environment declaration source =
      .ok signature) :
    signature.id = declaration.id ∧
      signature.scheme.parameters = declarationParameters declaration ∧
      signature.parameterNames.Nodup ∧
      signature.scheme.body = .function
        (TypeSystem.Ty.productMany signature.parameterTypes)
        (TypeSystem.Ty.productMany signature.returnTypes) := by
  cases scopeEq : validateProgramTypeScope
      (ProgramTypeScope.ofDeclaration declaration) with
  | error error =>
      simp only [functionSignatureOfDeclaration, scopeEq] at success
      change Except.error (ProgramSignatureError.typeResolution
          declaration.id error) = Except.ok signature at success
      cases success
  | ok scopeUnit =>
      cases scopeUnit
      simp only [functionSignatureOfDeclaration, scopeEq] at success
      cases parametersEq : resolveFunctionParameters environment declaration
          (ProgramTypeScope.ofDeclaration declaration)
          source.value.signature.parameters.elements 0 [] with
      | error error =>
          simp only [parametersEq] at success
          change Except.error error = Except.ok signature at success
          cases success
      | ok parameters =>
          have parameterNames :=
            (resolveFunctionParameters_success_names parametersEq).1
          simp only [parametersEq] at success
          cases returnsEq : resolveFunctionReturns environment declaration
              (ProgramTypeScope.ofDeclaration declaration)
              ((source.value.signature.returnsClause.map
                fun clause => clause.types.elements).getD []) with
          | error error =>
              simp only [returnsEq] at success
              change Except.error error = Except.ok signature at success
              cases success
          | ok returns =>
              simp only [returnsEq] at success
              rcases returns with ⟨returnTypes, returnComptime⟩
              cases predicatesEq : resolveWhereClause environment declaration
                  (ProgramTypeScope.ofDeclaration declaration)
                  source.value.signature.whereClause with
              | error error =>
                  simp only [predicatesEq] at success
                  change Except.error error = Except.ok signature at success
                  cases success
              | ok predicates =>
                  simp only [predicatesEq] at success
                  injection success with signatureEq
                  subst signature
                  exact ⟨rfl, rfl, by
                    simpa [ProgramFunctionSignature.parameterNames] using
                      parameterNames, by
                    simp [ProgramFunctionSignature.parameterTypes]⟩

private theorem functionSignatureOfDeclaration_success_id
    {environment : ProgramEnvironment} {declaration : ProgramDeclaration}
    {source : Syntax.FunctionDecl} {signature : ProgramFunctionSignature}
    (success : functionSignatureOfDeclaration environment declaration source =
      .ok signature) :
    signature.id = declaration.id :=
  (functionSignatureOfDeclaration_success_header success).1

private theorem functionSignatureOfDeclaration_success_parameters
    {environment : ProgramEnvironment} {declaration : ProgramDeclaration}
    {source : Syntax.FunctionDecl} {signature : ProgramFunctionSignature}
    (success : functionSignatureOfDeclaration environment declaration source =
      .ok signature) :
    SignatureParametersWellFormed signature.id signature.scheme.parameters := by
  have header := functionSignatureOfDeclaration_success_header success
  rw [header.1, header.2.1]
  exact declarationParameters_wellFormed declaration

private theorem functionSignatureOfDeclaration_success_shape
    {environment : ProgramEnvironment} {declaration : ProgramDeclaration}
    {source : Syntax.FunctionDecl} {signature : ProgramFunctionSignature}
    (success : functionSignatureOfDeclaration environment declaration source =
      .ok signature) :
    signature.parameterNames.Nodup ∧
      signature.scheme.body = .function
        (TypeSystem.Ty.productMany signature.parameterTypes)
        (TypeSystem.Ty.productMany signature.returnTypes) :=
  (functionSignatureOfDeclaration_success_header success).2.2

private theorem dataSignatureOfDeclaration_success_header
    {environment : ProgramEnvironment} {declaration : ProgramDeclaration}
    {source : Syntax.EnumDecl} {signature : ProgramDataSignature}
    (success : dataSignatureOfDeclaration environment declaration source =
      .ok signature) :
    signature.id = declaration.id ∧
      signature.parameters = declarationParameters declaration ∧
      DataSignatureStructuralWellFormed signature := by
  cases scopeEq : validateProgramTypeScope
      (ProgramTypeScope.ofDeclaration declaration) with
  | error error =>
      simp only [dataSignatureOfDeclaration, scopeEq] at success
      change Except.error (ProgramSignatureError.typeResolution
          declaration.id error) = Except.ok signature at success
      cases success
  | ok scopeUnit =>
      cases scopeUnit
      simp only [dataSignatureOfDeclaration, scopeEq] at success
      cases constructorsEq : dataConstructorsOfDeclaration environment
          declaration (ProgramTypeScope.ofDeclaration declaration)
          source.value.constructors 0 [] with
      | error error =>
          simp only [constructorsEq] at success
          change Except.error error = Except.ok signature at success
          cases success
      | ok constructors =>
          have constructorStructure :=
            dataConstructorsOfDeclaration_success_structure constructorsEq
          simp only [constructorsEq] at success
          injection success with signatureEq
          subst signature
          refine ⟨rfl, rfl, ?_⟩
          exact {
            constructor_names_nodup := constructorStructure.1
            constructor_owners := constructorStructure.2.2.1
            constructor_positions := by
              intro position
              simpa using constructorStructure.2.2.2 position
          }

private theorem dataSignatureOfDeclaration_success_id
    {environment : ProgramEnvironment} {declaration : ProgramDeclaration}
    {source : Syntax.EnumDecl} {signature : ProgramDataSignature}
    (success : dataSignatureOfDeclaration environment declaration source =
      .ok signature) :
    signature.id = declaration.id :=
  (dataSignatureOfDeclaration_success_header success).1

private theorem dataSignatureOfDeclaration_success_parameters
    {environment : ProgramEnvironment} {declaration : ProgramDeclaration}
    {source : Syntax.EnumDecl} {signature : ProgramDataSignature}
    (success : dataSignatureOfDeclaration environment declaration source =
      .ok signature) :
    SignatureParametersWellFormed signature.id signature.parameters := by
  have header := dataSignatureOfDeclaration_success_header success
  rw [header.1, header.2.1]
  exact declarationParameters_wellFormed declaration

private theorem dataSignatureOfDeclaration_success_structure
    {environment : ProgramEnvironment} {declaration : ProgramDeclaration}
    {source : Syntax.EnumDecl} {signature : ProgramDataSignature}
    (success : dataSignatureOfDeclaration environment declaration source =
      .ok signature) :
    DataSignatureStructuralWellFormed signature :=
  (dataSignatureOfDeclaration_success_header success).2.2

private theorem contractSignatureOfDeclaration_success_header
    {declaration : ProgramDeclaration} {source : Syntax.ContractDecl}
    {signature : ProgramContractSignature}
    (success : contractSignatureOfDeclaration declaration source =
      .ok signature) :
    signature.id = declaration.id ∧
      signature.parameters = declarationParameters declaration := by
  cases scopeEq : validateProgramTypeScope
      (ProgramTypeScope.ofDeclaration declaration) with
  | error error =>
      simp only [contractSignatureOfDeclaration, scopeEq] at success
      change Except.error (ProgramSignatureError.typeResolution
          declaration.id error) = Except.ok signature at success
      cases success
  | ok scopeUnit =>
      cases scopeUnit
      simp only [contractSignatureOfDeclaration, scopeEq] at success
      injection success with signatureEq
      subst signature
      exact ⟨rfl, rfl⟩

private theorem contractSignatureOfDeclaration_success_id
    {declaration : ProgramDeclaration} {source : Syntax.ContractDecl}
    {signature : ProgramContractSignature}
    (success : contractSignatureOfDeclaration declaration source =
      .ok signature) :
    signature.id = declaration.id :=
  (contractSignatureOfDeclaration_success_header success).1

private theorem contractSignatureOfDeclaration_success_parameters
    {declaration : ProgramDeclaration} {source : Syntax.ContractDecl}
    {signature : ProgramContractSignature}
    (success : contractSignatureOfDeclaration declaration source =
      .ok signature) :
    SignatureParametersWellFormed signature.id signature.parameters := by
  have header := contractSignatureOfDeclaration_success_header success
  rw [header.1, header.2]
  exact declarationParameters_wellFormed declaration

private def Except.SuccessSatisfies {error value : Type}
    (property : value → Prop) : Except error value → Prop
  | .error _ => True
  | .ok result => property result

@[simp] private theorem Except.SuccessSatisfies.bind
    {error source target : Type} {property : target → Prop}
    (computation : Except error source)
    (continuation : source → Except error target)
    (preserves : ∀ value, Except.SuccessSatisfies property
      (continuation value)) :
    Except.SuccessSatisfies property (computation.bind continuation) := by
  cases computation with
  | error error => trivial
  | ok value => exact preserves value

private theorem Except.SuccessSatisfies.of_success
    {error value : Type} {property : value → Prop}
    (computation : Except error value)
    (sound : ∀ result, computation = .ok result → property result) :
    Except.SuccessSatisfies property computation := by
  cases equation : computation with
  | error error => trivial
  | ok result => exact sound result equation

private theorem Except.SuccessSatisfies.bind_property
    {error source target : Type}
    {sourceProperty : source → Prop} {targetProperty : target → Prop}
    (computation : Except error source)
    (continuation : source → Except error target)
    (sourceFacts : Except.SuccessSatisfies sourceProperty computation)
    (preserves : ∀ value, sourceProperty value →
      Except.SuccessSatisfies targetProperty (continuation value)) :
    Except.SuccessSatisfies targetProperty
      (computation.bind continuation) := by
  cases computation with
  | error error => trivial
  | ok value => exact preserves value sourceFacts

private theorem implementationSignatureOfDeclaration_success_header
    {environment : ProgramEnvironment} {declaration : ProgramDeclaration}
    {traits : List ProgramTraitSignature} {source : Syntax.ImplDecl}
    {signature : ProgramImplementationSignature}
    (success : implementationSignatureOfDeclaration environment declaration
      traits source = .ok signature) :
    signature.id = declaration.id ∧
      signature.parameters = declarationParameters declaration ∧
      ImplementationSignatureStructuralWellFormed signature ∧
      ImplementationSignatureHeadValidated traits signature := by
  have satisfies : Except.SuccessSatisfies
      (fun result : ProgramImplementationSignature =>
        result.id = declaration.id ∧
          result.parameters = declarationParameters declaration ∧
          ImplementationSignatureStructuralWellFormed result ∧
          ImplementationSignatureHeadValidated traits result)
      (implementationSignatureOfDeclaration environment declaration traits
        source) := by
    cases scopeEq : validateProgramTypeScope
        (ProgramTypeScope.ofDeclaration declaration) with
    | error error =>
        simp only [implementationSignatureOfDeclaration, scopeEq]
        change True
        trivial
    | ok scopeUnit =>
        cases scopeUnit
        simp only [implementationSignatureOfDeclaration, scopeEq]
        apply Except.SuccessSatisfies.bind
        intro headTypes
        cases headTypes with
        | nil =>
            change True
            trivial
        | cons subject arguments =>
            apply Except.SuccessSatisfies.bind
            intro head
            rcases head with ⟨resolvedSubject, resolvedArguments⟩
            apply Except.SuccessSatisfies.bind
            intro trait
            apply Except.SuccessSatisfies.bind_property
              (validateContained
                (ProgramSignatureError.implementationParameterNotInHead
                  declaration.id)
                (TypedTraitResolution.predicateParameters {
                  trait
                  subject := resolvedSubject
                  arguments := resolvedArguments
                })
                (declarationParameters declaration)) _
              (Except.SuccessSatisfies.of_success _
                (fun _ resultEq => validateContained_success resultEq))
            intro parametersChecked parametersContained
            apply Except.SuccessSatisfies.bind
            intro wherePredicates
            cases traitEq : traits.find? fun candidate =>
                decide (candidate.id = trait) with
            | none =>
                change True
                trivial
            | some traitSignature =>
                let substitution : TypeSystem.ParameterSubstitution :=
                  traitSignature.parameters.zip
                    (resolvedSubject :: resolvedArguments)
                let requiredPredicates := traitSignature.wherePredicates.map
                  (ProgramPredicate.applyParameters substitution)
                have predicatesContained : ∀ predicate, predicate ∈ requiredPredicates →
                    predicate ∈ impliedConditions wherePredicates requiredPredicates :=
                  fun _ member => mem_impliedConditions_of_required member
                apply Except.SuccessSatisfies.bind_property
                  (unmatchedImplMethodsOfDeclaration environment declaration
                    (ProgramTypeScope.ofDeclaration declaration)
                    source.value.methods 0 []) _
                  (Except.SuccessSatisfies.of_success _ (fun result resultEq =>
                    unmatchedImplMethodsOfDeclaration_success_structure resultEq))
                intro unmatchedMethods unmatchedStructure
                apply Except.SuccessSatisfies.bind
                intro methodsChecked
                apply Except.SuccessSatisfies.bind_property
                  (attachTraitMethods traitSignature.methods unmatchedMethods) _
                  (Except.SuccessSatisfies.of_success _ (fun result resultEq =>
                    (attachTraitMethods_success_structure resultEq
                      unmatchedStructure).1))
                intro methods methodsStructure
                refine ⟨rfl, rfl, {
                  method_names_nodup := methodsStructure.method_names_nodup
                  method_owners := methodsStructure.method_owners
                  method_positions := by
                    intro position
                    simpa using methodsStructure.method_positions position
                  method_parameter_names_nodup :=
                    methodsStructure.method_parameter_names_nodup
                }, ?_⟩
                have traitMember : traitSignature ∈ traits :=
                  List.mem_of_find?_eq_some traitEq
                have traitId : traitSignature.id = trait := by
                  have traitMatches : decide (traitSignature.id = trait) = true :=
                    List.find?_some (p := fun candidate : ProgramTraitSignature =>
                      decide (candidate.id = trait)) traitEq
                  exact of_decide_eq_true traitMatches
                exact {
                  parameters_in_head := parametersContained
                  trait_catalog := ⟨traitSignature, traitMember, by
                    simp [traitId], predicatesContained⟩
                }
  simpa [success, Except.SuccessSatisfies] using satisfies

/-- Successful implementation collection validates every attached method
against the exact selected trait and retains every required trait method.  The
trait structural premise is used only here to connect the two opposite name
lookups performed by validation and attachment. -/
private theorem implementationSignatureOfDeclaration_success_method_catalog
    {environment : ProgramEnvironment} {declaration : ProgramDeclaration}
    {traits : List ProgramTraitSignature} {source : Syntax.ImplDecl}
    {signature : ProgramImplementationSignature}
    (traitStructures : TraitSignaturesStructurallyWellFormed traits)
    (success : implementationSignatureOfDeclaration environment declaration
      traits source = .ok signature) :
    ImplementationSignatureMethodCatalogValidated traits signature := by
  have satisfies : Except.SuccessSatisfies
      (ImplementationSignatureMethodCatalogValidated traits)
      (implementationSignatureOfDeclaration environment declaration traits
        source) := by
    cases scopeEq : validateProgramTypeScope
        (ProgramTypeScope.ofDeclaration declaration) with
    | error error =>
        simp only [implementationSignatureOfDeclaration, scopeEq]
        change True
        trivial
    | ok scopeUnit =>
        cases scopeUnit
        simp only [implementationSignatureOfDeclaration, scopeEq]
        apply Except.SuccessSatisfies.bind
        intro headTypes
        cases headTypes with
        | nil =>
            change True
            trivial
        | cons subject arguments =>
            apply Except.SuccessSatisfies.bind
            intro head
            rcases head with ⟨resolvedSubject, resolvedArguments⟩
            apply Except.SuccessSatisfies.bind
            intro trait
            apply Except.SuccessSatisfies.bind
            intro parametersChecked
            apply Except.SuccessSatisfies.bind
            intro wherePredicates
            cases traitEq : traits.find? fun candidate =>
                decide (candidate.id = trait) with
            | none =>
                change True
                trivial
            | some traitSignature =>
                let substitution : TypeSystem.ParameterSubstitution :=
                  traitSignature.parameters.zip
                    (resolvedSubject :: resolvedArguments)
                let requiredPredicates := traitSignature.wherePredicates.map
                  (ProgramPredicate.applyParameters substitution)
                have traitMember : traitSignature ∈ traits :=
                  List.mem_of_find?_eq_some traitEq
                have traitId : traitSignature.id = trait := by
                  have traitMatches : decide (traitSignature.id = trait) = true :=
                    List.find?_some (p := fun candidate : ProgramTraitSignature =>
                      decide (candidate.id = trait)) traitEq
                  exact of_decide_eq_true traitMatches
                have traitStructure := traitStructures traitSignature traitMember
                apply Except.SuccessSatisfies.bind_property
                  (unmatchedImplMethodsOfDeclaration environment declaration
                    (ProgramTypeScope.ofDeclaration declaration)
                    source.value.methods 0 []) _
                  (Except.SuccessSatisfies.of_success _ (fun result resultEq =>
                    unmatchedImplMethodsOfDeclaration_success_structure resultEq))
                intro unmatchedMethods unmatchedStructure
                have validationFacts : Except.SuccessSatisfies
                    (fun _ : Unit =>
                      validateRequiredImplMethods declaration.id substitution
                        (impliedConditions wherePredicates requiredPredicates)
                        traitSignature.methods unmatchedMethods = .ok ())
                    (validateRequiredImplMethods declaration.id substitution
                      (impliedConditions wherePredicates requiredPredicates)
                      traitSignature.methods unmatchedMethods) :=
                  Except.SuccessSatisfies.of_success _ (fun result resultEq => by
                    cases result
                    exact resultEq)
                apply Except.SuccessSatisfies.bind_property
                  (validateRequiredImplMethods declaration.id substitution
                    (impliedConditions wherePredicates requiredPredicates)
                    traitSignature.methods unmatchedMethods) _
                  validationFacts
                intro methodsChecked validationSuccess
                cases methodsChecked
                apply Except.SuccessSatisfies.bind_property
                  (attachTraitMethods traitSignature.methods unmatchedMethods) _
                  (Except.SuccessSatisfies.of_success _ (fun methods attached =>
                    validatedAndAttachedImplMethods_matchTrait traitStructure
                      unmatchedStructure validationSuccess attached))
                intro methods methodCatalog
                exact {
                  trait_catalog := ⟨traitSignature, traitMember, by
                    simp [traitId], by
                    simpa [substitution] using
                      methodCatalog.method_correspondence, methodCatalog.complete⟩
                }
  simpa [success, Except.SuccessSatisfies] using satisfies

private theorem implementationSignatureOfDeclaration_success_id
    {environment : ProgramEnvironment} {declaration : ProgramDeclaration}
    {traits : List ProgramTraitSignature} {source : Syntax.ImplDecl}
    {signature : ProgramImplementationSignature}
    (success : implementationSignatureOfDeclaration environment declaration
      traits source = .ok signature) :
    signature.id = declaration.id :=
  (implementationSignatureOfDeclaration_success_header success).1

private theorem implementationSignatureOfDeclaration_success_parameters
    {environment : ProgramEnvironment} {declaration : ProgramDeclaration}
    {traits : List ProgramTraitSignature} {source : Syntax.ImplDecl}
    {signature : ProgramImplementationSignature}
    (success : implementationSignatureOfDeclaration environment declaration
      traits source = .ok signature) :
    SignatureParametersWellFormed signature.id signature.parameters := by
  have header := implementationSignatureOfDeclaration_success_header success
  rw [header.1, header.2.1]
  exact declarationParameters_wellFormed declaration

private theorem implementationSignatureOfDeclaration_success_structure
    {environment : ProgramEnvironment} {declaration : ProgramDeclaration}
    {traits : List ProgramTraitSignature} {source : Syntax.ImplDecl}
    {signature : ProgramImplementationSignature}
    (success : implementationSignatureOfDeclaration environment declaration
      traits source = .ok signature) :
    ImplementationSignatureStructuralWellFormed signature :=
  (implementationSignatureOfDeclaration_success_header success).2.2.1

private theorem implementationSignatureOfDeclaration_success_head_validated
    {environment : ProgramEnvironment} {declaration : ProgramDeclaration}
    {traits : List ProgramTraitSignature} {source : Syntax.ImplDecl}
    {signature : ProgramImplementationSignature}
    (success : implementationSignatureOfDeclaration environment declaration
      traits source = .ok signature) :
    ImplementationSignatureHeadValidated traits signature :=
  (implementationSignatureOfDeclaration_success_header success).2.2.2

private theorem all_mem_append_singleton {value : Type} {property : value → Prop}
    {values : List value} {last : value}
    (preceding : ∀ candidate, candidate ∈ values → property candidate)
    (suffix : property last) :
    ∀ candidate, candidate ∈ values ++ [last] → property candidate := by
  intro candidate member
  simp only [List.mem_append, List.mem_singleton] at member
  rcases member with member | rfl
  · exact preceding candidate member
  · exact suffix

private def TraitSignatureParametersWellFormed
    (traits : List ProgramTraitSignature) : Prop :=
  ∀ signature, signature ∈ traits →
    SignatureParametersWellFormed signature.id signature.parameters

private theorem collectProgramTraits_parameters_wellFormed
    (environment : ProgramEnvironment)
    (declarations : List ProgramDeclaration)
    (state : ProgramTraitBuildState)
    (initial : TraitSignatureParametersWellFormed state.traits) :
    TraitSignatureParametersWellFormed
      (collectProgramTraits environment declarations state).traits := by
  induction declarations generalizing state with
  | nil => simpa [collectProgramTraits] using initial
  | cons declaration rest induction =>
      cases sourceEq : declaration.source.value with
      | trait source =>
          simp only [collectProgramTraits, sourceEq]
          cases signatureEq : traitSignatureOfDeclaration environment declaration
              source with
          | error error => exact induction _ initial
          | ok signature =>
              apply induction _
              exact all_mem_append_singleton initial
                (traitSignatureOfDeclaration_success_parameters signatureEq)
      | importDecl _ | exportDecl _ | pragmaDecl _ | typeAlias _ | enum _
      | impl _ | contract _ | function _ | error =>
          simp only [collectProgramTraits, sourceEq]
          exact induction _ initial

private theorem collectProgramTraits_structurally_wellFormed
    (environment : ProgramEnvironment)
    (declarations : List ProgramDeclaration)
    (state : ProgramTraitBuildState)
    (initial : TraitSignaturesStructurallyWellFormed state.traits) :
    TraitSignaturesStructurallyWellFormed
      (collectProgramTraits environment declarations state).traits := by
  induction declarations generalizing state with
  | nil => simpa [collectProgramTraits] using initial
  | cons declaration rest induction =>
      cases sourceEq : declaration.source.value with
      | trait source =>
          simp only [collectProgramTraits, sourceEq]
          cases signatureEq : traitSignatureOfDeclaration environment declaration
              source with
          | error error => exact induction _ initial
          | ok signature =>
              apply induction _
              exact all_mem_append_singleton initial
                (traitSignatureOfDeclaration_success_structure signatureEq)
      | importDecl _ | exportDecl _ | pragmaDecl _ | typeAlias _ | enum _
      | impl _ | contract _ | function _ | error =>
          simp only [collectProgramTraits, sourceEq]
          exact induction _ initial

private theorem collectedProgramTraits_structurally_wellFormed
    (environment : ProgramEnvironment) :
    TraitSignaturesStructurallyWellFormed
      (collectProgramTraits environment environment.declarations {}).traits := by
  apply collectProgramTraits_structurally_wellFormed environment
    environment.declarations ({} : ProgramTraitBuildState)
  intro signature member
  simp at member

private structure ProgramSignatureBuildFacts
    (traits : List ProgramTraitSignature)
    (state : ProgramSignatureBuildState) : Prop where
  functions : ∀ signature, signature ∈ state.functions →
    SignatureParametersWellFormed signature.id signature.scheme.parameters
  functionShapes : ∀ signature, signature ∈ state.functions →
    signature.parameterNames.Nodup ∧
      signature.scheme.body = .function
        (TypeSystem.Ty.productMany signature.parameterTypes)
        (TypeSystem.Ty.productMany signature.returnTypes)
  dataTypes : ∀ signature, signature ∈ state.dataTypes →
    SignatureParametersWellFormed signature.id signature.parameters
  dataShapes : ∀ signature, signature ∈ state.dataTypes →
    DataSignatureStructuralWellFormed signature
  implementations : ∀ signature, signature ∈ state.implementations →
    SignatureParametersWellFormed signature.id signature.parameters
  implementationShapes : ∀ signature, signature ∈ state.implementations →
    ImplementationSignatureStructuralWellFormed signature
  implementationHeads : ∀ signature, signature ∈ state.implementations →
    ImplementationSignatureHeadValidated traits signature
  implementationMethods : ∀ signature, signature ∈ state.implementations →
    ImplementationSignatureMethodCatalogValidated traits signature
  contracts : ∀ signature, signature ∈ state.contracts →
    SignatureParametersWellFormed signature.id signature.parameters

private theorem ProgramSignatureBuildFacts.withErrors
    {traits : List ProgramTraitSignature} {state : ProgramSignatureBuildState}
    (initial : ProgramSignatureBuildFacts traits state)
    (errors : List ProgramSignatureError) :
    ProgramSignatureBuildFacts traits
      { state with errors } := {
  functions := initial.functions
  functionShapes := initial.functionShapes
  dataTypes := initial.dataTypes
  dataShapes := initial.dataShapes
  implementations := initial.implementations
  implementationShapes := initial.implementationShapes
  implementationHeads := initial.implementationHeads
  implementationMethods := initial.implementationMethods
  contracts := initial.contracts
}

private theorem ProgramSignatureBuildFacts.addFunction
    {traits : List ProgramTraitSignature} {state : ProgramSignatureBuildState}
    (initial : ProgramSignatureBuildFacts traits state)
    {signature : ProgramFunctionSignature}
    (wellFormed : SignatureParametersWellFormed signature.id
      signature.scheme.parameters)
    (shape : signature.parameterNames.Nodup ∧
      signature.scheme.body = .function
        (TypeSystem.Ty.productMany signature.parameterTypes)
        (TypeSystem.Ty.productMany signature.returnTypes)) :
    ProgramSignatureBuildFacts traits
      { state with functions := state.functions ++ [signature] } := {
  initial with
  functions := all_mem_append_singleton initial.functions wellFormed
  functionShapes := all_mem_append_singleton initial.functionShapes shape
}

private theorem ProgramSignatureBuildFacts.addDataType
    {traits : List ProgramTraitSignature} {state : ProgramSignatureBuildState}
    (initial : ProgramSignatureBuildFacts traits state)
    {signature : ProgramDataSignature}
    (wellFormed : SignatureParametersWellFormed signature.id
      signature.parameters)
    (shape : DataSignatureStructuralWellFormed signature) :
    ProgramSignatureBuildFacts traits
      { state with dataTypes := state.dataTypes ++ [signature] } := {
  initial with
  dataTypes := all_mem_append_singleton initial.dataTypes wellFormed
  dataShapes := all_mem_append_singleton initial.dataShapes shape
}

private theorem ProgramSignatureBuildFacts.addImplementation
    {traits : List ProgramTraitSignature} {state : ProgramSignatureBuildState}
    (initial : ProgramSignatureBuildFacts traits state)
    {signature : ProgramImplementationSignature}
    (wellFormed : SignatureParametersWellFormed signature.id
      signature.parameters)
    (shape : ImplementationSignatureStructuralWellFormed signature)
    (head : ImplementationSignatureHeadValidated traits signature)
    (methods : ImplementationSignatureMethodCatalogValidated traits signature) :
    ProgramSignatureBuildFacts traits
      { state with
        implementations := state.implementations ++ [signature]
      } := {
  initial with
  implementations := all_mem_append_singleton initial.implementations wellFormed
  implementationShapes :=
    all_mem_append_singleton initial.implementationShapes shape
  implementationHeads :=
    all_mem_append_singleton initial.implementationHeads head
  implementationMethods :=
    all_mem_append_singleton initial.implementationMethods methods
}

private theorem ProgramSignatureBuildFacts.addContract
    {traits : List ProgramTraitSignature} {state : ProgramSignatureBuildState}
    (initial : ProgramSignatureBuildFacts traits state)
    {signature : ProgramContractSignature}
    (wellFormed : SignatureParametersWellFormed signature.id
      signature.parameters) :
    ProgramSignatureBuildFacts traits
      { state with contracts := state.contracts ++ [signature] } := {
  initial with
  contracts := all_mem_append_singleton initial.contracts wellFormed
}

private theorem collectProgramSignatures_facts
    (environment : ProgramEnvironment) (traits : List ProgramTraitSignature)
    (declarations : List ProgramDeclaration)
    (state : ProgramSignatureBuildState)
    (traitStructures : TraitSignaturesStructurallyWellFormed traits)
    (initial : ProgramSignatureBuildFacts traits state) :
    ProgramSignatureBuildFacts traits
      (collectProgramSignatures environment traits declarations state) := by
  induction declarations generalizing state with
  | nil => simpa [collectProgramSignatures] using initial
  | cons declaration rest induction =>
      cases sourceEq : declaration.source.value with
      | typeAlias source =>
          simp only [collectProgramSignatures, sourceEq]
          cases resolveSignatureAliasBody environment declaration
              source.value.value with
          | error error =>
              simpa using induction
                { state with errors := state.errors ++ [error] }
                (initial.withErrors (state.errors ++ [error]))
          | ok type => simpa using induction state initial
      | enum source =>
          simp only [collectProgramSignatures, sourceEq]
          cases signatureEq : dataSignatureOfDeclaration environment declaration
              source with
          | error error =>
              simpa using induction
                { state with errors := state.errors ++ [error] }
                (initial.withErrors (state.errors ++ [error]))
          | ok signature =>
              simpa using induction
                { state with dataTypes := state.dataTypes ++ [signature] }
                (initial.addDataType
                  (dataSignatureOfDeclaration_success_parameters signatureEq)
                  (dataSignatureOfDeclaration_success_structure signatureEq))
      | contract source =>
          simp only [collectProgramSignatures, sourceEq]
          cases signatureEq : contractSignatureOfDeclaration declaration source with
          | error error =>
              simpa using induction
                { state with errors := state.errors ++ [error] }
                (initial.withErrors (state.errors ++ [error]))
          | ok signature =>
              simpa using induction
                { state with contracts := state.contracts ++ [signature] }
                (initial.addContract
                  (contractSignatureOfDeclaration_success_parameters signatureEq))
      | function source =>
          simp only [collectProgramSignatures, sourceEq,
            signatureItemOfDeclaration]
          cases signatureEq : functionSignatureOfDeclaration environment declaration
              source with
          | error error =>
              simpa [bind, Except.bind, pure, Pure.pure, Except.pure] using
                induction { state with errors := state.errors ++ [error] }
                  (initial.withErrors (state.errors ++ [error]))
          | ok signature =>
              simpa [bind, Except.bind, pure, Pure.pure, Except.pure] using induction
                { state with functions := state.functions ++ [signature] }
                (initial.addFunction
                  (functionSignatureOfDeclaration_success_parameters signatureEq)
                  (functionSignatureOfDeclaration_success_shape signatureEq))
      | impl source =>
          simp only [collectProgramSignatures, sourceEq,
            signatureItemOfDeclaration]
          cases signatureEq : implementationSignatureOfDeclaration environment
              declaration traits source with
          | error error =>
              simpa [bind, Except.bind, pure, Pure.pure, Except.pure] using
                induction { state with errors := state.errors ++ [error] }
                  (initial.withErrors (state.errors ++ [error]))
          | ok signature =>
              simpa [bind, Except.bind, pure, Pure.pure, Except.pure] using induction
                { state with
                  implementations := state.implementations ++ [signature]
                }
                (initial.addImplementation
                  (implementationSignatureOfDeclaration_success_parameters signatureEq)
                  (implementationSignatureOfDeclaration_success_structure signatureEq)
                  (implementationSignatureOfDeclaration_success_head_validated
                    signatureEq)
                  (implementationSignatureOfDeclaration_success_method_catalog
                    traitStructures signatureEq))
      | importDecl _ | exportDecl _ | pragmaDecl _ | trait _ | error =>
          simp only [collectProgramSignatures, sourceEq,
            signatureItemOfDeclaration]
          simpa using induction state initial

private theorem collectProgramTraits_ids_sublist
    (environment : ProgramEnvironment)
    (declarations : List ProgramDeclaration)
    (state : ProgramTraitBuildState) :
    ((collectProgramTraits environment declarations state).traits.map
        (fun signature => signature.id)).Sublist
      (state.traits.map (fun signature => signature.id) ++
        (declarations.filter isTraitSignatureDeclaration).map
          (fun declaration => declaration.id)) := by
  induction declarations generalizing state with
  | nil => simp [collectProgramTraits]
  | cons declaration rest induction =>
      cases sourceEq : declaration.source.value with
      | trait source =>
          simp only [collectProgramTraits, sourceEq]
          cases signatureEq : traitSignatureOfDeclaration environment declaration
              source with
          | error error =>
              exact (induction _).trans (by
                simp [List.filter, isTraitSignatureDeclaration, sourceEq])
          | ok signature =>
              have idEq := traitSignatureOfDeclaration_success_id signatureEq
              exact (induction _).trans (by
                simp [List.filter, isTraitSignatureDeclaration, sourceEq, idEq])
      | importDecl source | exportDecl source | pragmaDecl source
      | typeAlias source | enum source | impl source | contract source
      | function source =>
          simp only [collectProgramTraits, sourceEq]
          exact (induction state).trans (by
            simp [List.filter, isTraitSignatureDeclaration, sourceEq])
      | error =>
          simp only [collectProgramTraits, sourceEq]
          exact (induction state).trans (by
            simp [List.filter, isTraitSignatureDeclaration, sourceEq])

private theorem append_sublist_append_cons {alpha : Type}
    (before after : List alpha) (value : alpha) :
    (before ++ after).Sublist (before ++ value :: after) :=
  (List.Sublist.refl before).append
    (List.Sublist.cons value (List.Sublist.refl after))

private theorem collectProgramSignatures_ids_sublist
    (environment : ProgramEnvironment) (traits : List ProgramTraitSignature)
    (declarations : List ProgramDeclaration)
    (state : ProgramSignatureBuildState) :
    ((collectProgramSignatures environment traits declarations state).functions.map
        (fun signature => signature.id)).Sublist
      (state.functions.map (fun signature => signature.id) ++
        (declarations.filter isFunctionSignatureDeclaration).map
          (fun declaration => declaration.id)) ∧
    ((collectProgramSignatures environment traits declarations state).dataTypes.map
        (fun signature => signature.id)).Sublist
      (state.dataTypes.map (fun signature => signature.id) ++
        (declarations.filter isDataSignatureDeclaration).map
          (fun declaration => declaration.id)) ∧
    ((collectProgramSignatures environment traits declarations state).implementations.map
        (fun signature => signature.id)).Sublist
      (state.implementations.map (fun signature => signature.id) ++
        (declarations.filter isImplementationSignatureDeclaration).map
          (fun declaration => declaration.id)) := by
  induction declarations generalizing state with
  | nil => simp [collectProgramSignatures]
  | cons declaration rest induction =>
      cases sourceEq : declaration.source.value with
      | typeAlias source =>
          simp only [collectProgramSignatures, sourceEq]
          cases aliasEq : resolveSignatureAliasBody environment declaration
              source.value.value with
          | error error =>
              simpa [List.filter, isFunctionSignatureDeclaration,
                isDataSignatureDeclaration,
                isImplementationSignatureDeclaration, sourceEq] using
                induction { state with errors := state.errors ++ [error] }
          | ok type =>
              simpa [List.filter, isFunctionSignatureDeclaration,
                isDataSignatureDeclaration,
                isImplementationSignatureDeclaration, sourceEq] using
                induction state
      | enum source =>
          simp only [collectProgramSignatures, sourceEq]
          cases signatureEq : dataSignatureOfDeclaration environment declaration
              source with
          | error error =>
              obtain ⟨functions, dataTypes, implementations⟩ :=
                induction { state with errors := state.errors ++ [error] }
              refine ⟨?_, ?_, ?_⟩
              · simpa [List.filter, isFunctionSignatureDeclaration,
                  sourceEq] using functions
              · exact dataTypes.trans (by
                  simpa only [List.filter, isDataSignatureDeclaration,
                    sourceEq, Bool.true_eq, List.map]
                    using append_sublist_append_cons
                      (state.dataTypes.map fun signature => signature.id)
                      ((rest.filter isDataSignatureDeclaration).map
                        fun candidate => candidate.id)
                      declaration.id)
              · simpa [List.filter, isImplementationSignatureDeclaration,
                  sourceEq] using implementations
          | ok signature =>
              have idEq := dataSignatureOfDeclaration_success_id signatureEq
              simpa [List.filter, isFunctionSignatureDeclaration,
                isDataSignatureDeclaration,
                isImplementationSignatureDeclaration, sourceEq, idEq,
                List.map_append, List.append_assoc] using
                induction { state with dataTypes := state.dataTypes ++ [signature] }
      | function source =>
          simp only [collectProgramSignatures, sourceEq,
            signatureItemOfDeclaration]
          cases signatureEq : functionSignatureOfDeclaration environment declaration
              source with
          | error error =>
              obtain ⟨functions, dataTypes, implementations⟩ :=
                induction { state with errors := state.errors ++ [error] }
              refine ⟨?_, ?_, ?_⟩
              · exact functions.trans (by
                  simpa only [List.filter, isFunctionSignatureDeclaration,
                    sourceEq, Bool.true_eq, List.map]
                    using append_sublist_append_cons
                      (state.functions.map fun signature => signature.id)
                      ((rest.filter isFunctionSignatureDeclaration).map
                        fun candidate => candidate.id)
                      declaration.id)
              · simpa [List.filter, isDataSignatureDeclaration,
                  sourceEq, signatureEq, bind, Except.bind] using dataTypes
              · simpa [List.filter, isImplementationSignatureDeclaration,
                  sourceEq, signatureEq, bind, Except.bind] using implementations
          | ok signature =>
              have idEq := functionSignatureOfDeclaration_success_id signatureEq
              simpa [List.filter, isFunctionSignatureDeclaration,
                isDataSignatureDeclaration,
                isImplementationSignatureDeclaration, sourceEq, idEq,
                signatureEq, bind, Except.bind, pure, Pure.pure, Except.pure,
                List.map_append, List.append_assoc] using
                induction { state with
                  functions := state.functions ++ [signature]
                }
      | impl source =>
          simp only [collectProgramSignatures, sourceEq,
            signatureItemOfDeclaration]
          cases signatureEq : implementationSignatureOfDeclaration environment
              declaration traits source with
          | error error =>
              obtain ⟨functions, dataTypes, implementations⟩ :=
                induction { state with errors := state.errors ++ [error] }
              refine ⟨?_, ?_, ?_⟩
              · simpa [List.filter, isFunctionSignatureDeclaration,
                  sourceEq, signatureEq, bind, Except.bind] using functions
              · simpa [List.filter, isDataSignatureDeclaration,
                  sourceEq, signatureEq, bind, Except.bind] using dataTypes
              · exact implementations.trans (by
                  simpa only [List.filter,
                    isImplementationSignatureDeclaration, sourceEq,
                    Bool.true_eq, List.map]
                    using append_sublist_append_cons
                      (state.implementations.map fun signature => signature.id)
                      ((rest.filter isImplementationSignatureDeclaration).map
                        fun candidate => candidate.id)
                      declaration.id)
          | ok signature =>
              have idEq :=
                implementationSignatureOfDeclaration_success_id signatureEq
              simpa [List.filter, isFunctionSignatureDeclaration,
                isDataSignatureDeclaration,
                isImplementationSignatureDeclaration, sourceEq, idEq,
                signatureEq, bind, Except.bind, pure, Pure.pure, Except.pure,
                List.map_append, List.append_assoc] using
                induction { state with
                  implementations := state.implementations ++ [signature]
                }
      | contract source =>
          simp only [collectProgramSignatures, sourceEq]
          cases signatureEq : contractSignatureOfDeclaration declaration source with
          | error error =>
              simpa [List.filter, isFunctionSignatureDeclaration,
                isDataSignatureDeclaration,
                isImplementationSignatureDeclaration, sourceEq] using
                induction { state with errors := state.errors ++ [error] }
          | ok contract =>
              simpa [List.filter, isFunctionSignatureDeclaration,
                isDataSignatureDeclaration,
                isImplementationSignatureDeclaration, sourceEq, signatureEq] using
                induction { state with
                  contracts := state.contracts ++ [contract]
                }
      | importDecl source | exportDecl source | pragmaDecl source
      | trait source =>
          simp only [collectProgramSignatures, sourceEq,
            signatureItemOfDeclaration]
          simpa [List.filter, isFunctionSignatureDeclaration,
            isDataSignatureDeclaration,
            isImplementationSignatureDeclaration, sourceEq] using
            induction state
      | error =>
          simp only [collectProgramSignatures, sourceEq,
            signatureItemOfDeclaration]
          simpa [List.filter, isFunctionSignatureDeclaration,
            isDataSignatureDeclaration,
            isImplementationSignatureDeclaration, sourceEq] using
            induction state

private theorem collectProgramSignatures_contract_ids_sublist
    (environment : ProgramEnvironment) (traits : List ProgramTraitSignature)
    (declarations : List ProgramDeclaration)
    (state : ProgramSignatureBuildState) :
    ((collectProgramSignatures environment traits declarations state).contracts.map
        (fun signature => signature.id)).Sublist
      (state.contracts.map (fun signature => signature.id) ++
        (declarations.filter isContractSignatureDeclaration).map
          (fun declaration => declaration.id)) := by
  induction declarations generalizing state with
  | nil => simp [collectProgramSignatures]
  | cons declaration rest induction =>
      cases sourceEq : declaration.source.value with
      | typeAlias source =>
          simp only [collectProgramSignatures, sourceEq]
          cases aliasEq : resolveSignatureAliasBody environment declaration
              source.value.value with
          | error error =>
              simpa [List.filter, isContractSignatureDeclaration, sourceEq] using
                induction { state with errors := state.errors ++ [error] }
          | ok type =>
              simpa [List.filter, isContractSignatureDeclaration, sourceEq] using
                induction state
      | enum source =>
          simp only [collectProgramSignatures, sourceEq]
          cases signatureEq : dataSignatureOfDeclaration environment declaration
              source with
          | error error =>
              simpa [List.filter, isContractSignatureDeclaration, sourceEq] using
                induction { state with errors := state.errors ++ [error] }
          | ok signature =>
              simpa [List.filter, isContractSignatureDeclaration, sourceEq] using
                induction { state with
                  dataTypes := state.dataTypes ++ [signature]
                }
      | contract source =>
          simp only [collectProgramSignatures, sourceEq]
          cases signatureEq : contractSignatureOfDeclaration declaration source with
          | error error =>
              exact (induction { state with
                errors := state.errors ++ [error]
              }).trans (by
                simpa only [List.filter, isContractSignatureDeclaration,
                  sourceEq, Bool.true_eq, List.map]
                  using append_sublist_append_cons
                    (state.contracts.map fun signature => signature.id)
                    ((rest.filter isContractSignatureDeclaration).map
                      fun candidate => candidate.id)
                    declaration.id)
          | ok signature =>
              have idEq := contractSignatureOfDeclaration_success_id signatureEq
              simpa [List.filter, isContractSignatureDeclaration, sourceEq,
                idEq, List.map_append, List.append_assoc] using
                induction { state with
                  contracts := state.contracts ++ [signature]
                }
      | importDecl _ | exportDecl _ | pragmaDecl _ | trait _
      | impl _ | function _ | error =>
          simp only [collectProgramSignatures, sourceEq]
          cases itemEq : signatureItemOfDeclaration environment traits declaration with
          | error error =>
              simpa [List.filter, isContractSignatureDeclaration, sourceEq,
                itemEq] using
                induction { state with errors := state.errors ++ [error] }
          | ok item =>
              rcases item with ⟨function?, implementation?⟩
              simpa [List.filter, isContractSignatureDeclaration, sourceEq,
                itemEq] using
                induction { state with
                  functions := state.functions ++ function?.toList
                  implementations :=
                    state.implementations ++ implementation?.toList
                }
private theorem signature_category_ids_nodup
    (declarations : List ProgramDeclaration)
    (unique : (declarations.map fun declaration => declaration.id).Nodup) :
    ((declarations.filter isFunctionSignatureDeclaration).map
          (fun declaration => declaration.id) ++
      (declarations.filter isDataSignatureDeclaration).map
          (fun declaration => declaration.id) ++
      (declarations.filter isTraitSignatureDeclaration).map
          (fun declaration => declaration.id) ++
      (declarations.filter isImplementationSignatureDeclaration).map
          (fun declaration => declaration.id) ++
      (declarations.filter isContractSignatureDeclaration).map
          (fun declaration => declaration.id)).Nodup := by
  induction declarations with
  | nil => simp
  | cons declaration rest induction =>
      have uniqueParts := List.nodup_cons.mp unique
      have tailNodup := induction uniqueParts.2
      have headNotFiltered
          (selector : ProgramDeclaration → Bool) :
          declaration.id ∉
            (rest.filter selector).map (fun candidate => candidate.id) := by
        intro member
        apply uniqueParts.1
        exact ((List.filter_sublist (p := selector)).map
          (fun candidate : ProgramDeclaration => candidate.id)).subset member
      have headNotCategories :
          declaration.id ∉
            ((rest.filter isFunctionSignatureDeclaration).map
                (fun candidate => candidate.id) ++
              (rest.filter isDataSignatureDeclaration).map
                (fun candidate => candidate.id) ++
              (rest.filter isTraitSignatureDeclaration).map
                (fun candidate => candidate.id) ++
              (rest.filter isImplementationSignatureDeclaration).map
                (fun candidate => candidate.id) ++
              (rest.filter isContractSignatureDeclaration).map
                (fun candidate => candidate.id)) := by
        simp only [List.mem_append, not_or]
        exact ⟨⟨⟨⟨headNotFiltered _, headNotFiltered _⟩,
          headNotFiltered _⟩, headNotFiltered _⟩, headNotFiltered _⟩
      have inserted :
          (declaration.id ::
            ((rest.filter isFunctionSignatureDeclaration).map
                (fun candidate => candidate.id) ++
              (rest.filter isDataSignatureDeclaration).map
                (fun candidate => candidate.id) ++
              (rest.filter isTraitSignatureDeclaration).map
                (fun candidate => candidate.id) ++
              (rest.filter isImplementationSignatureDeclaration).map
                (fun candidate => candidate.id) ++
              (rest.filter isContractSignatureDeclaration).map
                (fun candidate => candidate.id))).Nodup :=
        List.nodup_cons.mpr ⟨headNotCategories, tailNodup⟩
      cases sourceEq : declaration.source.value with
      | function _ =>
          simpa [List.filter, isFunctionSignatureDeclaration,
            isDataSignatureDeclaration, isTraitSignatureDeclaration,
            isImplementationSignatureDeclaration,
            isContractSignatureDeclaration, sourceEq] using inserted
      | enum _ =>
          apply inserted.perm
          simpa [List.filter, isFunctionSignatureDeclaration,
            isDataSignatureDeclaration, isTraitSignatureDeclaration,
            isImplementationSignatureDeclaration,
            isContractSignatureDeclaration, sourceEq,
            List.append_assoc] using
            (List.perm_middle (α := Resolved.DeclarationId)
              (a := declaration.id)
              (l₁ := (rest.filter isFunctionSignatureDeclaration).map
                (fun candidate => candidate.id))
              (l₂ :=
                (rest.filter isDataSignatureDeclaration).map
                    (fun candidate => candidate.id) ++
                  (rest.filter isTraitSignatureDeclaration).map
                    (fun candidate => candidate.id) ++
                  (rest.filter isImplementationSignatureDeclaration).map
                    (fun candidate => candidate.id) ++
                  (rest.filter isContractSignatureDeclaration).map
                    (fun candidate => candidate.id))).symm
      | trait _ =>
          apply inserted.perm
          simpa [List.filter, isFunctionSignatureDeclaration,
            isDataSignatureDeclaration, isTraitSignatureDeclaration,
            isImplementationSignatureDeclaration,
            isContractSignatureDeclaration, sourceEq,
            List.append_assoc] using
            (List.perm_middle (α := Resolved.DeclarationId)
              (a := declaration.id)
              (l₁ :=
                (rest.filter isFunctionSignatureDeclaration).map
                    (fun candidate => candidate.id) ++
                  (rest.filter isDataSignatureDeclaration).map
                    (fun candidate => candidate.id))
              (l₂ :=
                (rest.filter isTraitSignatureDeclaration).map
                    (fun candidate => candidate.id) ++
                  (rest.filter isImplementationSignatureDeclaration).map
                    (fun candidate => candidate.id) ++
                  (rest.filter isContractSignatureDeclaration).map
                    (fun candidate => candidate.id))).symm
      | impl _ =>
          apply inserted.perm
          simpa [List.filter, isFunctionSignatureDeclaration,
            isDataSignatureDeclaration, isTraitSignatureDeclaration,
            isImplementationSignatureDeclaration,
            isContractSignatureDeclaration, sourceEq,
            List.append_assoc] using
            (List.perm_middle (α := Resolved.DeclarationId)
              (a := declaration.id)
              (l₁ :=
                (rest.filter isFunctionSignatureDeclaration).map
                    (fun candidate => candidate.id) ++
                  (rest.filter isDataSignatureDeclaration).map
                    (fun candidate => candidate.id) ++
                  (rest.filter isTraitSignatureDeclaration).map
                    (fun candidate => candidate.id))
              (l₂ :=
                (rest.filter isImplementationSignatureDeclaration).map
                    (fun candidate => candidate.id) ++
                  (rest.filter isContractSignatureDeclaration).map
                    (fun candidate => candidate.id))).symm
      | contract _ =>
          apply inserted.perm
          simpa [List.filter, isFunctionSignatureDeclaration,
            isDataSignatureDeclaration, isTraitSignatureDeclaration,
            isImplementationSignatureDeclaration,
            isContractSignatureDeclaration, sourceEq,
            List.append_assoc] using
            (List.perm_middle (α := Resolved.DeclarationId)
              (a := declaration.id)
              (l₁ :=
                (rest.filter isFunctionSignatureDeclaration).map
                    (fun candidate => candidate.id) ++
                  (rest.filter isDataSignatureDeclaration).map
                    (fun candidate => candidate.id) ++
                  (rest.filter isTraitSignatureDeclaration).map
                    (fun candidate => candidate.id) ++
                  (rest.filter isImplementationSignatureDeclaration).map
                    (fun candidate => candidate.id))
              (l₂ :=
                (rest.filter isContractSignatureDeclaration).map
                  (fun candidate => candidate.id))).symm
      | importDecl _ | exportDecl _ | pragmaDecl _ | typeAlias _
      | error =>
          simpa [List.filter, isFunctionSignatureDeclaration,
            isDataSignatureDeclaration, isTraitSignatureDeclaration,
            isImplementationSignatureDeclaration,
            isContractSignatureDeclaration, sourceEq] using tailNodup

/-- Successful collection cannot duplicate a declaration identity across or
within the five declaration-backed signature categories when the input
environment itself has unique declaration identities. -/
theorem buildProgramSignatures_success_declaration_ids_nodup
    {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    (environmentIds :
      (environment.declarations.map fun declaration => declaration.id).Nodup)
    (success : buildProgramSignatures environment = .ok signatures) :
    (signatures.functions.map (fun signature => signature.id) ++
      signatures.dataTypes.map (fun signature => signature.id) ++
      signatures.traits.map (fun signature => signature.id) ++
      signatures.implementations.map (fun signature => signature.id) ++
      signatures.contracts.map (fun signature => signature.id)).Nodup := by
  let traitState := collectProgramTraits environment environment.declarations {}
  let state := collectProgramSignatures environment traitState.traits
    environment.declarations {}
  have traitsSublist :
      (traitState.traits.map (fun signature => signature.id)).Sublist
        ((environment.declarations.filter
          isTraitSignatureDeclaration).map
            (fun declaration => declaration.id)) := by
    simpa [traitState] using collectProgramTraits_ids_sublist environment
      environment.declarations {}
  have collected := collectProgramSignatures_ids_sublist environment
    traitState.traits environment.declarations ({} : ProgramSignatureBuildState)
  have functionsSublist :
      (state.functions.map (fun signature => signature.id)).Sublist
        ((environment.declarations.filter
          isFunctionSignatureDeclaration).map
            (fun declaration => declaration.id)) := by
    simpa [state] using collected.1
  have dataSublist :
      (state.dataTypes.map (fun signature => signature.id)).Sublist
        ((environment.declarations.filter isDataSignatureDeclaration).map
          (fun declaration => declaration.id)) := by
    simpa [state] using collected.2.1
  have implementationsSublist :
      (state.implementations.map (fun signature => signature.id)).Sublist
        ((environment.declarations.filter
          isImplementationSignatureDeclaration).map
            (fun declaration => declaration.id)) := by
    simpa [state] using collected.2.2
  have contractsSublist :
      (state.contracts.map (fun signature => signature.id)).Sublist
        ((environment.declarations.filter
          isContractSignatureDeclaration).map
            (fun declaration => declaration.id)) := by
    simpa [state] using collectProgramSignatures_contract_ids_sublist environment
      traitState.traits environment.declarations
        ({} : ProgramSignatureBuildState)
  have allSublist :=
    (((functionsSublist.append dataSublist).append traitsSublist).append
      implementationsSublist).append contractsSublist
  have collectedNodup :=
    allSublist.nodup
      (signature_category_ids_nodup environment.declarations environmentIds)
  simp only [buildProgramSignatures] at success
  split at success
  · injection success with signaturesEq
    subst signatures
    simpa [traitState, state, List.map_map, Function.comp_def] using collectedNodup
  · simp at success

/-- Internal collector boundary used by `ProgramSignaturesProperties`: every
successful catalog retains the canonical declaration-owned parameter rows
constructed for its five declaration-backed signature categories. -/
theorem buildProgramSignatures_success_parameter_state
    {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    (success : buildProgramSignatures environment = .ok signatures) :
    ProgramSignatureParametersWellFormed signatures := by
  let traitState := collectProgramTraits environment environment.declarations {}
  let state := collectProgramSignatures environment traitState.traits
    environment.declarations {}
  have traitParameters : TraitSignatureParametersWellFormed traitState.traits := by
    apply collectProgramTraits_parameters_wellFormed environment
      environment.declarations ({} : ProgramTraitBuildState)
    intro signature member
    simp at member
  have signatureParameters :
      ProgramSignatureBuildFacts traitState.traits state := by
    apply collectProgramSignatures_facts environment
      traitState.traits environment.declarations
      ({} : ProgramSignatureBuildState)
      (by simpa [traitState] using
        collectedProgramTraits_structurally_wellFormed environment)
    constructor <;> intro signature member <;> simp at member
  simp only [buildProgramSignatures] at success
  split at success
  · injection success with signaturesEq
    subst signatures
    exact {
      functions := fun signature member => by
        obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
        exact signatureParameters.functions original originalMember
      dataTypes := signatureParameters.dataTypes
      traits := fun signature member => by
        obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
        exact traitParameters original originalMember
      implementations := fun signature member => by
        obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
        exact signatureParameters.implementations original originalMember
      contracts := signatureParameters.contracts
    }
  · simp at success

/-- Internal collector boundary used by `ProgramSignaturesProperties`: every
successfully collected function retains duplicate-free source parameter names
and the canonical scheme body assembled from its parameter and return rows. -/
theorem buildProgramSignatures_success_function_shape_state
    {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    (success : buildProgramSignatures environment = .ok signatures) :
    ∀ signature, signature ∈ signatures.functions →
      signature.parameterNames.Nodup ∧
        signature.scheme.body = .function
          (TypeSystem.Ty.productMany signature.parameterTypes)
          (TypeSystem.Ty.productMany signature.returnTypes) := by
  let traitState := collectProgramTraits environment environment.declarations {}
  let state := collectProgramSignatures environment traitState.traits
    environment.declarations {}
  have signatureFacts :
      ProgramSignatureBuildFacts traitState.traits state := by
    apply collectProgramSignatures_facts environment
      traitState.traits environment.declarations
      ({} : ProgramSignatureBuildState)
      (by simpa [traitState] using
        collectedProgramTraits_structurally_wellFormed environment)
    constructor <;> intro signature member <;> simp at member
  simp only [buildProgramSignatures] at success
  split at success
  · injection success with signaturesEq
    subst signatures
    intro signature member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    exact signatureFacts.functionShapes original originalMember
  · simp at success

/-- Internal collector boundary used by `ProgramSignaturesProperties`: every
successfully collected data signature retains the constructor-name and stable
identity structure established while traversing its source declaration. -/
theorem buildProgramSignatures_success_data_structure_state
    {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    (success : buildProgramSignatures environment = .ok signatures) :
    ∀ signature, signature ∈ signatures.dataTypes →
      DataSignatureStructuralWellFormed signature := by
  let traitState := collectProgramTraits environment environment.declarations {}
  let state := collectProgramSignatures environment traitState.traits
    environment.declarations {}
  have signatureFacts :
      ProgramSignatureBuildFacts traitState.traits state := by
    apply collectProgramSignatures_facts environment
      traitState.traits environment.declarations
      ({} : ProgramSignatureBuildState)
      (by simpa [traitState] using
        collectedProgramTraits_structurally_wellFormed environment)
    constructor <;> intro signature member <;> simp at member
  simp only [buildProgramSignatures] at success
  split at success
  · injection success with signaturesEq
    subst signatures
    exact signatureFacts.dataShapes
  · simp at success

/-- Internal collector boundary used by `ProgramSignaturesProperties`: every
successfully collected implementation signature retains the method-name and
stable identity structure established while traversing its source declaration. -/
theorem buildProgramSignatures_success_implementation_structure_state
    {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    (success : buildProgramSignatures environment = .ok signatures) :
    ∀ signature, signature ∈ signatures.implementations →
      ImplementationSignatureStructuralWellFormed signature := by
  let traitState := collectProgramTraits environment environment.declarations {}
  let state := collectProgramSignatures environment traitState.traits
    environment.declarations {}
  have signatureFacts :
      ProgramSignatureBuildFacts traitState.traits state := by
    apply collectProgramSignatures_facts environment
      traitState.traits environment.declarations
      ({} : ProgramSignatureBuildState)
      (by simpa [traitState] using
        collectedProgramTraits_structurally_wellFormed environment)
    constructor <;> intro signature member <;> simp at member
  simp only [buildProgramSignatures] at success
  split at success
  · injection success with signaturesEq
    subst signatures
    intro signature member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    exact (signatureFacts.implementationShapes original originalMember).closeUnderSuperclasses
  · simp at success

/-- Internal collector boundary used by `ProgramSignaturesProperties`: every
successfully collected implementation retains its generic-parameter occurrence,
selected trait, and required-trait-predicate checks. -/
theorem buildProgramSignatures_success_implementation_head_validated_state
    {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    (success : buildProgramSignatures environment = .ok signatures) :
    ∀ signature, signature ∈ signatures.implementations →
      ImplementationSignatureHeadValidated signatures.traits signature := by
  let traitState := collectProgramTraits environment environment.declarations {}
  let state := collectProgramSignatures environment traitState.traits
    environment.declarations {}
  have signatureFacts :
      ProgramSignatureBuildFacts traitState.traits state := by
    apply collectProgramSignatures_facts environment
      traitState.traits environment.declarations
      ({} : ProgramSignatureBuildState)
      (by simpa [traitState] using
        collectedProgramTraits_structurally_wellFormed environment)
    constructor <;> intro signature member <;> simp at member
  simp only [buildProgramSignatures] at success
  split at success
  · injection success with signaturesEq
    subst signatures
    intro signature member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    exact ((signatureFacts.implementationHeads original originalMember).closeUnderSuperclasses).closeTraits
  · simp at success

/-- Internal collector boundary used by `ProgramSignaturesProperties`: every
successfully collected implementation retains exact method correspondence and
completeness for the trait selected by its resolved head. -/
theorem buildProgramSignatures_success_implementation_method_catalog_state
    {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    (success : buildProgramSignatures environment = .ok signatures) :
    ∀ signature, signature ∈ signatures.implementations →
      ImplementationSignatureMethodCatalogValidated signatures.traits
        signature := by
  let traitState := collectProgramTraits environment environment.declarations {}
  let state := collectProgramSignatures environment traitState.traits
    environment.declarations {}
  have signatureFacts :
      ProgramSignatureBuildFacts traitState.traits state := by
    apply collectProgramSignatures_facts environment
      traitState.traits environment.declarations
      ({} : ProgramSignatureBuildState)
      (by simpa [traitState] using
        collectedProgramTraits_structurally_wellFormed environment)
    constructor <;> intro signature member <;> simp at member
  simp only [buildProgramSignatures] at success
  split at success
  · injection success with signaturesEq
    subst signatures
    intro signature member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    exact (signatureFacts.implementationMethods original originalMember).closeUnderSuperclasses
  · simp at success

/-- Internal collector boundary used by `ProgramSignaturesProperties`: every
successfully collected trait signature retains the method-name and stable
identity structure established while traversing its source declaration. -/
theorem buildProgramSignatures_success_trait_structure_state
    {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    (success : buildProgramSignatures environment = .ok signatures) :
    ∀ signature, signature ∈ signatures.traits →
      TraitSignatureStructuralWellFormed signature := by
  let traitState := collectProgramTraits environment environment.declarations {}
  have traitStructures :
      TraitSignaturesStructurallyWellFormed traitState.traits := by
    apply collectProgramTraits_structurally_wellFormed environment
      environment.declarations ({} : ProgramTraitBuildState)
    intro signature member
    simp at member
  simp only [buildProgramSignatures] at success
  split at success
  · injection success with signaturesEq
    subst signatures
    intro signature member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    exact (traitStructures original originalMember).closeMethods
  · simp at success

end Solcore.Frontend

namespace Solcore.Frontend.ConstrainedDeclarationScheme
private theorem freshParameterSubstitution_domain_reverse
    (parameters : List TypeSystem.TypeParameterId) (next : Nat)
    (substitution : TypeSystem.ParameterSubstitution)
    (unique : parameters.Nodup)
    (disjoint : ∀ parameter, parameter ∈ parameters → parameter ∉ substitution.map Prod.fst) :
    (freshParameterSubstitution parameters next substitution).1.map Prod.fst =
      parameters.reverse ++ substitution.map Prod.fst := by
  induction parameters generalizing next substitution with
  | nil => simp [freshParameterSubstitution]
  | cons parameter parameters ih =>
    obtain ⟨absent, unique⟩ := List.nodup_cons.mp unique
    have missing : substitution.lookup? parameter = none := by
      cases found : substitution.lookup? parameter with
      | none => rfl
      | some value =>
        exact False.elim (disjoint parameter (by simp)
          (List.mem_map.mpr ⟨(parameter, value), TypeSystem.ParameterSubstitution.lookup?_eq_some_mem found, rfl⟩))
    simp only [freshParameterSubstitution, missing]
    have remaining : ∀ candidate, candidate ∈ parameters →
        candidate ∉ (((parameter, TypeSystem.Ty.variable ⟨next⟩) :: substitution).map Prod.fst) := by
      intro candidate member known
      simp only [List.map_cons, List.mem_cons] at known
      rcases known with same | old
      · exact absent (same.symm ▸ member)
      · exact disjoint candidate (List.mem_cons_of_mem _ member) old
    rw [ih (next + 1) ((parameter, TypeSystem.Ty.variable ⟨next⟩) :: substitution) unique remaining]
    simp [List.reverse_cons, List.append_assoc]

/-- The checker prepends freshly allocated substitutions, so retained declaration
metadata follows reverse declaration order. Final type solving preserves it. -/
theorem instantiate_parameterSubstitution_domain_reverse
    (scheme : ConstrainedDeclarationScheme) (next : Nat)
    (unique : scheme.parameters.Nodup) :
    (scheme.instantiate next).parameterSubstitution.map Prod.fst = scheme.parameters.reverse := by
  simpa only [instantiate, List.map_nil, List.append_nil] using
    freshParameterSubstitution_domain_reverse scheme.parameters next [] unique (by simp)
end Solcore.Frontend.ConstrainedDeclarationScheme

namespace Solcore.Frontend.ConstrainedDeclarationScheme

private theorem freshParameterSubstitution_range_lower
    (parameters : List TypeSystem.TypeParameterId) (next : Nat)
    (substitution : TypeSystem.ParameterSubstitution) (lower : Nat)
    (bound : lower ≤ next)
    (prior : ∀ parameter replacement, (parameter,replacement) ∈ substitution →
      ∃ metavariable, replacement = .variable metavariable ∧ lower ≤ metavariable.index) :
    ∀ parameter replacement,
      (parameter,replacement) ∈ (freshParameterSubstitution parameters next substitution).1 →
      ∃ metavariable, replacement = .variable metavariable ∧ lower ≤ metavariable.index := by
  induction parameters generalizing next substitution with
  | nil => exact prior
  | cons parameter parameters ih =>
    cases found : substitution.lookup? parameter with
    | some existing =>
      simp only [freshParameterSubstitution, found]
      exact ih next substitution bound prior
    | none =>
      simp only [freshParameterSubstitution, found]
      apply ih (next + 1) ((parameter, .variable ⟨next⟩) :: substitution)
        (Nat.le_trans bound (Nat.le_succ next))
      intro candidate replacement member
      rcases List.mem_cons.mp member with same | old
      · cases same
        exact ⟨⟨next⟩, rfl, bound⟩
      · exact prior candidate replacement old

/-- Every replacement issued by the real declaration allocator belongs to
this instantiation's fresh interval, including when parameters repeat. -/
theorem instantiate_parameterSubstitution_range_fresh
    (scheme : ConstrainedDeclarationScheme) (next : Nat)
    {parameter : TypeSystem.TypeParameterId} {replacement : TypeSystem.Ty}
    (member : (parameter,replacement) ∈ (scheme.instantiate next).parameterSubstitution) :
    ∃ metavariable, replacement = .variable metavariable ∧
      next ≤ metavariable.index ∧ metavariable.index < (scheme.instantiate next).next := by
  obtain ⟨metavariable, same, lower⟩ :=
    freshParameterSubstitution_range_lower scheme.parameters next [] next (Nat.le_refl _)
      (by simp) parameter replacement member
  have upper := instantiate_parameterSubstitution_range_variablesBelow scheme next member
  rw [same] at upper
  exact ⟨metavariable, same, lower,
    (TypeSystem.Ty.variablesBelow_variable_iff _ _).mp upper⟩

end Solcore.Frontend.ConstrainedDeclarationScheme
