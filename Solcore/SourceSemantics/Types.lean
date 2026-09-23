import Solcore.SourceSemantics.Context

/-!
Algorithm-independent well-formedness for source types.

The judgment treats flexible inference variables and rigid declaration
parameters as distinct binders.  Nominal applications are accepted only as a
complete application of a cataloged data declaration; arbitrary type-level
application and recovery types are deliberately absent from the rules.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics

/-- The rigid binder list has no duplicates and every binder belongs to the
declaration selected by the context.  The empty list is valid outside a
declaration. -/
def TypeParameterBindersWellFormed (context : Context) : Prop :=
  context.typeParameters.Nodup ∧
    ∀ parameter ∈ context.typeParameters,
      context.currentDeclaration = some parameter.owner

mutual

/-- A source type mentions only the supplied flexible variables and the rigid
parameters of the current declaration. -/
inductive TypeWellScoped (context : Context)
    (flexibleVariables : List TypeSystem.TypeVarId) :
    TypeSystem.Ty → Prop where
  | variable
      {metavariable : TypeSystem.TypeVarId}
      (bound : metavariable ∈ flexibleVariables) :
      TypeWellScoped context flexibleVariables (.variable metavariable)
  | parameter
      {parameter : TypeSystem.TypeParameterId}
      (bound : parameter ∈ context.typeParameters)
      (owned : context.currentDeclaration = some parameter.owner) :
      TypeWellScoped context flexibleVariables (.parameter parameter)
  | builtin (builtin : TypeSystem.BuiltinType) :
      TypeWellScoped context flexibleVariables (.constructor (.builtin builtin))
  | nominal
      (dataType : Frontend.ProgramDataSignature)
      (arguments : List TypeSystem.Ty)
      (cataloged : dataType ∈ context.signatures.dataTypes)
      (arity : arguments.length = dataType.parameters.length)
      (argumentsWellScoped :
        TypesWellScoped context flexibleVariables arguments) :
      TypeWellScoped context flexibleVariables
        (TypeSystem.Ty.nominal dataType.id arguments)
  | function
      {parameter result : TypeSystem.Ty}
      (parameterWellScoped :
        TypeWellScoped context flexibleVariables parameter)
      (resultWellScoped : TypeWellScoped context flexibleVariables result) :
      TypeWellScoped context flexibleVariables (.function parameter result)
  | product
      {left right : TypeSystem.Ty}
      (leftWellScoped : TypeWellScoped context flexibleVariables left)
      (rightWellScoped : TypeWellScoped context flexibleVariables right) :
      TypeWellScoped context flexibleVariables (.product left right)
  | mapping
      {key value : TypeSystem.Ty}
      (keyWellScoped : TypeWellScoped context flexibleVariables key)
      (valueWellScoped : TypeWellScoped context flexibleVariables value) :
      TypeWellScoped context flexibleVariables (.mapping key value)
  | proxy
      {inner : TypeSystem.Ty}
      (innerWellScoped : TypeWellScoped context flexibleVariables inner) :
      TypeWellScoped context flexibleVariables (.proxy inner)
  | comptime
      {inner : TypeSystem.Ty}
      (innerWellScoped : TypeWellScoped context flexibleVariables inner) :
      TypeWellScoped context flexibleVariables (.comptime inner)

/-- Pointwise well-scopedness for nominal type arguments. -/
inductive TypesWellScoped (context : Context)
    (flexibleVariables : List TypeSystem.TypeVarId) :
    List TypeSystem.Ty → Prop where
  | nil : TypesWellScoped context flexibleVariables []
  | cons
      {head : TypeSystem.Ty} {tail : List TypeSystem.Ty}
      (headWellScoped : TypeWellScoped context flexibleVariables head)
      (tailWellScoped : TypesWellScoped context flexibleVariables tail) :
      TypesWellScoped context flexibleVariables (head :: tail)

end

/-- A closed source type has no free inference variables.  Rigid parameters
may occur only when they are bound by the current declaration. -/
structure TypeWellFormed (context : Context) (type : TypeSystem.Ty) : Prop where
  binders : TypeParameterBindersWellFormed context
  typeWellScoped : TypeWellScoped context [] type

/-- A rank-1 scheme binds every flexible variable in its body exactly once. -/
structure SchemeWellFormed (context : Context)
    (scheme : TypeSystem.Scheme) : Prop where
  binders : TypeParameterBindersWellFormed context
  quantified_nodup : scheme.quantified.Nodup
  body : TypeWellScoped context scheme.quantified scheme.body

/-- Syntactic occurrence of one rigid declaration parameter in a type.  This
is intentionally independent of substitution lookup and is used to rule out
phantom implementation parameters. -/
def TypeParameterOccurs (parameter : TypeSystem.TypeParameterId) :
    TypeSystem.Ty → Prop
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

/-- One rigid parameter occurs in the subject or an argument of a trait
predicate. -/
def TypeParameterOccursInPredicate
    (parameter : TypeSystem.TypeParameterId)
    (predicate : Frontend.ProgramPredicate) : Prop :=
  TypeParameterOccurs parameter predicate.subject ∨
    ∃ argument, argument ∈ predicate.arguments ∧
      TypeParameterOccurs parameter argument

/-- A trait predicate names a cataloged trait at its exact arity and all of
its type arguments are meaningful in the surrounding declaration scope.  The
distinguished subject occupies the first trait-parameter position. -/
structure PredicateWellFormed (context : Context)
    (predicate : Frontend.ProgramPredicate) : Prop where
  subject : TypeWellFormed context predicate.subject
  arguments : ∀ argument, argument ∈ predicate.arguments →
    TypeWellFormed context argument
  trait : match predicate.trait with
    | .builtin .int => predicate.arguments = []
    | .declaration id =>
        ∃ signature ∈ context.signatures.traits,
          signature.id = id ∧
          predicate.arguments.length + 1 = signature.parameters.length

/-- Pointwise well-formedness of a source-ordered predicate list. -/
def PredicatesWellFormed (context : Context)
    (predicates : List Frontend.ProgramPredicate) : Prop :=
  ∀ predicate, predicate ∈ predicates → PredicateWellFormed context predicate

namespace TypeParameterBindersWellFormed

/-- Extending only the lexical scope cannot change the validity of the rigid
declaration binders. -/
theorem withLocal
    {context : Context} (wellFormed : TypeParameterBindersWellFormed context)
    (id : Resolved.LocalId) (scheme : TypeSystem.Scheme) :
    TypeParameterBindersWellFormed (context.withLocal id scheme) := by
  simpa [Context.withLocal, TypeParameterBindersWellFormed] using wellFormed

theorem ofSignatures (signatures : Frontend.ProgramSignatures) :
    TypeParameterBindersWellFormed (.ofSignatures signatures) := by
  constructor
  · simp [Context.ofSignatures]
  · intro parameter member
    simp [Context.ofSignatures] at member

theorem forDeclaration
    (context : Context)
    (declaration : Resolved.DeclarationId)
    (parameters : List TypeSystem.TypeParameterId)
    (nodup : parameters.Nodup)
    (owned : ∀ parameter ∈ parameters, parameter.owner = declaration) :
    TypeParameterBindersWellFormed
      (context.forDeclaration declaration parameters) := by
  constructor
  · simpa [Context.forDeclaration] using nodup
  · intro parameter member
    have owner_eq := owned parameter (by
      simpa [Context.forDeclaration] using member)
    simp [Context.forDeclaration, owner_eq]

theorem withoutDeclaration (context : Context) :
    TypeParameterBindersWellFormed context.withoutDeclaration := by
  constructor
  · simp [Context.withoutDeclaration]
  · intro parameter member
    simp [Context.withoutDeclaration] at member

end TypeParameterBindersWellFormed

namespace TypesWellScoped

theorem member {context : Context}
    {flexibleVariables : List TypeSystem.TypeVarId}
    {types : List TypeSystem.Ty}
    (wellScoped : TypesWellScoped context flexibleVariables types)
    {type : TypeSystem.Ty} (type_mem : type ∈ types) :
    TypeWellScoped context flexibleVariables type :=
  match wellScoped with
  | .nil => by simp at type_mem
  | .cons headWellScoped tailWellScoped => by
      simp only [List.mem_cons] at type_mem
      rcases type_mem with head_eq | tail_mem
      · simpa [head_eq] using headWellScoped
      · exact member tailWellScoped tail_mem

end TypesWellScoped

namespace TypeWellScoped

/-- Strip type arguments from the left of an application spine. -/
private def applicationHead : TypeSystem.Ty → TypeSystem.Ty
  | .application left _ => applicationHead left
  | type => type

private theorem applicationHead_foldl
    (head : TypeSystem.Ty) (arguments : List TypeSystem.Ty) :
    applicationHead (arguments.foldl TypeSystem.Ty.application head) =
      applicationHead head := by
  induction arguments generalizing head with
  | nil => rfl
  | cons argument arguments induction =>
      simp only [List.foldl_cons]
      rw [induction]
      rfl

private theorem applicationHead_nominal
    (declaration : Resolved.DeclarationId)
    (arguments : List TypeSystem.Ty) :
    applicationHead (TypeSystem.Ty.nominal declaration arguments) =
      .constructor (.declaration declaration) := by
  unfold TypeSystem.Ty.nominal TypeSystem.Ty.applyMany
  rw [applicationHead_foldl]
  rfl

private theorem nominal_ne_variable
    (declaration : Resolved.DeclarationId)
    (arguments : List TypeSystem.Ty)
    (metavariable : TypeSystem.TypeVarId) :
    TypeSystem.Ty.nominal declaration arguments ≠ .variable metavariable := by
  intro equal
  have heads := congrArg applicationHead equal
  rw [applicationHead_nominal] at heads
  cases heads

private theorem nominal_ne_parameter
    (declaration : Resolved.DeclarationId)
    (arguments : List TypeSystem.Ty)
    (parameter : TypeSystem.TypeParameterId) :
    TypeSystem.Ty.nominal declaration arguments ≠ .parameter parameter := by
  intro equal
  have heads := congrArg applicationHead equal
  rw [applicationHead_nominal] at heads
  cases heads

private theorem nominal_ne_error
    (declaration : Resolved.DeclarationId)
    (arguments : List TypeSystem.Ty) :
    TypeSystem.Ty.nominal declaration arguments ≠ .error := by
  intro equal
  have heads := congrArg applicationHead equal
  rw [applicationHead_nominal] at heads
  cases heads

/-- Inversion for flexible variables: every occurrence is explicitly bound by
the flexible-variable list of the judgment. -/
theorem variable_mem {context : Context}
    {flexibleVariables : List TypeSystem.TypeVarId}
    {type : TypeSystem.Ty}
    (wellScoped : TypeWellScoped context flexibleVariables type) :
    ∀ metavariable, type = .variable metavariable →
      metavariable ∈ flexibleVariables :=
  match wellScoped with
  | .variable bound => by
      intro metavariable equal
      cases equal
      exact bound
  | .parameter _ _ => by intro _ equal; cases equal
  | .builtin _ => by intro _ equal; cases equal
  | .nominal dataType arguments _ _ _ => by
      intro metavariable equal
      exact False.elim (nominal_ne_variable dataType.id arguments metavariable equal)
  | .function _ _ => by intro _ equal; cases equal
  | .product _ _ => by intro _ equal; cases equal
  | .mapping _ _ => by intro _ equal; cases equal
  | .proxy _ => by intro _ equal; cases equal
  | .comptime _ => by intro _ equal; cases equal

/-- Inversion for rigid parameters records both binder membership and
declaration ownership. -/
theorem parameter_scope {context : Context}
    {flexibleVariables : List TypeSystem.TypeVarId}
    {type : TypeSystem.Ty}
    (wellScoped : TypeWellScoped context flexibleVariables type) :
    ∀ parameter, type = .parameter parameter →
      parameter ∈ context.typeParameters ∧
        context.currentDeclaration = some parameter.owner :=
  match wellScoped with
  | .variable _ => by intro _ equal; cases equal
  | .parameter bound owned => by
      intro parameter equal
      cases equal
      exact ⟨bound, owned⟩
  | .builtin _ => by intro _ equal; cases equal
  | .nominal dataType arguments _ _ _ => by
      intro parameter equal
      exact False.elim (nominal_ne_parameter dataType.id arguments parameter equal)
  | .function _ _ => by intro _ equal; cases equal
  | .product _ _ => by intro _ equal; cases equal
  | .mapping _ _ => by intro _ equal; cases equal
  | .proxy _ => by intro _ equal; cases equal
  | .comptime _ => by intro _ equal; cases equal

/-- Recovery types never occur in a well-scoped source type. -/
theorem ne_error {context : Context}
    {flexibleVariables : List TypeSystem.TypeVarId}
    {type : TypeSystem.Ty}
    (wellScoped : TypeWellScoped context flexibleVariables type) :
    type ≠ .error :=
  match wellScoped with
  | .variable _ => by intro equal; cases equal
  | .parameter _ _ => by intro equal; cases equal
  | .builtin _ => by intro equal; cases equal
  | .nominal dataType arguments _ _ _ =>
      nominal_ne_error dataType.id arguments
  | .function _ _ => by intro equal; cases equal
  | .product _ _ => by intro equal; cases equal
  | .mapping _ _ => by intro equal; cases equal
  | .proxy _ => by intro equal; cases equal
  | .comptime _ => by intro equal; cases equal

theorem variable_iff {context : Context}
    {flexibleVariables : List TypeSystem.TypeVarId}
    {metavariable : TypeSystem.TypeVarId} :
    TypeWellScoped context flexibleVariables (.variable metavariable) ↔
      metavariable ∈ flexibleVariables := by
  constructor
  · intro wellScoped
    exact wellScoped.variable_mem metavariable rfl
  · exact TypeWellScoped.variable

end TypeWellScoped

namespace TypeWellFormed

theorem ne_error {context : Context} {type : TypeSystem.Ty}
    (wellFormed : TypeWellFormed context type) :
    type ≠ .error :=
  wellFormed.typeWellScoped.ne_error

theorem variable_impossible {context : Context}
    (metavariable : TypeSystem.TypeVarId) :
    ¬ TypeWellFormed context (.variable metavariable) := by
  intro wellFormed
  have member := wellFormed.typeWellScoped.variable_mem metavariable rfl
  simp at member

end TypeWellFormed

namespace SchemeWellFormed

theorem mono {context : Context} {type : TypeSystem.Ty}
    (wellFormed : TypeWellFormed context type) :
    SchemeWellFormed context (.mono type) := by
  exact {
    binders := wellFormed.binders
    quantified_nodup := by simp [TypeSystem.Scheme.mono]
    body := by simpa [TypeSystem.Scheme.mono] using wellFormed.typeWellScoped
  }

end SchemeWellFormed

end Solcore.SourceSemantics
