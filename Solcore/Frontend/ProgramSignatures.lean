import Solcore.Frontend.ProgramTypeResolution
import Solcore.Frontend.ProgramIdentity
import Solcore.Frontend.TraitResolution
import Solcore.Frontend.TypedTraitResolution
import Solcore.TypeSystem.Scheme

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

/-- Exact compiler-function spellings remain pairwise distinct. -/
theorem all_spellings_nodup : (all.map spelling).Nodup := by
  simp [all, spelling]

/-- Fixed source parameter types of one compiler-provided function. -/
def parameterTypes : BuiltinFunctionId → List TypeSystem.Ty
  | .integerSub => [TypeSystem.Ty.integer, TypeSystem.Ty.integer]
  | .wordFromInteger => [TypeSystem.Ty.integer]
  | .integerAdd
  | .integerEq
  | .integerLt
  | .integerMul => [TypeSystem.Ty.integer, TypeSystem.Ty.integer]
  | .wordToInteger => [TypeSystem.Ty.word]

/-- Fixed source result type of one compiler-provided function. -/
def returnType : BuiltinFunctionId → TypeSystem.Ty
  | .integerSub => TypeSystem.Ty.integer
  | .wordFromInteger => TypeSystem.Ty.word
  | .integerAdd => TypeSystem.Ty.integer
  | .integerEq
  | .integerLt => TypeSystem.Ty.bool
  | .integerMul => TypeSystem.Ty.integer
  | .wordToInteger => TypeSystem.Ty.integer

/-- Exact monomorphic function type of one compiler-provided function. -/
def type (function : BuiltinFunctionId) : TypeSystem.Ty :=
  .function (TypeSystem.Ty.productMany function.parameterTypes)
    function.returnType

/-- The compiler-provided function has no rigid or flexible parameters. -/
def scheme (function : BuiltinFunctionId) : TypeSystem.Scheme :=
  .mono function.type

end BuiltinFunctionId

/-- Resolve the deliberately small exact bare compiler-function namespace. -/
def builtinFunctionNamed? (name : String) : Option BuiltinFunctionId :=
  BuiltinFunctionId.all.find? fun function => function.spelling == name

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
allows later semantic consumers to transport it to any equal-headed entry. -/
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
        method.wherePredicates = traitMethod.wherePredicates.map
          (ProgramPredicate.applyParameters substitution)) ∧
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
  deriving Repr, BEq, DecidableEq

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
  }

end ProgramImplementationSignature

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

/-- Compiler-provided rules in stable resolution order. -/
def builtinResolutionRules : List ProgramImplRule :=
  [builtinIntWordRule, builtinIntIntegerRule]

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
  | implMethodPredicateMismatch
      (method : ProgramImplMethodId) (traitMethod : ProgramTraitMethodId)
      (expected actual : List ProgramPredicate)
  | traitCatalogUnavailable
      (implementation trait : Resolved.DeclarationId)
  | implementationParameterNotInHead
      (implementation : Resolved.DeclarationId)
      (parameter : TypeSystem.TypeParameterId)
  | missingImplementationTraitPredicate
      (implementation : Resolved.DeclarationId)
      (predicate : ProgramPredicate)
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
  | .implMethodPredicateMismatch method _ _ _ => method.implementation
  | .traitCatalogUnavailable implementation _ => implementation
  | .implementationParameterNotInHead implementation _ => implementation
  | .missingImplementationTraitPredicate implementation _ => implementation
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

/-- The exact signature comparison performed before an implementation method
is attached to its selected trait method identity. -/
private structure UnmatchedImplMethodMatchesTrait
    (substitution : TypeSystem.ParameterSubstitution)
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
  predicates : implMethod.wherePredicates = traitMethod.wherePredicates.map
    (ProgramPredicate.applyParameters substitution)

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

private def validateRequiredImplMethods
    (implementation : Resolved.DeclarationId)
    (substitution : TypeSystem.ParameterSubstitution) :
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
      let expectedPredicates := traitMethod.wherePredicates.map
        (ProgramPredicate.applyParameters substitution)
      if expectedParameters = implMethod.parameterTypes &&
          expectedReturns = implMethod.returnTypes then
        if traitMethod.parameterComptime = implMethod.parameterComptime &&
            traitMethod.returnComptime = implMethod.returnComptime then
          if expectedPredicates = implMethod.wherePredicates then
            validateRequiredImplMethods implementation substitution rest implMethods
          else
            throw (.implMethodPredicateMismatch implMethod.id traitMethod.id
              expectedPredicates implMethod.wherePredicates)
        else
          throw (.implMethodComptimeMismatch implMethod.id traitMethod.id
            traitMethod.parameterComptime implMethod.parameterComptime
            traitMethod.returnComptime implMethod.returnComptime)
      else
        throw (.implMethodSignatureMismatch implMethod.id traitMethod.id
          expectedParameters implMethod.parameterTypes
          expectedReturns implMethod.returnTypes)

/-- Successful required-method validation supplies one exactly matching source
implementation method for every trait method. -/
private theorem validateRequiredImplMethods_success_matches
    {implementation : Resolved.DeclarationId}
    {substitution : TypeSystem.ParameterSubstitution}
    {traitMethods : List ProgramTraitMethodSignature}
    {implMethods : List UnmatchedProgramImplMethod}
    (success : validateRequiredImplMethods implementation substitution
      traitMethods implMethods = .ok ()) :
    ∀ traitMethod, traitMethod ∈ traitMethods →
      ∃ implMethod, implMethod ∈ implMethods ∧
        UnmatchedImplMethodMatchesTrait substitution traitMethod implMethod := by
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
                · by_cases predicatesEq :
                      traitMethod.wherePredicates.map
                          (ProgramPredicate.applyParameters substitution) =
                        implMethod.wherePredicates
                  · have restSuccess :
                        validateRequiredImplMethods implementation substitution
                            rest implMethods = .ok () := by
                      simpa [parameterTypesEq, returnTypesEq,
                        parameterComptimeEq, returnComptimeEq, predicatesEq]
                        using success
                    intro candidate member
                    simp only [List.mem_cons] at member
                    rcases member with rfl | member
                    · have implMember : implMethod ∈ implMethods :=
                        List.mem_of_find?_eq_some foundEq
                      have nameEq : implMethod.name = candidate.name := by
                        have accepted := List.find?_some foundEq
                        simpa using accepted
                      exact ⟨implMethod, implMember, {
                        name := nameEq.symm
                        parameter_types := parameterTypesEq.symm
                        return_types := returnTypesEq.symm
                        parameter_comptime := parameterComptimeEq.symm
                        return_comptime := returnComptimeEq.symm
                        predicates := predicatesEq.symm
                      }⟩
                    · exact induction restSuccess candidate member
                  · simp [parameterTypesEq, returnTypesEq,
                      parameterComptimeEq, returnComptimeEq, predicatesEq]
                      at success
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
required-method validation and identity attachment. -/
private structure ImplMethodCatalogMatchesTrait
    (substitution : TypeSystem.ParameterSubstitution)
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
      method.wherePredicates = traitMethod.wherePredicates.map
        (ProgramPredicate.applyParameters substitution)
  complete : ∀ traitMethod, traitMethod ∈ trait.methods →
    ∃ method ∈ resolvedMethods, method.traitMethod = traitMethod.id

/-- The two executable method passes jointly establish exact correspondence.
The two duplicate-name witnesses are essential: validation and attachment use
independent name lookups in opposite directions. -/
private theorem validatedAndAttachedImplMethods_matchTrait
    {implementation : Resolved.DeclarationId}
    {substitution : TypeSystem.ParameterSubstitution}
    {trait : ProgramTraitSignature}
    {unmatchedMethods : List UnmatchedProgramImplMethod}
    {methods : List ProgramImplMethodSignature}
    (traitStructure : TraitSignatureStructuralWellFormed trait)
    (unmatchedStructure : UnmatchedImplMethodsStructural implementation 0 []
      unmatchedMethods)
    (validated : validateRequiredImplMethods implementation substitution
      trait.methods unmatchedMethods = .ok ())
    (attached : attachTraitMethods trait.methods unmatchedMethods = .ok methods) :
    ImplMethodCatalogMatchesTrait substitution trait methods := by
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
    · exact methodPredicates.trans methodMatch.predicates
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
  validateContained
    (ProgramSignatureError.missingImplementationTraitPredicate declaration.id)
    wherePredicates requiredPredicates
  let unmatchedMethods ← unmatchedImplMethodsOfDeclaration environment
    declaration scope source.value.methods 0 []
  validateRequiredImplMethods declaration.id substitution
    traitSignature.methods unmatchedMethods
  let methods ← attachTraitMethods traitSignature.methods unmatchedMethods
  pure {
    id := declaration.id
    isDefault := source.value.defaultMarker.isSome
    parameters
    head
    wherePredicates
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
  let collectedErrors := traitState.errors ++ nonCascadingErrors
  let errors := environment.declarations.flatMap fun declaration =>
    collectedErrors.filter fun error =>
      decide (programSignatureErrorDeclaration error = declaration.id)
  if errors.isEmpty then
    .ok {
      functions := state.functions
      implRules := state.implementations.map (ProgramImplementationSignature.implRule)
      traits := traitState.traits
      implementations := state.implementations
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
                apply Except.SuccessSatisfies.bind_property
                  (validateContained
                    (ProgramSignatureError.missingImplementationTraitPredicate
                      declaration.id)
                    wherePredicates requiredPredicates) _
                  (Except.SuccessSatisfies.of_success _
                    (fun _ resultEq => validateContained_success resultEq))
                intro predicatesChecked predicatesContained
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
                apply Except.SuccessSatisfies.bind
                intro predicatesChecked
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
                        traitSignature.methods unmatchedMethods = .ok ())
                    (validateRequiredImplMethods declaration.id substitution
                      traitSignature.methods unmatchedMethods) :=
                  Except.SuccessSatisfies.of_success _ (fun result resultEq => by
                    cases result
                    exact resultEq)
                apply Except.SuccessSatisfies.bind_property
                  (validateRequiredImplMethods declaration.id substitution
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
    simpa [traitState, state] using collectedNodup
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
      functions := signatureParameters.functions
      dataTypes := signatureParameters.dataTypes
      traits := traitParameters
      implementations := signatureParameters.implementations
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
    exact signatureFacts.functionShapes
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
    exact signatureFacts.implementationShapes
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
    exact signatureFacts.implementationHeads
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
    exact signatureFacts.implementationMethods
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
    exact traitStructures
  · simp at success

end Solcore.Frontend
