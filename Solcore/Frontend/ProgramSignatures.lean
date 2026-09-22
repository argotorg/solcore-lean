import Solcore.Frontend.ProgramTypeResolution
import Solcore.Frontend.ProgramIdentity
import Solcore.Frontend.TraitResolution
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

/-- Resolved signature catalog for one implementation, preserving method source
order and the parsed method bodies. -/
structure ProgramImplementationSignature where
  id : Resolved.DeclarationId
  parameters : List TypeSystem.TypeParameterId
  head : ProgramPredicate
  wherePredicates : List ProgramPredicate
  methods : List ProgramImplMethodSignature
  source : Syntax.ImplDecl
  deriving Repr

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

namespace ProgramImplementationSignature

/-- Backward-compatible trait-search projection of an implementation catalog. -/
def implRule (implementation : ProgramImplementationSignature) :
    ProgramImplRule := {
  id := implementation.id
  head := implementation.head
  wherePredicates := implementation.wherePredicates
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
  deriving Repr

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
  | .duplicateDataConstructor dataType _ _ _ => dataType

private def declarationParameters
    (declaration : ProgramDeclaration) : List TypeSystem.TypeParameterId :=
  declaration.genericParameters.zipIdx.map fun (_, index) =>
    { owner := declaration.id, index }

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

private def parameterTypes
    (method : UnmatchedProgramImplMethod) : List TypeSystem.Ty :=
  method.parameters.map (·.type)

private def parameterComptime
    (method : UnmatchedProgramImplMethod) : List Bool :=
  method.parameters.map (·.comptime)

end UnmatchedProgramImplMethod

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
  let wherePredicates ← resolveWhereClause environment declaration scope
    source.value.whereClause
  let some traitSignature := traits.find? fun signature =>
      decide (signature.id = trait)
    | throw (.traitCatalogUnavailable declaration.id trait)
  let unmatchedMethods ← unmatchedImplMethodsOfDeclaration environment
    declaration scope source.value.methods 0 []
  let substitution : TypeSystem.ParameterSubstitution :=
    traitSignature.parameters.zip (subject :: arguments)
  validateRequiredImplMethods declaration.id substitution
    traitSignature.methods unmatchedMethods
  let methods ← attachTraitMethods traitSignature.methods unmatchedMethods
  pure {
    id := declaration.id
    parameters := declarationParameters declaration
    head := { trait, subject, arguments }
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
    }
  else
    .error errors

end Solcore.Frontend
