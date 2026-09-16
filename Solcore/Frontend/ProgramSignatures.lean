import Solcore.Frontend.ProgramTypeResolution
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

/-- The concrete trait-predicate representation used by whole-program source
checking. -/
abbrev ProgramPredicate :=
  TraitResolution.Predicate Resolved.DeclarationId TypeSystem.Ty

/-- A source implementation after its trait and every type have resolved. -/
abbrev ProgramImplRule :=
  TraitResolution.ImplRule Resolved.DeclarationId TypeSystem.Ty
    Resolved.DeclarationId

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

/-- A resolved top-level function signature plus its source body. -/
structure ProgramFunctionSignature where
  id : Resolved.DeclarationId
  name : String
  parameterNames : List String
  parameterTypes : List TypeSystem.Ty
  returnTypes : List TypeSystem.Ty
  scheme : ConstrainedDeclarationScheme
  source : Syntax.FunctionDecl
  deriving Repr

/-- The declarations needed by source expression inference and trait search. -/
structure ProgramSignatures where
  functions : List ProgramFunctionSignature
  implRules : List ProgramImplRule
  deriving Repr

namespace ProgramSignatures

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

end ProgramSignatures

/-- Failures while turning cataloged declarations into typed signatures. -/
inductive ProgramSignatureError where
  | duplicateFunctionParameter
      (declaration : Resolved.DeclarationId)
      (name : String) (firstIndex duplicateIndex : Nat)
  | malformedFunctionParameter
      (declaration : Resolved.DeclarationId) (parameterIndex : Nat)
  | malformedType (declaration : Resolved.DeclarationId)
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
  deriving Repr, DecidableEq

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

private def resolveSignatureType
    (environment : ProgramEnvironment) (declaration : ProgramDeclaration)
    (scope : ProgramTypeScope) (source : Syntax.TypeExpr) :
    Except ProgramSignatureError TypeSystem.Ty :=
  match resolveProgramTypeExpr environment scope source with
  | .error error => .error (.typeResolution declaration.id error)
  | .ok type =>
      if typeContainsError type then
        .error (.malformedType declaration.id)
      else
        .ok type

private def resolveSignatureTypes
    (environment : ProgramEnvironment) (declaration : ProgramDeclaration)
    (scope : ProgramTypeScope) : List Syntax.TypeExpr →
      Except ProgramSignatureError (List TypeSystem.Ty)
  | [] => .ok []
  | source :: rest => do
      let type ← resolveSignatureType environment declaration scope source
      let types ← resolveSignatureTypes environment declaration scope rest
      pure (type :: types)

private def traitCandidates
    (environment : ProgramEnvironment) (declaration : ProgramDeclaration)
    (name : String) : Except ProgramSignatureError (List ProgramDeclaration) :=
  match environment.localTraitsNamed declaration.id.moduleId name with
  | localCandidates@(_ :: _) => .ok localCandidates
  | [] =>
      match buildProgramImports environment declaration.id.moduleId with
      | .error errors => .error (.importVisibility declaration.id errors)
      | .ok visibility =>
          if visibility.hasImports then
            .ok (visibility.traitsNamed name)
          else
            .ok (environment.traitsNamed name)

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
  names : List String
  types : List TypeSystem.Ty

private def resolveFunctionParameters
    (environment : ProgramEnvironment) (declaration : ProgramDeclaration)
    (scope : ProgramTypeScope) :
    List Syntax.FunctionParameter → Nat → List (String × Nat) →
      Except ProgramSignatureError ResolvedFunctionParameters
  | [], _, _ => .ok { names := [], types := [] }
  | parameter :: rest, index, seen =>
      match parameter.value with
      | .error => .error (.malformedFunctionParameter declaration.id index)
      | .typed _ name sourceType =>
          match seen.find? fun previous => previous.1 == name.value with
          | some previous =>
              .error (.duplicateFunctionParameter declaration.id name.value
                previous.2 index)
          | none => do
              let type ← resolveSignatureType environment declaration scope sourceType
              let resolvedRest ← resolveFunctionParameters environment declaration
                scope rest (index + 1) ((name.value, index) :: seen)
              pure {
                names := name.value :: resolvedRest.names
                types := type :: resolvedRest.types
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
  let returnTypes ← resolveSignatureTypes environment declaration scope returnSources
  let predicates ← resolveWhereClause environment declaration scope
    signature.whereClause
  let body := TypeSystem.Ty.function
    (TypeSystem.Ty.productMany parameters.types)
    (TypeSystem.Ty.productMany returnTypes)
  pure {
    id := declaration.id
    name := signature.name.value
    parameterNames := parameters.names
    parameterTypes := parameters.types
    returnTypes
    scheme := {
      parameters := declarationParameters declaration
      predicates
      body
    }
    source
  }

private def implRuleOfDeclaration
    (environment : ProgramEnvironment) (declaration : ProgramDeclaration)
    (source : Syntax.ImplDecl) :
    Except ProgramSignatureError ProgramImplRule := do
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
  pure {
    id := declaration.id
    head := { trait, subject, arguments }
    wherePredicates
  }

private def signatureItemOfDeclaration
    (environment : ProgramEnvironment) (declaration : ProgramDeclaration) :
    Except ProgramSignatureError
      (Option ProgramFunctionSignature × Option ProgramImplRule) :=
  match declaration.source.value with
  | .function source => do
      pure (some (← functionSignatureOfDeclaration environment declaration source), none)
  | .impl source => do
      pure (none, some (← implRuleOfDeclaration environment declaration source))
  | _ => .ok (none, none)

private structure ProgramSignatureBuildState where
  errors : List ProgramSignatureError := []
  functions : List ProgramFunctionSignature := []
  implRules : List ProgramImplRule := []

private def collectProgramSignatures
    (environment : ProgramEnvironment) :
    List ProgramDeclaration → ProgramSignatureBuildState →
      ProgramSignatureBuildState
  | [], state => state
  | declaration :: rest, state =>
      let state :=
        match signatureItemOfDeclaration environment declaration with
        | .error error => { state with errors := state.errors ++ [error] }
        | .ok (function?, implRule?) => {
            state with
            functions := state.functions ++ function?.toList
            implRules := state.implRules ++ implRule?.toList
          }
      collectProgramSignatures environment rest state

/-- Resolve every top-level function signature and implementation rule.
Independent declaration failures are accumulated in source order. -/
def buildProgramSignatures (environment : ProgramEnvironment) :
    Except (List ProgramSignatureError) ProgramSignatures :=
  let state := collectProgramSignatures environment environment.declarations {}
  if state.errors.isEmpty then
    .ok { functions := state.functions, implRules := state.implRules }
  else
    .error state.errors

end Solcore.Frontend
