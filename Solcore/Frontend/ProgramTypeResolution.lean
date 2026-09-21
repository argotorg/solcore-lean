import Solcore.Frontend.ProgramImports
import Solcore.TypeSystem.Type

/-!
Executable whole-program resolution of canonical source type expressions.

Unqualified names prefer a generic parameter, then the legacy builtins, then
the current module, and then imported public entities.  The exact lowercase
`integer` intrinsic is a final fallback after user-defined types.  Imported
namespace paths traverse public module re-exports.  The no-import and explicit
canonical-path fallbacks remain as the initial-profile compatibility boundary.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- The declaration-local information needed to resolve source types. -/
structure ProgramTypeScope where
  currentModule : Workspace.ModuleId
  genericOwner : Resolved.DeclarationId
  genericParameters : List String
  deriving Repr

namespace ProgramTypeScope

/-- Resolve types in the scope introduced by one cataloged declaration. -/
def ofDeclaration (declaration : ProgramDeclaration) : ProgramTypeScope := {
  currentModule := declaration.id.moduleId
  genericOwner := declaration.id
  genericParameters := declaration.genericParameters
}

end ProgramTypeScope

/-- Ordinary source-type resolution failures. -/
inductive ProgramTypeResolutionError where
  | duplicateGenericParameter
      (name : String) (firstIndex duplicateIndex : Nat)
  | unknownTypeName (components : List String)
  | ambiguousTypeName
      (components : List String) (candidates : List Resolved.DeclarationId)
  | typeParameterApplied
      (name : String) (parameterIndex argumentCount : Nat)
  | typeArityMismatch
      (components : List String) (expected actual : Nat)
  | importVisibility (errors : List ProgramImportError)
  | nestingLimit
  deriving Repr, DecidableEq

/-- Exact source spelling components, with all occurrence spans erased. -/
def programTypeNameComponents (name : Syntax.QualifiedName) : List String :=
  name.value.components.toList.map (·.value)

private def findNameIndex? (needle : String) : List String → Nat → Option Nat
  | [], _ => none
  | name :: rest, index =>
      if name = needle then some index else findNameIndex? needle rest (index + 1)

private def duplicateGenericParameterAux?
    (seen : List (String × Nat)) : List String → Nat →
      Option ProgramTypeResolutionError
  | [], _ => none
  | name :: rest, index =>
      match seen.find? fun previous => previous.1 == name with
      | some previous => some (.duplicateGenericParameter name previous.2 index)
      | none => duplicateGenericParameterAux? ((name, index) :: seen) rest (index + 1)

/-- Reject an ambiguous generic binder list before resolving any occurrence. -/
def validateProgramTypeScope
    (scope : ProgramTypeScope) : Except ProgramTypeResolutionError Unit :=
  match duplicateGenericParameterAux? [] scope.genericParameters 0 with
  | none => .ok ()
  | some error => .error error

private def builtinTypeName? : String → Option TypeSystem.BuiltinType
  | "Unit" | "unit" => some .unit
  | "Bool" | "bool" => some .bool
  | "Word" | "word" => some .word
  | _ => none

private def modulePathComponents (moduleId : Workspace.ModuleId) : List String :=
  moduleId.path.segments.map (·.text)

private def exactLibraryPrefixMatches
    (components : List String) (moduleId : Workspace.ModuleId) : Bool :=
  match components, moduleId.library with
  | "main" :: rest, .main => rest == modulePathComponents moduleId
  | "standard" :: rest, .standard => rest == modulePathComponents moduleId
  | library :: rest, .external name =>
      library == name.render && rest == modulePathComponents moduleId
  | _, _ => false

private def moduleQualifierMatches
    (current : Workspace.ModuleId) (components : List String)
    (candidate : Workspace.ModuleId) : Bool :=
  (decide (candidate.library = current.library) &&
      components == modulePathComponents candidate) ||
    exactLibraryPrefixMatches components candidate

private def qualifiedCandidates
    (environment : ProgramEnvironment) (scope : ProgramTypeScope)
    (moduleComponents : List String) (name : String) :
    List ProgramDeclaration :=
  environment.declarations.filter fun declaration =>
    declaration.nameSpace == some ProgramDeclarationNamespace.type &&
      declaration.name == some name &&
      moduleQualifierMatches scope.currentModule moduleComponents
        declaration.id.moduleId

private def declaredType
    (components : List String) (declaration : ProgramDeclaration)
    (arguments : List TypeSystem.Ty) :
    Except ProgramTypeResolutionError TypeSystem.Ty :=
  if declaration.genericParameters.length = arguments.length then
    .ok (TypeSystem.Ty.nominal declaration.id arguments)
  else
    .error (.typeArityMismatch components
      declaration.genericParameters.length arguments.length)

private def uniqueDeclaredType
    (components : List String) (arguments : List TypeSystem.Ty) :
    List ProgramDeclaration → Except ProgramTypeResolutionError TypeSystem.Ty
  | [] => .error (.unknownTypeName components)
  | [declaration] => declaredType components declaration arguments
  | declarations =>
      .error (.ambiguousTypeName components (declarations.map (·.id)))

/-- Resolve the staged integer intrinsic after the caller has exhausted every
user-defined type visible at the current lookup boundary. -/
private def resolveIntegerFallback
    (components : List String) (name : String)
    (arguments : List TypeSystem.Ty) :
    Except ProgramTypeResolutionError TypeSystem.Ty :=
  if name = "integer" then
    if arguments.isEmpty then
      .ok TypeSystem.Ty.integer
    else
      .error (.typeArityMismatch components 0 arguments.length)
  else
    .error (.unknownTypeName components)

private def resolveNamedProgramType
    (environment : ProgramEnvironment) (scope : ProgramTypeScope)
    (components : List String) (arguments : List TypeSystem.Ty) :
    Except ProgramTypeResolutionError TypeSystem.Ty :=
  match components with
  | [] => .error (.unknownTypeName [])
  | [name] =>
      match findNameIndex? name scope.genericParameters 0 with
      | some index =>
          if arguments.isEmpty then
            .ok (.parameter { owner := scope.genericOwner, index })
          else
            .error (.typeParameterApplied name index arguments.length)
      | none =>
          match builtinTypeName? name with
          | some builtin =>
              if arguments.isEmpty then
                .ok (.constructor (.builtin builtin))
              else
                .error (.typeArityMismatch components 0 arguments.length)
          | none =>
              match environment.localTypesNamed scope.currentModule name with
              | [] =>
                  match buildProgramImports environment scope.currentModule with
                  | .error errors => .error (.importVisibility errors)
                  | .ok visibility =>
                      match visibility.typesNamed name with
                      | [] =>
                          if visibility.hasImports then
                            resolveIntegerFallback components name arguments
                          else
                            match environment.typesNamed name with
                            | [] =>
                                resolveIntegerFallback components name arguments
                            | globalCandidates =>
                                uniqueDeclaredType components arguments
                                  globalCandidates
                      | importedCandidates =>
                          uniqueDeclaredType components arguments
                            importedCandidates
              | localCandidates =>
                  uniqueDeclaredType components arguments localCandidates
  | _ =>
      let name := components.getLast!
      let moduleComponents := components.dropLast
      match buildProgramImports environment scope.currentModule with
      | .error errors => .error (.importVisibility errors)
      | .ok visibility =>
          if visibility.hasNamespaceRoot moduleComponents then
            uniqueDeclaredType components arguments
              (visibility.typesInNamespacePathNamed moduleComponents name)
          else
            -- Kept for the executable initial profile: an unbound canonical
            -- module path may still address a declaration directly.
            uniqueDeclaredType components arguments
              (qualifiedCandidates environment scope moduleComponents name)

private def tupleProgramType : List TypeSystem.Ty → TypeSystem.Ty
  | [] => .constructor (.builtin .unit)
  | [type] => type
  | type :: rest => .product type (tupleProgramType rest)

mutual

  private def resolveProgramTypeExprFuel
      (environment : ProgramEnvironment) (scope : ProgramTypeScope) :
      Nat → Syntax.TypeExpr → Except ProgramTypeResolutionError TypeSystem.Ty
    | 0, _ => .error .nestingLimit
    | fuel + 1, ⟨_, .named name arguments⟩ => do
        let resolvedArguments ←
          match arguments with
          | none => pure []
          | some values =>
              resolveProgramTypeExprListFuel environment scope fuel
                values.elements.toList
        resolveNamedProgramType environment scope
          (programTypeNameComponents name) resolvedArguments
    | fuel + 1, ⟨_, .mapping _ _ key value⟩ => do
        let resolvedKey ← resolveProgramTypeExprFuel environment scope fuel key
        let resolvedValue ← resolveProgramTypeExprFuel environment scope fuel value
        pure (.mapping resolvedKey resolvedValue)
    | fuel + 1, ⟨_, .proxy _ inner⟩ => do
        let resolved ← resolveProgramTypeExprFuel environment scope fuel inner
        pure (.proxy resolved)
    | fuel + 1, ⟨_, .function _ parameters returns⟩ => do
        let resolvedParameters ←
          resolveProgramTypeExprListFuel environment scope fuel parameters.elements
        let resolvedReturns ←
          match returns with
          | none => pure []
          | some values =>
              resolveProgramTypeExprListFuel environment scope fuel values.elements
        pure (.function (tupleProgramType resolvedParameters)
          (tupleProgramType resolvedReturns))
    | fuel + 1, ⟨_, .comptime _ _ inner⟩ => do
        let resolved ← resolveProgramTypeExprFuel environment scope fuel inner
        pure (.comptime resolved)
    | fuel + 1, ⟨_, .tuple elements⟩ => do
        let resolved ← resolveProgramTypeExprListFuel environment scope fuel elements
        pure (tupleProgramType resolved)
    | _ + 1, ⟨_, .error⟩ => pure .error

  private def resolveProgramTypeExprListFuel
      (environment : ProgramEnvironment) (scope : ProgramTypeScope) :
      Nat → List Syntax.TypeExpr →
        Except ProgramTypeResolutionError (List TypeSystem.Ty)
    | _, [] => pure []
    | 0, _ :: _ => .error .nestingLimit
    | fuel + 1, source :: rest => do
        let type ← resolveProgramTypeExprFuel environment scope fuel source
        let types ← resolveProgramTypeExprListFuel environment scope fuel rest
        pure (type :: types)

end

/-- Default structural-resolution budget; extreme generated trees can opt in
to a larger explicit budget through `resolveProgramTypeExprWithFuel`. -/
def defaultProgramTypeResolutionFuel : Nat := 4096

/-- Resolve every name occurrence with an explicit structural budget. -/
def resolveProgramTypeExprWithFuel
    (environment : ProgramEnvironment) (scope : ProgramTypeScope)
    (fuel : Nat) (source : Syntax.TypeExpr) :
    Except ProgramTypeResolutionError TypeSystem.Ty := do
  validateProgramTypeScope scope
  resolveProgramTypeExprFuel environment scope fuel source

/-- Resolve a source-ordered list with an explicit structural budget. -/
def resolveProgramTypeExprListWithFuel
    (environment : ProgramEnvironment) (scope : ProgramTypeScope)
    (fuel : Nat) (sources : List Syntax.TypeExpr) :
    Except ProgramTypeResolutionError (List TypeSystem.Ty) := do
  validateProgramTypeScope scope
  resolveProgramTypeExprListFuel environment scope fuel sources

/-- Resolve every name occurrence in one canonical source type expression. -/
def resolveProgramTypeExpr
    (environment : ProgramEnvironment) (scope : ProgramTypeScope)
    (source : Syntax.TypeExpr) :
    Except ProgramTypeResolutionError TypeSystem.Ty :=
  resolveProgramTypeExprWithFuel environment scope
    defaultProgramTypeResolutionFuel source

/-- Resolve a source-ordered list of type expressions. -/
def resolveProgramTypeExprList
    (environment : ProgramEnvironment) (scope : ProgramTypeScope)
    (sources : List Syntax.TypeExpr) :
    Except ProgramTypeResolutionError (List TypeSystem.Ty) :=
  resolveProgramTypeExprListWithFuel environment scope
    defaultProgramTypeResolutionFuel sources

end Solcore.Frontend
