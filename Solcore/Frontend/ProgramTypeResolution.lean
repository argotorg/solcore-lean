import Solcore.Frontend.ProgramImports
import Solcore.TypeSystem.Substitution

/-!
Executable whole-program resolution of canonical source type expressions.

Unqualified names prefer a generic parameter, then the legacy builtins, then
the current module, and then explicitly imported public entities.  The exact
lowercase `integer` intrinsic is a final fallback after visible user-defined
types.  Qualified names traverse only namespace paths bound by imports and
public module re-exports.
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
  | cyclicTypeAlias (cycle : List Resolved.DeclarationId)
  | aliasExpansionLimit
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
                          resolveIntegerFallback components name arguments
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
            .error (.unknownTypeName components)

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

/-! Type aliases are first cataloged as declaration-headed types by the
structural resolver above.  Normalization is a separate pass so that an alias
body can be resolved in the scope of its declaration rather than the scope of
the use which selected it. -/

private structure ProgramTypeAliasApplication where
  declaration : ProgramDeclaration
  body : Syntax.TypeExpr
  arguments : List TypeSystem.Ty

private def programTypeApplicationSpine :
    TypeSystem.Ty → TypeSystem.Ty × List TypeSystem.Ty
  | .application function argument =>
      let (head, arguments) := programTypeApplicationSpine function
      (head, arguments ++ [argument])
  | type => (type, [])

private def programTypeAliasApplication?
    (environment : ProgramEnvironment) (type : TypeSystem.Ty) :
    Option ProgramTypeAliasApplication :=
  let (head, arguments) := programTypeApplicationSpine type
  match head with
  | .constructor (.declaration id) => do
      let declaration ← environment.declaration? id
      match declaration.kind, declaration.source.value with
      | .typeAlias, .typeAlias alias => some {
          declaration
          body := alias.value.value
          arguments
        }
      | _, _ => none
  | _ => none

private def programTypeAliasParameters
    (declaration : ProgramDeclaration) :
    List TypeSystem.TypeParameterId :=
  declaration.genericParameters.zipIdx.map fun (_, index) =>
    { owner := declaration.id, index }

private def programTypeAliasNameComponents
    (declaration : ProgramDeclaration) : List String :=
  match declaration.name with
  | some name => [name]
  | none => []

private def programTypeAliasCycle
    (stack : List Resolved.DeclarationId) (repeated : Resolved.DeclarationId) :
    List Resolved.DeclarationId :=
  let cycle := stack.dropWhile fun declaration =>
    decide (declaration ≠ repeated)
  cycle ++ [repeated]

private abbrev ProgramTypeAliasNormalizationM (α : Type) :=
  StateT Nat (Except ProgramTypeResolutionError) α

/-- Consume one shared alias-normalization node.  The state is threaded across
siblings so branching aliases cannot multiply work outside the total budget. -/
private def consumeProgramTypeAliasNode :
    ProgramTypeAliasNormalizationM Unit := do
  match ← get with
  | 0 => throw .aliasExpansionLimit
  | remaining + 1 => set remaining

mutual

  private def normalizeProgramTypeAliasesFuel
      (environment : ProgramEnvironment) :
      Nat → Nat → List Resolved.DeclarationId → TypeSystem.Ty →
        ProgramTypeAliasNormalizationM TypeSystem.Ty
    | 0, _, _, _ => throw .nestingLimit
    | structuralFuel + 1, aliasDepth, stack, type => do
        consumeProgramTypeAliasNode
        let structuralBudget := structuralFuel + 1
        match programTypeAliasApplication? environment type with
        | some application =>
            match aliasDepth with
            | 0 => throw .aliasExpansionLimit
            | remainingAliasDepth + 1 => do
                let declaration := application.declaration
                if stack.any fun active => decide (active = declaration.id) then
                  throw (.cyclicTypeAlias
                    (programTypeAliasCycle stack declaration.id))
                if declaration.genericParameters.length !=
                    application.arguments.length then
                  throw (.typeArityMismatch
                    (programTypeAliasNameComponents declaration)
                    declaration.genericParameters.length
                    application.arguments.length)
                let arguments ← normalizeProgramTypeAliasListFuel environment
                  structuralFuel (remainingAliasDepth + 1) stack
                    application.arguments
                let aliasScope := ProgramTypeScope.ofDeclaration declaration
                validateProgramTypeScope aliasScope
                let rawBody ← resolveProgramTypeExprFuel environment
                  aliasScope structuralBudget application.body
                let substitution : TypeSystem.ParameterSubstitution :=
                  (programTypeAliasParameters declaration).zip arguments
                normalizeProgramTypeAliasesFuel environment structuralBudget
                  remainingAliasDepth (stack ++ [declaration.id])
                  (substitution.apply rawBody)
        | none =>
            match type with
            | .application function argument => do
                let normalizedFunction ← normalizeProgramTypeAliasesFuel environment
                  structuralFuel aliasDepth stack function
                let normalizedArgument ← normalizeProgramTypeAliasesFuel environment
                  structuralFuel aliasDepth stack argument
                pure (.application normalizedFunction normalizedArgument)
            | .function parameter result => do
                let normalizedParameter ← normalizeProgramTypeAliasesFuel environment
                  structuralFuel aliasDepth stack parameter
                let normalizedResult ← normalizeProgramTypeAliasesFuel environment
                  structuralFuel aliasDepth stack result
                pure (.function normalizedParameter normalizedResult)
            | .product left right => do
                let normalizedLeft ← normalizeProgramTypeAliasesFuel environment
                  structuralFuel aliasDepth stack left
                let normalizedRight ← normalizeProgramTypeAliasesFuel environment
                  structuralFuel aliasDepth stack right
                pure (.product normalizedLeft normalizedRight)
            | .mapping key value => do
                let normalizedKey ← normalizeProgramTypeAliasesFuel environment
                  structuralFuel aliasDepth stack key
                let normalizedValue ← normalizeProgramTypeAliasesFuel environment
                  structuralFuel aliasDepth stack value
                pure (.mapping normalizedKey normalizedValue)
            | .proxy inner =>
                return .proxy (← normalizeProgramTypeAliasesFuel environment
                  structuralFuel aliasDepth stack inner)
            | .comptime inner =>
                return .comptime (← normalizeProgramTypeAliasesFuel environment
                  structuralFuel aliasDepth stack inner)
            | .variable _
            | .parameter _
            | .constructor _
            | .error => pure type
  termination_by structuralFuel aliasDepth _ type =>
    (structuralFuel + aliasDepth, sizeOf type)
  decreasing_by all_goals omega

  private def normalizeProgramTypeAliasListFuel
      (environment : ProgramEnvironment) :
      Nat → Nat → List Resolved.DeclarationId → List TypeSystem.Ty →
        ProgramTypeAliasNormalizationM (List TypeSystem.Ty)
    | _, _, _, [] => pure []
    | 0, _, _, _ :: _ => throw .nestingLimit
    | structuralFuel + 1, aliasDepth, stack, type :: rest => do
        let normalized ← normalizeProgramTypeAliasesFuel environment
          structuralFuel aliasDepth stack type
        let normalizedRest ← normalizeProgramTypeAliasListFuel environment
          (structuralFuel + 1) aliasDepth stack rest
        pure (normalized :: normalizedRest)
  termination_by structuralFuel aliasDepth _ types =>
    (structuralFuel + aliasDepth, sizeOf types)

end

private def runProgramTypeAliasNormalization
    {α : Type} (nodeBudget : Nat)
    (computation : ProgramTypeAliasNormalizationM α) :
    Except ProgramTypeResolutionError α := do
  let result ← computation.run nodeBudget
  pure result.1

/-- Default structural-resolution budget; extreme generated trees can opt in
to a larger explicit budget through `resolveProgramTypeExprWithFuel`. -/
def defaultProgramTypeResolutionFuel : Nat := 4096

/-- Default total node budget for transparent-alias normalization.  The same
value also bounds a single alias chain for executable termination. -/
def defaultProgramTypeAliasExpansionFuel : Nat := 16384

/-- Resolve and transparently expand one source type with independent
structural and alias-expansion budgets. -/
def resolveProgramTypeExprWithBudgets
    (environment : ProgramEnvironment) (scope : ProgramTypeScope)
    (structuralFuel aliasExpansionFuel : Nat) (source : Syntax.TypeExpr) :
    Except ProgramTypeResolutionError TypeSystem.Ty := do
  validateProgramTypeScope scope
  let raw ← resolveProgramTypeExprFuel environment scope structuralFuel source
  runProgramTypeAliasNormalization aliasExpansionFuel
    (normalizeProgramTypeAliasesFuel environment structuralFuel
      aliasExpansionFuel [] raw)

/-- Resolve and transparently expand a source-ordered list with independent
structural and alias-expansion budgets. -/
def resolveProgramTypeExprListWithBudgets
    (environment : ProgramEnvironment) (scope : ProgramTypeScope)
    (structuralFuel aliasExpansionFuel : Nat) (sources : List Syntax.TypeExpr) :
    Except ProgramTypeResolutionError (List TypeSystem.Ty) := do
  validateProgramTypeScope scope
  let raw ← resolveProgramTypeExprListFuel environment scope structuralFuel sources
  runProgramTypeAliasNormalization aliasExpansionFuel
    (normalizeProgramTypeAliasListFuel environment structuralFuel
      aliasExpansionFuel [] raw)

/-- Resolve and normalize one alias declaration body while treating the
declaration itself as the root of cycle diagnostics. -/
def resolveProgramTypeAliasBodyWithBudgets
    (environment : ProgramEnvironment) (declaration : ProgramDeclaration)
    (structuralFuel aliasExpansionFuel : Nat) (source : Syntax.TypeExpr) :
    Except ProgramTypeResolutionError TypeSystem.Ty := do
  let scope := ProgramTypeScope.ofDeclaration declaration
  validateProgramTypeScope scope
  let raw ← resolveProgramTypeExprFuel environment scope structuralFuel source
  runProgramTypeAliasNormalization aliasExpansionFuel
    (normalizeProgramTypeAliasesFuel environment structuralFuel
      aliasExpansionFuel [declaration.id] raw)

/-- Resolve every name occurrence with an explicit structural budget. -/
def resolveProgramTypeExprWithFuel
    (environment : ProgramEnvironment) (scope : ProgramTypeScope)
    (fuel : Nat) (source : Syntax.TypeExpr) :
    Except ProgramTypeResolutionError TypeSystem.Ty :=
  resolveProgramTypeExprWithBudgets environment scope fuel
    defaultProgramTypeAliasExpansionFuel source

/-- Resolve a source-ordered list with an explicit structural budget. -/
def resolveProgramTypeExprListWithFuel
    (environment : ProgramEnvironment) (scope : ProgramTypeScope)
    (fuel : Nat) (sources : List Syntax.TypeExpr) :
    Except ProgramTypeResolutionError (List TypeSystem.Ty) :=
  resolveProgramTypeExprListWithBudgets environment scope fuel
    defaultProgramTypeAliasExpansionFuel sources

/-- Resolve one alias declaration body with declaration-rooted cycle paths. -/
def resolveProgramTypeAliasBody
    (environment : ProgramEnvironment) (declaration : ProgramDeclaration)
    (source : Syntax.TypeExpr) :
    Except ProgramTypeResolutionError TypeSystem.Ty :=
  resolveProgramTypeAliasBodyWithBudgets environment declaration
    defaultProgramTypeResolutionFuel defaultProgramTypeAliasExpansionFuel source

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
