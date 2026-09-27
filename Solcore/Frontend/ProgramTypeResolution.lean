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

/-! Successful source-type resolution cannot manufacture flexible inference
metavariables.  This is the algorithmic closedness premise needed before a
resolved type can be related to the declaration-owned binders and nominal
catalogs of `SourceSemantics.TypeWellScoped`. -/

private def ProgramTypesVariablesBelow
    (next : Nat) (types : List TypeSystem.Ty) : Prop :=
  ∀ type ∈ types, type.VariablesBelow next

private theorem programTypesVariablesBelow_nil (next : Nat) :
    ProgramTypesVariablesBelow next [] := by
  simp [ProgramTypesVariablesBelow]

private theorem programTypesVariablesBelow_cons
    {next : Nat} {head : TypeSystem.Ty} {tail : List TypeSystem.Ty}
    (headBelow : head.VariablesBelow next)
    (tailBelow : ProgramTypesVariablesBelow next tail) :
    ProgramTypesVariablesBelow next (head :: tail) := by
  simpa [ProgramTypesVariablesBelow] using ⟨headBelow, tailBelow⟩

private theorem applyMany_variablesBelow
    {next : Nat} {head : TypeSystem.Ty} {arguments : List TypeSystem.Ty}
    (headBelow : head.VariablesBelow next)
    (argumentsBelow : ProgramTypesVariablesBelow next arguments) :
    (TypeSystem.Ty.applyMany head arguments).VariablesBelow next := by
  induction arguments generalizing head with
  | nil => simpa [TypeSystem.Ty.applyMany] using headBelow
  | cons argument arguments induction =>
      apply induction
      · simp only [TypeSystem.Ty.variablesBelow_application_iff]
        exact ⟨headBelow, argumentsBelow argument (by simp)⟩
      · intro type member
        exact argumentsBelow type (by simp [member])

private theorem nominal_variablesBelow
    {next : Nat} {declaration : Resolved.DeclarationId}
    {arguments : List TypeSystem.Ty}
    (argumentsBelow : ProgramTypesVariablesBelow next arguments) :
    (TypeSystem.Ty.nominal declaration arguments).VariablesBelow next := by
  apply applyMany_variablesBelow
  · simp
  · exact argumentsBelow

private theorem tupleProgramType_variablesBelow
    {next : Nat} {types : List TypeSystem.Ty}
    (typesBelow : ProgramTypesVariablesBelow next types) :
    (tupleProgramType types).VariablesBelow next := by
  induction types with
  | nil => simp [tupleProgramType]
  | cons head tail induction =>
      cases tail with
      | nil => exact typesBelow head (by simp)
      | cons nextHead rest =>
          simp only [tupleProgramType,
            TypeSystem.Ty.variablesBelow_product_iff]
          exact ⟨typesBelow head (by simp), induction (by
            intro type member
            exact typesBelow type (by simp [member]))⟩

private theorem parameterSubstitution_lookup_mem
    {substitution : TypeSystem.ParameterSubstitution}
    {parameter : TypeSystem.TypeParameterId} {replacement : TypeSystem.Ty}
    (found : substitution.lookup? parameter = some replacement) :
    (parameter, replacement) ∈ substitution := by
  induction substitution with
  | nil => simp [TypeSystem.ParameterSubstitution.lookup?] at found
  | cons entry rest induction =>
      rcases entry with ⟨candidate, candidateReplacement⟩
      by_cases same : candidate = parameter
      · subst candidate
        simp [TypeSystem.ParameterSubstitution.lookup?] at found
        cases found
        simp
      · have tailFound :
            TypeSystem.ParameterSubstitution.lookup? rest parameter =
              some replacement := by
          simpa [TypeSystem.ParameterSubstitution.lookup?, same] using found
        exact List.mem_cons_of_mem _ (induction tailFound)

private theorem parameterSubstitution_variablesBelow
    {next : Nat} {substitution : TypeSystem.ParameterSubstitution}
    {type : TypeSystem.Ty}
    (rangesBelow : ProgramTypesVariablesBelow next (substitution.map Prod.snd))
    (typeBelow : type.VariablesBelow next) :
    (substitution.apply type).VariablesBelow next := by
  induction type with
  | «variable» metavariable =>
      simpa [TypeSystem.ParameterSubstitution.apply] using typeBelow
  | parameter candidate =>
      cases found : substitution.lookup? candidate with
      | none => simp [TypeSystem.ParameterSubstitution.apply, found]
      | some replacement =>
          simp only [TypeSystem.ParameterSubstitution.apply, found,
            Option.getD_some]
          exact rangesBelow replacement (List.mem_map.mpr
            ⟨(candidate, replacement), parameterSubstitution_lookup_mem found,
              rfl⟩)
  | constructor constructor => simp [TypeSystem.ParameterSubstitution.apply]
  | application left right leftInduction rightInduction =>
      have parts := (TypeSystem.Ty.variablesBelow_application_iff
        next left right).mp typeBelow
      simp only [TypeSystem.ParameterSubstitution.apply,
        TypeSystem.Ty.variablesBelow_application_iff]
      exact ⟨leftInduction parts.1, rightInduction parts.2⟩
  | function parameter result parameterInduction resultInduction =>
      have parts := (TypeSystem.Ty.variablesBelow_function_iff
        next parameter result).mp typeBelow
      simp only [TypeSystem.ParameterSubstitution.apply,
        TypeSystem.Ty.variablesBelow_function_iff]
      exact ⟨parameterInduction parts.1, resultInduction parts.2⟩
  | product left right leftInduction rightInduction =>
      have parts := (TypeSystem.Ty.variablesBelow_product_iff
        next left right).mp typeBelow
      simp only [TypeSystem.ParameterSubstitution.apply,
        TypeSystem.Ty.variablesBelow_product_iff]
      exact ⟨leftInduction parts.1, rightInduction parts.2⟩
  | mapping key value keyInduction valueInduction =>
      have parts := (TypeSystem.Ty.variablesBelow_mapping_iff
        next key value).mp typeBelow
      simp only [TypeSystem.ParameterSubstitution.apply,
        TypeSystem.Ty.variablesBelow_mapping_iff]
      exact ⟨keyInduction parts.1, valueInduction parts.2⟩
  | proxy inner induction =>
      simpa [TypeSystem.ParameterSubstitution.apply] using induction typeBelow
  | comptime inner induction =>
      simpa [TypeSystem.ParameterSubstitution.apply] using induction typeBelow
  | error => simp [TypeSystem.ParameterSubstitution.apply]

private theorem declaredType_variablesBelow
    {next : Nat} {components : List String}
    {declaration : ProgramDeclaration} {arguments : List TypeSystem.Ty}
    {resolved : TypeSystem.Ty}
    (argumentsBelow : ProgramTypesVariablesBelow next arguments)
    (success : declaredType components declaration arguments = .ok resolved) :
    resolved.VariablesBelow next := by
  simp only [declaredType] at success
  split at success
  · injection success with resolvedEq
    subst resolved
    exact nominal_variablesBelow argumentsBelow
  · simp at success

private theorem uniqueDeclaredType_variablesBelow
    {next : Nat} {components : List String} {arguments : List TypeSystem.Ty}
    {declarations : List ProgramDeclaration} {resolved : TypeSystem.Ty}
    (argumentsBelow : ProgramTypesVariablesBelow next arguments)
    (success : uniqueDeclaredType components arguments declarations =
      .ok resolved) :
    resolved.VariablesBelow next := by
  cases declarations with
  | nil => simp [uniqueDeclaredType] at success
  | cons declaration rest =>
      cases rest with
      | nil =>
          exact declaredType_variablesBelow argumentsBelow
            (by simpa [uniqueDeclaredType] using success)
      | cons nextDeclaration tail =>
          simp [uniqueDeclaredType] at success

private theorem resolveIntegerFallback_variablesBelow
    {next : Nat} {components : List String} {name : String}
    {arguments : List TypeSystem.Ty} {resolved : TypeSystem.Ty}
    (success : resolveIntegerFallback components name arguments =
      .ok resolved) :
    resolved.VariablesBelow next := by
  simp only [resolveIntegerFallback] at success
  split at success
  · split at success
    · injection success with resolvedEq
      subst resolved
      exact TypeSystem.Ty.variablesBelow_constructor next
        (.builtin .integer)
    · simp at success
  · simp at success

private theorem resolveNamedProgramType_variablesBelow
    {next : Nat} {environment : ProgramEnvironment}
    {scope : ProgramTypeScope} {components : List String}
    {arguments : List TypeSystem.Ty} {resolved : TypeSystem.Ty}
    (argumentsBelow : ProgramTypesVariablesBelow next arguments)
    (success : resolveNamedProgramType environment scope components arguments =
      .ok resolved) :
    resolved.VariablesBelow next := by
  cases components with
  | nil => simp [resolveNamedProgramType] at success
  | cons first rest =>
      cases rest with
      | nil =>
          simp only [resolveNamedProgramType] at success
          split at success
          · split at success
            · injection success with resolvedEq
              subst resolved
              simp
            · simp at success
          · split at success
            · split at success
              · injection success with resolvedEq
                subst resolved
                simp
              · simp at success
            · split at success
              · split at success
                · simp at success
                · split at success
                  · exact resolveIntegerFallback_variablesBelow success
                  · exact uniqueDeclaredType_variablesBelow argumentsBelow success
              · exact uniqueDeclaredType_variablesBelow argumentsBelow success
      | cons second tail =>
          simp only [resolveNamedProgramType] at success
          split at success
          · simp at success
          · split at success
            · exact uniqueDeclaredType_variablesBelow argumentsBelow success
            · simp at success

private theorem resolveProgramTypeFuel_variablesBelow
    (next : Nat) (environment : ProgramEnvironment) (scope : ProgramTypeScope)
    (fuel : Nat) :
    (∀ source resolved,
      resolveProgramTypeExprFuel environment scope fuel source = .ok resolved →
        resolved.VariablesBelow next) ∧
    (∀ sources resolved,
      resolveProgramTypeExprListFuel environment scope fuel sources =
          .ok resolved →
        ProgramTypesVariablesBelow next resolved) := by
  induction fuel with
  | zero =>
      constructor
      · intro source resolved success
        simp [resolveProgramTypeExprFuel] at success
      · intro sources resolved success
        cases sources with
        | nil =>
            simp [resolveProgramTypeExprListFuel, pure, Pure.pure,
              Except.pure] at success
            subst resolved
            exact programTypesVariablesBelow_nil next
        | cons source rest =>
            simp [resolveProgramTypeExprListFuel] at success
  | succ fuel induction =>
      rcases induction with ⟨resolveInduction, listInduction⟩
      constructor
      · intro source resolved success
        rcases source with ⟨span, source⟩
        cases source with
        | named name arguments =>
            cases arguments with
            | none =>
                exact resolveNamedProgramType_variablesBelow
                  (programTypesVariablesBelow_nil next)
                  (by simpa [resolveProgramTypeExprFuel] using success)
            | some arguments =>
                cases argumentsResult : resolveProgramTypeExprListFuel
                    environment scope fuel arguments.elements.toList with
                | error error =>
                    simp [resolveProgramTypeExprFuel, argumentsResult, bind,
                      Except.bind] at success
                | ok resolvedArguments =>
                    apply resolveNamedProgramType_variablesBelow
                      (listInduction _ _ argumentsResult)
                    simpa [resolveProgramTypeExprFuel, argumentsResult, bind,
                      Except.bind] using success
        | mapping keyword argumentsSpan key value =>
            cases keyResult : resolveProgramTypeExprFuel environment scope fuel key with
            | error error =>
                simp [resolveProgramTypeExprFuel, keyResult, bind,
                  Except.bind] at success
            | ok resolvedKey =>
                cases valueResult : resolveProgramTypeExprFuel environment scope fuel value with
                | error error =>
                    simp [resolveProgramTypeExprFuel, keyResult, valueResult,
                      bind, Except.bind] at success
                | ok resolvedValue =>
                    simp [resolveProgramTypeExprFuel, keyResult, valueResult,
                      bind, Except.bind, pure, Pure.pure, Except.pure] at success
                    subst resolved
                    simp only [TypeSystem.Ty.variablesBelow_mapping_iff]
                    exact ⟨resolveInduction _ _ keyResult,
                      resolveInduction _ _ valueResult⟩
        | proxy marker inner =>
            cases innerResult : resolveProgramTypeExprFuel environment scope fuel inner with
            | error error =>
                simp [resolveProgramTypeExprFuel, innerResult, bind,
                  Except.bind] at success
            | ok resolvedInner =>
                simp [resolveProgramTypeExprFuel, innerResult, bind,
                  Except.bind, pure, Pure.pure, Except.pure] at success
                subst resolved
                simpa using resolveInduction _ _ innerResult
        | function keyword parameters returns =>
            cases parametersResult : resolveProgramTypeExprListFuel
                environment scope fuel parameters.elements with
            | error error =>
                simp [resolveProgramTypeExprFuel, parametersResult, bind,
                  Except.bind] at success
            | ok resolvedParameters =>
                cases returns with
                | none =>
                    simp [resolveProgramTypeExprFuel, parametersResult, bind,
                      Except.bind, pure, Pure.pure, Except.pure] at success
                    subst resolved
                    simp only [TypeSystem.Ty.variablesBelow_function_iff]
                    exact ⟨tupleProgramType_variablesBelow
                        (listInduction _ _ parametersResult),
                      tupleProgramType_variablesBelow
                        (programTypesVariablesBelow_nil next)⟩
                | some returns =>
                    cases returnsResult : resolveProgramTypeExprListFuel
                        environment scope fuel returns.elements with
                    | error error =>
                        simp [resolveProgramTypeExprFuel, parametersResult,
                          returnsResult, bind, Except.bind] at success
                    | ok resolvedReturns =>
                        simp [resolveProgramTypeExprFuel, parametersResult,
                          returnsResult, bind, Except.bind, pure, Pure.pure,
                          Except.pure] at success
                        subst resolved
                        simp only [TypeSystem.Ty.variablesBelow_function_iff]
                        exact ⟨tupleProgramType_variablesBelow
                            (listInduction _ _ parametersResult),
                          tupleProgramType_variablesBelow
                            (listInduction _ _ returnsResult)⟩
        | comptime keyword argumentsSpan inner =>
            cases innerResult : resolveProgramTypeExprFuel environment scope fuel inner with
            | error error =>
                simp [resolveProgramTypeExprFuel, innerResult, bind,
                  Except.bind] at success
            | ok resolvedInner =>
                simp [resolveProgramTypeExprFuel, innerResult, bind,
                  Except.bind, pure, Pure.pure, Except.pure] at success
                subst resolved
                simpa using resolveInduction _ _ innerResult
        | tuple elements =>
            cases elementsResult : resolveProgramTypeExprListFuel
                environment scope fuel elements with
            | error error =>
                simp [resolveProgramTypeExprFuel, elementsResult, bind,
                  Except.bind] at success
            | ok resolvedElements =>
                simp [resolveProgramTypeExprFuel, elementsResult, bind,
                  Except.bind, pure, Pure.pure, Except.pure] at success
                subst resolved
                exact tupleProgramType_variablesBelow
                  (listInduction _ _ elementsResult)
        | error =>
            simp [resolveProgramTypeExprFuel, pure, Pure.pure,
              Except.pure] at success
            subst resolved
            exact TypeSystem.Ty.variablesBelow_error next
      · intro sources resolved success
        cases sources with
        | nil =>
            simp [resolveProgramTypeExprListFuel, pure, Pure.pure,
              Except.pure] at success
            subst resolved
            exact programTypesVariablesBelow_nil next
        | cons source rest =>
            cases headResult : resolveProgramTypeExprFuel
                environment scope fuel source with
            | error error =>
                simp [resolveProgramTypeExprListFuel, headResult, bind,
                  Except.bind] at success
            | ok resolvedHead =>
                cases tailResult : resolveProgramTypeExprListFuel
                    environment scope fuel rest with
                | error error =>
                    simp [resolveProgramTypeExprListFuel, headResult,
                      tailResult, bind, Except.bind] at success
                | ok resolvedTail =>
                    simp [resolveProgramTypeExprListFuel, headResult,
                      tailResult, bind, Except.bind, pure, Pure.pure,
                      Except.pure] at success
                    subst resolved
                    exact programTypesVariablesBelow_cons
                      (resolveInduction _ _ headResult)
                      (listInduction _ _ tailResult)

private theorem programTypesVariablesBelow_append
    {next : Nat} {left right : List TypeSystem.Ty}
    (leftBelow : ProgramTypesVariablesBelow next left)
    (rightBelow : ProgramTypesVariablesBelow next right) :
    ProgramTypesVariablesBelow next (left ++ right) := by
  intro type member
  rcases List.mem_append.mp member with member | member
  · exact leftBelow type member
  · exact rightBelow type member

private theorem programTypeApplicationSpine_variablesBelow
    {next : Nat} {type head : TypeSystem.Ty}
    {arguments : List TypeSystem.Ty}
    (typeBelow : type.VariablesBelow next)
    (spine : programTypeApplicationSpine type = (head, arguments)) :
    head.VariablesBelow next ∧
      ProgramTypesVariablesBelow next arguments := by
  induction type generalizing head arguments with
  | application function argument induction =>
      simp only [programTypeApplicationSpine] at spine
      cases functionSpine : programTypeApplicationSpine function with
      | mk functionHead functionArguments =>
          simp only [functionSpine] at spine
          injection spine with headEq argumentsEq
          subst head
          subst arguments
          have parts := (TypeSystem.Ty.variablesBelow_application_iff
            next function argument).mp typeBelow
          have functionParts := induction parts.1 functionSpine
          exact ⟨functionParts.1, programTypesVariablesBelow_append
            functionParts.2 (programTypesVariablesBelow_cons parts.2
              (programTypesVariablesBelow_nil next))⟩
  | «variable» metavariable
  | parameter metavariable
  | constructor metavariable
  | error =>
      simp only [programTypeApplicationSpine] at spine
      injection spine with headEq argumentsEq
      subst head
      subst arguments
      exact ⟨typeBelow, programTypesVariablesBelow_nil next⟩
  | function left right leftInduction rightInduction
  | product left right leftInduction rightInduction
  | mapping left right leftInduction rightInduction =>
      simp only [programTypeApplicationSpine] at spine
      injection spine with headEq argumentsEq
      subst head
      subst arguments
      exact ⟨typeBelow, programTypesVariablesBelow_nil next⟩
  | proxy inner induction
  | comptime inner induction =>
      simp only [programTypeApplicationSpine] at spine
      injection spine with headEq argumentsEq
      subst head
      subst arguments
      exact ⟨typeBelow, programTypesVariablesBelow_nil next⟩

private theorem programTypeAliasApplication_arguments_variablesBelow
    {next : Nat} {environment : ProgramEnvironment} {type : TypeSystem.Ty}
    {application : ProgramTypeAliasApplication}
    (typeBelow : type.VariablesBelow next)
    (found : programTypeAliasApplication? environment type = some application) :
    ProgramTypesVariablesBelow next application.arguments := by
  simp only [programTypeAliasApplication?] at found
  cases spine : programTypeApplicationSpine type with
  | mk head arguments =>
      have spineBelow := programTypeApplicationSpine_variablesBelow
        typeBelow spine
      simp only [spine] at found
      cases head with
      | constructor constructor =>
          cases constructor with
          | declaration id =>
              cases declarationResult : environment.declaration? id with
              | none => simp [declarationResult] at found
              | some declaration =>
                  simp only [declarationResult] at found
                  cases kindEq : declaration.kind <;>
                    cases sourceEq : declaration.source.value <;>
                    simp [kindEq, sourceEq] at found
                  case typeAlias.typeAlias alias =>
                    subst application
                    exact spineBelow.2
          | builtin builtin => simp at found
      | «variable» metavariable
      | parameter metavariable
      | application function argument
      | function parameter result
      | product left right
      | mapping key value
      | proxy inner
      | comptime inner
      | error => simp at found

private theorem stateTExcept_bind_success
    {σ α β ε : Type} {first : StateT σ (Except ε) α}
    {next : α → StateT σ (Except ε) β}
    {initial final : σ} {result : β}
    (success : (first >>= next).run initial = .ok (result, final)) :
    ∃ value middle,
      first.run initial = .ok (value, middle) ∧
        (next value).run middle = .ok (result, final) := by
  simp only [StateT.run, bind, StateT.bind, Except.bind] at success
  cases firstResult : first initial with
  | error error => simp [firstResult] at success
  | ok pair =>
      rcases pair with ⟨value, middle⟩
      refine ⟨value, middle, by simpa [StateT.run] using firstResult, ?_⟩
      simpa [StateT.run, firstResult] using success

private theorem stateTExcept_lift_success
    {σ α ε : Type} {computation : Except ε α}
    {initial final : σ} {result : α}
    (success : (liftM computation : StateT σ (Except ε) α).run initial =
      .ok (result, final)) :
    computation = .ok result ∧ final = initial := by
  change (StateT.lift computation).run initial =
    .ok (result, final) at success
  cases computation with
  | error error =>
      change Except.error error = Except.ok (result, final) at success
      simp at success
  | ok value =>
      change Except.ok (value, initial) = Except.ok (result, final) at success
      injection success with pairEq
      injection pairEq with resultEq finalEq
      exact ⟨congrArg (Except.ok (ε := ε)) resultEq, finalEq.symm⟩

private theorem programTypesVariablesBelow_zip_snd
    {next : Nat} {parameters : List TypeSystem.TypeParameterId}
    {arguments : List TypeSystem.Ty}
    (argumentsBelow : ProgramTypesVariablesBelow next arguments) :
    ProgramTypesVariablesBelow next ((parameters.zip arguments).map Prod.snd) := by
  intro type member
  simp only [List.mem_map] at member
  obtain ⟨entry, entryMember, typeEq⟩ := member
  subst type
  exact argumentsBelow entry.2 (List.of_mem_zip entryMember).2

private theorem consumeProgramTypeAliasNode_then_success
    {α : Type} {continuation : ProgramTypeAliasNormalizationM α}
    {nodeBudget remaining : Nat} {resolved : α}
    (success : (do
      consumeProgramTypeAliasNode
      continuation).run (nodeBudget + 1) = .ok (resolved, remaining)) :
    continuation.run nodeBudget = .ok (resolved, remaining) := by
  exact success

private theorem consumeProgramTypeAliasNode_zero_impossible
    {α : Type} {continuation : ProgramTypeAliasNormalizationM α}
    {remaining : Nat} {resolved : α}
    (success : (do
      consumeProgramTypeAliasNode
      continuation).run 0 = .ok (resolved, remaining)) : False := by
  change Except.error ProgramTypeResolutionError.aliasExpansionLimit =
    .ok (resolved, remaining) at success
  simp at success

private theorem stateTExcept_pure_success
    {σ α ε : Type} {value result : α} {initial final : σ}
    (success : (pure value : StateT σ (Except ε) α).run initial =
      .ok (result, final)) :
    result = value ∧ final = initial := by
  change Except.ok (value, initial) = Except.ok (result, final) at success
  injection success with pairEq
  injection pairEq with valueEq stateEq
  exact ⟨valueEq.symm, stateEq.symm⟩

private theorem stateTExcept_throw_impossible
    {σ α ε : Type} {error : ε} {initial final : σ} {result : α}
    (success : (throw error : StateT σ (Except ε) α).run initial =
      .ok (result, final)) : False := by
  change Except.error error = Except.ok (result, final) at success
  simp at success

private theorem stateTExcept_throw_then_impossible
    {σ α β ε : Type} {error : ε}
    {continuation : α → StateT σ (Except ε) β}
    {initial final : σ} {result : β}
    (success : (do
      let value ← (throw error : StateT σ (Except ε) α)
      continuation value).run initial = .ok (result, final)) : False := by
  obtain ⟨value, middle, thrown, continued⟩ :=
    stateTExcept_bind_success success
  exact stateTExcept_throw_impossible thrown

private theorem stateTExcept_map_success
    {σ α β ε : Type} {computation : StateT σ (Except ε) α}
    {transform : α → β} {initial final : σ} {result : β}
    (success : (do
      let value ← computation
      pure (transform value)).run initial = .ok (result, final)) :
    ∃ value, computation.run initial = .ok (value, final) ∧
      result = transform value := by
  obtain ⟨value, middle, computationSuccess, pureSuccess⟩ :=
    stateTExcept_bind_success success
  have pureProperties := stateTExcept_pure_success pureSuccess
  refine ⟨value, ?_, pureProperties.1⟩
  rw [pureProperties.2]
  exact computationSuccess

private theorem stateTExcept_map₂_success
    {σ α β γ ε : Type} {left : StateT σ (Except ε) α}
    {right : StateT σ (Except ε) β} {combine : α → β → γ}
    {initial final : σ} {result : γ}
    (success : (do
      let leftValue ← left
      let rightValue ← right
      pure (combine leftValue rightValue)).run initial =
        .ok (result, final)) :
    ∃ leftValue middle rightValue,
      left.run initial = .ok (leftValue, middle) ∧
        right.run middle = .ok (rightValue, final) ∧
          result = combine leftValue rightValue := by
  obtain ⟨leftValue, middle, leftSuccess, restSuccess⟩ :=
    stateTExcept_bind_success success
  obtain ⟨rightValue, rightSuccess, resultEq⟩ :=
    stateTExcept_map_success restSuccess
  exact ⟨leftValue, middle, rightValue, leftSuccess, rightSuccess, resultEq⟩

private theorem normalizeProgramTypeAliasesFuel_variablesBelow_mutual
    (next : Nat) (environment : ProgramEnvironment) :
    (∀ structuralFuel aliasDepth stack type nodeBudget resolved remaining,
        type.VariablesBelow next →
        (normalizeProgramTypeAliasesFuel environment structuralFuel aliasDepth
            stack type).run nodeBudget = .ok (resolved, remaining) →
        resolved.VariablesBelow next) ∧
      (∀ structuralFuel aliasDepth stack types nodeBudget resolved remaining,
        ProgramTypesVariablesBelow next types →
        (normalizeProgramTypeAliasListFuel environment structuralFuel aliasDepth
            stack types).run nodeBudget = .ok (resolved, remaining) →
        ProgramTypesVariablesBelow next resolved) := by
  apply normalizeProgramTypeAliasesFuel.mutual_induct
    (motive2 := fun structuralFuel aliasDepth stack types =>
      ∀ nodeBudget resolved remaining,
        ProgramTypesVariablesBelow next types →
        (normalizeProgramTypeAliasListFuel environment structuralFuel aliasDepth
            stack types).run nodeBudget = .ok (resolved, remaining) →
        ProgramTypesVariablesBelow next resolved)
  · intro aliasDepth stack type nodeBudget resolved remaining typeBelow success
    unfold normalizeProgramTypeAliasesFuel at success
    change Except.error ProgramTypeResolutionError.nestingLimit =
      .ok (resolved, remaining) at success
    simp at success
  · intro structuralFuel aliasDepth stack type aliasInduction typeInduction
      nodeBudget resolved remaining typeBelow success
    unfold normalizeProgramTypeAliasesFuel at success
    cases nodeBudget with
    | zero => exact (consumeProgramTypeAliasNode_zero_impossible success).elim
    | succ nodeBudget =>
        have continued := consumeProgramTypeAliasNode_then_success success
        cases applicationEq : programTypeAliasApplication? environment type with
        | some application =>
            simp only [applicationEq] at continued
            cases aliasDepth with
            | zero => exact (stateTExcept_throw_impossible continued).elim
            | succ remainingAliasDepth =>
                have aliasParts := aliasInduction application
                by_cases cyclic :
                    (stack.any fun active =>
                      decide (active = application.declaration.id)) = true
                · simp only [cyclic] at continued
                  exact (stateTExcept_throw_then_impossible continued).elim
                · simp only [cyclic] at continued
                  by_cases arityMismatch :
                      (application.declaration.genericParameters.length !=
                        application.arguments.length) = true
                  · simp only [arityMismatch] at continued
                    exact (stateTExcept_throw_then_impossible continued).elim
                  · simp only [arityMismatch] at continued
                    obtain ⟨normalizedArguments, afterArguments,
                        argumentsSuccess, afterArgumentsSuccess⟩ :=
                      stateTExcept_bind_success continued
                    obtain ⟨validated, afterValidation, validationSuccess,
                        afterValidationSuccess⟩ :=
                      stateTExcept_bind_success afterArgumentsSuccess
                    obtain ⟨rawBody, afterRaw, rawLiftSuccess,
                        normalizedSuccess⟩ :=
                      stateTExcept_bind_success afterValidationSuccess
                    have _validationResult :=
                      stateTExcept_lift_success validationSuccess
                    have rawResult := stateTExcept_lift_success rawLiftSuccess
                    have sourceArgumentsBelow :=
                      programTypeAliasApplication_arguments_variablesBelow
                        typeBelow applicationEq
                    have normalizedArgumentsBelow := aliasParts.1
                      nodeBudget normalizedArguments afterArguments
                      sourceArgumentsBelow argumentsSuccess
                    have rawBodyBelow :=
                      (resolveProgramTypeFuel_variablesBelow next environment
                        (ProgramTypeScope.ofDeclaration application.declaration)
                        (structuralFuel + 1)).1 _ _ rawResult.1
                    have substitutionBelow := parameterSubstitution_variablesBelow
                      (substitution :=
                        (programTypeAliasParameters application.declaration).zip
                          normalizedArguments)
                      (programTypesVariablesBelow_zip_snd
                        (parameters :=
                          programTypeAliasParameters application.declaration)
                        normalizedArgumentsBelow)
                      rawBodyBelow
                    exact aliasParts.2 normalizedArguments rawBody afterRaw
                      resolved remaining substitutionBelow normalizedSuccess
        | none =>
            simp only [applicationEq] at continued
            cases type with
            | «variable» metavariable
            | parameter metavariable
            | constructor metavariable
            | error =>
                have resultProperties := stateTExcept_pure_success continued
                rw [resultProperties.1]
                exact typeBelow
            | application function argument =>
                obtain ⟨normalizedFunction, middle, normalizedArgument,
                    functionSuccess, argumentSuccess, resultEq⟩ :=
                  stateTExcept_map₂_success continued
                rw [resultEq]
                have parts := (TypeSystem.Ty.variablesBelow_application_iff
                  next function argument).mp typeBelow
                exact (TypeSystem.Ty.variablesBelow_application_iff
                  next normalizedFunction normalizedArgument).mpr
                    ⟨typeInduction.1 _ _ _ parts.1 functionSuccess,
                      typeInduction.2 _ _ _ parts.2 argumentSuccess⟩
            | function parameter result =>
                obtain ⟨normalizedParameter, middle, normalizedResult,
                    parameterSuccess, resultSuccess, resultEq⟩ :=
                  stateTExcept_map₂_success continued
                rw [resultEq]
                have parts := (TypeSystem.Ty.variablesBelow_function_iff
                  next parameter result).mp typeBelow
                exact (TypeSystem.Ty.variablesBelow_function_iff
                  next normalizedParameter normalizedResult).mpr
                    ⟨typeInduction.1 _ _ _ parts.1 parameterSuccess,
                      typeInduction.2 _ _ _ parts.2 resultSuccess⟩
            | product left right =>
                obtain ⟨normalizedLeft, middle, normalizedRight,
                    leftSuccess, rightSuccess, resultEq⟩ :=
                  stateTExcept_map₂_success continued
                rw [resultEq]
                have parts := (TypeSystem.Ty.variablesBelow_product_iff
                  next left right).mp typeBelow
                exact (TypeSystem.Ty.variablesBelow_product_iff
                  next normalizedLeft normalizedRight).mpr
                    ⟨typeInduction.1 _ _ _ parts.1 leftSuccess,
                      typeInduction.2 _ _ _ parts.2 rightSuccess⟩
            | mapping key value =>
                obtain ⟨normalizedKey, middle, normalizedValue,
                    keySuccess, valueSuccess, resultEq⟩ :=
                  stateTExcept_map₂_success continued
                rw [resultEq]
                have parts := (TypeSystem.Ty.variablesBelow_mapping_iff
                  next key value).mp typeBelow
                exact (TypeSystem.Ty.variablesBelow_mapping_iff
                  next normalizedKey normalizedValue).mpr
                    ⟨typeInduction.1 _ _ _ parts.1 keySuccess,
                      typeInduction.2 _ _ _ parts.2 valueSuccess⟩
            | proxy inner =>
                obtain ⟨normalizedInner, innerSuccess, resultEq⟩ :=
                  stateTExcept_map_success continued
                rw [resultEq]
                simpa using typeInduction nodeBudget normalizedInner remaining
                  typeBelow innerSuccess
            | comptime inner =>
                obtain ⟨normalizedInner, innerSuccess, resultEq⟩ :=
                  stateTExcept_map_success continued
                rw [resultEq]
                simpa using typeInduction nodeBudget normalizedInner remaining
                  typeBelow innerSuccess
  · intro structuralFuel aliasDepth stack nodeBudget resolved remaining
      typesBelow success
    unfold normalizeProgramTypeAliasListFuel at success
    have resultProperties := stateTExcept_pure_success success
    rw [resultProperties.1]
    exact programTypesVariablesBelow_nil next
  · intro aliasDepth stack head tail nodeBudget resolved remaining
      typesBelow success
    unfold normalizeProgramTypeAliasListFuel at success
    change Except.error ProgramTypeResolutionError.nestingLimit =
      .ok (resolved, remaining) at success
    simp at success
  · intro structuralFuel aliasDepth stack type rest typeInduction restInduction
      nodeBudget resolved remaining typesBelow success
    rw [normalizeProgramTypeAliasListFuel] at success
    obtain ⟨normalizedHead, middle, normalizedTail, headSuccess,
        tailSuccess, resultEq⟩ := stateTExcept_map₂_success success
    rw [resultEq]
    exact programTypesVariablesBelow_cons
      (typeInduction _ _ _ (typesBelow type (by simp)) headSuccess)
      (restInduction _ _ _ (by
        intro candidate member
        exact typesBelow candidate (by simp [member])) tailSuccess)

private theorem normalizeProgramTypeAliasesFuel_variablesBelow
    (next : Nat) (environment : ProgramEnvironment) :
    ∀ structuralFuel aliasDepth stack type nodeBudget resolved remaining,
      type.VariablesBelow next →
      (normalizeProgramTypeAliasesFuel environment structuralFuel aliasDepth
          stack type).run nodeBudget = .ok (resolved, remaining) →
      resolved.VariablesBelow next :=
  (normalizeProgramTypeAliasesFuel_variablesBelow_mutual next environment).1

private theorem normalizeProgramTypeAliasListFuel_variablesBelow
    (next : Nat) (environment : ProgramEnvironment) :
    ∀ structuralFuel aliasDepth stack types nodeBudget resolved remaining,
      ProgramTypesVariablesBelow next types →
      (normalizeProgramTypeAliasListFuel environment structuralFuel aliasDepth
          stack types).run nodeBudget = .ok (resolved, remaining) →
      ProgramTypesVariablesBelow next resolved :=
  (normalizeProgramTypeAliasesFuel_variablesBelow_mutual next environment).2

private theorem runProgramTypeAliasNormalization_success
    {α : Type} {nodeBudget : Nat}
    {computation : ProgramTypeAliasNormalizationM α} {resolved : α}
    (success : runProgramTypeAliasNormalization nodeBudget computation =
      .ok resolved) :
    ∃ remaining, computation.run nodeBudget = .ok (resolved, remaining) := by
  unfold runProgramTypeAliasNormalization at success
  cases computationResult : computation.run nodeBudget with
  | error error =>
      simp [computationResult, bind, Except.bind] at success
  | ok pair =>
      rcases pair with ⟨value, remaining⟩
      simp [computationResult, bind, Except.bind, pure, Pure.pure,
        Except.pure] at success
      refine ⟨remaining, ?_⟩
      rw [← success]

/-- Successful resolution of one source type never manufactures a flexible
inference metavariable.  The arbitrary `next` bound makes this stronger than
mere closedness (`next = 0`) and suitable for later source-semantics bridges. -/
theorem resolveProgramTypeExprWithBudgets_success_variablesBelow
    (next : Nat) (environment : ProgramEnvironment) (scope : ProgramTypeScope)
    (structuralFuel aliasExpansionFuel : Nat) (source : Syntax.TypeExpr)
    {resolved : TypeSystem.Ty}
    (success : resolveProgramTypeExprWithBudgets environment scope
      structuralFuel aliasExpansionFuel source = .ok resolved) :
    resolved.VariablesBelow next := by
  unfold resolveProgramTypeExprWithBudgets at success
  cases validationResult : validateProgramTypeScope scope with
  | error error =>
      simp [validationResult, bind, Except.bind] at success
  | ok _unit =>
      cases rawResult :
          resolveProgramTypeExprFuel environment scope structuralFuel source with
      | error error =>
          simp [validationResult, rawResult, bind, Except.bind] at success
      | ok raw =>
          simp only [validationResult, rawResult, bind, Except.bind] at success
          obtain ⟨remaining, normalizedResult⟩ :=
            runProgramTypeAliasNormalization_success success
          exact normalizeProgramTypeAliasesFuel_variablesBelow next environment
            structuralFuel aliasExpansionFuel [] raw aliasExpansionFuel resolved
            remaining
            ((resolveProgramTypeFuel_variablesBelow next environment scope
              structuralFuel).1 source raw rawResult)
            normalizedResult

/-- Successful list resolution preserves the source-order list while proving
that every resolved element is free of flexible inference metavariables. -/
theorem resolveProgramTypeExprListWithBudgets_success_variablesBelow
    (next : Nat) (environment : ProgramEnvironment) (scope : ProgramTypeScope)
    (structuralFuel aliasExpansionFuel : Nat)
    (sources : List Syntax.TypeExpr) {resolved : List TypeSystem.Ty}
    (success : resolveProgramTypeExprListWithBudgets environment scope
      structuralFuel aliasExpansionFuel sources = .ok resolved) :
    ∀ type ∈ resolved, type.VariablesBelow next := by
  unfold resolveProgramTypeExprListWithBudgets at success
  cases validationResult : validateProgramTypeScope scope with
  | error error =>
      simp [validationResult, bind, Except.bind] at success
  | ok _unit =>
      cases rawResult :
          resolveProgramTypeExprListFuel environment scope structuralFuel sources with
      | error error =>
          simp [validationResult, rawResult, bind, Except.bind] at success
      | ok raw =>
          simp only [validationResult, rawResult, bind, Except.bind] at success
          obtain ⟨remaining, normalizedResult⟩ :=
            runProgramTypeAliasNormalization_success success
          exact normalizeProgramTypeAliasListFuel_variablesBelow next environment
            structuralFuel aliasExpansionFuel [] raw aliasExpansionFuel resolved
            remaining
            ((resolveProgramTypeFuel_variablesBelow next environment scope
              structuralFuel).2 sources raw rawResult)
            normalizedResult

/-- Alias-body resolution, including declaration-rooted cycle tracking and
transparent expansion, cannot introduce a flexible inference metavariable. -/
theorem resolveProgramTypeAliasBodyWithBudgets_success_variablesBelow
    (next : Nat) (environment : ProgramEnvironment)
    (declaration : ProgramDeclaration)
    (structuralFuel aliasExpansionFuel : Nat) (source : Syntax.TypeExpr)
    {resolved : TypeSystem.Ty}
    (success : resolveProgramTypeAliasBodyWithBudgets environment declaration
      structuralFuel aliasExpansionFuel source = .ok resolved) :
    resolved.VariablesBelow next := by
  unfold resolveProgramTypeAliasBodyWithBudgets at success
  let scope := ProgramTypeScope.ofDeclaration declaration
  cases validationResult : validateProgramTypeScope scope with
  | error error =>
      simp [scope, validationResult, bind, Except.bind] at success
  | ok _unit =>
      cases rawResult :
          resolveProgramTypeExprFuel environment scope structuralFuel source with
      | error error =>
          simp [scope, validationResult, rawResult, bind, Except.bind] at success
      | ok raw =>
          simp only [scope, validationResult, rawResult, bind, Except.bind] at success
          obtain ⟨remaining, normalizedResult⟩ :=
            runProgramTypeAliasNormalization_success success
          exact normalizeProgramTypeAliasesFuel_variablesBelow next environment
            structuralFuel aliasExpansionFuel [declaration.id] raw
            aliasExpansionFuel resolved remaining
            ((resolveProgramTypeFuel_variablesBelow next environment scope
              structuralFuel).1 source raw rawResult)
            normalizedResult

end Solcore.Frontend
