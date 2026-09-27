import Solcore.Frontend.SourceInference.Expression

/-! Public expression, body, and whole-program source-checking entry points. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceInference

open TypeSystem

namespace Detail

def defaultIntegerPatternTarget (state : State)
    (origin : IntegerPatternOrigin) : Except Error State :=
  match state.resolve (.variable origin.metavariable) with
  | .variable _ => unify state (.variable origin.metavariable) .word
  | _ => pure state

def defaultIntegerPatternTargets :
    List IntegerPatternOrigin → State → Except Error State
  | [], state => .ok state
  | origin :: rest, state => do
      let state ← defaultIntegerPatternTarget state origin
      defaultIntegerPatternTargets rest state

def defaultIntegerLiteralTarget (state : State)
    (origin : IntegerLiteralOrigin) : Except Error State :=
  match state.resolve (.variable origin.metavariable) with
  | .variable _ => unify state (.variable origin.metavariable) .word
  | _ => pure state

def defaultIntegerLiteralTargets :
    List IntegerLiteralOrigin → State → Except Error State
  | [], state => .ok state
  | origin :: rest, state => do
      let state ← defaultIntegerLiteralTarget state origin
      defaultIntegerLiteralTargets rest state

def validateIntegerLiteralTarget (origin : IntegerLiteralOrigin)
    (state : State) : Except Error Unit := do
  let type := state.resolve (.variable origin.metavariable)
  if type.freeVariables.isEmpty then pure ()
  else throw (.unresolvedIntegerLiteralTarget origin.expression type)

def validateIntegerLiteralTargets (state : State) :
    List IntegerLiteralOrigin → Except Error Unit
  | [] => .ok ()
  | origin :: rest => do
      validateIntegerLiteralTarget origin state
      validateIntegerLiteralTargets state rest

def finalize (context : Context) (type : Ty) (state : State)
    (roots : List NodeId) :
    Except Error Result := do
  let state ← defaultIntegerPatternTargets state.integerPatterns state
  let state ← defaultIntegerLiteralTargets state.integerLiterals state
  validateIntegerLiteralTargets state state.integerLiterals
  let solvedRequirements ← solveRequirements context state state.requirements
  let substitution := state.inference.substitution
  pure {
    type := state.resolve type
    substitution
    solvedRequirements
    typedSource := (state.toTypedSource roots).applySubstitution substitution
  }

end Detail

/-- Infer one canonical source expression from an optional local environment. -/
def inferExpression (context : Context) (expression : Syntax.Expr)
    (locals : TypeSystem.Environment := []) (fuel : Nat := 1024) :
    Except Error Result := do
  let (expression, state) ← Detail.inferExprFuel fuel context expression none
    (.initial context.scope.genericOwner locals)
  Detail.finalize context expression.type state [.expression expression.id]

/-- Check one source expression against an expected semantic source type. -/
def checkExpression (context : Context) (expression : Syntax.Expr) (expected : Ty)
    (locals : TypeSystem.Environment := []) (fuel : Nat := 1024) :
    Except Error Result := do
  let (expression, state) ← Detail.inferExprFuel fuel context expression
    (some expected)
    (.initial context.scope.genericOwner locals)
  Detail.finalize context expression.type state [.expression expression.id]

private def functionLocals (signature : ProgramFunctionSignature) :
    TypeSystem.Environment :=
  (signature.parameterNames.zip signature.parameterTypes).map fun parameter =>
    (parameter.1, Scheme.mono parameter.2)

private def functionDeclaration?
    (environment : ProgramEnvironment) (signature : ProgramFunctionSignature) :
    Option ProgramDeclaration :=
  environment.declaration? signature.id

private def checkFunctionBodyResult (environment : ProgramEnvironment)
    (signatures : ProgramSignatures) (signature : ProgramFunctionSignature)
    (fuel : Nat) : Except Error Result := do
  let declaration ← match functionDeclaration? environment signature with
    | some declaration => pure declaration
    | none => throw (.malformedFunctionType signature.id)
  let context : Context := {
    environment
    signatures
    scope := .ofDeclaration declaration
    assumptions := signature.scheme.predicates
  }
  let expected := Ty.productMany signature.returnTypes
  let state := State.initial context.scope.genericOwner (functionLocals signature)
    signature.parameterComptime
  let body ← Detail.inferStatementsFuel fuel context signature.source.value.body.value
    expected state
  let state ← Detail.unify body.state body.type expected
  Detail.finalize context expected state
    (body.statements.map NodeId.statement)

private def checkedFunctionOfResult (signature : ProgramFunctionSignature)
    (result : Result) : CheckedFunction := {
    declaration := signature.id
    type := signature.scheme.body
    inferredBodyType := result.type
    returnComptime := signature.returnComptime
    substitution := result.substitution
    solvedRequirements := result.solvedRequirements
    typedBody := result.typedSource
  }

/-- Check the parsed body owned by one resolved top-level function signature. -/
def checkFunctionBody (environment : ProgramEnvironment)
    (signatures : ProgramSignatures) (signature : ProgramFunctionSignature)
    (fuel : Nat := 1024) : Except Error CheckedFunction := do
  let result ← checkFunctionBodyResult environment signatures signature fuel
  pure (checkedFunctionOfResult signature result)

/-- A successful body check retains the declaration identity of its input
signature. -/
theorem checkFunctionBody_success_declaration
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : CheckedFunction}
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked) :
    checked.declaration = signature.id := by
  unfold checkFunctionBody at success
  cases resultEq :
      checkFunctionBodyResult environment signatures signature fuel with
  | error error => simp [resultEq, bind, Except.bind] at success
  | ok result =>
      simp only [resultEq, bind, Except.bind] at success
      injection success with checkedEq
      subst checked
      rfl

private def checkFunctionBodiesAux (environment : ProgramEnvironment)
    (signatures : ProgramSignatures) (fuel : Nat) :
    List ProgramFunctionSignature → List CheckedFunction → List FunctionError →
      List CheckedFunction × List FunctionError
  | [], checked, errors => (checked, errors)
  | signature :: rest, checked, errors =>
      match checkFunctionBody environment signatures signature fuel with
      | .ok result =>
          checkFunctionBodiesAux environment signatures fuel rest
            (checked ++ [result]) errors
      | .error error =>
          checkFunctionBodiesAux environment signatures fuel rest checked
            (errors ++ [{ declaration := signature.id, error }])

private theorem checkFunctionBodiesAux_success_declaration_ids
    (environment : ProgramEnvironment)
    (signatures : ProgramSignatures)
    (fuel : Nat) :
    ∀ remaining checked errors finalChecked,
      checkFunctionBodiesAux environment signatures fuel remaining checked
          errors = (finalChecked, []) →
        errors = [] ∧
          finalChecked.map (fun function => function.declaration) =
            checked.map (fun function => function.declaration) ++
              remaining.map (fun signature => signature.id) := by
  intro remaining
  induction remaining with
  | nil =>
      intro checked errors finalChecked success
      have checkedEq := congrArg Prod.fst success
      have errorsEq := congrArg Prod.snd success
      simp only [checkFunctionBodiesAux] at checkedEq errorsEq
      subst finalChecked
      exact ⟨errorsEq, by simp⟩
  | cons signature rest induction =>
      intro checked errors finalChecked success
      cases bodyResult :
          checkFunctionBody environment signatures signature fuel with
      | error error =>
          have tail := induction checked
            (errors ++ [{ declaration := signature.id, error }]) finalChecked (by
              simpa [checkFunctionBodiesAux, bodyResult] using success)
          simp at tail
      | ok result =>
          have tail := induction (checked ++ [result]) errors finalChecked (by
            simpa [checkFunctionBodiesAux, bodyResult] using success)
          refine ⟨tail.1, ?_⟩
          have resultId := checkFunctionBody_success_declaration bodyResult
          simpa [List.map_append, resultId, List.append_assoc] using tail.2

/-- Check every top-level source function, accumulating independent failures. -/
def checkFunctionBodies (environment : ProgramEnvironment)
    (signatures : ProgramSignatures) (fuel : Nat := 1024) :
    Except (List FunctionError) (List CheckedFunction) :=
  let (checked, errors) := checkFunctionBodiesAux environment signatures fuel
    signatures.functions [] []
  if errors.isEmpty then .ok checked else .error errors

/-- Successful whole-catalog body checking retains every function declaration
identity exactly once and in signature-catalog order. -/
theorem checkFunctionBodies_success_declaration_ids
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {fuel : Nat}
    {functions : List CheckedFunction}
    (success : checkFunctionBodies environment signatures fuel =
      .ok functions) :
    functions.map (fun function => function.declaration) =
      signatures.functions.map (fun signature => signature.id) := by
  unfold checkFunctionBodies at success
  cases resultEq :
      checkFunctionBodiesAux environment signatures fuel signatures.functions
        [] [] with
  | mk checked errors =>
      rw [resultEq] at success
      change (if errors.isEmpty then Except.ok checked else Except.error errors) =
        Except.ok functions at success
      by_cases errorsEmpty : errors.isEmpty = true
      · simp only [errorsEmpty, if_true, Except.ok.injEq] at success
        have errorsEq : errors = [] := List.isEmpty_iff.mp errorsEmpty
        subst checked
        subst errors
        have ids :=
          (checkFunctionBodiesAux_success_declaration_ids environment signatures
            fuel signatures.functions [] [] functions resultEq).2
        simpa using ids
      · simp [errorsEmpty] at success

/-- Resolve signatures and check all bodies of an already loaded program. -/
def checkLoadedProgram (loaded : LoadedProgram) (fuel : Nat := 1024) :
    Except (List ProgramCheckError) (List CheckedFunction) :=
  match buildProgramSignatures loaded.environment with
  | .error errors => .error (errors.map ProgramCheckError.signatures)
  | .ok signatures =>
      match checkFunctionBodies loaded.environment signatures fuel with
      | .ok checked => .ok checked
      | .error errors => .error (errors.map ProgramCheckError.body)

/-- Validate, parse, catalog, resolve, and type-check one whole workspace. -/
def loadAndCheckProgram (raw : Workspace.RawWorkspace) (fuel : Nat := 1024) :
    Except (List ProgramCheckError) (List CheckedFunction) :=
  match loadProgram raw with
  | .error errors => .error (errors.map ProgramCheckError.loading)
  | .ok loaded => checkLoadedProgram loaded fuel

end Solcore.Frontend.SourceInference
