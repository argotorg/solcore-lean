import Solcore.Frontend.SourceInference.Expression

/-! Public expression, body, and whole-program source-checking entry points. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceInference

open TypeSystem

namespace Detail

def defaultNumericVariable (context : Context) (metavariable : TypeVarId)
    (state : State) : Except Error State := do
  let type := state.resolve (.variable metavariable)
  if type = .word then
    pure state
  else
    match type with
    | .variable _ => unify state type .word
    | _ =>
        match ← conventionalTrait? context ["FromLiteral", "Numeric"] with
        | some trait => pure (state.addRequirement {
            trait, subject := type, arguments := []
          })
        | none => throw (.nonNumericLiteral type)

def defaultNumerics (context : Context) :
    List TypeVarId → State → Except Error State
  | [], state => .ok state
  | metavariable :: rest, state => do
      let state ← defaultNumericVariable context metavariable state
      defaultNumerics context rest state

def finalize (context : Context) (type : Ty) (state : State) :
    Except Error Result := do
  let state ← defaultNumerics context state.numericVariables state
  let (predicates, evidence) ← solvePredicates context state state.requirements
  pure {
    type := state.resolve type
    substitution := state.inference.substitution
    predicates
    evidence
  }

end Detail

/-- Infer one canonical source expression from an optional local environment. -/
def inferExpression (context : Context) (expression : Syntax.Expr)
    (locals : TypeSystem.Environment := []) (fuel : Nat := 1024) :
    Except Error Result := do
  let (type, state) ← Detail.inferExprFuel fuel context expression none (.initial locals)
  Detail.finalize context type state

/-- Check one source expression against an expected semantic source type. -/
def checkExpression (context : Context) (expression : Syntax.Expr) (expected : Ty)
    (locals : TypeSystem.Environment := []) (fuel : Nat := 1024) :
    Except Error Result := do
  let (type, state) ← Detail.inferExprFuel fuel context expression (some expected)
    (.initial locals)
  Detail.finalize context type state

private def functionLocals (signature : ProgramFunctionSignature) :
    TypeSystem.Environment :=
  (signature.parameterNames.zip signature.parameterTypes).map fun parameter =>
    (parameter.1, Scheme.mono parameter.2)

private def functionDeclaration?
    (environment : ProgramEnvironment) (signature : ProgramFunctionSignature) :
    Option ProgramDeclaration :=
  environment.declaration? signature.id

/-- Check the parsed body owned by one resolved top-level function signature. -/
def checkFunctionBody (environment : ProgramEnvironment)
    (signatures : ProgramSignatures) (signature : ProgramFunctionSignature)
    (fuel : Nat := 1024) : Except Error CheckedFunction := do
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
  let state := State.initial (functionLocals signature)
  let body ← Detail.inferStatementsFuel fuel context signature.source.value.body.value
    expected state
  let state ← Detail.unify body.state body.type expected
  let result ← Detail.finalize context expected state
  pure {
    declaration := signature.id
    type := signature.scheme.body
    inferredBodyType := result.type
    substitution := result.substitution
    predicates := result.predicates
    evidence := result.evidence
  }

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

/-- Check every top-level source function, accumulating independent failures. -/
def checkFunctionBodies (environment : ProgramEnvironment)
    (signatures : ProgramSignatures) (fuel : Nat := 1024) :
    Except (List FunctionError) (List CheckedFunction) :=
  let (checked, errors) := checkFunctionBodiesAux environment signatures fuel
    signatures.functions [] []
  if errors.isEmpty then .ok checked else .error errors

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
