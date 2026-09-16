import Solcore.Frontend.SourceInference.Resolution

/-! Fuel-bounded inference for canonical expressions and simple bodies. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceInference.Detail

open TypeSystem

structure StatementResult where
  type : Ty
  hasValue : Bool
  sawReturn : Bool
  state : State

structure BlockResult where
  type : Ty
  sawReturn : Bool
  state : State

def bindLambdaParameters (context : Context) :
    List Syntax.LambdaParameter → Nat → List String → State →
      Except Error (List Ty × State)
  | [], _, _, state => .ok ([], state)
  | parameter :: rest, index, seen, state => do
      let (name, type, state) ← match parameter.value with
        | .error => throw (.malformedLambdaParameter index)
        | .inferred name =>
            let (type, state) := state.fresh
            pure (name.value, type, state)
        | .typed _ name sourceType =>
            pure (name.value, (← resolveSourceType context sourceType), state)
      if seen.contains name then
        throw (.duplicateLambdaParameter name)
      else
        let state := { state with locals := (name, .mono type) :: state.locals }
        let (types, state) ← bindLambdaParameters context rest (index + 1)
          (name :: seen) state
        pure (type :: types, state)

def typeDependsOnNumeric (state : State) (type : Ty) : Bool :=
  type.freeVariables.any fun metavariable =>
    isNumericVariable state (.variable metavariable)

def generalizeValue (state : State) (locals : TypeSystem.Environment)
    (type : Ty) : Scheme :=
  let requirementVariables := state.requirements.flatMap fun predicate =>
    TypedTraitResolution.predicateVariables (applyPredicate state predicate)
  let blockedVariables := locals.freeVariables ++ requirementVariables
  {
    quantified := type.freeVariables.filter fun metavariable =>
      !(blockedVariables.contains metavariable)
    body := type
  }

mutual

  def inferExprFuel (fuel : Nat) (context : Context)
      (expression : Syntax.Expr) (expected : Option Ty) (state : State) :
      Except Error (Ty × State) :=
    match fuel with
    | 0 => .error .nestingLimit
    | fuel + 1 =>
      match expression.value with
      | .literal literal =>
          match literal.value with
          | .decimal _ | .hexadecimal _ => do
              let (type, state) := state.fresh
              let metavariable := match type with
                | .variable metavariable => metavariable
                | _ => ⟨state.inference.next⟩
              let state := {
                state with numericVariables := state.numericVariables ++ [metavariable]
              }
              withExpected context state type expected
          | .string _ => .error (.unsupportedLiteral "string")
      | .identifier name =>
          match state.locals.lookup? name.value with
          | some scheme =>
              let (type, inference) := state.inference.instantiate scheme
              withExpected context { state with inference } type expected
          | none =>
              if name.value == "true" || name.value == "false" then
                withExpected context state .bool expected
              else
                match functionsNamed context name.value with
                | [] => .error (.unknownVariable name.value)
                | [signature] =>
                    let instantiated := signature.scheme.instantiate state.inference.next
                    let inference := { state.inference with next := instantiated.next }
                    let state := { state with inference }
                      |>.addRequirements instantiated.predicates
                    withExpected context state instantiated.body expected
                | candidates =>
                    .error (.ambiguousOverload name.value (candidates.map (·.id)))
      | .group inner => inferExprFuel fuel context inner expected state
      | .tuple elements => do
          let (types, state) ← inferExprsFuel fuel context elements.elements state
          withExpected context state (Ty.productMany types) expected
      | .unary operator operand => do
          let (operandType, state) ← inferExprFuel fuel context operand none state
          let (type, state) ← inferUnaryOperator context operator.value operandType state
          withExpected context state type expected
      | .binary left operator right => do
          let (leftType, state) ← inferExprFuel fuel context left none state
          let (rightType, state) ← inferExprFuel fuel context right none state
          let (type, state) ← inferBinaryOperator context operator.value
            leftType rightType state
          withExpected context state type expected
      | .conditional condition _ thenBranch _ elseBranch => do
          let (_, state) ← inferExprFuel fuel context condition (some .bool) state
          let (thenType, state) ← inferExprFuel fuel context thenBranch expected state
          let (elseType, state) ← inferExprFuel fuel context elseBranch expected state
          let state ← unify state thenType elseType
          withExpected context state (state.resolve thenType) expected
      | .lambda _ parameters returnType body => do
          let outerLocals := state.locals
          let (parameterTypes, state) ← bindLambdaParameters context
            parameters.elements 0 [] state
          let parameterType := Ty.productMany parameterTypes
          let expectedParts := expected.bind fun type => functionParts? (state.resolve type)
          let state ← match expectedParts with
            | some (expectedParameter, _) => unify state parameterType expectedParameter
            | none => pure state
          let (resultType, state) ← match returnType with
            | some sourceType => pure ((← resolveSourceType context sourceType), state)
            | none =>
                match expectedParts with
                | some (_, result) => pure (result, state)
                | none => pure state.fresh
          let bodyResult ← inferStatementsFuel fuel context body.value resultType state
          let state ← unify bodyResult.state bodyResult.type resultType
          let state := state.withLocals outerLocals
          withExpected context state (.function (state.resolve parameterType)
            (state.resolve resultType)) expected
      | .call callee arguments => do
          let (argumentTypes, state) ← inferExprsFuel fuel context
            arguments.elements state
          let argumentType := Ty.productMany argumentTypes
          match calleeIdentifier? callee with
          | some name =>
              match state.locals.lookup? name with
              | none => selectFunctionCandidate context name argumentType expected state
              | some _ =>
                  let (calleeType, state) ← inferExprFuel fuel context callee none state
                  applyFunctionType context calleeType argumentType expected state
          | none =>
              let (calleeType, state) ← inferExprFuel fuel context callee none state
              applyFunctionType context calleeType argumentType expected state
      | .dotConstructor .. => .error (.unsupportedExpression "dot constructor")
      | .proxy .. => .error (.unsupportedExpression "proxy value")
      | .index .. => .error (.unsupportedExpression "index")
      | .field .. => .error (.unsupportedExpression "field")
      | .array .. => .error (.unsupportedExpression "array")
      | .error => .error (.unsupportedExpression "parser recovery")

  def inferExprsFuel (fuel : Nat) (context : Context) :
      List Syntax.Expr → State → Except Error (List Ty × State)
    | expressions, state =>
      match fuel with
      | 0 => .error .nestingLimit
      | fuel + 1 =>
        match expressions with
        | [] => .ok ([], state)
        | expression :: rest => do
            let (type, state) ← inferExprFuel fuel context expression none state
            let (types, state) ← inferExprsFuel fuel context rest state
            pure (type :: types, state)

  def inferStatementFuel (fuel : Nat) (context : Context)
      (statement : Syntax.Statement) (expectedReturn : Ty) (state : State) :
      Except Error StatementResult :=
    match fuel with
    | 0 => .error .nestingLimit
    | fuel + 1 =>
      match statement.value with
      | .letDecl name sourceType initializer => do
          let (valueType, state) ← match sourceType, initializer with
            | none, none => throw (.missingInitializer name.value)
            | some sourceType, none => pure ((← resolveSourceType context sourceType), state)
            | none, some initializer => inferExprFuel fuel context initializer none state
            | some sourceType, some initializer => do
                let type ← resolveSourceType context sourceType
                inferExprFuel fuel context initializer (some type) state
          let locals := state.locals.apply state.inference.substitution
          let valueType := state.resolve valueType
          let scheme := if typeDependsOnNumeric state valueType then
              Scheme.mono valueType
            else
              generalizeValue state locals valueType
          pure {
            type := .unit
            hasValue := false
            sawReturn := false
            state := { state with locals := (name.value, scheme) :: locals }
          }
      | .returnStmt value => do
          let state ← match value with
            | none => unify state .unit expectedReturn
            | some value => pure (← inferExprFuel fuel context value
                (some expectedReturn) state).2
          pure {
            type := state.resolve expectedReturn
            hasValue := true
            sawReturn := true
            state
          }
      | .expression expression trailingSemicolon => do
          let (type, state) ← inferExprFuel fuel context expression none state
          pure {
            type := if trailingSemicolon then .unit else type
            hasValue := !trailingSemicolon
            sawReturn := false
            state
          }
      | .ifThen condition thenBody elseBody => do
          let (_, state) ← inferExprFuel fuel context condition (some .bool) state
          let outerLocals := state.locals
          let thenResult ← inferStatementsFuel fuel context thenBody.value
            expectedReturn state
          let afterThen := thenResult.state.withLocals outerLocals
          match elseBody with
          | none => pure {
              type := .unit
              hasValue := false
              sawReturn := false
              state := afterThen
            }
          | some elseBody => do
              let elseResult ← inferStatementsFuel fuel context elseBody.value
                expectedReturn afterThen
              pure {
                type := if thenResult.sawReturn && elseResult.sawReturn then
                    elseResult.state.resolve expectedReturn
                  else
                    .unit
                hasValue := thenResult.sawReturn && elseResult.sawReturn
                sawReturn := thenResult.sawReturn && elseResult.sawReturn
                state := elseResult.state.withLocals outerLocals
              }
      | .block body => do
          let outerLocals := state.locals
          let result ← inferStatementsFuel fuel context body expectedReturn state
          pure {
            type := result.type
            hasValue := result.sawReturn
            sawReturn := result.sawReturn
            state := result.state.withLocals outerLocals
          }
      | .assignValue .. => .error (.unsupportedStatement "assignment")
      | .assignBitNot .. => .error (.unsupportedStatement "bit-not assignment")
      | .matchWith .. => .error (.unsupportedStatement "match")
      | .forLoop .. => .error (.unsupportedStatement "for loop")
      | .whileLoop .. => .error (.unsupportedStatement "while loop")
      | .assembly .. => .error (.unsupportedStatement "assembly")
      | .breakStmt => .error (.unsupportedStatement "break")
      | .continueStmt => .error (.unsupportedStatement "continue")
      | .error => .error (.unsupportedStatement "parser recovery")

  def inferStatementsFuel (fuel : Nat) (context : Context) :
      List Syntax.Statement → Ty → State → Except Error BlockResult
    | statements, expectedReturn, state =>
      match fuel with
      | 0 => .error .nestingLimit
      | fuel + 1 =>
        match statements with
        | [] => .ok { type := .unit, sawReturn := false, state }
        | statement :: rest => do
            let head ← inferStatementFuel fuel context statement expectedReturn state
            match rest with
            | [] => pure {
                type := if head.sawReturn || head.hasValue then head.type else .unit
                sawReturn := head.sawReturn
                state := head.state
              }
            | _ => do
                let tail ← inferStatementsFuel fuel context rest expectedReturn head.state
                pure {
                  type := if tail.sawReturn then tail.type
                    else if head.sawReturn then head.type
                    else tail.type
                  sawReturn := head.sawReturn || tail.sawReturn
                  state := tail.state
                }

end

end Solcore.Frontend.SourceInference.Detail
