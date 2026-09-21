import Solcore.Frontend.SourceInference.Resolution
import Solcore.Frontend.WordLiteral

/-! Fuel-bounded inference for canonical expressions and simple bodies. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceInference.Detail

open TypeSystem

structure StatementResult where
  id : StatementId
  type : Ty
  hasValue : Bool
  sawReturn : Bool
  state : State

structure BlockResult where
  statements : List StatementId
  type : Ty
  sawReturn : Bool
  state : State

def bindLambdaParameters (context : Context) :
    List Syntax.LambdaParameter → Nat → List String → State →
      Except Error (List TypedBinder × List Ty × State)
  | [], _, _, state => .ok ([], [], state)
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
        let (binder, state) :=
          state.allocateBinder name (.mono type) (some parameter.span)
        let (binders, types, state) ← bindLambdaParameters context rest
          (index + 1) (name :: seen) state
        pure (binder :: binders, type :: types, state)

/-- Keep every literal created in the current argument subtree, plus an older
literal whose still-flexible target flows through an argument type.  The
second case covers monomorphic let-bound literals without making unrelated
earlier literals affect overload ranking. -/
def relevantIntegerLiterals (state : State) (start : Nat)
    (arguments : List InferredExpression) : List IntegerLiteralOrigin :=
  let introduced := state.integerLiterals.drop start
  state.integerLiterals.filter fun origin =>
    introduced.contains origin ||
      (state.resolve (.variable origin.metavariable)).freeVariables.any
        fun metavariable => arguments.any fun argument =>
          (state.resolve argument.type).freeVariables.contains metavariable

def generalizeValue (state : State) (locals : TypeSystem.Environment)
    (type : Ty) : Scheme :=
  let requirementVariables := state.requirements.flatMap fun requirement =>
    TypedTraitResolution.predicateVariables
      (applyPredicate state requirement.predicate)
  let blockedVariables := locals.freeVariables ++ requirementVariables
  {
    quantified := type.freeVariables.filter fun metavariable =>
      !(blockedVariables.contains metavariable)
    body := type
  }

def coercionRequirements (coercions : List CoercionStep) :
    List RequirementId :=
  coercions.flatMap (·.requirements)

def attachExpressionCoercions (state : State)
    (entries : List ExpressionCoercions) : State :=
  entries.foldl (fun state entry =>
    state.modifyExpressionNode entry.expression fun node => {
      node with
      type := entry.coercions.foldl (fun _ step => step.target) node.type
      requirements := node.requirements ++ coercionRequirements entry.coercions
      coercions := node.coercions ++ entry.coercions
    }) state

def recordExpression (source : Syntax.Expr) (expression : InferredExpression)
    (form : ExpressionForm) (requirements : List RequirementId)
    (coercions : List CoercionStep) (state : State) :
    InferredExpression × State :=
  let node : ExpressionNode := {
    id := expression.id
    span := source.span
    type := expression.type
    form
    requirements
    coercions
  }
  (expression, state.recordNode (.expression node))

def recordExpressionWithExpected (context : Context) (source : Syntax.Expr)
    (id : ExpressionId) (type : Ty) (form : ExpressionForm)
    (requirements : List RequirementId) (expected : Option Ty) (state : State) :
    Except Error (InferredExpression × State) := do
  let fitted ← withExpected context state { id, type } expected
  pure <| recordExpression source fitted.expression form
    (requirements ++ coercionRequirements fitted.coercions)
    fitted.coercions fitted.state

def recordSelectedCallResult (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult)
    (result : InferredExpression) (trailingCoercions : List CoercionStep)
    (state : State) :
    InferredExpression × State :=
  let state := attachExpressionCoercions state attempt.argumentCoercions
  let (calleeId, state) := state.allocateExpressionId
  let calleeExpression : InferredExpression := {
    id := calleeId
    type := state.resolve attempt.instantiation.type
  }
  let (_, state) := recordExpression callee calleeExpression
    (.reference name (.declaration attempt.instantiation)) [] [] state
  recordExpression source result
    (.call calleeId (arguments.map (·.id))
      (.declaration attempt.instantiation))
    (coercionRequirements attempt.callCoercions ++
      attempt.signatureRequirements ++
      coercionRequirements trailingCoercions)
    (attempt.callCoercions ++ trailingCoercions) state

def recordSelectedCall (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult) :
    InferredExpression × State :=
  recordSelectedCallResult source callee name arguments attempt
    attempt.result [] attempt.state

def recordIndirectCall (source : Syntax.Expr) (callee : InferredExpression)
    (arguments : List InferredExpression) (result : IndirectApplicationResult) :
    InferredExpression × State :=
  let argumentType := Ty.productMany (arguments.map (·.type))
  let coercedArgumentType := result.argumentCoercions.foldl
    (fun _ step => step.target) argumentType
  recordExpression source result.result
    (.call callee.id (arguments.map (·.id)) (.indirect {
      argumentTypeBeforeCoercion := argumentType
      argumentTypeAfterCoercion := coercedArgumentType
      argumentCoercions := result.argumentCoercions
    }))
    (coercionRequirements result.argumentCoercions ++
      coercionRequirements result.callCoercions)
    result.callCoercions result.state

mutual

  def inferExprFuel (fuel : Nat) (context : Context)
      (expression : Syntax.Expr) (expected : Option Ty) (state : State) :
      Except Error (InferredExpression × State) :=
    match fuel with
    | 0 => .error .nestingLimit
    | fuel + 1 =>
      let (id, state) := state.allocateExpressionId
      match expression.value with
      | .literal literal =>
          match literal.value with
          | value@(.decimal _) | value@(.hexadecimal _) => do
              let rawValue ← match numericLiteralValue? value with
                | some rawValue => pure rawValue
                | none => throw (.unsupportedLiteral "malformed integer")
              let (type, state) := state.fresh
              let .variable metavariable := type
                | throw (.unsupportedLiteral "integer target allocation")
              let (requirement, state) := state.addRequirementWithId
                (ProgramSignatures.builtinIntPredicate type)
              let state := {
                state with integerLiterals := state.integerLiterals ++ [{
                  metavariable
                  expression := id
                  requirement
                }]
              }
              recordExpressionWithExpected context expression id type
                (.integerLiteral value {
                  rawValue
                  targetType := type
                  requirement
                }) [requirement] expected state
          | .string _ => .error (.unsupportedLiteral "string")
      | .identifier name =>
          match state.lookupBinder? name.value with
          | some binder =>
              let (type, inference) := state.inference.instantiate binder.scheme
              recordExpressionWithExpected context expression id type
                (.reference name.value (.local binder.id)) [] expected
                { state with inference }
          | none =>
              if name.value == "true" || name.value == "false" then
                recordExpressionWithExpected context expression id .bool
                  (.reference name.value
                    (.builtinBoolean (name.value == "true"))) [] expected state
              else do
                match ← functionsNamed context name.value with
                | [] => .error (.unknownVariable name.value)
                | [signature] =>
                    let instantiated :=
                      signature.scheme.instantiate state.inference.next
                    let inference := {
                      state.inference with next := instantiated.next
                    }
                    let (requirements, state) :=
                      ({ state with inference }).addRequirementsWithIds
                        instantiated.predicates
                    recordExpressionWithExpected context expression id
                      instantiated.body
                      (.reference name.value (.declaration
                        (DeclarationInstantiation.ofInstantiated
                          signature.id instantiated)))
                      requirements expected state
                | candidates =>
                    .error (.ambiguousOverload name.value (candidates.map (·.id)))
      | .group inner => do
          let (inner, state) ← inferExprFuel fuel context inner expected state
          recordExpressionWithExpected context expression id inner.type
            (.group inner.id) [] expected state
      | .tuple elements => do
          let (elements, state) ← inferExprsFuel fuel context
            elements.elements state
          recordExpressionWithExpected context expression id
            (Ty.productMany (elements.map (·.type)))
            (.tuple (elements.map (·.id))) [] expected state
      | .unary operator operand => do
          let integerLiteralStart := state.integerLiterals.length
          let (operand, state) ← inferExprFuel fuel context operand none state
          let integerLiterals :=
            relevantIntegerLiterals state integerLiteralStart [operand]
          match unaryOperatorDispatch operator.value with
          | .function name =>
              match ← functionsNamed context name with
              | [] =>
                  let inferred ← inferUnaryOperator context operator.value
                    operand.type expected state
                  recordExpressionWithExpected context expression id
                    inferred.type (.unary operator.value operand.id)
                    inferred.requirements expected inferred.state
              | candidates =>
                  let attempt ← selectFunctionCandidateFrom context name
                    candidates [operand] integerLiterals id expected state
                  let callee : Syntax.Expr := {
                    span := operator.span
                    value := .identifier { span := operator.span, value := name }
                  }
                  pure <| recordSelectedCall expression callee name
                    [operand] attempt
          | .traitMethod _ _ =>
              let inferred ← inferUnaryOperator context operator.value
                operand.type expected state
              recordExpressionWithExpected context expression id inferred.type
                (.unary operator.value operand.id) inferred.requirements expected
                inferred.state
      | .binary left operator right => do
          let integerLiteralStart := state.integerLiterals.length
          let (left, state) ← inferExprFuel fuel context left none state
          let (right, state) ← inferExprFuel fuel context right none state
          let integerLiterals :=
            relevantIntegerLiterals state integerLiteralStart [left, right]
          match binaryOperatorDispatch operator.value with
          | .function name =>
              match ← functionsNamed context name with
              | [] =>
                  let inferred ← inferBinaryOperator context operator.value
                    left.type right.type expected state
                  recordExpressionWithExpected context expression id inferred.type
                    (.binary left.id operator.value right.id)
                    inferred.requirements expected inferred.state
              | candidates =>
                  let attempt ← selectFunctionCandidateFrom context name
                    candidates [left, right] integerLiterals id (some .bool)
                      state
                  let fitted ← withExpected context attempt.state
                    attempt.result expected
                  let callee : Syntax.Expr := {
                    span := operator.span
                    value := .identifier { span := operator.span, value := name }
                  }
                  pure <| recordSelectedCallResult expression callee name
                    [left, right] attempt fitted.expression fitted.coercions
                    fitted.state
          | .traitMethod _ _ =>
              let inferred ← inferBinaryOperator context operator.value
                left.type right.type expected state
              recordExpressionWithExpected context expression id inferred.type
                (.binary left.id operator.value right.id) inferred.requirements
                expected inferred.state
      | .conditional condition _ thenBranch _ elseBranch => do
          let (condition, state) ← inferExprFuel fuel context condition
            (some .bool) state
          let (thenBranch, state) ← inferExprFuel fuel context thenBranch
            expected state
          let (elseBranch, state) ← inferExprFuel fuel context elseBranch
            expected state
          let state ← unify state thenBranch.type elseBranch.type
          recordExpressionWithExpected context expression id
            (state.resolve thenBranch.type)
            (.conditional condition.id thenBranch.id elseBranch.id) []
            expected state
      | .lambda _ parameters returnType body => do
          let outerScope := state.lexicalScope
          let (parameters, parameterTypes, state) ← bindLambdaParameters context
            parameters.elements 0 [] state
          let parameterType := Ty.productMany parameterTypes
          let expectedParts := expected.bind fun type =>
            functionParts? (state.resolve type)
          let state ← match expectedParts with
            | some (expectedParameter, _) =>
                unify state parameterType expectedParameter
            | none => pure state
          let (resultType, state) ← match returnType with
            | some sourceType =>
                pure ((← resolveSourceType context sourceType), state)
            | none =>
                match expectedParts with
                | some (_, result) => pure (result, state)
                | none => pure state.fresh
          let bodyResult ← inferStatementsFuel fuel context body.value
            resultType state
          let state ← unify bodyResult.state bodyResult.type resultType
          let state := state.restoreLexicalScope outerScope
          recordExpressionWithExpected context expression id
            (.function (state.resolve parameterType) (state.resolve resultType))
            (.lambda parameters (state.resolve resultType)
              bodyResult.statements) [] expected state
      | .call callee arguments => do
          let integerLiteralStart := state.integerLiterals.length
          let (arguments, state) ← inferExprsFuel fuel context
            arguments.elements state
          let integerLiterals :=
            relevantIntegerLiterals state integerLiteralStart arguments
          match calleeQualifiedIdentifier? callee with
          | some (namespacePath, name) =>
              let namespaceName := namespacePath.head!
              match state.lookupBinder? namespaceName with
              | some _ =>
                  let (calleeResult, state) ←
                    inferExprFuel fuel context callee none state
                  let result ← applyFunctionType context id calleeResult.type
                    arguments expected state
                  pure <| recordIndirectCall expression calleeResult
                    arguments result
              | none =>
                  match ← qualifiedFunctionsNamed context namespacePath name with
                  | some candidates =>
                      let displayName :=
                        String.intercalate "." (namespacePath ++ [name])
                      let attempt ← selectFunctionCandidateFrom context
                        displayName candidates arguments integerLiterals id
                        expected state
                      pure <| recordSelectedCall expression callee displayName
                        arguments attempt
                  | none =>
                      let (calleeResult, state) ←
                        inferExprFuel fuel context callee none state
                      let result ← applyFunctionType context id calleeResult.type
                        arguments expected state
                      pure <| recordIndirectCall expression calleeResult
                        arguments result
          | none =>
              match calleeIdentifier? callee with
              | some name =>
                  match state.lookupBinder? name with
                  | none =>
                      let attempt ← selectFunctionCandidate context name arguments
                        integerLiterals id expected state
                      pure <| recordSelectedCall expression callee name arguments
                        attempt
                  | some _ =>
                      let (calleeResult, state) ←
                        inferExprFuel fuel context callee none state
                      let result ← applyFunctionType context id calleeResult.type
                        arguments expected state
                      pure <| recordIndirectCall expression calleeResult
                        arguments result
              | none =>
                  let (calleeResult, state) ←
                    inferExprFuel fuel context callee none state
                  let result ← applyFunctionType context id calleeResult.type
                    arguments expected state
                  pure <| recordIndirectCall expression calleeResult arguments result
      | .dotConstructor .. => .error (.unsupportedExpression "dot constructor")
      | .proxy _ sourceType => do
          let inner ← resolveSourceType context sourceType
          recordExpressionWithExpected context expression id (.proxy inner)
            (.proxy inner) [] expected state
      | .index base _ index => do
          let (base, state) ← inferExprFuel fuel context base none state
          let (keyType, state) := state.fresh
          let (valueType, state) := state.fresh
          let state ← unify state base.type (.mapping keyType valueType)
          let (index, state) ← inferExprFuel fuel context index
            (some (state.resolve keyType)) state
          recordExpressionWithExpected context expression id
            (state.resolve valueType) (.index base.id index.id) [] expected state
      | .field .. => .error (.unsupportedExpression "field")
      | .array .. => .error (.unsupportedExpression "array")
      | .error => .error (.unsupportedExpression "parser recovery")

  def inferExprsFuel (fuel : Nat) (context : Context) :
      List Syntax.Expr → State →
        Except Error (List InferredExpression × State)
    | expressions, state =>
      match fuel with
      | 0 => .error .nestingLimit
      | fuel + 1 =>
        match expressions with
        | [] => .ok ([], state)
        | expression :: rest => do
            let (expression, state) ←
              inferExprFuel fuel context expression none state
            let (expressions, state) ←
              inferExprsFuel fuel context rest state
            pure (expression :: expressions, state)

  def inferStatementFuel (fuel : Nat) (context : Context)
      (statement : Syntax.Statement) (expectedReturn : Ty) (state : State) :
      Except Error StatementResult :=
    match fuel with
    | 0 => .error .nestingLimit
    | fuel + 1 =>
      let (id, state) := state.allocateStatementId
      match statement.value with
      | .letDecl name sourceType initializer => do
          let (valueType, initializerId, state) ←
            match sourceType, initializer with
            | none, none => throw (.missingInitializer name.value)
            | some sourceType, none =>
                pure ((← resolveSourceType context sourceType), none, state)
            | none, some initializer => do
                let (initializer, state) ←
                  inferExprFuel fuel context initializer none state
                pure (initializer.type, some initializer.id, state)
            | some sourceType, some initializer => do
                let type ← resolveSourceType context sourceType
                let (initializer, state) ← inferExprFuel fuel context initializer
                  (some type) state
                pure (initializer.type, some initializer.id, state)
          let locals := state.locals.apply state.inference.substitution
          let valueType := state.resolve valueType
          let scheme := generalizeValue state locals valueType
          let (binder, state) := ({ state with locals }).allocateBinder
            name.value scheme (some name.span)
          let state := state.recordNode (.statement {
            id
            span := statement.span
            type := .unit
            form := .letDecl binder initializerId
          })
          pure {
            id
            type := .unit
            hasValue := false
            sawReturn := false
            state
          }
      | .returnStmt value => do
          let (valueId, state) ← match value with
            | none => pure (none, ← unify state .unit expectedReturn)
            | some value => do
                let (value, state) ← inferExprFuel fuel context value
                  (some expectedReturn) state
                pure (some value.id, state)
          let type := state.resolve expectedReturn
          let state := state.recordNode (.statement {
            id
            span := statement.span
            type
            form := .returnStmt valueId
          })
          pure {
            id
            type
            hasValue := true
            sawReturn := true
            state
          }
      | .expression expression trailingSemicolon => do
          let (expression, state) ←
            inferExprFuel fuel context expression none state
          let type := if trailingSemicolon then .unit else expression.type
          let state := state.recordNode (.statement {
            id
            span := statement.span
            type
            form := .expression expression.id trailingSemicolon
          })
          pure {
            id
            type
            hasValue := !trailingSemicolon
            sawReturn := false
            state
          }
      | .ifThen condition thenBody elseBody => do
          let (condition, state) ← inferExprFuel fuel context condition
            (some .bool) state
          let outerScope := state.lexicalScope
          let thenResult ← inferStatementsFuel fuel context thenBody.value
            expectedReturn state
          let afterThen := thenResult.state.restoreLexicalScope outerScope
          match elseBody with
          | none =>
              let type := Ty.unit
              let state := afterThen.recordNode (.statement {
                id
                span := statement.span
                type
                form := .ifThen condition.id thenResult.statements none
              })
              pure {
                id
                type
                hasValue := false
                sawReturn := false
                state
              }
          | some elseBody => do
              let elseResult ← inferStatementsFuel fuel context elseBody.value
                expectedReturn afterThen
              let type := if thenResult.sawReturn && elseResult.sawReturn then
                  elseResult.state.resolve expectedReturn
                else
                  .unit
              let hasValue := thenResult.sawReturn && elseResult.sawReturn
              let state := elseResult.state.restoreLexicalScope outerScope
                |>.recordNode (.statement {
                  id
                  span := statement.span
                  type
                  form := .ifThen condition.id thenResult.statements
                    (some elseResult.statements)
                })
              pure {
                id
                type
                hasValue
                sawReturn := hasValue
                state
              }
      | .block body => do
          let outerScope := state.lexicalScope
          let result ← inferStatementsFuel fuel context body expectedReturn state
          let state := result.state.restoreLexicalScope outerScope
            |>.recordNode (.statement {
              id
              span := statement.span
              type := result.type
              form := .block result.statements
            })
          pure {
            id
            type := result.type
            hasValue := result.sawReturn
            sawReturn := result.sawReturn
            state
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
        | [] => .ok {
            statements := []
            type := .unit
            sawReturn := false
            state
          }
        | statement :: rest => do
            let head ← inferStatementFuel fuel context statement
              expectedReturn state
            match rest with
            | [] => pure {
                statements := [head.id]
                type := if head.sawReturn || head.hasValue then head.type
                  else .unit
                sawReturn := head.sawReturn
                state := head.state
              }
            | _ => do
                let tail ← inferStatementsFuel fuel context rest
                  expectedReturn head.state
                pure {
                  statements := head.id :: tail.statements
                  type := if tail.sawReturn then tail.type
                    else if head.sawReturn then head.type
                    else tail.type
                  sawReturn := head.sawReturn || tail.sawReturn
                  state := tail.state
                }

end

end Solcore.Frontend.SourceInference.Detail
