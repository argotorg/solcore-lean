import Solcore.Frontend.SourceInference.Types

/-! Operator, overload, and trait selection used by source inference. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceInference.Detail

open TypeSystem

def localFunctionsNamed (context : Context) (name : String) :
    List ProgramFunctionSignature :=
  context.signatures.functions.filter fun signature =>
    signature.name == name &&
      decide (signature.id.moduleId = context.scope.currentModule)

def signaturesForDeclarations (context : Context)
    (declarations : List ProgramDeclaration) : List ProgramFunctionSignature :=
  declarations.filterMap fun declaration =>
    context.signatures.functions.find? fun signature =>
      decide (signature.id = declaration.id)

def functionsNamed (context : Context) (name : String) :
    Except Error (List ProgramFunctionSignature) :=
  let localCandidates := localFunctionsNamed context name
  if !localCandidates.isEmpty then
    .ok localCandidates
  else
    match buildProgramImports context.environment context.scope.currentModule with
    | .error errors => .error (.importVisibility errors)
    | .ok visibility =>
        if visibility.hasImports then
          .ok (signaturesForDeclarations context (visibility.valuesNamed name))
        else
          .ok (context.signatures.functions.filter fun signature =>
            signature.name == name)

def qualifiedFunctionsNamed (context : Context)
    (namespacePath : List String) (name : String) :
    Except Error (Option (List ProgramFunctionSignature)) :=
  match buildProgramImports context.environment context.scope.currentModule with
  | .error errors => .error (.importVisibility errors)
  | .ok visibility =>
      if !visibility.hasNamespaceRoot namespacePath then
        .ok none
      else
        match visibility.namespacePathTargets namespacePath with
        | [] => .ok (some [])
        | [_] =>
            .ok (some (signaturesForDeclarations context
              (visibility.valuesInNamespacePathNamed namespacePath name)))
        | modules => .error (.ambiguousImportedNamespace
            (String.intercalate "." namespacePath) modules)

def traitCandidates (context : Context) (name : String) :
    Except Error (List ProgramDeclaration) :=
  match context.environment.localTraitsNamed context.scope.currentModule name with
  | localCandidates@(_ :: _) => .ok localCandidates
  | [] =>
      match buildProgramImports context.environment context.scope.currentModule with
      | .error errors => .error (.importVisibility errors)
      | .ok visibility =>
          if visibility.hasImports then
            .ok (visibility.traitsNamed name)
          else
            .ok (context.environment.traitsNamed name)

def conventionalTraitWithArity? (context : Context) (name : String)
    (arity : Nat) :
    Except Error (Option Resolved.DeclarationId) := do
  let candidates := (← traitCandidates context name).filter fun declaration =>
    declaration.genericParameters.length == arity
  match candidates with
  | [] => .ok none
  | [candidate] => .ok (some candidate.id)
  | _ => .error (.ambiguousOperatorTrait name (candidates.map (·.id)))

def operatorTrait? (context : Context) (name : String) :
    Except Error (Option Resolved.DeclarationId) :=
  conventionalTraitWithArity? context name 1

def conventionalTrait?
    (context : Context) : List String → Except Error (Option Resolved.DeclarationId)
  | [] => .ok none
  | name :: rest => do
      match ← operatorTrait? context name with
      | some trait => pure (some trait)
      | none => conventionalTrait? context rest

structure CoercionEdge where
  source : Ty
  target : Ty
  predicate : ProgramPredicate
  deriving Repr, DecidableEq

/-- One not-yet-committed edge selected by coercion search.  Requirement IDs
are allocated only after the whole path has been selected. -/
structure PlannedCoercionStep where
  source : Ty
  target : Ty
  predicate : ProgramPredicate
  deriving Repr, DecidableEq

structure CoercionPath where
  current : Ty
  visited : List Ty
  steps : List PlannedCoercionStep
  deriving Repr, DecidableEq

/-- Outgoing edges whose evidence is unique, plus inconclusive edges retained
only as a fallback diagnostic if every viable frontier is exhausted. -/
structure CoercionEdges where
  viable : List CoercionEdge := []
  blocked : List Error := []

structure CoercionExpansion where
  paths : List CoercionPath := []
  blocked : List Error := []

def typeHasParameter : Ty → Bool
  | .parameter _ => true
  | .variable _
  | .constructor _
  | .error => false
  | .application left right
  | .function left right
  | .product left right
  | .mapping left right => typeHasParameter left || typeHasParameter right
  | .proxy inner
  | .comptime inner => typeHasParameter inner

def isGroundCoercionTarget (type : Ty) : Bool :=
  type.freeVariables.isEmpty && !typeHasParameter type

def coercionRuleEdge? (trait : Resolved.DeclarationId) (source : Ty)
    (rule : ProgramImplRule) : Option CoercionEdge := do
  if rule.head.trait != trait then none else pure ()
  let freshened := TypedTraitResolution.freshenRuleFor rule {
    trait
    subject := source
    arguments := [source]
  }
  let freshTarget ← match freshened.head.arguments with
    | [target] => some target
    | _ => none
  let substitution ← (Unification.unify [{
    left := freshened.head.subject
    right := source
  }]).toOption
  if substitution.domain.any source.freeVariables.contains then none else pure ()
  let target := substitution.apply freshTarget
  if !isGroundCoercionTarget target then none else pure ()
  pure {
    source
    target
    predicate := { trait, subject := source, arguments := [target] }
  }

def assumptionCoercionEdges (context : Context) (state : State)
    (trait : Resolved.DeclarationId) (source : Ty) : List CoercionEdge :=
  context.assumptions.filterMap fun assumption =>
    let predicate := applyPredicate state assumption
    if predicate.trait != trait || predicate.subject != source then
      none
    else
      match predicate.arguments with
      | [target] =>
          if isGroundCoercionTarget target then some { source, target, predicate }
          else none
      | _ => none

def coercionEdges (context : Context) (state : State)
    (trait : Resolved.DeclarationId) (source : Ty) : List CoercionEdge :=
  ((context.signatures.implRules.filterMap (coercionRuleEdge? trait source)) ++
    assumptionCoercionEdges context state trait source).eraseDups

def viableCoercionEdges (context : Context) (state : State) :
    List CoercionEdge → CoercionEdges
  | [] => {}
  | edge :: rest =>
      let tail := viableCoercionEdges context state rest
      match solvePredicate context state edge.predicate with
      | .ok _ => { tail with viable := edge :: tail.viable }
      | .error (.noTraitImplementation _) => tail
      | .error error => { tail with blocked := error :: tail.blocked }

def expandCoercionPath (context : Context) (state : State)
    (trait : Resolved.DeclarationId) (path : CoercionPath) :
    CoercionExpansion :=
  let candidates := (coercionEdges context state trait path.current).filter
    fun edge => !path.visited.contains edge.target
  let edges := viableCoercionEdges context state
    candidates
  {
    paths := edges.viable.map fun edge => {
      current := edge.target
      visited := path.visited ++ [edge.target]
      steps := path.steps ++ [{
        source := edge.source
        target := edge.target
        predicate := edge.predicate
      }]
    }
    blocked := edges.blocked
  }

def expandCoercionPaths (context : Context) (state : State)
    (trait : Resolved.DeclarationId) :
    List CoercionPath → CoercionExpansion
  | [] => {}
  | path :: rest =>
      let head := expandCoercionPath context state trait path
      let tail := expandCoercionPaths context state trait rest
      {
        paths := head.paths ++ tail.paths
        blocked := head.blocked ++ tail.blocked
      }

def finishCoercionSearch (blocked : List Error) :
    Except Error (Option (List PlannedCoercionStep)) :=
  match blocked with
  | error :: _ => .error error
  | [] => .ok none

def selectCoercionPath (source target : Ty)
    (paths : List CoercionPath) :
    Except Error (Option (List PlannedCoercionStep)) :=
  match (paths.filter fun path => path.current == target).eraseDups with
  | [] => .ok none
  | [path] => .ok (some path.steps)
  | first :: second :: _ =>
      .error (.ambiguousCoercion source target first.visited second.visited)

/-- Breadth-first search for a unique shortest coercion path. The fuel is an
edge bound, not a recursion guard: one additional expansion distinguishes
ordinary exhaustion from an explicitly truncated search. -/
def searchCoercionPaths (context : Context) (state : State)
    (trait : Resolved.DeclarationId) (source target : Ty) :
    Nat → List CoercionPath → List Error →
      Except Error (Option (List PlannedCoercionStep))
  | 0, frontier, blocked => do
      let beyond := expandCoercionPaths context state trait frontier
      if beyond.paths.isEmpty then
        finishCoercionSearch (blocked ++ beyond.blocked)
      else throw (.coercionDepthLimit source target context.coercionDepth)
  | fuel + 1, frontier, blocked => do
      let next := expandCoercionPaths context state trait frontier
      match ← selectCoercionPath source target next.paths with
      | some predicates => pure (some predicates)
      | none => do
          let blocked := blocked ++ next.blocked
          if next.paths.isEmpty then finishCoercionSearch blocked
          else
            searchCoercionPaths context state trait source target fuel
              next.paths blocked

/-- Prefer the direct obligation, then search concrete intermediate types.
Returning the unsolved direct predicate preserves the existing final error when
the bounded graph has neither a path nor an inconclusive edge. -/
def coercionPlan? (context : Context) (state : State)
    (source target : Ty) :
    Except Error (Option (List PlannedCoercionStep)) := do
  match ← conventionalTraitWithArity? context "Coerce" 2 with
  | none => pure none
  | some trait =>
      let direct : ProgramPredicate := {
        trait
        subject := source
        arguments := [target]
      }
      match solvePredicate context state direct with
      | .ok _ => pure (some [{ source, target, predicate := direct }])
      | .error (.noTraitImplementation _) =>
          match ← searchCoercionPaths context state trait source target
              context.coercionDepth [{
                current := source
                visited := [source]
                steps := []
              }] [] with
          | some steps => pure (some steps)
          | none => pure (some [{ source, target, predicate := direct }])
      | .error error => throw error

/-- Allocate requirement identities for a selected coercion path in path
order.  Search itself is pure, so rejected overload candidates never consume
identities in the committed state. -/
def commitCoercionPlan : State → List PlannedCoercionStep →
    List CoercionStep × State
  | state, [] => ([], state)
  | state, step :: rest =>
      let (requirement, state) :=
        state.addRequirementWithId step.predicate
      let (steps, state) := commitCoercionPlan state rest
      ({
        requirement
        source := step.source
        target := step.target
      } :: steps, state)

def isNumericVariable (state : State) (type : Ty) : Bool :=
  state.numericVariables.any fun origin =>
    decide (state.resolve (.variable origin.metavariable) = state.resolve type)

def binaryTraitName : Syntax.BinaryOp → String
  | .multiply => "Mul"
  | .divide => "Div"
  | .modulo => "Mod"
  | .add => "Add"
  | .subtract => "Sub"
  | .bitAnd => "BitAnd"
  | .bitXor => "BitXor"
  | .bitOr => "BitOr"
  | .less => "Less"
  | .greater => "Greater"
  | .lessEqual => "LessEqual"
  | .greaterEqual => "GreaterEqual"
  | .equal => "Eq"
  | .notEqual => "Eq"
  | .logicalAnd => "And"
  | .logicalOr => "Or"

def binaryResultIsBool : Syntax.BinaryOp → Bool
  | .less | .greater | .lessEqual | .greaterEqual
  | .equal | .notEqual | .logicalAnd | .logicalOr => true
  | _ => false

def binaryBuiltinType : Syntax.BinaryOp → Ty
  | .logicalAnd | .logicalOr => .bool
  | _ => .word

/-- Operator inference result together with the obligations introduced by the
operator occurrence itself. -/
structure OperatorInferenceResult where
  type : Ty
  requirements : List RequirementId
  state : State

def inferBinaryOperator (context : Context) (operator : Syntax.BinaryOp)
    (left right : Ty) (state : State) :
    Except Error OperatorInferenceResult := do
  let state ← unify state left right
  let operand := state.resolve left
  let builtin := binaryBuiltinType operator
  if operand = builtin then
    pure {
      type := if binaryResultIsBool operator then .bool else builtin
      requirements := []
      state
    }
  else if operand.freeVariables.isEmpty = false && isNumericVariable state operand then
    let state ← unify state operand builtin
    pure {
      type := if binaryResultIsBool operator then .bool else builtin
      requirements := []
      state
    }
  else
    match ← operatorTrait? context (binaryTraitName operator) with
    | some trait =>
        let (requirement, state) := state.addRequirementWithId {
          trait, subject := operand, arguments := []
        }
        pure {
          type := if binaryResultIsBool operator then .bool else operand
          requirements := [requirement]
          state
        }
    | none => throw (.operatorNotSupported (binaryTraitName operator) operand)

def inferUnaryOperator (context : Context) (operator : Syntax.UnaryOp)
    (operandType : Ty) (state : State) :
    Except Error OperatorInferenceResult := do
  let operand := state.resolve operandType
  let builtin := match operator with
    | .logicalNot => Ty.bool
    | .bitNot => Ty.word
  let traitName := match operator with
    | .logicalNot => "Not"
    | .bitNot => "BitNot"
  if operand = builtin then
    pure { type := builtin, requirements := [], state }
  else if operand.freeVariables.isEmpty = false && isNumericVariable state operand then
    let state ← unify state operand builtin
    pure { type := builtin, requirements := [], state }
  else
    match ← operatorTrait? context traitName with
    | some trait =>
        let (requirement, state) := state.addRequirementWithId {
          trait, subject := operand, arguments := []
        }
        pure {
          type := if operator == .logicalNot then .bool else operand
          requirements := [requirement]
          state
        }
    | none => throw (.operatorNotSupported traitName operand)

/-- Expected-type checking result for one exact source occurrence. -/
structure ExpectationResult where
  expression : InferredExpression
  coercions : List CoercionStep
  state : State

def withExpected (context : Context) (state : State)
    (actual : InferredExpression) : Option Ty →
    Except Error ExpectationResult
  | none => .ok {
      expression := { actual with type := state.resolve actual.type }
      coercions := []
      state
    }
  | some expected =>
      match state.inference.unify actual.type expected with
      | .ok inference =>
          let state := { state with inference }
          .ok {
            expression := { actual with type := state.resolve expected }
            coercions := []
            state
          }
      | .error error =>
          match error with
          | .mismatch _ _ => do
              let source := state.resolve actual.type
              let target := state.resolve expected
              match ← coercionPlan? context state source target with
              | none => throw (.unification error)
              | some plan =>
                  let (coercions, state) := commitCoercionPlan state plan
                  pure {
                    expression := { actual with type := target }
                    coercions
                    state
                  }
          | _ => throw (.unification error)

def candidateWithExpected (context : Context) (state : State)
    (actual : InferredExpression) (expected : Option Ty) :
    Except Error (Option ExpectationResult) :=
  match withExpected context state actual expected with
  | .ok result => .ok (some result)
  | .error (.unification (.mismatch _ _)) => .ok none
  | .error error => .error error

def functionParts? : Ty → Option (Ty × Ty)
  | .function parameter result => some (parameter, result)
  | _ => none

/-- Recover the source-level parameter list from its bundled function type.

The source arity is authoritative. In particular, an arity-one function keeps a
product parameter intact instead of treating its components as separate call
arguments. -/
def parameterTypesForArity? : Nat → Ty → Option (List Ty)
  | 0, parameter => if parameter = .unit then some [] else none
  | 1, parameter => some [parameter]
  | arity + 2, .product parameter rest => do
      let parameters ← parameterTypesForArity? (arity + 1) rest
      pure (parameter :: parameters)
  | _ + 2, _ => none

structure ExpressionCoercions where
  expression : ExpressionId
  coercions : List CoercionStep
  deriving Repr, BEq, DecidableEq

structure ArgumentFitResult where
  state : State
  cost : Nat
  coercions : List ExpressionCoercions

def fitArguments (context : Context) :
    State → List InferredExpression → List Ty →
      Except Error (Option ArgumentFitResult)
  | state, [], [] => .ok (some { state, cost := 0, coercions := [] })
  | state, argument :: arguments, parameter :: parameters => do
      let requirementMark := state.requirementMark
      match ← candidateWithExpected context state argument (some parameter) with
      | none => pure none
      | some fitted =>
          let headCost := fitted.state.requirementCountSince requirementMark
          match ← fitArguments context fitted.state arguments parameters with
          | none => pure none
          | some tail =>
              pure (some {
                state := tail.state
                cost := headCost + tail.cost
                coercions := {
                  expression := argument.id
                  coercions := fitted.coercions
                } :: tail.coercions
              })
  | _, _, _ => .ok none

structure RequirementAttachment where
  expression : ExpressionId
  requirement : RequirementId
  deriving Repr, BEq, DecidableEq

structure CandidateNumericResult where
  state : State
  cost : Nat
  requirements : List RequirementAttachment

def defaultCandidateNumericVariable (context : Context)
    (origin : NumericOrigin) (state : State) :
    Except Error CandidateNumericResult := do
  let type := state.resolve (.variable origin.metavariable)
  if type = .word then
    pure { state, cost := 0, requirements := [] }
  else
    match type with
    | .variable _ =>
        pure {
          state := ← unify state type .word
          cost := 0
          requirements := []
        }
    | _ =>
        match ← conventionalTrait? context ["FromLiteral", "Numeric"] with
        | none => throw (.nonNumericLiteral type)
        | some trait =>
            let predicate : ProgramPredicate := {
              trait
              subject := type
              arguments := []
            }
            let (requirement, state) := state.addRequirementWithId predicate
            pure {
              state
              cost := 1
              requirements := [{ expression := origin.expression, requirement }]
            }

def defaultCandidateNumerics (context : Context) :
    List NumericOrigin → State → Except Error CandidateNumericResult
  | [], state => .ok { state, cost := 0, requirements := [] }
  | origin :: rest, state => do
      let head ← defaultCandidateNumericVariable context origin state
      let tail ← defaultCandidateNumerics context rest head.state
      pure {
        state := tail.state
        cost := head.cost + tail.cost
        requirements := head.requirements ++ tail.requirements
      }

def removeCandidateNumerics (state : State)
    (origins : List NumericOrigin) : State := {
  state with
  numericVariables := state.numericVariables.filter fun origin =>
    !origins.contains origin
}

def validateCandidatePredicates (context : Context) (state : State) :
    List ProgramPredicate → Except Error Unit
  | [] => .ok ()
  | predicate :: rest => do
      let normalized := applyPredicate state predicate
      if (TypedTraitResolution.predicateVariables normalized).isEmpty then
        let _ ← solvePredicate context state normalized
        validateCandidatePredicates context state rest
      else
        validateCandidatePredicates context state rest

structure CandidateAttemptResult where
  instantiation : DeclarationInstantiation
  result : InferredExpression
  argumentCoercions : List ExpressionCoercions
  callCoercions : List CoercionStep
  signatureRequirements : List RequirementId
  numericRequirements : List RequirementAttachment
  state : State
  cost : Nat

def tryFunctionCandidate (context : Context)
    (arguments : List InferredExpression) (numericOrigins : List NumericOrigin)
    (call : ExpressionId) (expected : Option Ty) (state : State)
    (signature : ProgramFunctionSignature) :
    Except Error (Option CandidateAttemptResult) :=
  let requirementMark := state.requirementMark
  let instantiated := signature.scheme.instantiate state.inference.next
  match functionParts? instantiated.body with
  | none => .ok none
  | some (parameter, result) => do
      match parameterTypesForArity? signature.parameterTypes.length parameter with
      | none => pure none
      | some parameters =>
          let inference := { state.inference with next := instantiated.next }
          let state := { state with inference }
          match ← fitArguments context state arguments parameters with
          | none => pure none
          | some fittedArguments =>
              let resultRequirementMark := fittedArguments.state.requirementMark
              match ← candidateWithExpected context fittedArguments.state
                  { id := call, type := result } expected with
              | none => pure none
              | some fittedResult =>
                  let resultCost := fittedResult.state.requirementCountSince
                    resultRequirementMark
                  let numeric ←
                    defaultCandidateNumerics context numericOrigins fittedResult.state
                  let state := removeCandidateNumerics numeric.state numericOrigins
                  let introducedRequirements :=
                    state.requirementsSince requirementMark
                  validateCandidatePredicates context state
                    (instantiated.predicates ++
                      introducedRequirements.map (·.predicate))
                  let (signatureRequirements, state) :=
                    state.addRequirementsWithIds instantiated.predicates
                  pure (some {
                    instantiation :=
                      DeclarationInstantiation.ofInstantiated signature.id instantiated
                    result := {
                      fittedResult.expression with
                      type := state.resolve fittedResult.expression.type
                    }
                    argumentCoercions := fittedArguments.coercions
                    callCoercions := fittedResult.coercions
                    signatureRequirements
                    numericRequirements := numeric.requirements
                    state
                    cost := fittedArguments.cost + resultCost + numeric.cost
                  })

structure CandidateSuccess where
  signature : ProgramFunctionSignature
  attempt : CandidateAttemptResult

structure CandidateSearch where
  successes : List CandidateSuccess := []
  failures : List Error := []

def collectCandidateAttempts
    (attempt : ProgramFunctionSignature →
      Except Error (Option CandidateAttemptResult)) :
    List ProgramFunctionSignature → CandidateSearch
  | [] => {}
  | signature :: rest =>
      let tail := collectCandidateAttempts attempt rest
      match attempt signature with
      | .ok none => tail
      | .ok (some result) => {
          tail with successes := {
            signature
            attempt := result
          } :: tail.successes
        }
      | .error error => { tail with failures := error :: tail.failures }

def firstBlockingFailure? : List Error → Option Error
  | [] => none
  | error :: rest =>
      match error with
      | .noTraitImplementation _
      | .nonNumericLiteral _ => firstBlockingFailure? rest
      | _ => some error

def firstNoSolution? : List Error → Option Error
  | [] => none
  | error :: rest =>
      match error with
      | .noTraitImplementation _
      | .nonNumericLiteral _ => some error
      | _ => firstNoSolution? rest

def minimumCandidateCost : List CandidateSuccess → Option Nat
  | [] => none
  | success :: rest => some <| rest.foldl
      (fun cost candidate => min cost candidate.attempt.cost) success.attempt.cost

def bestCandidateSuccesses (successes : List CandidateSuccess) :
    List CandidateSuccess :=
  match minimumCandidateCost successes with
  | none => []
  | some cost => successes.filter fun success => success.attempt.cost == cost

def selectCandidateSearch (name : String)
    (allCandidates : List ProgramFunctionSignature)
    (search : CandidateSearch) :
    Except Error CandidateAttemptResult :=
  match bestCandidateSuccesses search.successes with
  | [] =>
      match firstBlockingFailure? search.failures with
      | some error => .error error
      | none =>
          match firstNoSolution? search.failures with
          | some error => .error error
          | none => .error (.noMatchingOverload name (allCandidates.map (·.id)))
  | [success] =>
      match firstBlockingFailure? search.failures with
      | some error => .error error
      | none => .ok success.attempt
  | successes =>
      .error (.ambiguousOverload name
        (successes.map fun success => success.signature.id))

def selectFunctionCandidateFrom (context : Context) (name : String)
    (candidates : List ProgramFunctionSignature)
    (arguments : List InferredExpression) (numericOrigins : List NumericOrigin)
    (call : ExpressionId) (expected : Option Ty) (state : State) :
    Except Error CandidateAttemptResult :=
  let search := collectCandidateAttempts
    (tryFunctionCandidate context arguments numericOrigins call expected state)
    candidates
  selectCandidateSearch name candidates search

def selectFunctionCandidate (context : Context) (name : String)
    (arguments : List InferredExpression) (numericOrigins : List NumericOrigin)
    (call : ExpressionId) (expected : Option Ty) (state : State) :
    Except Error CandidateAttemptResult := do
  selectFunctionCandidateFrom context name (← functionsNamed context name)
    arguments numericOrigins call expected state

structure IndirectApplicationResult where
  result : InferredExpression
  argumentCoercions : List CoercionStep
  callCoercions : List CoercionStep
  state : State

/-- Apply an indirectly obtained function type.  The existing bundled-argument
acceptance behavior is preserved; any coercion of that bundle is attributed to
the call occurrence because there is no synthetic tuple expression node. -/
def applyFunctionType (context : Context) (call : ExpressionId)
    (calleeType : Ty) (arguments : List InferredExpression)
    (expected : Option Ty) (state : State) :
    Except Error IndirectApplicationResult :=
  let argumentType := Ty.productMany (arguments.map (·.type))
  match functionParts? (state.resolve calleeType) with
  | some (parameter, result) => do
      let fittedArgument ← withExpected context state
        { id := call, type := argumentType } (some parameter)
      let fittedResult ← withExpected context fittedArgument.state
        { id := call, type := result } expected
      pure {
        result := fittedResult.expression
        argumentCoercions := fittedArgument.coercions
        callCoercions := fittedResult.coercions
        state := fittedResult.state
      }
  | none => do
      let (resultType, state) := state.fresh
      let state ← unify state calleeType (.function argumentType resultType)
      let fittedResult ← withExpected context state
        { id := call, type := resultType } expected
      pure {
        result := fittedResult.expression
        argumentCoercions := []
        callCoercions := fittedResult.coercions
        state := fittedResult.state
      }

def calleeIdentifier? : Syntax.Expr → Option String
  | ⟨_, .identifier name⟩ => some name.value
  | ⟨_, .group inner⟩ => calleeIdentifier? inner
  | _ => none

def calleeNameComponents? : Syntax.Expr → Option (List String)
  | ⟨_, .identifier name⟩ => some [name.value]
  | ⟨_, .field base _ name⟩ => do
      let components ← calleeNameComponents? base
      pure (components ++ [name.value])
  | ⟨_, .group inner⟩ => calleeNameComponents? inner
  | _ => none

def calleeQualifiedIdentifier? (expression : Syntax.Expr) :
    Option (List String × String) := do
  let components ← calleeNameComponents? expression
  match components with
  | _ :: _ :: _ => some (components.dropLast, components.getLast!)
  | _ => none

end Solcore.Frontend.SourceInference.Detail
