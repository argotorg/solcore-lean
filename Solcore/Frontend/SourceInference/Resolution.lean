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
  target : Ty
  predicate : ProgramPredicate
  deriving Repr, DecidableEq

structure CoercionPath where
  current : Ty
  visited : List Ty
  predicates : List ProgramPredicate
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
          if isGroundCoercionTarget target then some { target, predicate }
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
      predicates := path.predicates ++ [edge.predicate]
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
    Except Error (Option (List ProgramPredicate)) :=
  match blocked with
  | error :: _ => .error error
  | [] => .ok none

def selectCoercionPath (source target : Ty)
    (paths : List CoercionPath) : Except Error (Option (List ProgramPredicate)) :=
  match (paths.filter fun path => path.current == target).eraseDups with
  | [] => .ok none
  | [path] => .ok (some path.predicates)
  | first :: second :: _ =>
      .error (.ambiguousCoercion source target first.visited second.visited)

/-- Breadth-first search for a unique shortest coercion path. The fuel is an
edge bound, not a recursion guard: one additional expansion distinguishes
ordinary exhaustion from an explicitly truncated search. -/
def searchCoercionPaths (context : Context) (state : State)
    (trait : Resolved.DeclarationId) (source target : Ty) :
    Nat → List CoercionPath → List Error →
      Except Error (Option (List ProgramPredicate))
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
    (source target : Ty) : Except Error (Option (List ProgramPredicate)) := do
  match ← conventionalTraitWithArity? context "Coerce" 2 with
  | none => pure none
  | some trait =>
      let direct : ProgramPredicate := {
        trait
        subject := source
        arguments := [target]
      }
      match solvePredicate context state direct with
      | .ok _ => pure (some [direct])
      | .error (.noTraitImplementation _) =>
          match ← searchCoercionPaths context state trait source target
              context.coercionDepth [{
                current := source
                visited := [source]
                predicates := []
              }] [] with
          | some predicates => pure (some predicates)
          | none => pure (some [direct])
      | .error error => throw error

def isNumericVariable (state : State) (type : Ty) : Bool :=
  state.numericVariables.any fun metavariable =>
    decide (state.resolve (.variable metavariable) = state.resolve type)

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

def inferBinaryOperator (context : Context) (operator : Syntax.BinaryOp)
    (left right : Ty) (state : State) : Except Error (Ty × State) := do
  let state ← unify state left right
  let operand := state.resolve left
  let builtin := binaryBuiltinType operator
  if operand = builtin then
    pure (if binaryResultIsBool operator then .bool else builtin, state)
  else if operand.freeVariables.isEmpty = false && isNumericVariable state operand then
    let state ← unify state operand builtin
    pure (if binaryResultIsBool operator then .bool else builtin, state)
  else
    match ← operatorTrait? context (binaryTraitName operator) with
    | some trait =>
        let state := state.addRequirement { trait, subject := operand, arguments := [] }
        pure (if binaryResultIsBool operator then .bool else operand, state)
    | none => throw (.operatorNotSupported (binaryTraitName operator) operand)

def inferUnaryOperator (context : Context) (operator : Syntax.UnaryOp)
    (operandType : Ty) (state : State) : Except Error (Ty × State) := do
  let operand := state.resolve operandType
  let builtin := match operator with
    | .logicalNot => Ty.bool
    | .bitNot => Ty.word
  let traitName := match operator with
    | .logicalNot => "Not"
    | .bitNot => "BitNot"
  if operand = builtin then
    pure (builtin, state)
  else if operand.freeVariables.isEmpty = false && isNumericVariable state operand then
    let state ← unify state operand builtin
    pure (builtin, state)
  else
    match ← operatorTrait? context traitName with
    | some trait =>
        let state := state.addRequirement { trait, subject := operand, arguments := [] }
        pure (if operator == .logicalNot then .bool else operand, state)
    | none => throw (.operatorNotSupported traitName operand)

def withExpected (context : Context) (state : State) (actual : Ty) : Option Ty →
    Except Error (Ty × State)
  | none => .ok (state.resolve actual, state)
  | some expected =>
      match state.inference.unify actual expected with
      | .ok inference =>
          let state := { state with inference }
          .ok (state.resolve expected, state)
      | .error error =>
          match error with
          | .mismatch _ _ => do
              let source := state.resolve actual
              let target := state.resolve expected
              match ← coercionPlan? context state source target with
              | none => throw (.unification error)
              | some predicates =>
                  pure (target, state.addRequirements predicates)
          | _ => throw (.unification error)

def candidateWithExpected (context : Context) (state : State) (actual : Ty)
    (expected : Option Ty) : Except Error (Option (Ty × State)) :=
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

def fitArguments (context : Context) :
    State → List Ty → List Ty → Except Error (Option (State × Nat))
  | state, [], [] => .ok (some (state, 0))
  | state, argument :: arguments, parameter :: parameters => do
      let requirementCount := state.requirements.length
      match ← candidateWithExpected context state argument (some parameter) with
      | none => pure none
      | some (_, state) =>
          let headCost := state.requirements.length - requirementCount
          match ← fitArguments context state arguments parameters with
          | none => pure none
          | some (state, cost) =>
              pure (some (state, headCost + cost))
  | _, _, _ => .ok none

structure CandidateNumericResult where
  state : State
  cost : Nat

def defaultCandidateNumericVariable (context : Context)
    (metavariable : TypeVarId) (state : State) :
    Except Error CandidateNumericResult := do
  let type := state.resolve (.variable metavariable)
  if type = .word then
    pure { state, cost := 0 }
  else
    match type with
    | .variable _ =>
        pure { state := ← unify state type .word, cost := 0 }
    | _ =>
        match ← conventionalTrait? context ["FromLiteral", "Numeric"] with
        | none => throw (.nonNumericLiteral type)
        | some trait =>
            let predicate : ProgramPredicate := {
              trait
              subject := type
              arguments := []
            }
            pure { state := state.addRequirement predicate, cost := 1 }

def defaultCandidateNumerics (context : Context) :
    List TypeVarId → State → Except Error CandidateNumericResult
  | [], state => .ok { state, cost := 0 }
  | metavariable :: rest, state => do
      let head ← defaultCandidateNumericVariable context metavariable state
      let tail ← defaultCandidateNumerics context rest head.state
      pure { state := tail.state, cost := head.cost + tail.cost }

def removeCandidateNumerics (state : State)
    (metavariables : List TypeVarId) : State := {
  state with
  numericVariables := state.numericVariables.filter fun metavariable =>
    !metavariables.contains metavariable
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
  result : Ty
  state : State
  cost : Nat

def tryFunctionCandidate (context : Context)
    (argumentTypes : List Ty) (numericVariables : List TypeVarId)
    (expected : Option Ty) (state : State)
    (signature : ProgramFunctionSignature) :
    Except Error (Option CandidateAttemptResult) :=
  let requirementCount := state.requirements.length
  let instantiated := signature.scheme.instantiate state.inference.next
  match functionParts? instantiated.body with
  | none => .ok none
  | some (parameter, result) => do
      match parameterTypesForArity? signature.parameterTypes.length parameter with
      | none => pure none
      | some parameters =>
          let inference := { state.inference with next := instantiated.next }
          let state := { state with inference }
          match ← fitArguments context state argumentTypes parameters with
          | none => pure none
          | some (state, argumentCost) =>
              let resultRequirementCount := state.requirements.length
              match ← candidateWithExpected context state result expected with
              | none => pure none
              | some (result, state) =>
                  let resultCost :=
                    state.requirements.length - resultRequirementCount
                  let numeric ←
                    defaultCandidateNumerics context numericVariables state
                  let state := removeCandidateNumerics numeric.state numericVariables
                  let introducedRequirements :=
                    state.requirements.drop requirementCount
                  validateCandidatePredicates context state
                    (instantiated.predicates ++ introducedRequirements)
                  pure (some {
                    result := state.resolve result
                    state := state.addRequirements instantiated.predicates
                    cost := argumentCost + resultCost + numeric.cost
                  })

structure CandidateSuccess where
  signature : ProgramFunctionSignature
  result : Ty
  state : State
  cost : Nat

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
            result := result.result
            state := result.state
            cost := result.cost
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
      (fun cost candidate => min cost candidate.cost) success.cost

def bestCandidateSuccesses (successes : List CandidateSuccess) :
    List CandidateSuccess :=
  match minimumCandidateCost successes with
  | none => []
  | some cost => successes.filter fun success => success.cost == cost

def selectCandidateSearch (name : String)
    (allCandidates : List ProgramFunctionSignature)
    (search : CandidateSearch) :
    Except Error (Ty × State) :=
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
      | none => .ok (success.result, success.state)
  | successes =>
      .error (.ambiguousOverload name
        (successes.map fun success => success.signature.id))

def selectFunctionCandidateFrom (context : Context) (name : String)
    (candidates : List ProgramFunctionSignature)
    (argumentTypes : List Ty) (numericVariables : List TypeVarId)
    (expected : Option Ty) (state : State) :
    Except Error (Ty × State) :=
  let search := collectCandidateAttempts
    (tryFunctionCandidate context argumentTypes numericVariables expected state)
    candidates
  selectCandidateSearch name candidates search

def selectFunctionCandidate (context : Context) (name : String)
    (argumentTypes : List Ty) (numericVariables : List TypeVarId)
    (expected : Option Ty) (state : State) :
    Except Error (Ty × State) := do
  selectFunctionCandidateFrom context name (← functionsNamed context name)
    argumentTypes numericVariables expected state

def applyFunctionType (context : Context) (calleeType argumentType : Ty)
    (expected : Option Ty) (state : State) : Except Error (Ty × State) :=
  match functionParts? (state.resolve calleeType) with
  | some (parameter, result) => do
      let (_, state) ← withExpected context state argumentType (some parameter)
      withExpected context state result expected
  | none => do
      let (resultType, state) := state.fresh
      let state ← unify state calleeType (.function argumentType resultType)
      withExpected context state resultType expected

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
