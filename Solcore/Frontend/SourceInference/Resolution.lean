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

structure CoercionEdge where
  source : Ty
  target : Ty
  predicate : ProgramPredicate
  methodPredicates : List ProgramPredicate := []
  deriving Repr, DecidableEq

/-- One not-yet-committed edge selected by coercion search.  Requirement IDs
are allocated only after the whole path has been selected. -/
structure PlannedCoercionStep where
  source : Ty
  target : Ty
  predicate : ProgramPredicate
  methodPredicates : List ProgramPredicate := []
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

/-- The optional named method catalog used to attach caller-owned predicates
to every coercion edge.  Empty legacy marker traits remain usable by the
inference-only graph; executable linking still requires `coerce`. -/
structure CoercionMethodProfile where
  trait : Resolved.DeclarationId
  parameters : List TypeParameterId
  method : ProgramTraitMethodSignature

def coercionMethodProfile? (context : Context)
    (trait : Resolved.DeclarationId) :
    Except Error (Option CoercionMethodProfile) := do
  let signature ← match context.signatures.trait? trait with
    | some signature => pure signature
    | none => throw (.missingCoercionTraitCatalog trait)
  unless signature.parameters.length = 2 do
    throw (.coercionTraitArityMismatch trait 2 signature.parameters.length)
  match signature.methods.filter fun method => method.name == "coerce" with
  | [] => pure none
  | [method] => pure (some {
      trait
      parameters := signature.parameters
      method
    })
  | methods => throw (.duplicateCoercionTraitMethod trait methods.length)

def coercionMethodPredicates (profile : Option CoercionMethodProfile)
    (source target : Ty) : Except Error (List ProgramPredicate) := do
  let some profile := profile | pure []
  let substitution : ParameterSubstitution :=
    profile.parameters.zip [source, target]
  let actualParameters := profile.method.parameterTypes.map substitution.apply
  let actualReturns := profile.method.returnTypes.map substitution.apply
  let expectedParameters := [source]
  let expectedReturns := [target]
  unless actualParameters = expectedParameters &&
      actualReturns = expectedReturns do
    throw (.coercionTraitMethodSignatureMismatch profile.trait
      expectedParameters actualParameters expectedReturns actualReturns)
  pure (profile.method.wherePredicates.map
    (ProgramPredicate.applyParameters substitution))

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
    (profile : Option CoercionMethodProfile)
    (trait : Resolved.DeclarationId) (source : Ty) :
    Except Error (List CoercionEdge) := do
  let edges :=
    ((context.signatures.implRules.filterMap (coercionRuleEdge? trait source)) ++
      assumptionCoercionEdges context state trait source).eraseDups
  edges.mapM fun edge => do
    let methodPredicates ←
      coercionMethodPredicates profile edge.source edge.target
    pure { edge with methodPredicates }

def coercionEvidenceViable (context : Context) (state : State)
    (predicate : ProgramPredicate) (methodPredicates : List ProgramPredicate) :
    Except Error Bool := do
  match solvePredicate context state predicate with
  | .error (.noTraitImplementation _) => pure false
  | .error error => throw error
  | .ok _ =>
      match solvePredicates context state methodPredicates with
      | .ok _ => pure true
      | .error (.noTraitImplementation _) => pure false
      | .error error => throw error

def viableCoercionEdges (context : Context) (state : State) :
    List CoercionEdge → CoercionEdges
  | [] => {}
  | edge :: rest =>
      let tail := viableCoercionEdges context state rest
      match coercionEvidenceViable context state edge.predicate
          edge.methodPredicates with
      | .ok true => { tail with viable := edge :: tail.viable }
      | .ok false => tail
      | .error error => { tail with blocked := error :: tail.blocked }

def expandCoercionPath (context : Context) (state : State)
    (profile : Option CoercionMethodProfile)
    (trait : Resolved.DeclarationId) (path : CoercionPath) :
    Except Error CoercionExpansion := do
  let candidates := (← coercionEdges context state profile trait path.current).filter
    fun edge => !path.visited.contains edge.target
  let edges := viableCoercionEdges context state
    candidates
  pure {
    paths := edges.viable.map fun edge => {
      current := edge.target
      visited := path.visited ++ [edge.target]
      steps := path.steps ++ [{
        source := edge.source
        target := edge.target
        predicate := edge.predicate
        methodPredicates := edge.methodPredicates
      }]
    }
    blocked := edges.blocked
  }

def expandCoercionPaths (context : Context) (state : State)
    (profile : Option CoercionMethodProfile)
    (trait : Resolved.DeclarationId) :
    List CoercionPath → Except Error CoercionExpansion
  | [] => pure {}
  | path :: rest =>
      do
      let head ← expandCoercionPath context state profile trait path
      let tail ← expandCoercionPaths context state profile trait rest
      pure {
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
    (profile : Option CoercionMethodProfile)
    (trait : Resolved.DeclarationId) (source target : Ty) :
    Nat → List CoercionPath → List Error →
      Except Error (Option (List PlannedCoercionStep))
  | 0, frontier, blocked => do
      let beyond ← expandCoercionPaths context state profile trait frontier
      if beyond.paths.isEmpty then
        finishCoercionSearch (blocked ++ beyond.blocked)
      else throw (.coercionDepthLimit source target context.coercionDepth)
  | fuel + 1, frontier, blocked => do
      let next ← expandCoercionPaths context state profile trait frontier
      match ← selectCoercionPath source target next.paths with
      | some predicates => pure (some predicates)
      | none => do
          let blocked := blocked ++ next.blocked
          if next.paths.isEmpty then finishCoercionSearch blocked
          else
            searchCoercionPaths context state profile trait source target fuel
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
      let profile ← coercionMethodProfile? context trait
      let direct : ProgramPredicate := {
        trait
        subject := source
        arguments := [target]
      }
      let methodPredicates ← coercionMethodPredicates profile source target
      let directStep : PlannedCoercionStep := {
        source
        target
        predicate := direct
        methodPredicates
      }
      match coercionEvidenceViable context state direct methodPredicates with
      | .ok true => pure (some [directStep])
      | .ok false =>
          match ← searchCoercionPaths context state profile trait source target
              context.coercionDepth [{
                current := source
                visited := [source]
                steps := []
              }] [] with
          | some steps => pure (some steps)
          | none => pure (some [directStep])
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
      let (methodRequirements, state) :=
        state.addRequirementsWithIds step.methodPredicates
      let (steps, state) := commitCoercionPlan state rest
      ({
        requirement
        methodRequirements
        source := step.source
        target := step.target
      } :: steps, state)

def isOpenIntegerLiteralTarget (state : State)
    (origins : List IntegerLiteralOrigin) (type : Ty) : Bool :=
  match state.resolve type with
  | .variable _ => origins.any fun origin =>
      decide (state.resolve (.variable origin.metavariable) = state.resolve type)
  | _ => false

/-- An operator with no source-level catalog may postpone direct builtin
selection only while its operand is the open target of a relevant literal. -/
def isDeferredBuiltinOperatorTarget (state : State)
    (hasOpenLiteralOperand : Bool) (builtin type : Ty) : Bool :=
  builtin == Ty.word && hasOpenLiteralOperand &&
    match state.resolve type with
    | .variable _ => true
    | _ => false

/-- `integer` shares the literal-facing operator surface with Word during
source checking, but remains staged and is still rejected by Core lowering. -/
def isStagedIntegerOperatorTarget (state : State)
    (hasOpenLiteralOperand : Bool) (builtin type : Ty) : Bool :=
  builtin == Ty.word && state.resolve type == Ty.integer &&
    hasOpenLiteralOperand

/-- The target language deliberately mixes trait-backed operators with ordinary
named functions from its standard prelude.  Keeping that distinction in one
table prevents inference and executable linking from inventing incompatible
operator traits independently. -/
inductive OperatorDispatch where
  | traitMethod (traitName methodName : String)
  | function (name : String)
  deriving Repr, DecidableEq

def binaryOperatorDispatch : Syntax.BinaryOp → OperatorDispatch
  | .multiply => .traitMethod "Mul" "mul"
  | .divide => .traitMethod "Div" "div"
  | .modulo => .traitMethod "Mod" "mod"
  | .add => .traitMethod "Add" "add"
  | .subtract => .traitMethod "Sub" "sub"
  | .bitAnd => .traitMethod "BitAnd" "band"
  | .bitXor => .traitMethod "BitXor" "bxor"
  | .bitOr => .traitMethod "BitOr" "bor"
  | .less => .function "lt"
  | .greater => .traitMethod "Ord" "gt"
  | .lessEqual => .function "le"
  | .greaterEqual => .function "ge"
  | .equal => .traitMethod "Eq" "eq"
  | .notEqual => .function "ne"
  | .logicalAnd => .function "and"
  | .logicalOr => .function "or"

def unaryOperatorDispatch : Syntax.UnaryOp → OperatorDispatch
  | .logicalNot => .function "not"
  | .bitNot => .traitMethod "BitNot" "bnot"

def binaryResultIsBool : Syntax.BinaryOp → Bool
  | .less | .greater | .lessEqual | .greaterEqual
  | .equal | .notEqual | .logicalAnd | .logicalOr => true
  | _ => false

def binaryBuiltinType : Syntax.BinaryOp → Ty
  | .logicalAnd | .logicalOr => .bool
  | _ => .word

/-- Select the exact trait method assigned to an operator spelling.  Program
signature construction rejects duplicate method names, but keeping the
cardinality check here makes inference reject malformed or independently
assembled catalogs instead of silently selecting one entry. -/
def exactOperatorTraitMethod (context : Context)
    (trait : Resolved.DeclarationId) (methodName : String) :
    Except Error (ProgramTraitSignature × ProgramTraitMethodSignature) := do
  let signature ← match context.signatures.trait? trait with
    | some signature => pure signature
    | none => throw (.missingOperatorTraitCatalog trait)
  match signature.methods.filter fun method => method.name == methodName with
  | [] => throw (.missingOperatorTraitMethod trait methodName)
  | [method] => pure (signature, method)
  | methods => throw (.duplicateOperatorTraitMethod trait methodName methods.length)

/-- The operator occurrence owns both selection of the primary trait and the
named method's declaration-ordered local obligations.  Operator traits have
one source parameter, so instantiating it with the inferred operand closes the
same method predicates that implementation signatures are checked against.
The instantiated parameter and result lists must also match the operator's
fixed source-level signature. -/
def operatorTraitPredicates (context : Context)
    (trait : Resolved.DeclarationId) (methodName : String) (operand : Ty)
    (expectedParameters expectedReturns : List Ty) :
    Except Error (List ProgramPredicate) := do
  let (signature, method) ←
    exactOperatorTraitMethod context trait methodName
  unless signature.parameters.length = 1 do
    throw (.operatorTraitArityMismatch trait 1 signature.parameters.length)
  let substitution : ParameterSubstitution :=
    signature.parameters.zip [operand]
  let actualParameters := method.parameterTypes.map substitution.apply
  let actualReturns := method.returnTypes.map substitution.apply
  unless actualParameters = expectedParameters &&
      actualReturns = expectedReturns do
    throw (.operatorTraitMethodSignatureMismatch trait methodName
      expectedParameters actualParameters expectedReturns actualReturns)
  let primary : ProgramPredicate := {
    trait
    subject := operand
    arguments := []
  }
  pure (primary :: method.wherePredicates.map
    (ProgramPredicate.applyParameters substitution))

/-- Operator inference result together with the obligations introduced by the
operator occurrence itself. -/
structure OperatorInferenceResult where
  type : Ty
  requirements : List RequirementId
  state : State

def inferBinaryOperator (context : Context) (operator : Syntax.BinaryOp)
    (left right : Ty) (expected : Option Ty)
    (integerLiterals : List IntegerLiteralOrigin) (state : State) :
    Except Error OperatorInferenceResult := do
  let hasOpenLiteralOperand :=
    isOpenIntegerLiteralTarget state integerLiterals left ||
      isOpenIntegerLiteralTarget state integerLiterals right
  let state ← unify state left right
  let state ← match expected with
    | some expected =>
        let operand := state.resolve left
        if binaryResultIsBool operator || operand.freeVariables.isEmpty ||
            !hasOpenLiteralOperand then
          pure state
        else
          unify state operand expected
    | none => pure state
  let operand := state.resolve left
  let builtin := binaryBuiltinType operator
  if operand = builtin then
    pure {
      type := if binaryResultIsBool operator then .bool else builtin
      requirements := []
      state
    }
  else
    match binaryOperatorDispatch operator with
    | .function name =>
        if isDeferredBuiltinOperatorTarget state hasOpenLiteralOperand
              builtin operand ||
            isStagedIntegerOperatorTarget state hasOpenLiteralOperand
              builtin operand then
          pure {
            type := if binaryResultIsBool operator then .bool else operand
            requirements := []
            state
          }
        else
          throw (.unknownVariable name)
    | .traitMethod traitName methodName =>
        match ← operatorTrait? context traitName with
        | some trait =>
            let result := if binaryResultIsBool operator then .bool else operand
            let predicates ←
              operatorTraitPredicates context trait methodName operand
                [operand, operand] [result]
            let (requirements, state) :=
              state.addRequirementsWithIds predicates
            pure {
              type := result
              requirements
              state
            }
        | none =>
            if isDeferredBuiltinOperatorTarget state hasOpenLiteralOperand
                  builtin operand ||
                isStagedIntegerOperatorTarget state hasOpenLiteralOperand
                  builtin operand then
              pure {
                type := if binaryResultIsBool operator then .bool else operand
                requirements := []
                state
              }
            else
              throw (.operatorNotSupported traitName operand)

def inferUnaryOperator (context : Context) (operator : Syntax.UnaryOp)
    (operandType : Ty) (expected : Option Ty)
    (integerLiterals : List IntegerLiteralOrigin) (state : State) :
    Except Error OperatorInferenceResult := do
  let hasOpenLiteralOperand :=
    isOpenIntegerLiteralTarget state integerLiterals operandType
  let state ← match expected with
    | some expected =>
        let operand := state.resolve operandType
        if operator == .logicalNot || operand.freeVariables.isEmpty ||
            !hasOpenLiteralOperand then
          pure state
        else
          unify state operand expected
    | none => pure state
  let operand := state.resolve operandType
  let builtin := match operator with
    | .logicalNot => Ty.bool
    | .bitNot => Ty.word
  if operand = builtin then
    pure { type := builtin, requirements := [], state }
  else
    match unaryOperatorDispatch operator with
    | .function name =>
        if isDeferredBuiltinOperatorTarget state hasOpenLiteralOperand
              builtin operand ||
            isStagedIntegerOperatorTarget state hasOpenLiteralOperand
              builtin operand then
          pure {
            type := if operator == .logicalNot then .bool else operand
            requirements := []
            state
          }
        else
          throw (.unknownVariable name)
    | .traitMethod traitName methodName =>
        match ← operatorTrait? context traitName with
        | some trait =>
            let result := if operator == .logicalNot then .bool else operand
            let predicates ←
              operatorTraitPredicates context trait methodName operand
                [operand] [result]
            let (requirements, state) :=
              state.addRequirementsWithIds predicates
            pure {
              type := result
              requirements
              state
            }
        | none =>
            if isDeferredBuiltinOperatorTarget state hasOpenLiteralOperand
                  builtin operand ||
                isStagedIntegerOperatorTarget state hasOpenLiteralOperand
                  builtin operand then
              pure {
                type := if operator == .logicalNot then .bool else operand
                requirements := []
                state
              }
            else
              throw (.operatorNotSupported traitName operand)

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
      match ← candidateWithExpected context state argument (some parameter) with
      | none => pure none
      | some fitted =>
          let headCost := fitted.coercions.length
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

def validateCandidateIntegerLiterals (context : Context) (state : State) :
    List IntegerLiteralOrigin → Except Error Bool
  | [] => .ok false
  | origin :: rest => do
      let requirement ← match state.requirements.find? fun requirement =>
          requirement.id == origin.requirement with
        | some requirement => pure requirement
        | none => throw (.missingIntegerLiteralRequirement
            origin.expression origin.requirement)
      let expected := ProgramSignatures.builtinIntPredicate
        (.variable origin.metavariable)
      if requirement.predicate != expected then
        throw (.integerLiteralRequirementPredicateMismatch
          origin.expression origin.requirement expected requirement.predicate)
      let target := state.resolve (.variable origin.metavariable)
      let deferred := match target with
        | .variable _ => true
        | _ => false
      if !deferred then
        let _ ← solvePredicate context state requirement.predicate
      let tailDeferred ← validateCandidateIntegerLiterals context state rest
      pure (deferred || tailDeferred)

structure CandidateAttemptResult where
  instantiation : DeclarationInstantiation
  result : InferredExpression
  argumentCoercions : List ExpressionCoercions
  callCoercions : List CoercionStep
  signatureRequirements : List RequirementId
  hasDeferredIntegerLiterals : Bool
  state : State
  cost : Nat

def tryFunctionCandidate (context : Context)
    (arguments : List InferredExpression)
    (integerLiteralOrigins : List IntegerLiteralOrigin)
    (call : ExpressionId) (expected : Option Ty) (state : State)
    (signature : ProgramFunctionSignature) :
    Except Error (Option CandidateAttemptResult) :=
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
              match ← candidateWithExpected context fittedArguments.state
                  { id := call, type := result } expected with
              | none => pure none
              | some fittedResult =>
                  let resultCost := fittedResult.coercions.length
                  let hasDeferredIntegerLiterals ←
                    validateCandidateIntegerLiterals context fittedResult.state
                      integerLiteralOrigins
                  let state := fittedResult.state
                  validateCandidatePredicates context state
                    (instantiated.predicates ++
                      state.requirements.map (·.predicate))
                  let (signatureRequirements, state) :=
                    state.addRequirementsWithIds instantiated.predicates
                  pure (some {
                    instantiation :=
                      DeclarationInstantiation.ofInstantiated signature instantiated
                    result := {
                      fittedResult.expression with
                      type := state.resolve fittedResult.expression.type
                    }
                    argumentCoercions := fittedArguments.coercions
                    callCoercions := fittedResult.coercions
                    signatureRequirements
                    hasDeferredIntegerLiterals
                    state
                    cost := fittedArguments.cost + resultCost
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
      | .noTraitImplementation _ => firstBlockingFailure? rest
      | _ => some error

def firstNoSolution? : List Error → Option Error
  | [] => none
  | error :: rest =>
      match error with
      | .noTraitImplementation _ => some error
      | _ => firstNoSolution? rest

def minimumCandidateCost : List CandidateSuccess → Option Nat
  | [] => none
  | success :: rest => some <| rest.foldl
      (fun cost candidate => min cost candidate.attempt.cost) success.attempt.cost

def bestCandidateSuccesses (successes : List CandidateSuccess) :
    List CandidateSuccess :=
  let ground := successes.filter fun success =>
    !success.attempt.hasDeferredIntegerLiterals
  let preferred := if ground.isEmpty then successes else ground
  match minimumCandidateCost preferred with
  | none => []
  | some cost => preferred.filter fun success => success.attempt.cost == cost

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
    (arguments : List InferredExpression)
    (integerLiteralOrigins : List IntegerLiteralOrigin)
    (call : ExpressionId) (expected : Option Ty) (state : State) :
    Except Error CandidateAttemptResult :=
  let search := collectCandidateAttempts
    (tryFunctionCandidate context arguments integerLiteralOrigins call expected
      state)
    candidates
  selectCandidateSearch name candidates search

def selectFunctionCandidate (context : Context) (name : String)
    (arguments : List InferredExpression)
    (integerLiteralOrigins : List IntegerLiteralOrigin)
    (call : ExpressionId) (expected : Option Ty) (state : State) :
    Except Error CandidateAttemptResult := do
  selectFunctionCandidateFrom context name (← functionsNamed context name)
    arguments integerLiteralOrigins call expected state

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
