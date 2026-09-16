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
              match ← conventionalTraitWithArity? context "Coerce" 2 with
              | none => throw (.unification error)
              | some trait =>
                  let predicate : ProgramPredicate := {
                    trait
                    subject := state.resolve actual
                    arguments := [state.resolve expected]
                  }
                  pure (state.resolve expected, state.addRequirement predicate)
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

def tryFunctionCandidate (context : Context)
    (argumentType : Ty) (expected : Option Ty) (state : State)
    (signature : ProgramFunctionSignature) :
    Except Error (Option (Ty × State)) :=
  let instantiated := signature.scheme.instantiate state.inference.next
  let candidate? : Option (Ty × State) := do
    let (parameter, result) ← functionParts? instantiated.body
    let inference := { state.inference with next := instantiated.next }
    let state := { state with inference }
    let state ← (unify state parameter argumentType).toOption
    let state ← match expected with
      | none => some state
      | some expected => (unify state result expected).toOption
    some (result, state)
  match candidate? with
  | none => .ok none
  | some (result, state) => do
      validateCandidatePredicates context state instantiated.predicates
      pure (some (state.resolve result,
        state.addRequirements instantiated.predicates))

def tryCoercibleFunctionCandidate (context : Context)
    (argumentType : Ty) (expected : Option Ty) (state : State)
    (signature : ProgramFunctionSignature) :
    Except Error (Option (Ty × State)) :=
  let requirementCount := state.requirements.length
  let instantiated := signature.scheme.instantiate state.inference.next
  match functionParts? instantiated.body with
  | none => .ok none
  | some (parameter, result) => do
      let inference := { state.inference with next := instantiated.next }
      let state := { state with inference }
      match ← candidateWithExpected context state argumentType (some parameter) with
      | none => pure none
      | some (_, state) =>
          match ← candidateWithExpected context state result expected with
          | none => pure none
          | some (result, state) =>
              let introducedRequirements :=
                state.requirements.drop requirementCount
              validateCandidatePredicates context state
                (instantiated.predicates ++ introducedRequirements)
              pure (some (state.resolve result,
                state.addRequirements instantiated.predicates))

structure CandidateSearch where
  successes : List (ProgramFunctionSignature × Ty × State) := []
  failures : List Error := []

def collectCandidateAttempts
    (attempt : ProgramFunctionSignature →
      Except Error (Option (Ty × State))) :
    List ProgramFunctionSignature → CandidateSearch
  | [] => {}
  | signature :: rest =>
      let tail := collectCandidateAttempts attempt rest
      match attempt signature with
      | .ok none => tail
      | .ok (some (result, state)) => {
          tail with successes := (signature, result, state) :: tail.successes
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

def selectCandidateSearch (name : String)
    (allCandidates : List ProgramFunctionSignature)
    (fallbackFailures : List Error) (search : CandidateSearch) :
    Except Error (Ty × State) :=
  match search.successes with
  | [] =>
      match firstBlockingFailure? search.failures with
      | some error => .error error
      | none =>
          match firstNoSolution? (search.failures ++ fallbackFailures) with
          | some error => .error error
          | none => .error (.noMatchingOverload name (allCandidates.map (·.id)))
  | [(_, result, state)] =>
      match firstBlockingFailure? search.failures with
      | some error => .error error
      | none => .ok (result, state)
  | successes =>
      .error (.ambiguousOverload name (successes.map fun success => success.1.id))

def selectFunctionCandidateFrom (context : Context) (name : String)
    (candidates : List ProgramFunctionSignature)
    (argumentType : Ty) (expected : Option Ty) (state : State) :
    Except Error (Ty × State) :=
  let exact := collectCandidateAttempts
    (tryFunctionCandidate context argumentType expected state) candidates
  match exact.successes with
  | [] =>
      match firstBlockingFailure? exact.failures with
      | some error => .error error
      | none =>
          let coercible := collectCandidateAttempts
            (tryCoercibleFunctionCandidate context argumentType expected state)
            candidates
          selectCandidateSearch name candidates exact.failures coercible
  | _ => selectCandidateSearch name candidates [] exact

def selectFunctionCandidate (context : Context) (name : String)
    (argumentType : Ty) (expected : Option Ty) (state : State) :
    Except Error (Ty × State) := do
  selectFunctionCandidateFrom context name (← functionsNamed context name)
    argumentType expected state

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
