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

def functionsNamed (context : Context) (name : String) :
    List ProgramFunctionSignature :=
  let localCandidates := localFunctionsNamed context name
  if localCandidates.isEmpty then
    context.signatures.functions.filter fun signature => signature.name == name
  else
    localCandidates

def traitCandidates (context : Context) (name : String) :
    List ProgramDeclaration :=
  match context.environment.localTraitsNamed context.scope.currentModule name with
  | [] => context.environment.traitsNamed name
  | localCandidates => localCandidates

def operatorTrait? (context : Context) (name : String) :
    Except Error (Option Resolved.DeclarationId) :=
  let candidates := (traitCandidates context name).filter fun declaration =>
    declaration.genericParameters.length == 1
  match candidates with
  | [] => .ok none
  | [candidate] => .ok (some candidate.id)
  | _ => .error (.ambiguousOperatorTrait name (candidates.map (·.id)))

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

def withExpected (state : State) (actual : Ty) : Option Ty →
    Except Error (Ty × State)
  | none => .ok (state.resolve actual, state)
  | some expected => do
      let state ← unify state actual expected
      pure (state.resolve expected, state)

def functionParts? : Ty → Option (Ty × Ty)
  | .function parameter result => some (parameter, result)
  | _ => none

def allPredicatesSolvable (context : Context) (state : State) :
    List ProgramPredicate → Bool
  | [] => true
  | predicate :: rest =>
      predicateSolvable context state predicate &&
        allPredicatesSolvable context state rest

def tryFunctionCandidate (context : Context)
    (argumentType : Ty) (expected : Option Ty) (state : State)
    (signature : ProgramFunctionSignature) : Option (Ty × State) := do
  let instantiated := signature.scheme.instantiate state.inference.next
  let (parameter, result) ← functionParts? instantiated.body
  let inference := { state.inference with next := instantiated.next }
  let state := { state with inference }
  let state ← (unify state parameter argumentType).toOption
  let state ← match expected with
    | none => some state
    | some expected => (unify state result expected).toOption
  if allPredicatesSolvable context state instantiated.predicates then
    some (state.resolve result, state.addRequirements instantiated.predicates)
  else
    none

def successfulCandidates (context : Context) (argumentType : Ty)
    (expected : Option Ty) (state : State) :
    List ProgramFunctionSignature →
      List (ProgramFunctionSignature × Ty × State)
  | [] => []
  | signature :: rest =>
      match tryFunctionCandidate context argumentType expected state signature with
      | none => successfulCandidates context argumentType expected state rest
      | some (result, next) =>
          (signature, result, next) ::
            successfulCandidates context argumentType expected state rest

def selectFunctionCandidate (context : Context) (name : String)
    (argumentType : Ty) (expected : Option Ty) (state : State) :
    Except Error (Ty × State) :=
  let candidates := functionsNamed context name
  match successfulCandidates context argumentType expected state candidates with
  | [] => .error (.noMatchingOverload name (candidates.map (·.id)))
  | [(_, result, state)] => .ok (result, state)
  | successes =>
      .error (.ambiguousOverload name (successes.map fun success => success.1.id))

def calleeIdentifier? : Syntax.Expr → Option String
  | ⟨_, .identifier name⟩ => some name.value
  | ⟨_, .group inner⟩ => calleeIdentifier? inner
  | _ => none

end Solcore.Frontend.SourceInference.Detail
