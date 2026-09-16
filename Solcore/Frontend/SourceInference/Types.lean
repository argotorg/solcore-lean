import Solcore.Frontend.ProgramLoading
import Solcore.Frontend.ProgramSignatures
import Solcore.Frontend.TypedTraitResolution
import Solcore.TypeSystem.Inference

/-! Shared data and solver boundaries for source-connected inference. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceInference

open TypeSystem

/-- Evidence retained at the source-checking boundary. -/
inductive PredicateEvidence where
  | assumption (predicate : ProgramPredicate)
  | implementation (evidence : TypedTraitResolution.Evidence)
  deriving Repr, BEq

/-- Failures reported by the executable source inference slice. -/
inductive Error where
  | unknownVariable (name : String)
  | noMatchingOverload
      (name : String) (candidates : List Resolved.DeclarationId)
  | ambiguousOverload
      (name : String) (candidates : List Resolved.DeclarationId)
  | malformedFunctionType (declaration : Resolved.DeclarationId)
  | malformedLambdaParameter (index : Nat)
  | duplicateLambdaParameter (name : String)
  | missingInitializer (name : String)
  | typeResolution (error : ProgramTypeResolutionError)
  | unification (error : Unification.Error)
  | noTraitImplementation (predicate : ProgramPredicate)
  | inconclusiveTrait
      (reason : TraitResolution.InconclusiveReason
        Resolved.DeclarationId Ty Resolved.DeclarationId)
  | ambiguousOperatorTrait
      (name : String) (candidates : List Resolved.DeclarationId)
  | operatorNotSupported (operator : String) (operand : Ty)
  | nonNumericLiteral (type : Ty)
  | unsupportedLiteral (kind : String)
  | unsupportedExpression (kind : String)
  | unsupportedStatement (kind : String)
  | nestingLimit
  deriving Repr, DecidableEq

/-- Static information shared by all expressions in one declaration. -/
structure Context where
  environment : ProgramEnvironment
  signatures : ProgramSignatures
  scope : ProgramTypeScope
  assumptions : List ProgramPredicate := []
  traitDepth : Nat := 32

/-- Mutable inference information threaded through a source body. -/
structure State where
  inference : InferState
  locals : TypeSystem.Environment
  numericVariables : List TypeVarId := []
  requirements : List ProgramPredicate := []
  deriving Repr, DecidableEq

/-- Final source-expression result after numeric defaulting and trait search. -/
structure Result where
  type : Ty
  substitution : Substitution
  predicates : List ProgramPredicate
  evidence : List PredicateEvidence
  deriving Repr, BEq

/-- One successfully checked top-level source function. -/
structure CheckedFunction where
  declaration : Resolved.DeclarationId
  type : Ty
  inferredBodyType : Ty
  substitution : Substitution
  predicates : List ProgramPredicate
  evidence : List PredicateEvidence
  deriving Repr, BEq

/-- A source function paired with its body-checking failure. -/
structure FunctionError where
  declaration : Resolved.DeclarationId
  error : Error
  deriving Repr, DecidableEq

/-- Errors from the full raw-workspace-to-checked-functions entry point. -/
inductive ProgramCheckError where
  | loading (error : ProgramLoadError)
  | signatures (error : ProgramSignatureError)
  | body (error : FunctionError)
  deriving Repr

namespace State

def initial (locals : TypeSystem.Environment := []) : State := {
  inference := .initial locals.nextVariable
  locals
}

def resolve (state : State) (type : Ty) : Ty :=
  state.inference.resolve type

def fresh (state : State) : Ty × State :=
  let (type, inference) := state.inference.fresh
  (type, { state with inference })

def withLocals (state : State) (locals : TypeSystem.Environment) : State :=
  { state with locals }

def addRequirement (state : State) (predicate : ProgramPredicate) : State :=
  { state with requirements := state.requirements ++ [predicate] }

def addRequirements (state : State) (predicates : List ProgramPredicate) : State :=
  { state with requirements := state.requirements ++ predicates }

end State

namespace Detail

def liftUnification {alpha : Type} :
    Except Unification.Error alpha → Except Error alpha
  | .ok value => .ok value
  | .error error => .error (.unification error)

def unify (state : State) (left right : Ty) : Except Error State := do
  let inference ← liftUnification (state.inference.unify left right)
  pure { state with inference }

def applyPredicate (state : State)
    (predicate : ProgramPredicate) : ProgramPredicate :=
  TypedTraitResolution.applySubstitution state.inference.substitution predicate

def requirementAssumption?
    (context : Context) (state : State) (goal : ProgramPredicate) : Bool :=
  context.assumptions.any fun assumption =>
    decide (applyPredicate state assumption = goal)

def solvePredicate (context : Context) (state : State)
    (source : ProgramPredicate) : Except Error PredicateEvidence :=
  let goal := applyPredicate state source
  if requirementAssumption? context state goal then
    .ok (.assumption goal)
  else
    match TypedTraitResolution.resolve context.signatures.implRules
        context.traitDepth goal with
    | { outcome := .success evidence, .. } => .ok (.implementation evidence)
    | { outcome := .noSolution, .. } => .error (.noTraitImplementation goal)
    | { outcome := .inconclusive reason, .. } => .error (.inconclusiveTrait reason)

def predicateSolvable (context : Context) (state : State)
    (predicate : ProgramPredicate) : Bool :=
  match solvePredicate context state predicate with
  | .ok _ => true
  | .error _ => false

def solvePredicates (context : Context) (state : State) :
    List ProgramPredicate → Except Error (List ProgramPredicate × List PredicateEvidence)
  | [] => .ok ([], [])
  | predicate :: rest => do
      let normalized := applyPredicate state predicate
      let evidence ← solvePredicate context state normalized
      let (predicates, evidenceRest) ← solvePredicates context state rest
      pure (normalized :: predicates, evidence :: evidenceRest)

def resolveSourceType (context : Context)
    (source : Syntax.TypeExpr) : Except Error Ty :=
  match resolveProgramTypeExpr context.environment context.scope source with
  | .ok type => .ok type
  | .error error => .error (.typeResolution error)

end Detail

end Solcore.Frontend.SourceInference
