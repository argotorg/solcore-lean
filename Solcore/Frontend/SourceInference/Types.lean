import Solcore.Frontend.ProgramLoading
import Solcore.Frontend.ProgramSignatures
import Solcore.Frontend.SourceInference.Identity
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

namespace PredicateEvidence

/-- The normalized obligation justified by this evidence. -/
def goal : PredicateEvidence → ProgramPredicate
  | .assumption predicate => predicate
  | .implementation (.byImpl predicate _ _) => predicate

end PredicateEvidence

/-- An unsolved obligation retained independently of its eventual evidence. -/
structure Requirement where
  id : RequirementId
  predicate : ProgramPredicate
  deriving Repr, BEq, DecidableEq

/-- Append-only checkpoint used by speculative candidate evaluation. -/
structure RequirementMark where
  count : Nat
  deriving Repr, BEq, DecidableEq

/-- A normalized obligation paired with the evidence selected at finalization. -/
structure SolvedRequirement where
  id : RequirementId
  predicate : ProgramPredicate
  evidence : PredicateEvidence
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
  | ambiguousImportedNamespace
      (name : String) (candidates : List Workspace.ModuleId)
  | ambiguousCoercion
      (source target : Ty) (firstPath secondPath : List Ty)
  | coercionDepthLimit (source target : Ty) (limit : Nat)
  | importVisibility (errors : List ProgramImportError)
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
  coercionDepth : Nat := 4

/-- Mutable inference information threaded through a source body. -/
structure State where
  inference : InferState
  locals : TypeSystem.Environment
  numericVariables : List TypeVarId := []
  nextRequirement : Nat := 0
  requirements : List Requirement := []
  deriving Repr, DecidableEq

/-- Final source-expression result after numeric defaulting and trait search. -/
structure Result where
  type : Ty
  substitution : Substitution
  solvedRequirements : List SolvedRequirement
  deriving Repr, BEq

/-- One successfully checked top-level source function. -/
structure CheckedFunction where
  declaration : Resolved.DeclarationId
  type : Ty
  inferredBodyType : Ty
  substitution : Substitution
  solvedRequirements : List SolvedRequirement
  deriving Repr, BEq

namespace Result

/-- Backward-compatible predicate projection in requirement order. -/
def predicates (result : Result) : List ProgramPredicate :=
  result.solvedRequirements.map (·.predicate)

/-- Backward-compatible evidence projection in requirement order. -/
def evidence (result : Result) : List PredicateEvidence :=
  result.solvedRequirements.map (·.evidence)

end Result

namespace CheckedFunction

/-- Backward-compatible predicate projection in requirement order. -/
def predicates (function : CheckedFunction) : List ProgramPredicate :=
  function.solvedRequirements.map (·.predicate)

/-- Backward-compatible evidence projection in requirement order. -/
def evidence (function : CheckedFunction) : List PredicateEvidence :=
  function.solvedRequirements.map (·.evidence)

end CheckedFunction

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

/-- Canonical states allocate every function-local requirement ID exactly once
and in append order. -/
def RequirementsWellFormed (state : State) : Prop :=
  state.requirements.map (·.id.index) = List.range state.nextRequirement

def fresh (state : State) : Ty × State :=
  let (type, inference) := state.inference.fresh
  (type, { state with inference })

def withLocals (state : State) (locals : TypeSystem.Environment) : State :=
  { state with locals }

def addRequirementWithId (state : State) (predicate : ProgramPredicate) :
    RequirementId × State :=
  let id : RequirementId := ⟨state.nextRequirement⟩
  (id, {
    state with
    nextRequirement := state.nextRequirement + 1
    requirements := state.requirements ++ [{ id, predicate }]
  })

def addRequirement (state : State) (predicate : ProgramPredicate) : State :=
  (state.addRequirementWithId predicate).2

def addRequirementsWithIds : State → List ProgramPredicate →
    List RequirementId × State
  | state, [] => ([], state)
  | state, predicate :: rest =>
      let (id, state) := state.addRequirementWithId predicate
      let (ids, state) := addRequirementsWithIds state rest
      (id :: ids, state)

def addRequirements (state : State) (predicates : List ProgramPredicate) : State :=
  (state.addRequirementsWithIds predicates).2

def requirementMark (state : State) : RequirementMark :=
  ⟨state.requirements.length⟩

def requirementsSince (state : State) (mark : RequirementMark) :
    List Requirement :=
  state.requirements.drop mark.count

def requirementCountSince (state : State) (mark : RequirementMark) : Nat :=
  state.requirements.length - mark.count

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

def solveNormalizedPredicate (context : Context) (state : State)
    (goal : ProgramPredicate) : Except Error PredicateEvidence :=
  if requirementAssumption? context state goal then
    .ok (.assumption goal)
  else
    match TypedTraitResolution.resolve context.signatures.implRules
        context.traitDepth goal with
    | { outcome := .success evidence, .. } => .ok (.implementation evidence)
    | { outcome := .noSolution, .. } => .error (.noTraitImplementation goal)
    | { outcome := .inconclusive reason, .. } => .error (.inconclusiveTrait reason)

def solvePredicate (context : Context) (state : State)
    (source : ProgramPredicate) : Except Error PredicateEvidence :=
  solveNormalizedPredicate context state (applyPredicate state source)

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

def solveRequirements (context : Context) (state : State) :
    List Requirement → Except Error (List SolvedRequirement)
  | [] => .ok []
  | requirement :: rest => do
      let predicate := applyPredicate state requirement.predicate
      let evidence ← solveNormalizedPredicate context state predicate
      let solved ← solveRequirements context state rest
      pure ({ id := requirement.id, predicate, evidence } :: solved)

def resolveSourceType (context : Context)
    (source : Syntax.TypeExpr) : Except Error Ty :=
  match resolveProgramTypeExpr context.environment context.scope source with
  | .ok type => .ok type
  | .error error => .error (.typeResolution error)

end Detail

end Solcore.Frontend.SourceInference
