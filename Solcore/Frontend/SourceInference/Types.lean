import Solcore.Frontend.ProgramLoading
import Solcore.Frontend.ProgramSignatures
import Solcore.Frontend.SourceInference.TypedIR
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

/-- The lexical portion of inference state.  Restoring this snapshot leaves
identity allocators and every accumulated semantic fact untouched. -/
structure LexicalScope where
  locals : TypeSystem.Environment
  binders : List TypedBinder
  deriving Repr, DecidableEq

/-- Mutable inference information threaded through a source body. -/
structure State where
  owner : Resolved.DeclarationId
  inference : InferState
  locals : TypeSystem.Environment
  inputs : List TypedBinder
  localBinders : List TypedBinder
  nextLocal : Nat
  nextOccurrence : Nat := 0
  nodes : List Node := []
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

private def initialBinders (owner : Resolved.DeclarationId)
    (locals : TypeSystem.Environment) : List TypedBinder :=
  locals.mapIdx fun index entry => {
    id := { owner, binderIndex := index }
    name := entry.1
    scheme := entry.2
  }

def initial (owner : Resolved.DeclarationId)
    (locals : TypeSystem.Environment := []) : State :=
  let binders := initialBinders owner locals
  {
    owner
    inference := .initial locals.nextVariable
    locals
    inputs := binders
    localBinders := binders
    nextLocal := locals.length
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

/-- Compatibility helper for the pre-typed-IR traversal.  It replaces only the
type environment; typed traversal should use `lexicalScope` and
`restoreLexicalScope` so its binder scope remains aligned. -/
def withLocals (state : State) (locals : TypeSystem.Environment) : State :=
  { state with locals }

/-- Resolve the innermost stable binder carrying a source name. -/
def lookupBinder? (state : State) (name : String) : Option TypedBinder :=
  state.localBinders.find? fun binder => binder.name == name

/-- Capture only the name/type and stable-binder portion of the current lexical
scope. -/
def lexicalScope (state : State) : LexicalScope := {
  locals := state.locals
  binders := state.localBinders
}

/-- Leave a nested lexical scope without reusing any local, occurrence, or
requirement identities allocated inside it. -/
def restoreLexicalScope (state : State) (scope : LexicalScope) : State := {
  state with
  locals := scope.locals
  localBinders := scope.binders
}

/-- Allocate and enter one stable local binder in the current lexical scope. -/
def allocateBinder (state : State) (name : String) (scheme : Scheme)
    (span : Option Syntax.SourceSpan := none) : TypedBinder × State :=
  let binder : TypedBinder := {
    id := { owner := state.owner, binderIndex := state.nextLocal }
    name
    scheme
    span
  }
  (binder, {
    state with
    locals := (name, scheme) :: state.locals
    localBinders := binder :: state.localBinders
    nextLocal := state.nextLocal + 1
  })

private def allocateOccurrence (state : State) : OccurrenceId × State :=
  let id : OccurrenceId := { owner := state.owner, index := state.nextOccurrence }
  (id, { state with nextOccurrence := state.nextOccurrence + 1 })

/-- Allocate one expression occurrence from the declaration-wide node stream. -/
def allocateExpressionId (state : State) : ExpressionId × State :=
  let (occurrence, state) := state.allocateOccurrence
  (⟨occurrence⟩, state)

/-- Allocate one statement occurrence from the same declaration-wide node
stream used by expressions. -/
def allocateStatementId (state : State) : StatementId × State :=
  let (occurrence, state) := state.allocateOccurrence
  (⟨occurrence⟩, state)

/-- Append one already allocated node, preserving source-inference order. -/
def recordNode (state : State) (node : Node) : State :=
  { state with nodes := state.nodes ++ [node] }

/-- Modify one expression node without permitting its identity or category to
change.  Missing identities leave the table unchanged. -/
def modifyExpressionNode (state : State) (id : ExpressionId)
    (modify : ExpressionNode → ExpressionNode) : State :=
  { state with nodes := state.nodes.map fun
      | .expression node =>
          if node.id = id then
            .expression { modify node with id }
          else
            .expression node
      | .statement node => .statement node }

/-- Modify one statement node without permitting its identity or category to
change.  Missing identities leave the table unchanged. -/
def modifyStatementNode (state : State) (id : StatementId)
    (modify : StatementNode → StatementNode) : State :=
  { state with nodes := state.nodes.map fun
      | .expression node => .expression node
      | .statement node =>
          if node.id = id then
            .statement { modify node with id }
          else
            .statement node }

/-- Materialize the additive typed-source carrier for the requested roots. -/
def toTypedSource (state : State) (roots : List NodeId) : TypedSource := {
  owner := state.owner
  inputs := state.inputs
  roots
  nodes := state.nodes
}

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
