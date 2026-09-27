import Solcore.Frontend.ProgramLoading
import Solcore.Frontend.ProgramSignatureFormation
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
  | builtinFunctionArityMismatch
      (function : BuiltinFunctionId) (expected actual : Nat)
  | malformedFunctionType (declaration : Resolved.DeclarationId)
  | malformedLambdaParameter (index : Nat)
  | duplicateLambdaParameter (name : String)
  | missingInitializer (name : String)
  | typeResolution (error : ProgramTypeResolutionError)
  | typeFormation (error : ProgramSignatureFormationError)
  | unification (error : Unification.Error)
  | noTraitImplementation (predicate : ProgramPredicate)
  | inconclusiveTrait
      (reason : TraitResolution.InconclusiveReason
        ProgramTraitId Ty ProgramImplId)
  | ambiguousOperatorTrait
      (name : String) (candidates : List Resolved.DeclarationId)
  | missingOperatorTraitCatalog (trait : Resolved.DeclarationId)
  | missingOperatorTraitMethod
      (trait : Resolved.DeclarationId) (name : String)
  | duplicateOperatorTraitMethod
      (trait : Resolved.DeclarationId) (name : String) (count : Nat)
  | operatorTraitArityMismatch
      (trait : Resolved.DeclarationId) (expected actual : Nat)
  | operatorTraitMethodSignatureMismatch
      (trait : Resolved.DeclarationId) (name : String)
      (expectedParameters actualParameters : List Ty)
      (expectedReturns actualReturns : List Ty)
  | missingCoercionTraitCatalog (trait : Resolved.DeclarationId)
  | duplicateCoercionTraitMethod
      (trait : Resolved.DeclarationId) (count : Nat)
  | coercionTraitArityMismatch
      (trait : Resolved.DeclarationId) (expected actual : Nat)
  | coercionTraitMethodSignatureMismatch
      (trait : Resolved.DeclarationId)
      (expectedParameters actualParameters : List Ty)
      (expectedReturns actualReturns : List Ty)
  | ambiguousImportedNamespace
      (name : String) (candidates : List Workspace.ModuleId)
  | ambiguousCoercion
      (source target : Ty) (firstPath secondPath : List Ty)
  | coercionDepthLimit (source target : Ty) (limit : Nat)
  | importVisibility (errors : List ProgramImportError)
  | operatorNotSupported (operator : String) (operand : Ty)
  | unsupportedIntegerLiteralTarget
      (expression : ExpressionId) (type : Ty)
  | missingIntegerLiteralRequirement
      (expression : ExpressionId) (requirement : RequirementId)
  | integerLiteralRequirementPredicateMismatch
      (expression : ExpressionId) (requirement : RequirementId)
      (expected actual : ProgramPredicate)
  | nodeOwnerMismatch
      (expected : Resolved.DeclarationId) (actual : OccurrenceId)
  | duplicateOccurrence (occurrence : OccurrenceId)
  | localIdentityOwnerMismatch
      (expected : Resolved.DeclarationId) (actual : Resolved.LocalId)
  | duplicateLocalIdentity (id : Resolved.LocalId)
  | duplicatePrimaryRequirement (id : RequirementId)
  | duplicateRequirementLedgerRow (id : RequirementId)
  | missingRequirementLedgerRow (id : RequirementId)
  | unattachedRequirementLedgerRow (id : RequirementId)
  | duplicateLocalSchemeTemplate (id : RequirementId)
  | duplicateLocalSchemeAssumption (id : RequirementId)
  | missingLocalSchemeAssumption (id : RequirementId)
  | unownedLocalSchemeAssumption (id : RequirementId)
  | missingLocalSchemeRequirement (id : RequirementId)
  | localSchemeTemplatePredicateMismatch
      (id : RequirementId) (expected actual : ProgramPredicate)
  | missingLocalSchemePrimaryRequirement (id : RequirementId)
  | localSchemeTemplateOutOfScope
      (id : RequirementId) (initializer occurrence : NodeId)
  | missingRoot (root : NodeId)
  | missingChild (parent child : NodeId)
  | duplicateIncomingNode (id : NodeId)
  | unreachableNode (id : NodeId)
  | matchScrutineeArityMismatch (expected actual : Nat)
  | constructorNeedsExpectedType (name : String)
  | unknownConstructor (qualifiers : List String) (name : String)
  | ambiguousConstructor
      (qualifiers : List String) (name : String)
      (candidates : List ProgramDataConstructorId)
  | constructorArityMismatch
      (constructor : ProgramDataConstructorId) (expected actual : Nat)
  | constructorResultMismatch
      (constructor : ProgramDataConstructorId) (expected actual : Ty)
  | invalidAssignmentTarget (span : Syntax.SourceSpan)
  | controlOutsideLoop (kind : String)
  | duplicatePatternBinder (name : String)
  | unsupportedPattern (span : Syntax.SourceSpan) (kind : String)
  | nonNumericPatternType (span : Syntax.SourceSpan) (type : Ty)
  | nonReturningMatchArm (span : Syntax.SourceSpan)
  | nonReturningMatchDefault (span : Syntax.SourceSpan)
  | nonExhaustiveMatch (span : Syntax.SourceSpan)
  | nonTerminalMatch (span : Syntax.SourceSpan)
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
  /-- Canonical rigid parameters available to source-level type annotations in
  the current declaration. -/
  typeParameters : List TypeSystem.TypeParameterId := []
  assumptions : List ProgramPredicate := []
  traitDepth : Nat := 32
  coercionDepth : Nat := 4
  /-- Lexical loop nesting used to reject control statements which would
  otherwise escape a function or lambda boundary. -/
  loopDepth : Nat := 0

/-- The lexical portion of inference state.  Restoring this snapshot leaves
identity allocators and every accumulated semantic fact untouched. -/
structure LexicalScope where
  locals : TypeSystem.Environment
  binders : List TypedBinder
  deriving Repr, DecidableEq

/-- The identity and current semantic type of one inferred expression.

Resolution helpers carry these together so that every coercion, overload
requirement, and integer-literal requirement can be returned to the exact
source occurrence that introduced it. -/
structure InferredExpression where
  id : ExpressionId
  type : Ty
  deriving Repr, BEq, DecidableEq

/-- A flexible builtin-`Int` target together with its source occurrence and
the unique requirement allocated when that integer literal was recorded. -/
structure IntegerLiteralOrigin where
  metavariable : TypeVarId
  expression : ExpressionId
  requirement : RequirementId
  deriving Repr, BEq, DecidableEq

/-- A numeric pattern's fresh builtin-`Int` target.  Unlike expression
literal origins, a target which is still flexible after the whole body has
been inferred is defaulted to Word during finalization. -/
structure IntegerPatternOrigin where
  metavariable : TypeVarId
  span : Syntax.SourceSpan
  requirement : RequirementId
  deriving Repr, BEq, DecidableEq

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
  integerLiterals : List IntegerLiteralOrigin := []
  integerPatterns : List IntegerPatternOrigin := []
  nextRequirement : Nat := 0
  requirements : List Requirement := []
  /-- Requirement identities introduced by selected direct declaration calls.
  This provenance lets local generalization abstract only proof-only `where`
  obligations, while literal, operator, and coercion requirements continue to
  block generalization. -/
  directCallRequirements : List RequirementId := []
  /-- Declaration-local requirements abstracted into qualified local schemes.
  They stay in the canonical requirement ledger, but finalization retains them
  as assumptions instead of attempting whole-function class resolution. -/
  localSchemeAssumptions : List RequirementId := []
  deriving Repr, DecidableEq

/-- Final source-expression result after literal validation and trait search. -/
structure Result where
  type : Ty
  substitution : Substitution
  solvedRequirements : List SolvedRequirement
  typedSource : TypedSource
  deriving Repr, BEq

/-- One successfully checked top-level source function. -/
structure CheckedFunction where
  declaration : Resolved.DeclarationId
  type : Ty
  inferredBodyType : Ty
  /-- Whether the canonical source result is available during staged
  evaluation.  This marker is intentionally independent of its semantic
  result type. -/
  returnComptime : Bool := false
  substitution : Substitution
  solvedRequirements : List SolvedRequirement
  typedBody : TypedSource
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

/-- The declaration-scoped part of inference state that no body traversal may
change. -/
structure Header where
  owner : Resolved.DeclarationId
  inputs : List TypedBinder
  deriving Repr, DecidableEq

/-- Project the immutable declaration-scoped portion of inference state. -/
def header (state : State) : Header := {
  owner := state.owner
  inputs := state.inputs
}

private def initialBinders (owner : Resolved.DeclarationId)
    (locals : TypeSystem.Environment) (inputComptime : List Bool) :
    List TypedBinder :=
  locals.mapIdx fun index entry => {
    id := { owner, binderIndex := index }
    name := entry.1
    scheme := entry.2
    comptime := inputComptime.getD index false
  }

def initial (owner : Resolved.DeclarationId)
    (locals : TypeSystem.Environment := [])
    (inputComptime : List Bool := []) : State :=
  let binders := initialBinders owner locals inputComptime
  {
    owner
    inference := .initial locals.nextVariable
    locals
    inputs := binders
    localBinders := binders
    nextLocal := locals.length
  }

theorem initial_inputs_definition (owner : Resolved.DeclarationId)
    (locals : TypeSystem.Environment) (inputComptime : List Bool) :
    (initial owner locals inputComptime).inputs =
      locals.mapIdx fun index entry => {
        id := { owner, binderIndex := index }
        name := entry.1
        scheme := entry.2
        comptime := inputComptime.getD index false
      } := by
  rfl

/-- Reconstruct the canonical inference environment from stable lexical
binders.  `State.locals` remains as a compatibility cache, but generalization
uses this projection so stale cached schemes cannot change which variables
are quantified. -/
def binderEnvironment (state : State) : TypeSystem.Environment :=
  state.localBinders.map fun binder => (binder.name, binder.scheme)

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
    (span : Option Syntax.SourceSpan := none) (comptime : Bool := false)
    (schemeRequirements : List LocalSchemeRequirement := []) :
    TypedBinder × State :=
  let binder : TypedBinder := {
    id := { owner := state.owner, binderIndex := state.nextLocal }
    name
    scheme
    schemeRequirements
    comptime
    span
  }
  (binder, {
    state with
    locals := (name, scheme) :: state.locals
    localBinders := binder :: state.localBinders
    nextLocal := state.nextLocal + 1
    localSchemeAssumptions := state.localSchemeAssumptions ++
      schemeRequirements.map fun requirement => requirement.templateRequirement
  })

/-- Reserve one stable declaration-owned local identity without making it
source-visible.  Terminal match lowering uses this identity for its once-only
scrutinee binding; lexical lookup must never observe it. -/
def allocateHiddenLocal (state : State) : Resolved.LocalId × State :=
  let id : Resolved.LocalId := {
    owner := state.owner
    binderIndex := state.nextLocal
  }
  (id, { state with nextLocal := state.nextLocal + 1 })

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

/-- Record that these freshly allocated requirements came from the selected
direct declaration call rather than from an operational language feature. -/
def markDirectCallRequirements (state : State)
    (requirements : List RequirementId) : State := {
  state with
  directCallRequirements := state.directCallRequirements ++ requirements
}

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
    match TypedTraitResolution.resolve context.signatures.resolutionRules
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
      let evidence ← solveNormalizedPredicate context state normalized
      let (predicates, evidenceRest) ← solvePredicates context state rest
      pure (normalized :: predicates, evidence :: evidenceRest)

/-- Select evidence for one ledger row.  Qualified-local templates are scoped
assumptions; every other row follows ordinary trait resolution. -/
def solveRequirementEvidence (context : Context) (state : State)
    (requirement : Requirement) : Except Error PredicateEvidence :=
  let predicate := applyPredicate state requirement.predicate
  if state.localSchemeAssumptions.contains requirement.id then
    pure (.assumption predicate)
  else
    solveNormalizedPredicate context state predicate

def solveRequirements (context : Context) (state : State) :
    List Requirement → Except Error (List SolvedRequirement)
  | [] => .ok []
  | requirement :: rest => do
      let predicate := applyPredicate state requirement.predicate
      let evidence ← solveRequirementEvidence context state requirement
      let solved ← solveRequirements context state rest
      pure ({ id := requirement.id, predicate, evidence } :: solved)

def resolveSourceType (context : Context)
    (source : Syntax.TypeExpr) : Except Error Ty :=
  match resolveProgramTypeExpr context.environment context.scope source with
  | .ok type =>
      match validateResolvedTypeFormation context.signatures
          context.scope.genericOwner context.typeParameters type with
      | .ok () => .ok type
      | .error error => .error (.typeFormation error)
  | .error error => .error (.typeResolution error)

/-- Successful source-type resolution now certifies rigid scope, nominal
catalog membership and arity, structural formation, and absence of recovery
or flexible inference types. -/
theorem resolveSourceType_success_formation
    {context : Context} {source : Syntax.TypeExpr} {type : Ty}
    (success : resolveSourceType context source = .ok type) :
    SignatureTypeFormationValidated context.signatures
      context.scope.genericOwner context.typeParameters type := by
  unfold resolveSourceType at success
  cases resolution : resolveProgramTypeExpr context.environment context.scope
      source with
  | error error =>
      simp [resolution] at success
  | ok resolved =>
      cases formation : validateResolvedTypeFormation context.signatures
          context.scope.genericOwner context.typeParameters resolved with
      | error error =>
          simp [resolution, formation] at success
      | ok formationUnit =>
          cases formationUnit
          simp [resolution, formation] at success
          subst type
          exact validateResolvedTypeFormation_success formation

end Detail

end Solcore.Frontend.SourceInference
