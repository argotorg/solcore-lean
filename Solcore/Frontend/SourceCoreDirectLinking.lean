import Solcore.Frontend.SourceCoreElaboration
import Solcore.Frontend.SourceSpecializationWorklist
import Solcore.Frontend.ExecutableImplMethods
import Solcore.Core.Machine

/-!
Closed direct-call linking for specialized typed source.

The specialization worklist remains the authority for whole-program reachability
and direct-call metadata.  This layer defensively reconstructs that plan, then
elaborates every seed while replacing each direct call with a capture-free
`Resolved.Expr` expansion.  Argument expressions are evaluated from left to
right into fresh temporary identities before the callee's stable input
identities are aliased to those temporaries.

Direct-call signature predicates are proof-only in the current executable
fragment.  Each call must account positionally for its exact requirement IDs;
implementation evidence is threaded into the callee, while assumption evidence
must be discharged by a unique incoming witness with the same goal.  Evidence
never becomes a runtime Core value.  Deliberately narrow required-unary,
required-binary, and coercion profiles use closed `BitNot<T>`, arithmetic,
bitwise, `Eq<T>`, `Ord<T>` and `Coerce<From, To>` evidence to select, check, and
inline the uniquely named ground specialization of an implementation method;
unrelated methods in the same trait and implementation are ignored.  Operators
backed by ordinary prelude functions are represented as ordinary direct calls
before this layer.  Every other runtime-evidence shape remains an explicit
staged boundary.

The current Core has no recursive binding construct.  Accordingly, recursive
specialization cycles are rejected explicitly rather than assigned an
approximate runtime meaning.
-/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreDirectLinking

open SourceInference TypeSystem

abbrev SpecializationKey := SourceSpecialization.SpecializationKey
abbrev SpecializedFunction := SourceSpecialization.SpecializedFunction
abbrev WorklistError := SourceSpecializationWorklist.Error
abbrev CallEdge := SourceSpecializationWorklist.CallEdge
abbrev Plan := SourceSpecializationWorklist.Plan

/-- Exact failures at the validated specialization-to-Core linking boundary. -/
inductive Error where
  | budgetExhausted
      (next : SpecializationKey) (pendingCount : Nat)
  | worklist (error : WorklistError)
  | malformedCall (error : WorklistError)
  | nonCanonicalSpecialization (key : SpecializationKey)
  | duplicateSpecialization (key : SpecializationKey)
  | missingSpecialization (key : SpecializationKey)
  | specializationOrderMismatch
      (expected actual : List SpecializationKey)
  | callEdgesMismatch
      (expected actual : List CallEdge)
  | unresolvedAssumptions
      (key : SpecializationKey) (assumptions : List ProgramPredicate)
  | assumptionEvidenceCountMismatch
      (key : SpecializationKey) (expected actual : Nat)
  | assumptionEvidenceGoalMismatch
      (key : SpecializationKey) (index : Nat)
      (expected actual : ProgramPredicate)
  | unresolvedAssumptionEvidence
      (key : SpecializationKey) (predicate : ProgramPredicate)
  | callRequirementCountMismatch
      (caller : SpecializationKey) (occurrence : ExpressionId)
      (expected actual : Nat)
  | duplicateCallRequirement
      (caller : SpecializationKey) (occurrence : ExpressionId)
      (requirement : RequirementId)
  | missingSolvedRequirement
      (caller : SpecializationKey) (occurrence : ExpressionId)
      (requirement : RequirementId)
  | duplicateSolvedRequirements
      (caller : SpecializationKey) (occurrence : ExpressionId)
      (requirement : RequirementId) (count : Nat)
  | callRequirementPredicateMismatch
      (caller : SpecializationKey) (occurrence : ExpressionId)
      (requirement : RequirementId)
      (expected actual : ProgramPredicate)
  | callRequirementEvidenceGoalMismatch
      (caller : SpecializationKey) (occurrence : ExpressionId)
      (requirement : RequirementId)
      (expected actual : ProgramPredicate)
  | unaryRequirementCountMismatch
      (caller : SpecializationKey) (occurrence : ExpressionId)
      (expected actual : Nat)
  | duplicateUnaryRequirement
      (caller : SpecializationKey) (occurrence : ExpressionId)
      (requirement : RequirementId)
  | unaryRequirementPredicateMismatch
      (caller : SpecializationKey) (occurrence : ExpressionId)
      (requirement : RequirementId)
      (expected actual : ProgramPredicate)
  | unaryRequirementEvidenceGoalMismatch
      (caller : SpecializationKey) (occurrence : ExpressionId)
      (requirement : RequirementId)
      (expected actual : ProgramPredicate)
  | unsupportedRuntimeUnary
      (caller : SpecializationKey) (occurrence : ExpressionId)
      (operator : Syntax.UnaryOp)
  | runtimeUnaryEvidenceUnresolved
      (caller : SpecializationKey) (occurrence : ExpressionId)
      (requirement : RequirementId) (predicate : ProgramPredicate)
  | runtimeUnaryTraitNameMismatch
      (caller : SpecializationKey) (occurrence : ExpressionId)
      (expected actual : String)
  | runtimeUnaryInputTypesMismatch
      (caller : SpecializationKey) (occurrence : ExpressionId)
      (expected actual : List Core.Ty)
  | runtimeUnaryResultTypeMismatch
      (caller : SpecializationKey) (occurrence : ExpressionId)
      (expected actual : Core.Ty)
  | binaryRequirementCountMismatch
      (caller : SpecializationKey) (occurrence : ExpressionId)
      (expected actual : Nat)
  | duplicateBinaryRequirement
      (caller : SpecializationKey) (occurrence : ExpressionId)
      (requirement : RequirementId)
  | binaryRequirementPredicateMismatch
      (caller : SpecializationKey) (occurrence : ExpressionId)
      (requirement : RequirementId)
      (expected actual : ProgramPredicate)
  | binaryRequirementEvidenceGoalMismatch
      (caller : SpecializationKey) (occurrence : ExpressionId)
      (requirement : RequirementId)
      (expected actual : ProgramPredicate)
  | unsupportedRuntimeBinary
      (caller : SpecializationKey) (occurrence : ExpressionId)
      (operator : Syntax.BinaryOp)
  | runtimeBinaryEvidenceUnresolved
      (caller : SpecializationKey) (occurrence : ExpressionId)
      (requirement : RequirementId) (predicate : ProgramPredicate)
  | executableImplMethod
      (caller : SpecializationKey) (occurrence : ExpressionId)
      (error : ExecutableImplMethods.Error)
  | runtimeBinaryTraitNameMismatch
      (caller : SpecializationKey) (occurrence : ExpressionId)
      (expected actual : String)
  | runtimeBinaryInputTypesMismatch
      (caller : SpecializationKey) (occurrence : ExpressionId)
      (expected actual : List Core.Ty)
  | runtimeBinaryResultTypeMismatch
      (caller : SpecializationKey) (occurrence : ExpressionId)
      (expected actual : Core.Ty)
  | coercionRequirementEvidenceGoalMismatch
      (caller : SpecializationKey) (occurrence : ExpressionId)
      (requirement : RequirementId)
      (expected actual : ProgramPredicate)
  | coercionMethodRequirementCountMismatch
      (caller : SpecializationKey) (occurrence : ExpressionId)
      (primary : RequirementId) (expected actual : Nat)
  | coercionMethodRequirementPredicateMismatch
      (caller : SpecializationKey) (occurrence : ExpressionId)
      (requirement : RequirementId)
      (expected actual : ProgramPredicate)
  | runtimeCoercionEvidenceUnresolved
      (caller : SpecializationKey) (occurrence : ExpressionId)
      (requirement : RequirementId) (predicate : ProgramPredicate)
  | runtimeCoercionTraitNameMismatch
      (caller : SpecializationKey) (occurrence : ExpressionId)
      (requirement : RequirementId) (expected actual : String)
  | runtimeCoercionPredicateMismatch
      (caller : SpecializationKey) (occurrence : ExpressionId)
      (requirement : RequirementId)
      (expectedSource expectedTarget : TypeSystem.Ty)
      (actual : ProgramPredicate)
  | runtimeCoercionInputTypesMismatch
      (caller : SpecializationKey) (occurrence : ExpressionId)
      (requirement : RequirementId) (expected actual : List Core.Ty)
  | runtimeCoercionResultTypeMismatch
      (caller : SpecializationKey) (occurrence : ExpressionId)
      (requirement : RequirementId) (expected actual : Core.Ty)
  | implMethodSourceCore
      (caller : SpecializationKey) (occurrence : ExpressionId)
      (method : ProgramImplMethodId)
      (error : SourceCoreElaboration.Error)
  | missingAssumptionEvidence
      (caller : SpecializationKey) (occurrence : ExpressionId)
      (requirement : RequirementId) (predicate : ProgramPredicate)
  | ambiguousAssumptionEvidence
      (caller : SpecializationKey) (occurrence : ExpressionId)
      (requirement : RequirementId) (predicate : ProgramPredicate)
      (count : Nat)
  | missingCallEdge
      (caller : SpecializationKey) (occurrence : ExpressionId)
  | duplicateCallEdges
      (caller : SpecializationKey) (occurrence : ExpressionId) (count : Nat)
  | callEdgeCalleeMismatch
      (caller : SpecializationKey) (occurrence : ExpressionId)
      (edgeCallee resolvedCallee : SpecializationKey)
  | indirectCall (occurrence : ExpressionId)
  | recursiveCallCycle (key : SpecializationKey)
  | linkDepthLimit (key : SpecializationKey)
  | argumentArityMismatch
      (occurrence : ExpressionId) (expected actual : Nat)
  | callResultTypeMismatch
      (occurrence : ExpressionId) (expected actual : Core.Ty)
  | sourceCore (error : SourceCoreElaboration.Error)
  deriving Repr, DecidableEq

/-- One seed specialization linked to an independently checked open Core body. -/
structure LinkedEntry where
  key : SpecializationKey
  elaborated : SourceCoreElaboration.ElaboratedFunction
  deriving Repr

/-- Linked entries preserve worklist seed order, including repeated roots. -/
structure LinkedProgram where
  entries : List LinkedEntry
  deriving Repr

/-- Run a linked entry only when the supplied runtime values have exactly the
source input types and order retained by elaboration. -/
def LinkedEntry.run? (entry : LinkedEntry) (inputs : List Core.Value)
    (fuel : Nat) (store : Core.Store := []) :
    Option Core.StatefulRunResult :=
  if inputs.map Core.Value.type = entry.elaborated.inputs.values then
    some (Core.runStateful fuel
      (Core.State.initial entry.elaborated.core inputs store))
  else
    none

/-- First seed entry with a given canonical key. -/
def LinkedProgram.findEntry? (program : LinkedProgram)
    (key : SpecializationKey) : Option LinkedEntry :=
  program.entries.find? fun entry => decide (entry.key = key)

private def liftWorklistValidation : WorklistError → Error
  | error@(.missingCalleeNode _ _) => .malformedCall error
  | error@(.calleeNotDeclarationReference _ _) => .malformedCall error
  | error@(.calleeInstantiationDeclarationMismatch _ _ _) =>
      .malformedCall error
  | error@(.calleeInstantiationMetadataMismatch _ _ _) =>
      .malformedCall error
  | error@(.calleeNodeTypeMismatch _ _ _) => .malformedCall error
  | error@(.specializedCalleeTypeMismatch _ _ _) => .malformedCall error
  | error@(.specializedCalleeAssumptionsMismatch _ _ _) =>
      .malformedCall error
  | .indirectCall occurrence => .indirectCall occurrence
  | error => .worklist error

private def firstDuplicateKey : List SpecializationKey → Option SpecializationKey
  | [] => none
  | key :: rest =>
      if rest.contains key then some key else firstDuplicateKey rest

private def specializationKeys
    (specializations : List SpecializedFunction) : List SpecializationKey :=
  specializations.map (·.key)

private def lookupSpecialization? (plan : Plan)
    (key : SpecializationKey) : Option SpecializedFunction :=
  plan.specializations.find? fun specialized => decide (specialized.key = key)

private def exactSpecialization (plan : Plan)
    (key : SpecializationKey) : Except Error SpecializedFunction :=
  match lookupSpecialization? plan key with
  | none => .error (.missingSpecialization key)
  | some specialized => .ok specialized

private def validateCanonicalSpecializations (program : CheckedProgram) :
    List SpecializedFunction → Except Error Unit
  | [] => pure ()
  | specialized :: rest => do
      let canonical ← (SourceSpecializationWorklist.resolveRequest program {
        declaration := specialized.declaration
        parameterSubstitution := specialized.parameterSubstitution
      }).mapError liftWorklistValidation
      if canonical == specialized then
        validateCanonicalSpecializations program rest
      else
        throw (.nonCanonicalSpecialization specialized.key)

private def validateKnownEdgeKeys (plan : Plan) :
    List CallEdge → Except Error Unit
  | [] => pure ()
  | edge :: rest => do
      if (lookupSpecialization? plan edge.caller).isNone then
        throw (.missingSpecialization edge.caller)
      else if (lookupSpecialization? plan edge.callee).isNone then
        throw (.missingSpecialization edge.callee)
      else
        validateKnownEdgeKeys plan rest

private def seedRequests (plan : Plan) :
    List SpecializationKey →
      Except Error (List SourceSpecializationWorklist.Request)
  | [] => pure []
  | key :: rest => do
      let specialized ← exactSpecialization plan key
      pure ({
        declaration := specialized.declaration
        parameterSubstitution := specialized.parameterSubstitution
      } :: (← seedRequests plan rest))

/-- Reconstruct the complete worklist result from canonical roots.  This
simultaneously checks reachability/order, missing specializations, and the exact
per-occurrence call-edge list instead of trusting a supplied `Plan`. -/
def validatePlan (program : CheckedProgram) (plan : Plan) : Except Error Unit := do
  let keys := specializationKeys plan.specializations
  match firstDuplicateKey keys with
  | some key => throw (.duplicateSpecialization key)
  | none => pure ()
  validateCanonicalSpecializations program plan.specializations
  for key in plan.seedKeys do
    if (lookupSpecialization? plan key).isNone then
      throw (.missingSpecialization key)
  validateKnownEdgeKeys plan plan.callEdges
  let seeds ← seedRequests plan plan.seedKeys
  let rebuilt ← (SourceSpecializationWorklist.run program seeds
    plan.specializations.length).mapError liftWorklistValidation
  match rebuilt with
  | .budgetExhausted _ next _ =>
      throw (.missingSpecialization next)
  | .complete expected =>
      let expectedKeys := specializationKeys expected.specializations
      if expectedKeys != keys then
        throw (.specializationOrderMismatch expectedKeys keys)
      else if expected.callEdges != plan.callEdges then
        throw (.callEdgesMismatch expected.callEdges plan.callEdges)
      else
        pure ()

private def localIdsInExpressionForm : ExpressionForm → List Resolved.LocalId
  | .reference _ (.local binder) => [binder]
  | .lambda parameters _ _ => parameters.map (·.id)
  | _ => []

private def localIdsInNode : Node → List Resolved.LocalId
  | .expression node => localIdsInExpressionForm node.form
  | .statement node =>
      match node.form with
      | .letDecl binder _ => [binder.id]
      | _ => []

private def sourceLocalIds (source : TypedSource) : List Resolved.LocalId :=
  source.inputs.map (·.id) ++ source.nodes.flatMap localIdsInNode

/-- First binder index strictly greater than every local identity retained or
referenced anywhere in the validated specialization plan.  Including malformed
unbound references keeps generated temporaries from repairing them by capture. -/
private def freshBase (plan : Plan) : Nat :=
  plan.specializations.foldl (fun next specialized =>
    (sourceLocalIds specialized.function.typedBody).foldl
      (fun candidate id => Nat.max candidate (id.binderIndex + 1)) next) 0

private def freshTemporaries (owner : Resolved.DeclarationId)
    (base count : Nat) : List Resolved.LocalId :=
  (List.range count).map fun offset => {
    owner
    binderIndex := base + offset
  }

private def bindValues
    (bindings : List (Resolved.LocalId × Resolved.Expr))
    (body : Resolved.Expr) : Resolved.Expr :=
  bindings.foldr (fun binding rest =>
    .letE binding.1 binding.2 rest) body

private def aliasInputs (inputs : Resolved.Context)
    (temporaries : List Resolved.LocalId) (body : Resolved.Expr) :
    Resolved.Expr :=
  (inputs.zip temporaries).foldr (fun binding rest =>
    .letE binding.1.1 (.var binding.2) rest) body

private def exactCallEdge (plan : Plan) (caller : SpecializationKey)
    (occurrence : ExpressionId) : Except Error CallEdge :=
  let candidates := plan.callEdges.filter fun edge =>
    decide (edge.caller = caller && edge.occurrence = occurrence)
  match candidates with
  | [] => .error (.missingCallEdge caller occurrence)
  | [edge] => .ok edge
  | edges => .error (.duplicateCallEdges caller occurrence edges.length)

private def firstDuplicateRequirement :
    List RequirementId → Option RequirementId
  | [] => none
  | requirement :: rest =>
      if rest.contains requirement then some requirement
      else firstDuplicateRequirement rest

/-- Incoming witnesses correspond positionally to the specialized signature
assumptions.  A recursive call must receive actual implementation evidence;
forwarding another unresolved assumption would only move the proof hole. -/
private def validateAssumptionEvidenceGoals (key : SpecializationKey) :
    Nat → List ProgramPredicate → List PredicateEvidence →
      Except Error Unit
  | _, [], [] => pure ()
  | index, expected :: expectedRest, evidence :: evidenceRest => do
      let actual := evidence.goal
      if actual != expected then
        throw (.assumptionEvidenceGoalMismatch key index expected actual)
      match evidence with
      | .assumption predicate =>
          throw (.unresolvedAssumptionEvidence key predicate)
      | .implementation _ =>
          validateAssumptionEvidenceGoals key (index + 1) expectedRest
            evidenceRest
  | _, expected, evidence =>
      throw (.assumptionEvidenceCountMismatch key expected.length
        evidence.length)

private def validateAssumptionEvidence (key : SpecializationKey)
    (assumptions : List ProgramPredicate)
    (evidence : List PredicateEvidence) : Except Error Unit := do
  if assumptions.length != evidence.length then
    throw (.assumptionEvidenceCountMismatch key assumptions.length
      evidence.length)
  validateAssumptionEvidenceGoals key 0 assumptions evidence

private def exactSolvedRequirement (caller : SpecializedFunction)
    (occurrence : ExpressionId) (requirement : RequirementId) :
    Except Error SolvedRequirement :=
  let candidates := caller.function.solvedRequirements.filter fun solved =>
    decide (solved.id = requirement)
  match candidates with
  | [] => .error (.missingSolvedRequirement caller.key occurrence requirement)
  | [solved] => .ok solved
  | solved =>
      .error (.duplicateSolvedRequirements caller.key occurrence requirement
        solved.length)

/-- Replace a function-local assumption marker with the unique actual witness
supplied at this specialization invocation. -/
private def actualRequirementEvidence (caller : SpecializedFunction)
    (occurrence : ExpressionId) (requirement : RequirementId)
    (available : List PredicateEvidence) : PredicateEvidence →
      Except Error PredicateEvidence
  | evidence@(.implementation _) => pure evidence
  | .assumption predicate =>
      let candidates := available.filter fun evidence =>
        decide (evidence.goal = predicate)
      match candidates with
      | [] =>
          .error (.missingAssumptionEvidence caller.key occurrence requirement
            predicate)
      | [evidence] => .ok evidence
      | evidence =>
          .error (.ambiguousAssumptionEvidence caller.key occurrence
            requirement predicate evidence.length)

/-- Recover call evidence in the declaration instantiation's predicate order.
No operator, literal, or coercion requirement is accepted by this path. -/
private def callRequirementEvidence (caller : SpecializedFunction)
    (occurrence : ExpressionId) (available : List PredicateEvidence) :
    List RequirementId → List ProgramPredicate →
      Except Error (List PredicateEvidence)
  | [], [] => pure []
  | requirement :: requirements, predicate :: predicates => do
      let solved ← exactSolvedRequirement caller occurrence requirement
      if solved.predicate != predicate then
        throw (.callRequirementPredicateMismatch caller.key occurrence
          requirement predicate solved.predicate)
      let goal := solved.evidence.goal
      if goal != solved.predicate then
        throw (.callRequirementEvidenceGoalMismatch caller.key occurrence
          requirement solved.predicate goal)
      let evidence ← actualRequirementEvidence caller occurrence requirement
        available solved.evidence
      pure (evidence :: (← callRequirementEvidence caller occurrence
        available requirements predicates))
  | requirements, predicates =>
      throw (.callRequirementCountMismatch caller.key occurrence
        predicates.length requirements.length)

private def exactCallRequirementEvidence (caller : SpecializedFunction)
    (node : ExpressionNode) (available : List PredicateEvidence)
    (instantiation : DeclarationInstantiation) :
    Except Error (List PredicateEvidence) := do
  if node.requirements.length != instantiation.predicates.length then
    throw (.callRequirementCountMismatch caller.key node.id
      instantiation.predicates.length node.requirements.length)
  match firstDuplicateRequirement node.requirements with
  | some requirement =>
      throw (.duplicateCallRequirement caller.key node.id requirement)
  | none =>
      callRequirementEvidence caller node.id available node.requirements
        instantiation.predicates

private def exactRuntimeUnaryPrimaryEvidence (caller : SpecializedFunction)
    (node : ExpressionNode) (available : List PredicateEvidence) :
    Except Error (RequirementId × ProgramPredicate ×
      TypedTraitResolution.Evidence) := do
  let requirement ← match node.requirements with
    | requirement :: _ => pure requirement
    | [] => throw (.unaryRequirementCountMismatch caller.key node.id 1 0)
  let solved ← exactSolvedRequirement caller node.id requirement
  let goal := solved.evidence.goal
  if goal != solved.predicate then
    throw (.unaryRequirementEvidenceGoalMismatch caller.key node.id
      requirement solved.predicate goal)
  let evidence ← actualRequirementEvidence caller node.id requirement
    available solved.evidence
  match evidence with
  | .implementation implementation =>
      pure (requirement, solved.predicate, implementation)
  | .assumption predicate =>
      throw (.runtimeUnaryEvidenceUnresolved caller.key node.id requirement
        predicate)

private structure RuntimeUnaryProfile where
  traitName : String
  methodName : String

private def runtimeUnaryProfile? :
    Syntax.UnaryOp → Option RuntimeUnaryProfile
  | operator =>
      match SourceInference.Detail.unaryOperatorDispatch operator with
      | .traitMethod traitName methodName => some { traitName, methodName }
      | .function _ => none

private def runtimeUnaryResultType (operator : Syntax.UnaryOp)
    (operandType : Core.Ty) : Core.Ty :=
  if operator == .logicalNot then .bool else operandType

private def exactRuntimeBinaryPrimaryEvidence (caller : SpecializedFunction)
    (node : ExpressionNode) (available : List PredicateEvidence) :
    Except Error (RequirementId × ProgramPredicate ×
      TypedTraitResolution.Evidence) := do
  let requirement ← match node.requirements with
    | requirement :: _ => pure requirement
    | [] => throw (.binaryRequirementCountMismatch caller.key node.id 1 0)
  let solved ← exactSolvedRequirement caller node.id requirement
  let goal := solved.evidence.goal
  if goal != solved.predicate then
    throw (.binaryRequirementEvidenceGoalMismatch caller.key node.id
      requirement solved.predicate goal)
  let evidence ← actualRequirementEvidence caller node.id requirement
    available solved.evidence
  match evidence with
  | .implementation implementation =>
      pure (requirement, solved.predicate, implementation)
  | .assumption predicate =>
      throw (.runtimeBinaryEvidenceUnresolved caller.key node.id requirement
        predicate)

private def exactRuntimeMethodEvidenceRows
    (caller : SpecializedFunction) (node : ExpressionNode)
    (available : List PredicateEvidence)
    (countMismatch : Nat → Nat → Error)
    (predicateMismatch : RequirementId → ProgramPredicate →
      ProgramPredicate → Error)
    (goalMismatch : RequirementId → ProgramPredicate →
      ProgramPredicate → Error)
    (unresolved : RequirementId → ProgramPredicate → Error) :
    List RequirementId → List ProgramPredicate →
      Except Error (List TypedTraitResolution.Evidence)
  | [], [] => pure []
  | requirement :: requirements, predicate :: predicates => do
      let solved ← exactSolvedRequirement caller node.id requirement
      if solved.predicate != predicate then
        throw (predicateMismatch requirement predicate solved.predicate)
      let goal := solved.evidence.goal
      if goal != solved.predicate then
        throw (goalMismatch requirement solved.predicate goal)
      let evidence ← actualRequirementEvidence caller node.id requirement
        available solved.evidence
      let implementation ← match evidence with
        | .implementation implementation => pure implementation
        | .assumption actual => throw (unresolved requirement actual)
      pure (implementation :: (← exactRuntimeMethodEvidenceRows caller node
        available countMismatch predicateMismatch goalMismatch unresolved
        requirements predicates))
  | requirements, predicates =>
      throw (countMismatch predicates.length requirements.length)

private def exactRuntimeUnaryMethodEvidence (caller : SpecializedFunction)
    (node : ExpressionNode) (available : List PredicateEvidence)
    (predicates : List ProgramPredicate) :
    Except Error (List TypedTraitResolution.Evidence) := do
  let expectedCount := predicates.length + 1
  if node.requirements.length != expectedCount then
    throw (.unaryRequirementCountMismatch caller.key node.id expectedCount
      node.requirements.length)
  match firstDuplicateRequirement node.requirements with
  | some requirement =>
      throw (.duplicateUnaryRequirement caller.key node.id requirement)
  | none => pure ()
  exactRuntimeMethodEvidenceRows caller node available
    (fun expected actual =>
      .unaryRequirementCountMismatch caller.key node.id (expected + 1)
        (actual + 1))
    (fun requirement expected actual =>
      .unaryRequirementPredicateMismatch caller.key node.id requirement
        expected actual)
    (fun requirement expected actual =>
      .unaryRequirementEvidenceGoalMismatch caller.key node.id requirement
        expected actual)
    (fun requirement predicate =>
      .runtimeUnaryEvidenceUnresolved caller.key node.id requirement predicate)
    (node.requirements.drop 1) predicates

private def exactRuntimeBinaryMethodEvidence (caller : SpecializedFunction)
    (node : ExpressionNode) (available : List PredicateEvidence)
    (predicates : List ProgramPredicate) :
    Except Error (List TypedTraitResolution.Evidence) := do
  let expectedCount := predicates.length + 1
  if node.requirements.length != expectedCount then
    throw (.binaryRequirementCountMismatch caller.key node.id expectedCount
      node.requirements.length)
  match firstDuplicateRequirement node.requirements with
  | some requirement =>
      throw (.duplicateBinaryRequirement caller.key node.id requirement)
  | none => pure ()
  exactRuntimeMethodEvidenceRows caller node available
    (fun expected actual =>
      .binaryRequirementCountMismatch caller.key node.id (expected + 1)
        (actual + 1))
    (fun requirement expected actual =>
      .binaryRequirementPredicateMismatch caller.key node.id requirement
        expected actual)
    (fun requirement expected actual =>
      .binaryRequirementEvidenceGoalMismatch caller.key node.id requirement
        expected actual)
    (fun requirement predicate =>
      .runtimeBinaryEvidenceUnresolved caller.key node.id requirement predicate)
    (node.requirements.drop 1) predicates

private structure RuntimeBinaryProfile where
  traitName : String
  methodName : String

private def runtimeBinaryProfile? :
    Syntax.BinaryOp → Option RuntimeBinaryProfile
  | operator =>
      match SourceInference.Detail.binaryOperatorDispatch operator with
      | .traitMethod traitName methodName => some { traitName, methodName }
      | .function _ => none

private def runtimeBinaryResultType (operator : Syntax.BinaryOp)
    (operandType : Core.Ty) : Core.Ty :=
  if SourceInference.Detail.binaryResultIsBool operator then .bool
  else operandType

private def exactRuntimeCoercionPrimaryEvidence (caller : SpecializedFunction)
    (node : ExpressionNode) (step : CoercionStep)
    (available : List PredicateEvidence) :
    Except Error (ProgramPredicate × TypedTraitResolution.Evidence) := do
  let solved ← exactSolvedRequirement caller node.id step.requirement
  let goal := solved.evidence.goal
  if goal != solved.predicate then
    throw (.coercionRequirementEvidenceGoalMismatch caller.key node.id
      step.requirement solved.predicate goal)
  let evidence ← actualRequirementEvidence caller node.id step.requirement
    available solved.evidence
  match evidence with
  | .implementation implementation => pure (solved.predicate, implementation)
  | .assumption predicate =>
      throw (.runtimeCoercionEvidenceUnresolved caller.key node.id
        step.requirement predicate)

private def exactRuntimeCoercionMethodEvidence
    (caller : SpecializedFunction) (node : ExpressionNode)
    (step : CoercionStep) (available : List PredicateEvidence)
    (predicates : List ProgramPredicate) :
    Except Error (List TypedTraitResolution.Evidence) := do
  if step.methodRequirements.length != predicates.length then
    throw (.coercionMethodRequirementCountMismatch caller.key node.id
      step.requirement predicates.length step.methodRequirements.length)
  exactRuntimeMethodEvidenceRows caller node available
    (fun expected actual =>
      .coercionMethodRequirementCountMismatch caller.key node.id
        step.requirement expected actual)
    (fun requirement expected actual =>
      .coercionMethodRequirementPredicateMismatch caller.key node.id
        requirement expected actual)
    (fun requirement expected actual =>
      .coercionRequirementEvidenceGoalMismatch caller.key node.id requirement
        expected actual)
    (fun requirement predicate =>
      .runtimeCoercionEvidenceUnresolved caller.key node.id requirement predicate)
    step.methodRequirements predicates

private abbrev ExecutableMethodElaborator :=
  ExecutableImplMethods.CheckedMethod →
    Except Error SourceCoreElaboration.ElaboratedFunction

private def runtimeMethodPredicates (caller : SpecializedFunction)
    (node : ExpressionNode) (trait : ProgramTraitSignature)
    (goal : ProgramPredicate) (expectedTraitArity : Nat)
    (expectedName : String) : Except Error (List ProgramPredicate) := do
  let goalArity := goal.arguments.length + 1
  if goalArity != expectedTraitArity then
    throw (.executableImplMethod caller.key node.id
      (.evidenceGoalArityMismatch goal.trait expectedTraitArity goalArity))
  if trait.parameters.length != expectedTraitArity then
    throw (.executableImplMethod caller.key node.id
      (.traitArityMismatch trait.id expectedTraitArity
        trait.parameters.length))
  let method ← match trait.methods.filter fun method =>
      method.name == expectedName with
    | [] => throw (.executableImplMethod caller.key node.id
        (.missingTraitMethod trait.id expectedName))
    | [method] => pure method
    | methods => throw (.executableImplMethod caller.key node.id
        (.multipleTraitMethods trait.id methods.length))
  let substitution : ParameterSubstitution :=
    trait.parameters.zip (goal.subject :: goal.arguments)
  pure (method.wherePredicates.map
    (ProgramPredicate.applyParameters substitution))

/-- Turn one closed unary-operator witness into a checked, capture-free inline
plan.  The selected implementation method, rather than the operand's builtin
Core operation, is the runtime authority. -/
private def requiredUnaryPlan (program : CheckedProgram)
    (temporaryOwner : Resolved.DeclarationId) (temporaryBase : Nat)
    (elaborateMethod : ExecutableMethodElaborator)
    (caller : SpecializedFunction) (available : List PredicateEvidence)
    (node : ExpressionNode) (operator : Syntax.UnaryOp) :
    Except Error (SourceCoreElaboration.RequiredUnaryPlan Error) := do
  let profile ← match runtimeUnaryProfile? operator with
    | some profile => pure profile
    | none => throw (.unsupportedRuntimeUnary caller.key node.id operator)
  let (_, predicate, evidence) ←
    exactRuntimeUnaryPrimaryEvidence caller node available
  let traitId ← match predicate.trait with
    | .declaration id => pure id
    | .builtin id => throw (.executableImplMethod caller.key node.id
        (.builtinTraitNotExecutable id))
  let trait ← match program.signatures.trait? traitId with
    | some trait => pure trait
    | none => throw (.executableImplMethod caller.key node.id
        (.missingTrait traitId))
  if trait.name != profile.traitName then
    throw (.runtimeUnaryTraitNameMismatch caller.key node.id
      profile.traitName trait.name)
  let methodPredicates ← runtimeMethodPredicates caller node trait predicate
    1 profile.methodName
  let methodEvidence ← exactRuntimeUnaryMethodEvidence caller node available
    methodPredicates
  let method ←
    (ExecutableImplMethods.checkMethodWithEvidenceAndArity program evidence
      methodEvidence 1 profile.methodName).mapError fun error =>
        .executableImplMethod caller.key node.id error
  let elaborated ← elaborateMethod method
  let operandType ←
    (SourceCoreElaboration.lowerType (.occurrence node.id.occurrence)
      predicate.subject).mapError Error.sourceCore
  let expectedInputs := [operandType]
  if elaborated.inputs.values != expectedInputs then
    throw (.runtimeUnaryInputTypesMismatch caller.key node.id expectedInputs
      elaborated.inputs.values)
  let expectedResult := runtimeUnaryResultType operator operandType
  if elaborated.returnType != expectedResult then
    throw (.runtimeUnaryResultTypeMismatch caller.key node.id expectedResult
      elaborated.returnType)
  let nodeResult ←
    (SourceCoreElaboration.lowerType (.occurrence node.id.occurrence)
      node.type).mapError Error.sourceCore
  if elaborated.returnType != nodeResult then
    throw (.runtimeUnaryResultTypeMismatch caller.key node.id nodeResult
      elaborated.returnType)
  pure {
    operandType
    consumedRequirements := node.requirements
    build := fun operand =>
      let temporaries := freshTemporaries temporaryOwner temporaryBase 1
      let body := aliasInputs elaborated.inputs temporaries elaborated.resolved
      pure (bindValues (temporaries.zip [operand]) body)
  }

/-- Turn one closed operator witness into a checked, capture-free inline plan.
The implementation method body, not the specialized operand type, is the
runtime authority. -/
private def requiredBinaryPlan (program : CheckedProgram)
    (temporaryOwner : Resolved.DeclarationId) (temporaryBase : Nat)
    (elaborateMethod : ExecutableMethodElaborator)
    (caller : SpecializedFunction) (available : List PredicateEvidence)
    (node : ExpressionNode) (operator : Syntax.BinaryOp) :
    Except Error (SourceCoreElaboration.RequiredBinaryPlan Error) := do
  let profile ← match runtimeBinaryProfile? operator with
    | some profile => pure profile
    | none => throw (.unsupportedRuntimeBinary caller.key node.id operator)
  let (_, predicate, evidence) ←
    exactRuntimeBinaryPrimaryEvidence caller node available
  let traitId ← match predicate.trait with
    | .declaration id => pure id
    | .builtin id => throw (.executableImplMethod caller.key node.id
        (.builtinTraitNotExecutable id))
  let trait ← match program.signatures.trait? traitId with
    | some trait => pure trait
    | none => throw (.executableImplMethod caller.key node.id
        (.missingTrait traitId))
  if trait.name != profile.traitName then
    throw (.runtimeBinaryTraitNameMismatch caller.key node.id
      profile.traitName trait.name)
  let methodPredicates ← runtimeMethodPredicates caller node trait predicate
    1 profile.methodName
  let methodEvidence ← exactRuntimeBinaryMethodEvidence caller node available
    methodPredicates
  let method ←
    (ExecutableImplMethods.checkMethodWithEvidenceAndArity program evidence
      methodEvidence 1 profile.methodName).mapError fun error =>
        .executableImplMethod caller.key node.id error
  let elaborated ← elaborateMethod method
  let operandType ←
    (SourceCoreElaboration.lowerType (.occurrence node.id.occurrence)
      predicate.subject).mapError Error.sourceCore
  let expectedInputs := [operandType, operandType]
  if elaborated.inputs.values != expectedInputs then
    throw (.runtimeBinaryInputTypesMismatch caller.key node.id expectedInputs
      elaborated.inputs.values)
  let expectedResult := runtimeBinaryResultType operator operandType
  if elaborated.returnType != expectedResult then
    throw (.runtimeBinaryResultTypeMismatch caller.key node.id expectedResult
      elaborated.returnType)
  let nodeResult ←
    (SourceCoreElaboration.lowerType (.occurrence node.id.occurrence)
      node.type).mapError Error.sourceCore
  if elaborated.returnType != nodeResult then
    throw (.runtimeBinaryResultTypeMismatch caller.key node.id nodeResult
      elaborated.returnType)
  pure {
    leftType := operandType
    rightType := operandType
    consumedRequirements := node.requirements
    build := fun left right =>
      let temporaries := freshTemporaries temporaryOwner temporaryBase 2
      let body := aliasInputs elaborated.inputs temporaries elaborated.resolved
      pure (bindValues (temporaries.zip [left, right]) body)
  }

/-- Turn one closed `Coerce<From, To>` witness into a checked, capture-free
inline conversion.  Endpoint types validate the selected method; they never
invent the conversion's runtime behavior. -/
private def coercionPlan (program : CheckedProgram)
    (temporaryOwner : Resolved.DeclarationId) (temporaryBase : Nat)
    (elaborateMethod : ExecutableMethodElaborator)
    (caller : SpecializedFunction) (available : List PredicateEvidence)
    (node : ExpressionNode) (step : CoercionStep) :
    Except Error (SourceCoreElaboration.CoercionPlan Error) := do
  let (predicate, evidence) ←
    exactRuntimeCoercionPrimaryEvidence caller node step available
  let traitId ← match predicate.trait with
    | .declaration id => pure id
    | .builtin id => throw (.executableImplMethod caller.key node.id
        (.builtinTraitNotExecutable id))
  let trait ← match program.signatures.trait? traitId with
    | some trait => pure trait
    | none => throw (.executableImplMethod caller.key node.id
        (.missingTrait traitId))
  if trait.name != "Coerce" then
    throw (.runtimeCoercionTraitNameMismatch caller.key node.id
      step.requirement "Coerce" trait.name)
  if predicate.subject != step.source || predicate.arguments != [step.target] then
    throw (.runtimeCoercionPredicateMismatch caller.key node.id
      step.requirement step.source step.target predicate)
  let methodPredicates ← runtimeMethodPredicates caller node trait predicate
    2 "coerce"
  let methodEvidence ← exactRuntimeCoercionMethodEvidence caller node step
    available methodPredicates
  let method ←
    (ExecutableImplMethods.checkMethodWithEvidenceAndArity program evidence
      methodEvidence 2 "coerce").mapError fun error =>
        .executableImplMethod caller.key node.id error
  let elaborated ← elaborateMethod method
  let sourceType ←
    (SourceCoreElaboration.lowerType (.occurrence node.id.occurrence)
      step.source).mapError Error.sourceCore
  let targetType ←
    (SourceCoreElaboration.lowerType (.occurrence node.id.occurrence)
      step.target).mapError Error.sourceCore
  let expectedInputs := [sourceType]
  if elaborated.inputs.values != expectedInputs then
    throw (.runtimeCoercionInputTypesMismatch caller.key node.id
      step.requirement expectedInputs elaborated.inputs.values)
  if elaborated.returnType != targetType then
    throw (.runtimeCoercionResultTypeMismatch caller.key node.id
      step.requirement targetType elaborated.returnType)
  pure {
    sourceType
    targetType
    consumedRequirements := step.requirements
    build := fun value =>
      let temporaries := freshTemporaries temporaryOwner temporaryBase 1
      let body := aliasInputs elaborated.inputs temporaries elaborated.resolved
      pure (bindValues (temporaries.zip [value]) body)
  }

private def specializedExecutableMethod
    (method : ExecutableImplMethods.CheckedMethod) : SpecializedFunction :=
  method.specialized

/-- Resolve only those static method assumptions for which the whole-program
catalog has coherent closed evidence.  An unused unresolved trait-header
assumption remains harmless; attempting to consume it still fails through the
ordinary missing-assumption evidence gate.  Structurally identical witnesses
shared by trait-header and implementation predicates collapse to one candidate;
different witnesses for the same goal remain observably ambiguous. -/
private def resolvedMethodTraitEvidence (program : CheckedProgram) :
    List ProgramPredicate → List PredicateEvidence
  | [] => []
  | predicate :: rest =>
      let tail := resolvedMethodTraitEvidence program rest
      match (TypedTraitResolution.resolve program.signatures.implRules 32
          predicate).outcome with
      | .success evidence@(.byImpl goal _ _) =>
          if goal = predicate then .implementation evidence :: tail else tail
      | .noSolution
      | .inconclusive _ => tail

private def deduplicateExactEvidence
    (evidence : List PredicateEvidence) : List PredicateEvidence :=
  evidence.foldl (fun unique candidate =>
    if unique.any fun existing => existing == candidate then
      unique
    else
      unique ++ [candidate]) []

private def availableMethodAssumptionEvidence (program : CheckedProgram)
    (method : ExecutableImplMethods.CheckedMethod) : List PredicateEvidence :=
  deduplicateExactEvidence (
    resolvedMethodTraitEvidence program method.traitPredicates ++
      method.implementationPremises.map PredicateEvidence.implementation ++
      method.methodPremises.map PredicateEvidence.implementation)

private def validateDetachedCallMetadata (program : CheckedProgram)
    (caller : SpecializedFunction) (node : ExpressionNode)
    (callee : ExpressionId) (instantiation : DeclarationInstantiation) :
    Except Error SpecializedFunction := do
  let (reference, calleeType) ←
    match caller.function.typedBody.lookupExpression? callee with
    | none => throw (.malformedCall (.missingCalleeNode node.id callee))
    | some { type, form := .reference _ (.declaration reference), .. } =>
        pure (reference, type)
    | some _ => throw (.malformedCall
        (.calleeNotDeclarationReference node.id callee))
  if instantiation.declaration != reference.declaration then
    throw (.malformedCall (.calleeInstantiationDeclarationMismatch node.id
      instantiation.declaration reference.declaration))
  if instantiation != reference then
    throw (.malformedCall (.calleeInstantiationMetadataMismatch node.id
      instantiation reference))
  if calleeType != instantiation.type then
    throw (.malformedCall (.calleeNodeTypeMismatch node.id calleeType
      instantiation.type))
  let specialized ←
    (SourceSpecializationWorklist.resolveRequest program {
      declaration := instantiation.declaration
      parameterSubstitution := instantiation.parameterSubstitution
    }).mapError Error.malformedCall
  if specialized.function.type != instantiation.type then
    throw (.malformedCall (.specializedCalleeTypeMismatch node.id
      instantiation.type specialized.function.type))
  if specialized.assumptions != instantiation.predicates then
    throw (.malformedCall (.specializedCalleeAssumptionsMismatch node.id
      instantiation.predicates specialized.assumptions))
  pure specialized

/-- Link a checked function reached from an implementation method without
requiring it to have appeared in the top-level specialization plan.  Direct
call metadata is reconstructed from the program catalog, and recursive method
or function expansion consumes the same finite fuel. -/
private def buildDetachedDraftFuel (program : CheckedProgram)
    (temporaryOwner : Resolved.DeclarationId) (temporaryBase : Nat)
    (visiting : List SpecializationKey)
    (assumptionEvidence : List PredicateEvidence)
    (validateIncoming : Bool) (fuel : Nat)
    (specialized : SpecializedFunction) :
    Except Error SourceCoreElaboration.BodyDraft :=
  if visiting.contains specialized.key then
    .error (.recursiveCallCycle specialized.key)
  else
    match fuel with
    | 0 => .error (.linkDepthLimit specialized.key)
    | remaining + 1 => do
        if validateIncoming then
          validateAssumptionEvidence specialized.key specialized.assumptions
            assumptionEvidence
        else
          pure ()
        let elaborateMethodAt : ExpressionId → ExecutableMethodElaborator :=
          fun occurrence method => do
            let methodSpecialized := specializedExecutableMethod method
            let methodEvidence := availableMethodAssumptionEvidence program
              method
            let result : Except Error
                SourceCoreElaboration.ElaboratedFunction := do
              let draft ← buildDetachedDraftFuel program temporaryOwner
                temporaryBase (specialized.key :: visiting) methodEvidence false
                remaining methodSpecialized
              draft.finalizeWith Error.sourceCore
            match result with
            | .ok elaborated => pure elaborated
            | .error (.sourceCore error) =>
                throw (.implMethodSourceCore specialized.key occurrence
                  method.id error)
            | .error error => throw error
        SourceCoreElaboration.lowerFunctionBodyWithRuntimePolicies
          Error.sourceCore
          (fun _ node callee arguments resolution => do
            let instantiation ← match resolution with
              | .indirect _ => throw (.indirectCall node.id)
              | .declaration instantiation => pure instantiation
            let calleeEvidence ← exactCallRequirementEvidence specialized node
              assumptionEvidence instantiation
            let resolvedCallee ← validateDetachedCallMetadata program specialized
              node callee instantiation
            let calleeDraft ← buildDetachedDraftFuel program temporaryOwner
              temporaryBase (specialized.key :: visiting) calleeEvidence true
              remaining resolvedCallee
            let loweredCallee ← calleeDraft.finalizeWith Error.sourceCore
            if loweredCallee.inputs.length != arguments.length then
              throw (.argumentArityMismatch node.id loweredCallee.inputs.length
                arguments.length)
            let callResult ← (SourceCoreElaboration.lowerType
              (.occurrence node.id.occurrence) node.type).mapError
                Error.sourceCore
            if callResult != loweredCallee.returnType then
              throw (.callResultTypeMismatch node.id loweredCallee.returnType
                callResult)
            pure {
              argumentTypes := loweredCallee.inputs.values
              consumedRequirements := node.requirements
              build := fun loweredArguments => do
                if loweredArguments.length != loweredCallee.inputs.length then
                  throw (.argumentArityMismatch node.id
                    loweredCallee.inputs.length loweredArguments.length)
                let temporaries := freshTemporaries temporaryOwner
                  temporaryBase loweredArguments.length
                let body := aliasInputs loweredCallee.inputs temporaries
                  loweredCallee.resolved
                pure (bindValues (temporaries.zip loweredArguments) body)
            })
          (fun _ node operator _ =>
            requiredUnaryPlan program temporaryOwner temporaryBase
              (elaborateMethodAt node.id) specialized assumptionEvidence node
              operator)
          (fun _ node _ operator _ =>
            requiredBinaryPlan program temporaryOwner temporaryBase
              (elaborateMethodAt node.id) specialized assumptionEvidence node
              operator)
          (fun _ node step =>
            coercionPlan program temporaryOwner temporaryBase
              (elaborateMethodAt node.id) specialized assumptionEvidence node
              step)
          specialized.function
termination_by fuel

private def elaborateDetachedMethod (program : CheckedProgram)
    (temporaryOwner : Resolved.DeclarationId) (temporaryBase : Nat)
    (caller : SpecializedFunction) (visiting : List SpecializationKey)
    (fuel : Nat) (occurrence : ExpressionId)
    (method : ExecutableImplMethods.CheckedMethod) :
    Except Error SourceCoreElaboration.ElaboratedFunction :=
  let specialized := specializedExecutableMethod method
  let available := availableMethodAssumptionEvidence program method
  let result : Except Error SourceCoreElaboration.ElaboratedFunction := do
    let draft ← buildDetachedDraftFuel program temporaryOwner temporaryBase
      (caller.key :: visiting) available false fuel specialized
    draft.finalizeWith Error.sourceCore
  match result with
  | .ok elaborated => pure elaborated
  | .error (.sourceCore error) =>
      .error (.implMethodSourceCore caller.key occurrence method.id error)
  | .error error => .error error

private def buildDraftFuel (program : CheckedProgram) (plan : Plan)
    (temporaryOwner : Resolved.DeclarationId) (temporaryBase : Nat)
    (visiting : List SpecializationKey)
    (assumptionEvidence : List PredicateEvidence) (fuel : Nat)
    (key : SpecializationKey) :
    Except Error SourceCoreElaboration.BodyDraft :=
  if visiting.contains key then
    .error (.recursiveCallCycle key)
  else
    match fuel with
    | 0 => .error (.linkDepthLimit key)
    | remaining + 1 => do
        let specialized ← exactSpecialization plan key
        validateAssumptionEvidence specialized.key specialized.assumptions
          assumptionEvidence
        SourceCoreElaboration.lowerFunctionBodyWithRuntimePolicies
          Error.sourceCore
          (fun _ node _ arguments resolution => do
            let instantiation ← match resolution with
              | .indirect _ => throw (.indirectCall node.id)
              | .declaration instantiation => pure instantiation
            let calleeEvidence ← exactCallRequirementEvidence specialized node
              assumptionEvidence instantiation
            let edge ← exactCallEdge plan key node.id
            let resolvedCallee ←
              (SourceSpecializationWorklist.resolveRequest program {
                declaration := instantiation.declaration
                parameterSubstitution := instantiation.parameterSubstitution
              }).mapError (fun error => Error.malformedCall error)
            if edge.callee != resolvedCallee.key then
              throw (.callEdgeCalleeMismatch key node.id edge.callee
                resolvedCallee.key)
            let calleeDraft ← buildDraftFuel program plan temporaryOwner
              temporaryBase (key :: visiting) calleeEvidence remaining
              edge.callee
            let callee ← calleeDraft.finalizeWith Error.sourceCore
            if callee.inputs.length != arguments.length then
              throw (.argumentArityMismatch node.id callee.inputs.length
                arguments.length)
            let callResult ← (SourceCoreElaboration.lowerType
              (.occurrence node.id.occurrence) node.type).mapError
                Error.sourceCore
            if callResult != callee.returnType then
              throw (.callResultTypeMismatch node.id callee.returnType
                callResult)
            pure {
              argumentTypes := callee.inputs.values
              consumedRequirements := node.requirements
              build := fun loweredArguments => do
                if loweredArguments.length != callee.inputs.length then
                  throw (.argumentArityMismatch node.id callee.inputs.length
                    loweredArguments.length)
                let temporaries := freshTemporaries temporaryOwner
                  temporaryBase loweredArguments.length
                let body := aliasInputs callee.inputs temporaries
                  callee.resolved
                pure (bindValues (temporaries.zip loweredArguments) body)
            })
          (fun _ node operator _ =>
            requiredUnaryPlan program temporaryOwner temporaryBase
              (elaborateDetachedMethod program temporaryOwner temporaryBase
                specialized visiting remaining node.id)
              specialized assumptionEvidence node operator)
          (fun _ node _ operator _ =>
            requiredBinaryPlan program temporaryOwner temporaryBase
              (elaborateDetachedMethod program temporaryOwner temporaryBase
                specialized visiting remaining node.id)
              specialized assumptionEvidence node operator)
          (fun _ node step =>
            coercionPlan program temporaryOwner temporaryBase
              (elaborateDetachedMethod program temporaryOwner temporaryBase
                specialized visiting remaining node.id)
              specialized assumptionEvidence node step)
          specialized.function
termination_by fuel

private def linkSeeds (program : CheckedProgram) (plan : Plan)
    (temporaryBase : Nat) : List SpecializationKey →
      Except Error (List LinkedEntry)
  | [] => pure []
  | key :: rest => do
      let specialized ← exactSpecialization plan key
      unless specialized.assumptions.isEmpty do
        throw (.unresolvedAssumptions key specialized.assumptions)
      let expansionFuel := plan.specializations.length +
        program.functions.length +
        program.signatures.implementations.length + 1
      let draft ← buildDraftFuel program plan key.declaration temporaryBase
        [] [] expansionFuel key
      let elaborated ← draft.finalizeWith Error.sourceCore
      pure ({ key, elaborated } ::
        (← linkSeeds program plan temporaryBase rest))

/-- Link every seed of a complete, defensively reconstructed specialization
plan.  Budget exhaustion is never mistaken for a closed executable program. -/
def link (program : CheckedProgram)
    (outcome : SourceSpecializationWorklist.Outcome) :
    Except Error LinkedProgram := do
  let plan ← match outcome with
    | .complete plan => pure plan
    | .budgetExhausted _ next pending =>
        throw (.budgetExhausted next pending.length)
  validatePlan program plan
  pure { entries := ← linkSeeds program plan (freshBase plan) plan.seedKeys }

end Solcore.Frontend.SourceCoreDirectLinking
