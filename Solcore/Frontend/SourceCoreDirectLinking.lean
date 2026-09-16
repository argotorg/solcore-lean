import Solcore.Frontend.SourceCoreElaboration
import Solcore.Frontend.SourceSpecializationWorklist
import Solcore.Core.Machine

/-!
Closed direct-call linking for specialized typed source.

The specialization worklist remains the authority for whole-program reachability
and direct-call metadata.  This layer defensively reconstructs that plan, then
elaborates every seed while replacing each direct call with a capture-free
`Resolved.Expr` expansion.  Argument expressions are evaluated from left to
right into fresh temporary identities before the callee's stable input
identities are aliased to those temporaries.

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
        if specialized.assumptions.isEmpty then
          validateCanonicalSpecializations program rest
        else
          throw (.unresolvedAssumptions specialized.key
            specialized.assumptions)
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

private def buildDraftFuel (program : CheckedProgram) (plan : Plan)
    (temporaryOwner : Resolved.DeclarationId) (temporaryBase : Nat)
    (visiting : List SpecializationKey) (fuel : Nat)
    (key : SpecializationKey) :
    Except Error SourceCoreElaboration.BodyDraft :=
  if visiting.contains key then
    .error (.recursiveCallCycle key)
  else
    match fuel with
    | 0 => .error (.linkDepthLimit key)
    | remaining + 1 => do
        let specialized ← exactSpecialization plan key
        unless specialized.assumptions.isEmpty do
          throw (.unresolvedAssumptions key specialized.assumptions)
        SourceCoreElaboration.lowerFunctionBodyWith Error.sourceCore
          (fun lowerArgument _ node _ arguments resolution => do
            let instantiation ← match resolution with
              | .indirect => throw (.indirectCall node.id)
              | .declaration instantiation => pure instantiation
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
              temporaryBase (key :: visiting) remaining edge.callee
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
            let loweredArguments ← (callee.inputs.zip arguments).mapM
              fun pair => lowerArgument pair.1.2 pair.2
            let temporaries := freshTemporaries temporaryOwner temporaryBase
              arguments.length
            let body := aliasInputs callee.inputs temporaries callee.resolved
            pure (bindValues (temporaries.zip loweredArguments) body))
          specialized.function
termination_by fuel

private def linkSeeds (program : CheckedProgram) (plan : Plan)
    (temporaryBase : Nat) : List SpecializationKey →
      Except Error (List LinkedEntry)
  | [] => pure []
  | key :: rest => do
      let draft ← buildDraftFuel program plan key.declaration temporaryBase []
        (plan.specializations.length + 1) key
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
