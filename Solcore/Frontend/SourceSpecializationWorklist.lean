import Solcore.Frontend.ProgramChecking
import Solcore.Frontend.SourceSpecialization

/-!
Finite whole-program specialization planning.

Requests may present declaration parameters in any order.  The checked
program's exact signature/body pair and `SourceSpecialization.specializeFunction`
are the sole canonicalization boundary.  Each newly admitted specialization is
scanned in typed-source node order; direct calls append requests to the FIFO
tail, while already-seen canonical keys are skipped without consuming budget.

The budget counts distinct specializations admitted to the plan.  Exhaustion
is an ordinary outcome rather than a malformed-program error, which makes
unbounded polymorphic key growth observable.  A complete plan preserves every
specialized signature assumption and solved requirement/evidence exactly as
returned by `specializeFunction`: this layer discovers call edges but never
discharges, removes, or re-resolves predicates.
-/

set_option autoImplicit false

namespace Solcore.Frontend.SourceSpecializationWorklist

open SourceInference TypeSystem

/-- A potentially non-canonical request at the worklist boundary. -/
structure Request where
  declaration : Resolved.DeclarationId
  parameterSubstitution : ParameterSubstitution
  deriving Repr, BEq, DecidableEq

/-- One syntactic direct-call occurrence in one specialized caller.  Edges are
not deduplicated: two calls to the same callee key remain two edges. -/
structure CallEdge where
  caller : SourceSpecialization.SpecializationKey
  occurrence : ExpressionId
  callee : SourceSpecialization.SpecializationKey
  deriving Repr, BEq, DecidableEq

/-- Canonical roots plus FIFO-ordered specializations and call occurrences
discovered so far.  `seedKeys` preserves input seed order and duplicates even
though `specializations` is deduplicated by first-seen key. -/
structure Plan where
  seedKeys : List SourceSpecialization.SpecializationKey
  specializations : List SourceSpecialization.SpecializedFunction
  callEdges : List CallEdge
  deriving Repr, BEq

/-- A finite run either closes the reachable direct-call graph or exposes the
first canonical unseen key which did not fit in the distinct-key budget.
`pending` begins with the raw request for `next`; calls from that request have
not yet been scanned. -/
inductive Outcome where
  | complete (plan : Plan)
  | budgetExhausted
      (plan : Plan)
      (next : SourceSpecialization.SpecializationKey)
      (pending : List Request)
  deriving Repr, BEq

/-- Malformed catalogs, typed call metadata, and specialization requests are
separate from finite budget exhaustion. -/
inductive Error where
  | missingDeclaration (declaration : Resolved.DeclarationId)
  | duplicateDeclarations (declaration : Resolved.DeclarationId) (count : Nat)
  | declarationNotFunction
      (declaration : Resolved.DeclarationId) (kind : ProgramDeclarationKind)
  | missingSignature (declaration : Resolved.DeclarationId)
  | duplicateSignatures (declaration : Resolved.DeclarationId) (count : Nat)
  | missingFunction (declaration : Resolved.DeclarationId)
  | duplicateFunctions (declaration : Resolved.DeclarationId) (count : Nat)
  | specialization
      (declaration : Resolved.DeclarationId)
      (error : SourceSpecialization.Error)
  | missingCalleeNode
      (call callee : ExpressionId)
  | calleeNotDeclarationReference
      (call callee : ExpressionId)
  | calleeInstantiationDeclarationMismatch
      (call : ExpressionId)
      (callDeclaration referenceDeclaration : Resolved.DeclarationId)
  | calleeInstantiationMetadataMismatch
      (call : ExpressionId)
      (callInstantiation referenceInstantiation : DeclarationInstantiation)
  | calleeNodeTypeMismatch
      (call : ExpressionId) (nodeType instantiationType : Ty)
  | specializedCalleeTypeMismatch
      (call : ExpressionId) (instantiationType specializedType : Ty)
  | specializedCalleeAssumptionsMismatch
      (call : ExpressionId)
      (instantiationPredicates specializedAssumptions : List ProgramPredicate)
  | indirectCall (occurrence : ExpressionId)
  deriving Repr, DecidableEq

private def exactDeclaration (program : CheckedProgram)
    (declaration : Resolved.DeclarationId) : Except Error ProgramDeclaration :=
  let candidates := program.environment.declarations.filter fun entry =>
    decide (entry.id = declaration)
  match candidates with
  | [] => .error (.missingDeclaration declaration)
  | [entry] => .ok entry
  | entries => .error (.duplicateDeclarations declaration entries.length)

private def exactSignature (program : CheckedProgram)
    (declaration : Resolved.DeclarationId) :
    Except Error ProgramFunctionSignature :=
  let candidates := program.signatures.functions.filter fun signature =>
    decide (signature.id = declaration)
  match candidates with
  | [] => .error (.missingSignature declaration)
  | [signature] => .ok signature
  | signatures => .error (.duplicateSignatures declaration signatures.length)

private def exactFunction (program : CheckedProgram)
    (declaration : Resolved.DeclarationId) :
    Except Error CheckedFunction :=
  let candidates := program.functions.filter fun function =>
    decide (function.declaration = declaration)
  match candidates with
  | [] => .error (.missingFunction declaration)
  | [function] => .ok function
  | functions => .error (.duplicateFunctions declaration functions.length)

/-- Resolve a raw request against one exact checked catalog entry and recover
its signature-order canonical key and carrier. -/
def resolveRequest (program : CheckedProgram) (request : Request) :
    Except Error SourceSpecialization.SpecializedFunction := do
  let declaration ← exactDeclaration program request.declaration
  if declaration.kind != .function then
    throw (.declarationNotFunction declaration.id declaration.kind)
  let signature ← exactSignature program request.declaration
  let function ← exactFunction program request.declaration
  match SourceSpecialization.specializeFunction signature function
      request.parameterSubstitution with
  | .ok specialized => pure specialized
  | .error error => throw (.specialization request.declaration error)

/-- Canonicalize every seed eagerly for root recovery.  Unlike the execution
queue, this list intentionally retains repeated canonical keys. -/
def canonicalSeedKeys (program : CheckedProgram) :
    List Request → Except Error (List SourceSpecialization.SpecializationKey)
  | [] => pure []
  | request :: rest => do
      let specialized ← resolveRequest program request
      pure (specialized.key :: (← canonicalSeedKeys program rest))

private def directCall (program : CheckedProgram)
    (caller : SourceSpecialization.SpecializationKey)
    (source : TypedSource) (node : ExpressionNode)
    (callee : ExpressionId) (instantiation : DeclarationInstantiation) :
    Except Error (Request × CallEdge) := do
  let (reference, calleeType) ← match source.lookupExpression? callee with
    | none => throw (.missingCalleeNode node.id callee)
    | some { type, form := .reference _ (.declaration reference), .. } =>
        pure (reference, type)
    | some _ =>
        throw (.calleeNotDeclarationReference node.id callee)
  if instantiation.declaration != reference.declaration then
    throw (.calleeInstantiationDeclarationMismatch node.id
      instantiation.declaration reference.declaration)
  if instantiation != reference then
    throw (.calleeInstantiationMetadataMismatch node.id
      instantiation reference)
  if calleeType != instantiation.type then
    throw (.calleeNodeTypeMismatch node.id calleeType
      instantiation.type)
  let request : Request := {
    declaration := instantiation.declaration
    parameterSubstitution := instantiation.parameterSubstitution
  }
  let specialized ← resolveRequest program request
  if specialized.function.type != instantiation.type then
    throw (.specializedCalleeTypeMismatch node.id
      instantiation.type specialized.function.type)
  if specialized.assumptions != instantiation.predicates then
    throw (.specializedCalleeAssumptionsMismatch node.id
      instantiation.predicates specialized.assumptions)
  pure (request, {
    caller
    occurrence := node.id
    callee := specialized.key
  })

/-- Collect direct requests and per-occurrence edges in typed-source node
order.  An indirect call is outside this initial closed-call profile. -/
private def collectDirectCalls (program : CheckedProgram)
    (caller : SourceSpecialization.SpecializationKey)
    (source : TypedSource) :
    List Node → Except Error (List Request × List CallEdge)
  | [] => pure ([], [])
  | node :: rest => do
      match node with
      | .expression expression =>
          match expression.form with
          | .call _ _ .indirect =>
              throw (.indirectCall expression.id)
          | .call callee _ (.declaration instantiation) =>
              let (request, edge) ←
                directCall program caller source expression callee instantiation
              let (requests, edges) ←
                collectDirectCalls program caller source rest
              pure (request :: requests, edge :: edges)
          | _ => collectDirectCalls program caller source rest
      | .statement _ => collectDirectCalls program caller source rest

/-- Discard canonical keys already present in `seen` without consuming a
distinct-key budget unit, returning the first new specialization. -/
def nextUnseen (program : CheckedProgram)
    (seen : List SourceSpecialization.SpecializationKey) :
    List Request → Except Error
      (Option (Request × SourceSpecialization.SpecializedFunction ×
        List Request))
  | [] => pure none
  | request :: rest => do
      let specialized ← resolveRequest program request
      if seen.any fun key => decide (key = specialized.key) then
        nextUnseen program seen rest
      else
        pure (some (request, specialized, rest))

/-- Fuel-recursive implementation.  Public only so executable properties can
state the precise distinct-key budget law; ordinary callers should use `run`. -/
def runAux (program : CheckedProgram)
    (seedKeys : List SourceSpecialization.SpecializationKey)
    (queue : List Request)
    (seen : List SourceSpecialization.SpecializationKey)
    (specializations : List SourceSpecialization.SpecializedFunction)
    (callEdges : List CallEdge) : Nat → Except Error Outcome
  | 0 => do
      let next ← nextUnseen program seen queue
      match next with
      | none => pure (.complete { seedKeys, specializations, callEdges })
      | some (request, specialized, rest) =>
          pure (.budgetExhausted { seedKeys, specializations, callEdges }
            specialized.key (request :: rest))
  | remaining + 1 => do
      let next ← nextUnseen program seen queue
      match next with
      | none => pure (.complete { seedKeys, specializations, callEdges })
      | some (_, specialized, rest) =>
          let (requests, edges) ← collectDirectCalls program
            specialized.key specialized.function.typedBody
            specialized.function.typedBody.nodes
          runAux program seedKeys (rest ++ requests) (specialized.key :: seen)
            (specializations ++ [specialized]) (callEdges ++ edges) remaining

/-- Build a finite FIFO specialization plan from raw seed requests. -/
def run (program : CheckedProgram) (seeds : List Request) (budget : Nat) :
    Except Error Outcome := do
  let seedKeys ← canonicalSeedKeys program seeds
  runAux program seedKeys seeds [] [] [] budget

end Solcore.Frontend.SourceSpecializationWorklist
