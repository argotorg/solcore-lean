import Solcore.Frontend.ProgramChecking
import Solcore.Frontend.SourceSpecialization

/-!
Finite whole-program specialization planning.

Requests may present declaration parameters in any order.  The checked
program's exact signature/body pair and `SourceSpecialization.specializeFunction`
are the sole canonicalization boundary.  Each newly admitted specialization is
scanned in typed-source node order.  Ground direct source-declaration calls and
standalone source-declaration function references append requests to the FIFO
tail.  Open declaration uses inside a supported direct-lambda polymorphic let
are rescanned once for each distinct ground use of that let; exact duplicate
edges are removed, while different concrete callees at the same template
occurrence remain distinct.  Nested direct-lambda lets are discovered by a
finite FIFO context worklist: each cumulative substitution may ground further
local references in that lambda's direct lexical body, whose scheme matches
are composed outer-first and scanned in turn.  Nested polymorphic lambdas are
lexical boundaries until a concrete reference makes them reachable.
Compiler-function calls add no edge, and already-seen canonical keys are skipped
without consuming budget.

A declaration reference which is the callee child of a direct call is
represented only by that call edge, so adding first-class function discovery
does not perturb the established direct-call frontier.

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

/-- One concrete target of a syntactic direct-call occurrence in one
specialized caller.  Different source occurrences remain distinct; one local
polymorphic template occurrence may have several concrete callees, while an
exact duplicate `(caller, occurrence, callee)` is retained only once. -/
structure CallEdge where
  caller : SourceSpecialization.SpecializationKey
  occurrence : ExpressionId
  callee : SourceSpecialization.SpecializationKey
  deriving Repr, BEq, DecidableEq

/-- One concrete target of a declaration reference used as a first-class
function value.  Direct-call callee children are excluded because their
occurrence is already retained by `CallEdge`; contextual exact duplicates are
removed under the same policy as call edges. -/
structure ReferenceEdge where
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
  referenceEdges : List ReferenceEdge := []
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
  | specializedCalleeParameterComptimeMismatch
      (call : ExpressionId)
      (instantiation specialized : List Bool)
  | specializedCalleeReturnComptimeMismatch
      (call : ExpressionId)
      (instantiation specialized : Bool)
  | unsupportedOpenDeclaration
      (occurrence : ExpressionId) (variables : List TypeVarId)
  | localPolymorphicInstanceMismatch
      (occurrence : ExpressionId) (binder : Resolved.LocalId)
      (scheme : Scheme) (actual : Ty)
  | unsupportedLocalPolymorphicRequirements
      (occurrence : ExpressionId) (predicates : List ProgramPredicate)
  | localSchemeRequirementIdMultiplicity
      (occurrence : ExpressionId) (requirement : RequirementId) (count : Nat)
  | localSchemeRequirementPredicatesMismatch
      (occurrence : ExpressionId)
      (expected actual : List ProgramPredicate)
  | localSchemeCallRequirementCountMismatch
      (occurrence : ExpressionId) (expected actual : Nat)
  | foreignLocalSchemeRequirement
      (occurrence : ExpressionId) (requirement : RequirementId)
  | localPolymorphicScopeFuelExhausted (pending : NodeId)
  | localPolymorphicContextFuelExhausted (pending : Nat)
  | invalidExpressionCoercionPath
      (expression : ExpressionId) (source target : Ty)
      (coercions : List CoercionStep)
  | invalidIndirectArgumentCoercionPath
      (call : ExpressionId) (metadata : IndirectCallResolution)
  | indirectCalleeNotFunction (call : ExpressionId) (type : Ty)
  | missingIndirectArgument (call argument : ExpressionId)
  | indirectArgumentCountMismatch
      (call : ExpressionId) (expected actual : Nat)
  | indirectArgumentBundleMismatch
      (call : ExpressionId) (expected actual : Ty)
  | indirectParameterTypeMismatch
      (call : ExpressionId) (expected actual : Ty)
  | indirectResultTypeMismatch
      (call : ExpressionId) (expected actual : Ty)
  | indirectRequirementsMismatch
      (call : ExpressionId)
      (expected actual : List RequirementId)
  /-- Retained for downstream diagnostic compatibility.  Worklist discovery
  no longer produces this error for a well-typed indirect call. -/
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

private def canonicalReference (program : CheckedProgram)
    (occurrence : ExpressionId) (referenceType : Ty)
    (instantiation : DeclarationInstantiation) :
    Except Error (Request × SourceSpecialization.SpecializedFunction) := do
  if referenceType != instantiation.type then
    throw (.calleeNodeTypeMismatch occurrence referenceType
      instantiation.type)
  let request : Request := {
    declaration := instantiation.declaration
    parameterSubstitution := instantiation.parameterSubstitution
  }
  let specialized ← resolveRequest program request
  if specialized.function.type != instantiation.type then
    throw (.specializedCalleeTypeMismatch occurrence
      instantiation.type specialized.function.type)
  if specialized.assumptions != instantiation.predicates then
    throw (.specializedCalleeAssumptionsMismatch occurrence
      instantiation.predicates specialized.assumptions)
  let specializedParameterComptime :=
    specialized.function.typedBody.inputs.map (·.comptime)
  if instantiation.parameterComptime != specializedParameterComptime then
    throw (.specializedCalleeParameterComptimeMismatch occurrence
      instantiation.parameterComptime specializedParameterComptime)
  if instantiation.returnComptime != specialized.function.returnComptime then
    throw (.specializedCalleeReturnComptimeMismatch occurrence
      instantiation.returnComptime specialized.function.returnComptime)
  pure (request, specialized)

private def declarationInstantiationTypes
    (instantiation : DeclarationInstantiation) : List Ty :=
  instantiation.type ::
    instantiation.parameterSubstitution.map Prod.snd ++
    instantiation.predicates.flatMap fun predicate =>
      predicate.subject :: predicate.arguments

private def declarationInstantiationVariables
    (instantiation : DeclarationInstantiation) : List TypeVarId :=
  (declarationInstantiationTypes instantiation).flatMap Ty.freeVariables
    |>.eraseDups

private def declarationPredicateVariables
    (instantiation : DeclarationInstantiation) : List TypeVarId :=
  (instantiation.predicates.flatMap fun predicate =>
    predicate.subject :: predicate.arguments).flatMap Ty.freeVariables
    |>.eraseDups

private def declarationInstantiation? (node : ExpressionNode) :
    Option DeclarationInstantiation :=
  match node.form with
  | .call _ _ (.declaration instantiation)
  | .reference _ (.declaration instantiation) => some instantiation
  | _ => none

private def hasOpenDeclarationInstantiation (node : ExpressionNode) : Bool :=
  match declarationInstantiation? node with
  | some instantiation =>
      !(declarationInstantiationVariables instantiation).isEmpty
  | none => false

private structure LocalLambdaBinding where
  binder : TypedBinder
  initializer : ExpressionId
  deriving Repr, BEq, DecidableEq

private structure LocalLambdaInstance where
  binding : LocalLambdaBinding
  substitution : Substitution
  deriving Repr, BEq, DecidableEq

private def directPolymorphicLambdaBindings
    (source : TypedSource) : List LocalLambdaBinding :=
  source.nodes.filterMap fun
    | .statement { form := .letDecl binder (some initializer), .. } =>
        if binder.scheme.quantified.isEmpty ||
            !SourceSpecialization.isDirectLambdaInitializer source initializer then
          none
        else
          some { binder, initializer }
    | _ => none

private def exactLocalLambdaBinding?
    (bindings : List LocalLambdaBinding) (id : Resolved.LocalId) :
    Option LocalLambdaBinding :=
  match bindings.filter fun binding => binding.binder.id == id with
  | [binding] => some binding
  | _ => none

private def appendNodeId (ids : List NodeId) (id : NodeId) : List NodeId :=
  if ids.contains id then ids else ids ++ [id]

private def appendNodeIds (left right : List NodeId) : List NodeId :=
  right.foldl appendNodeId left

private def directLexicalChildren (source : TypedSource)
    (boundaries : List ExpressionId) (id : NodeId) : List NodeId :=
  match source.lookupNode? id.occurrenceId with
  | some (.expression node@{ form := .lambda _ _ _, .. }) =>
      if boundaries.contains node.id then []
      else SourceSpecialization.expressionChildNodeIds node
  | some (.expression node) =>
      SourceSpecialization.expressionChildNodeIds node
  | some (.statement node) =>
      SourceSpecialization.statementChildNodeIds source node
  | none => []

private def directLexicalTraversalFuel (source : TypedSource)
    (roots : List NodeId) : Nat :=
  let edges := source.nodes.foldl (fun count node =>
    count + match node with
      | .expression expression =>
          (SourceSpecialization.expressionChildNodeIds expression).length
      | .statement statement =>
          (SourceSpecialization.statementChildNodeIds source statement).length) 0
  roots.length + edges + 1

private def collectDirectLexicalNodeIds (source : TypedSource)
    (boundaries : List ExpressionId) :
    Nat → List NodeId → List NodeId → Except Error (List NodeId)
  | 0, [], seen => pure seen
  | 0, pending :: _, _ =>
      throw (.localPolymorphicScopeFuelExhausted pending)
  | _ + 1, [], seen => pure seen
  | fuel + 1, pending :: rest, seen =>
      if seen.contains pending then
        collectDirectLexicalNodeIds source boundaries fuel rest seen
      else
        let nextSeen := seen ++ [pending]
        let children :=
          (directLexicalChildren source boundaries pending).filter fun child =>
            !nextSeen.contains child
        collectDirectLexicalNodeIds source boundaries fuel
          (appendNodeIds rest children) nextSeen

private def directLexicalNodeIds (source : TypedSource)
    (boundaries : List ExpressionId) (roots : List NodeId) :
    Except Error (List NodeId) :=
  collectDirectLexicalNodeIds source boundaries
    (directLexicalTraversalFuel source roots) roots []

private def localLambdaBodyNodeIds (source : TypedSource)
    (bindings : List LocalLambdaBinding) (binding : LocalLambdaBinding) :
    Except Error (List NodeId) :=
  match source.lookupExpression? binding.initializer with
  | some { form := .lambda _ _ body, .. } =>
      directLexicalNodeIds source (bindings.map (·.initializer))
        (body.map NodeId.statement)
  | _ => pure []

private def selectedNodes (ids : List NodeId) : List Node → List Node
  | [] => []
  | node :: rest =>
      if ids.contains node.id then node :: selectedNodes ids rest
      else selectedNodes ids rest

private def insertLocalLambdaInstance
    (instances : List LocalLambdaInstance)
    (localInstance : LocalLambdaInstance) : List LocalLambdaInstance :=
  if instances.contains localInstance then instances
  else instances ++ [localInstance]

private def variablesBelongTo (variables quantified : List TypeVarId) : Bool :=
  variables.all fun metavariable => quantified.contains metavariable

private def collectGroundLocalLambdaInstances
    (bindings : List LocalLambdaBinding) :
    List Node → List LocalLambdaInstance → Except Error (List LocalLambdaInstance)
  | [], instances => pure instances
  | node :: rest, instances =>
      match node with
      | .expression expression =>
          match expression.form with
          | .reference _ (.local id) =>
              match exactLocalLambdaBinding? bindings id with
              | some binding => do
                  let variables := expression.rawType.freeVariables
                  if !variables.isEmpty then
                    collectGroundLocalLambdaInstances bindings rest instances
                  else
                    let substitution ← match
                        SourceSpecialization.matchClosedSchemeInstance?
                          binding.binder.scheme expression.rawType with
                      | some substitution => pure substitution
                      | none => throw (.localPolymorphicInstanceMismatch
                          expression.id id binding.binder.scheme
                          expression.rawType)
                    collectGroundLocalLambdaInstances bindings rest
                      (insertLocalLambdaInstance instances {
                        binding, substitution
                      })
              | none =>
                  collectGroundLocalLambdaInstances bindings rest instances
          | _ => collectGroundLocalLambdaInstances bindings rest instances
      | .statement _ =>
          collectGroundLocalLambdaInstances bindings rest instances

private def rootLocalLambdaInstances (source : TypedSource)
    (bindings : List LocalLambdaBinding) :
    Except Error (List LocalLambdaInstance) := do
  let rootIds ← directLexicalNodeIds source (bindings.map (·.initializer))
    source.roots
  collectGroundLocalLambdaInstances bindings
    (selectedNodes rootIds source.nodes) []

/-- Recover every direct-lambda instance whose open occurrence becomes ground
under one cumulative local context.  The child substitution is inferred
against the context-substituted scheme and composed as `child.compose parent`,
which applies the parent substitution first. -/
private def collectContextualLocalLambdaInstances
    (bindings : List LocalLambdaBinding) (parent : LocalLambdaInstance) :
    List Node → List LocalLambdaInstance →
      Except Error (List LocalLambdaInstance)
  | [], instances => pure instances
  | node :: rest, instances =>
      match node with
      | .expression expression =>
          match expression.form with
          | .reference _ (.local id) =>
              match exactLocalLambdaBinding? bindings id with
              | none =>
                  collectContextualLocalLambdaInstances bindings parent rest
                    instances
              | some binding => do
                  let actual := parent.substitution.apply expression.rawType
                  let remaining := actual.freeVariables
                  if !remaining.isEmpty then
                    collectContextualLocalLambdaInstances bindings parent rest
                      instances
                  else
                    let contextualScheme :=
                      Scheme.apply parent.substitution binding.binder.scheme
                    let child ← match
                        SourceSpecialization.matchClosedSchemeInstance?
                          contextualScheme actual with
                      | some substitution => pure substitution
                      | none => throw (.localPolymorphicInstanceMismatch
                          expression.id id contextualScheme actual)
                    let cumulative := child.compose parent.substitution
                    collectContextualLocalLambdaInstances bindings parent rest
                      (insertLocalLambdaInstance instances {
                        binding
                        substitution := cumulative
                      })
          | _ =>
              collectContextualLocalLambdaInstances bindings parent rest
                instances
      | .statement _ =>
          collectContextualLocalLambdaInstances bindings parent rest instances

private def appendLocalLambdaInstances
    (left right : List LocalLambdaInstance) : List LocalLambdaInstance :=
  right.foldl insertLocalLambdaInstance left

/-- Close the reachable local-template contexts in FIFO order.  `seen`
contains both processed and queued contexts, so an already-discovered instance
is never processed twice. -/
private def closeLocalLambdaInstancesAux (source : TypedSource)
    (bindings : List LocalLambdaBinding)
    (seen frontier : List LocalLambdaInstance) :
    Nat → Except Error (List LocalLambdaInstance)
  | 0 =>
      match frontier with
      | [] => pure seen
      | pending => throw (.localPolymorphicContextFuelExhausted pending.length)
  | fuel + 1 =>
      match frontier with
      | [] => pure seen
      | parent :: rest => do
          let bodyIds ← localLambdaBodyNodeIds source bindings parent.binding
          let discovered ← collectContextualLocalLambdaInstances bindings parent
            (selectedNodes bodyIds source.nodes) []
          let fresh := discovered.filter fun localInstance =>
            !seen.contains localInstance
          let nextSeen := appendLocalLambdaInstances seen fresh
          closeLocalLambdaInstancesAux source bindings nextSeen (rest ++ fresh)
            fuel

/-- A source with `n` nodes and `b` direct polymorphic lambda bindings has at
most `n` choices at each strictly growing lexical context.  This deliberately
loose derived bound keeps worklist termination explicit without exposing a
second public budget. -/
private def localLambdaContextFuel (source : TypedSource)
    (bindings : List LocalLambdaBinding) : Nat :=
  (source.nodes.length + 1) ^ (bindings.length + 1)

private def closeLocalLambdaInstances (source : TypedSource)
    (bindings : List LocalLambdaBinding)
    (initial : List LocalLambdaInstance) :
    Except Error (List LocalLambdaInstance) :=
  closeLocalLambdaInstancesAux source bindings initial initial
    (localLambdaContextFuel source bindings)

private def declarationGroundUnder (substitution : Substitution)
    (instantiation : DeclarationInstantiation) : Bool :=
  (declarationInstantiationTypes instantiation).all fun type =>
    (substitution.apply type).freeVariables.isEmpty

private def declarationVariablesUnder (substitution : Substitution)
    (instantiation : DeclarationInstantiation) : List TypeVarId :=
  (declarationInstantiationTypes instantiation).flatMap fun type =>
    (substitution.apply type).freeVariables
  |>.eraseDups

private def openDeclarationNodeIdsFor (source : TypedSource)
    (bindings : List LocalLambdaBinding)
    (localInstance : LocalLambdaInstance) : Except Error (List NodeId) := do
  let bodyIds ← localLambdaBodyNodeIds source bindings localInstance.binding
  pure <| source.nodes.filterMap fun
    | .expression node =>
        if !bodyIds.contains (.expression node.id) then
          none
        else match declarationInstantiation? node with
        | some instantiation =>
            let variables := declarationInstantiationVariables instantiation
            if !variables.isEmpty &&
                declarationGroundUnder localInstance.substitution
                  instantiation then
              some (.expression node.id)
            else
              none
        | none => none
    | .statement _ => none

private def appendCallEdge (edges : List CallEdge) (edge : CallEdge) :
    List CallEdge :=
  if edges.contains edge then edges else edges ++ [edge]

private def appendReferenceEdge (edges : List ReferenceEdge)
    (edge : ReferenceEdge) : List ReferenceEdge :=
  if edges.contains edge then edges else edges ++ [edge]

private def appendCallEdges (left right : List CallEdge) : List CallEdge :=
  right.foldl appendCallEdge left

private def appendReferenceEdges (left right : List ReferenceEdge) :
    List ReferenceEdge :=
  right.foldl appendReferenceEdge left

private def validateDirectCallShape (source : TypedSource)
    (node : ExpressionNode) (callee : ExpressionId)
    (instantiation : DeclarationInstantiation) : Except Error Ty := do
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
    throw (.calleeNodeTypeMismatch node.id calleeType instantiation.type)
  pure calleeType

private def directCall (program : CheckedProgram)
    (caller : SourceSpecialization.SpecializationKey)
    (source : TypedSource) (node : ExpressionNode)
    (callee : ExpressionId) (instantiation : DeclarationInstantiation) :
    Except Error (Request × CallEdge) := do
  let calleeType ← validateDirectCallShape source node callee instantiation
  let (request, specialized) ←
    canonicalReference program node.id calleeType instantiation
  pure (request, {
    caller
    occurrence := node.id
    callee := specialized.key
  })

private def validateExpressionCoercions (node : ExpressionNode) :
    Except Error Unit := do
  if !node.hasValidCoercionPath then
    throw (.invalidExpressionCoercionPath node.id node.rawType node.type
      node.coercions)

private def validateIndirectArgumentCoercions (node : ExpressionNode)
    (metadata : IndirectCallResolution) : Except Error Unit := do
  if !metadata.hasValidArgumentCoercionPath then
    throw (.invalidIndirectArgumentCoercionPath node.id metadata)

private def coercionRequirements (steps : List CoercionStep) :
    List RequirementId :=
  steps.flatMap (·.requirements)

/-- Reconstruct every indirect-call endpoint from authoritative child nodes.
The callee and argument list are runtime edges, but their retained bundle,
result and obligation metadata must still be exact at planning time. -/
private def validateIndirectCall (source : TypedSource)
    (node : ExpressionNode) (callee : ExpressionId)
    (arguments : List ExpressionId) (metadata : IndirectCallResolution) :
    Except Error Unit := do
  validateIndirectArgumentCoercions node metadata
  let calleeNode ← match source.lookupExpression? callee with
    | some calleeNode => pure calleeNode
    | none => throw (.missingCalleeNode node.id callee)
  let (parameterType, resultType) ← match calleeNode.type with
    | .function parameter result => pure (parameter, result)
    | type => throw (.indirectCalleeNotFunction node.id type)
  let argumentTypes ← arguments.mapM fun argument =>
    match source.lookupExpression? argument with
    | some argumentNode => pure argumentNode.type
    | none => throw (.missingIndirectArgument node.id argument)
  if metadata.argumentCount != arguments.length then
    throw (.indirectArgumentCountMismatch node.id metadata.argumentCount
      arguments.length)
  let bundledType := Ty.productMany argumentTypes
  if metadata.argumentTypeBeforeCoercion != bundledType then
    throw (.indirectArgumentBundleMismatch node.id bundledType
      metadata.argumentTypeBeforeCoercion)
  if metadata.argumentTypeAfterCoercion != parameterType then
    throw (.indirectParameterTypeMismatch node.id parameterType
      metadata.argumentTypeAfterCoercion)
  if node.rawType != resultType then
    throw (.indirectResultTypeMismatch node.id resultType node.rawType)
  let expectedRequirements :=
    coercionRequirements metadata.argumentCoercions ++
      coercionRequirements node.coercions
  if node.requirements != expectedRequirements then
    throw (.indirectRequirementsMismatch node.id expectedRequirements
      node.requirements)

private def directDeclarationCallees : List Node → List ExpressionId
  | [] => []
  | .expression { form := .call callee _ (.declaration _), .. } :: rest =>
      callee :: directDeclarationCallees rest
  | _ :: rest => directDeclarationCallees rest

/-- Collect source-declaration requests and exact per-occurrence edges in
typed-source node order.  Compiler-function calls have no source
specialization.  Indirect calls are validated here, while their runtime target
is represented by the callee expression and therefore adds no static edge. -/
private def collectReferences (program : CheckedProgram)
    (caller : SourceSpecialization.SpecializationKey)
    (source : TypedSource) :
    List ExpressionId → List Node →
      Except Error (List Request × List CallEdge × List ReferenceEdge)
  | _, [] => pure ([], [], [])
  | directCallees, node :: rest => do
      let collectRest := collectReferences program caller source directCallees rest
      match node with
      | .expression expression =>
          validateExpressionCoercions expression
          match expression.form with
          | .call callee arguments (.indirect metadata) =>
              validateIndirectCall source expression callee arguments metadata
              collectRest
          | .call callee _ (.declaration instantiation) =>
              if hasOpenDeclarationInstantiation expression then
                let _ ← validateDirectCallShape source expression callee
                  instantiation
                collectRest
              else
                let (request, edge) ←
                  directCall program caller source expression callee instantiation
                let (requests, callEdges, referenceEdges) ← collectRest
                pure (request :: requests, edge :: callEdges, referenceEdges)
          | .reference _ (.declaration instantiation) =>
              if directCallees.contains expression.id then
                collectRest
              else if hasOpenDeclarationInstantiation expression then
                if expression.type = instantiation.type then
                  collectRest
                else
                  throw (.calleeNodeTypeMismatch expression.id
                    expression.type instantiation.type)
              else
                let (request, specialized) ← canonicalReference program
                  expression.id expression.type instantiation
                let (requests, callEdges, referenceEdges) ← collectRest
                pure (request :: requests, callEdges, {
                  caller
                  occurrence := expression.id
                  callee := specialized.key
                } :: referenceEdges)
          | _ => collectRest
      | .statement _ => collectRest

private def hasFlexiblePredicateVariables
    (predicate : ProgramPredicate) : Bool :=
  !(TypedTraitResolution.predicateVariables predicate).isEmpty

private def firstDuplicateRequirement :
    List RequirementId → Option RequirementId
  | [] => none
  | requirement :: rest =>
      if rest.contains requirement then some requirement
      else firstDuplicateRequirement rest

private def validateQualifiedLocalDirectCall
    (localInstance : LocalLambdaInstance) (expression : ExpressionNode)
    (instantiation : DeclarationInstantiation) : Except Error Unit := do
  if expression.requirements.length != instantiation.predicates.length then
    throw (.localSchemeCallRequirementCountMismatch expression.id
      instantiation.predicates.length expression.requirements.length)
  match firstDuplicateRequirement expression.requirements with
  | some requirement =>
      let count := (expression.requirements.filter fun candidate =>
        candidate == requirement).length
      throw (.localSchemeRequirementIdMultiplicity expression.id requirement count)
  | none => pure ()
  let owned := localInstance.binding.binder.schemeRequirements.filter fun owned =>
    expression.requirements.contains owned.templateRequirement
  for requirement in owned do
    let count := (expression.requirements.filter fun candidate =>
      candidate == requirement.templateRequirement).length
    if count != 1 then
      throw (.localSchemeRequirementIdMultiplicity expression.id
        requirement.templateRequirement count)
  let expected := owned.map (·.predicate)
  let actual := instantiation.predicates.filter hasFlexiblePredicateVariables
  if expected != actual then
    throw (.localSchemeRequirementPredicatesMismatch expression.id
      expected actual)
  let concreteExpected := owned.map fun requirement =>
    (requirement.applySubstitution localInstance.substitution).predicate
  let concreteActual := actual.map
    (TypedTraitResolution.applySubstitution localInstance.substitution)
  if concreteExpected != concreteActual then
    throw (.localSchemeRequirementPredicatesMismatch expression.id
      concreteExpected concreteActual)

private def validateLocalSchemeTemplateUses
    (bindings : List LocalLambdaBinding) (localInstance : LocalLambdaInstance)
    (nodes : List Node) : Except Error Unit := do
  let own := localInstance.binding.binder.schemeRequirements.map
    (·.templateRequirement)
  let all := bindings.flatMap fun binding =>
    binding.binder.schemeRequirements.map (·.templateRequirement)
  let calls := nodes.filterMap fun
    | .expression node@{ form := .call _ _ (.declaration _), .. } => some node
    | _ => none
  for requirement in own do
    let count := calls.foldl (fun count call =>
      count + (call.requirements.filter fun candidate =>
        candidate == requirement).length) 0
    if count != 1 then
      throw (.localSchemeRequirementIdMultiplicity
        localInstance.binding.initializer requirement count)
  for call in calls do
    match call.requirements.find? fun requirement =>
        all.contains requirement && !own.contains requirement with
    | some requirement =>
        throw (.foreignLocalSchemeRequirement call.id requirement)
    | none => pure ()

private def validateReachableOpenDeclarations (source : TypedSource)
    (bindings : List LocalLambdaBinding) :
    List LocalLambdaInstance → Except Error Unit
  | [] => pure ()
  | localInstance :: rest => do
      let bodyIds ← localLambdaBodyNodeIds source bindings localInstance.binding
      let selected := selectedNodes bodyIds source.nodes
      let directCallees := directDeclarationCallees selected
      validateLocalSchemeTemplateUses bindings localInstance selected
      for node in selected do
        match node with
        | .expression expression =>
            match declarationInstantiation? expression with
            | some instantiation =>
                let variables :=
                  declarationInstantiationVariables instantiation
                if variables.isEmpty then
                  pure ()
                else
                  let remaining := declarationVariablesUnder
                    localInstance.substitution instantiation
                  if !remaining.isEmpty then
                    throw (.unsupportedOpenDeclaration expression.id remaining)
                  else if !instantiation.predicates.isEmpty then
                    match expression.form with
                    | .call _ _ (.declaration _) =>
                        validateQualifiedLocalDirectCall localInstance expression
                          instantiation
                    | .reference _ (.declaration _) =>
                        if directCallees.contains expression.id then
                          pure ()
                        else
                          throw (.unsupportedLocalPolymorphicRequirements
                            expression.id instantiation.predicates)
                    | _ => pure ()
                  else
                    pure ()
            | none => pure ()
        | .statement _ => pure ()
      validateReachableOpenDeclarations source bindings rest

private def validateOpenDeclarationsCovered (source : TypedSource)
    (bindings : List LocalLambdaBinding)
    (instances : List LocalLambdaInstance) : Except Error Unit := do
  let localVariables :=
    (bindings.flatMap fun binding => binding.binder.scheme.quantified).eraseDups
  for node in source.nodes do
    match node with
    | .expression expression =>
        match declarationInstantiation? expression with
        | some instantiation =>
            let variables := declarationInstantiationVariables instantiation
            if variables.isEmpty then
              pure ()
            else if variablesBelongTo variables localVariables then
              pure ()
            else
              throw (.unsupportedOpenDeclaration expression.id variables)
        | none => pure ()
    | .statement _ => pure ()
  validateReachableOpenDeclarations source bindings instances

private def collectInstantiatedReferences (program : CheckedProgram)
    (caller : SourceSpecialization.SpecializationKey)
    (source : TypedSource) (bindings : List LocalLambdaBinding) :
    List LocalLambdaInstance →
      Except Error (List Request × List CallEdge × List ReferenceEdge)
  | [] => pure ([], [], [])
  | localInstance :: rest => do
      let instantiated := source.applySubstitution localInstance.substitution
      let openIds ← openDeclarationNodeIdsFor source bindings localInstance
      let selected := selectedNodes openIds instantiated.nodes
      let directCallees := directDeclarationCallees selected
      let (requests, calls, references) ←
        collectReferences program caller instantiated directCallees selected
      let (restRequests, restCalls, restReferences) ←
        collectInstantiatedReferences program caller source bindings rest
      pure (requests ++ restRequests,
        appendCallEdges calls restCalls,
        appendReferenceEdges references restReferences)

private def collectAllReferences (program : CheckedProgram)
    (caller : SourceSpecialization.SpecializationKey)
    (source : TypedSource) :
    Except Error (List Request × List CallEdge × List ReferenceEdge) := do
  let directCallees := directDeclarationCallees source.nodes
  let (requests, calls, references) ←
    collectReferences program caller source directCallees source.nodes
  let bindings := directPolymorphicLambdaBindings source
  let initialInstances ← rootLocalLambdaInstances source bindings
  let instances ← closeLocalLambdaInstances source bindings initialInstances
  validateOpenDeclarationsCovered source bindings instances
  let (instantiatedRequests, instantiatedCalls, instantiatedReferences) ←
    collectInstantiatedReferences program caller source bindings instances
  pure (requests ++ instantiatedRequests,
    appendCallEdges calls instantiatedCalls,
    appendReferenceEdges references instantiatedReferences)

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
    (callEdges : List CallEdge)
    (referenceEdges : List ReferenceEdge) : Nat → Except Error Outcome
  | 0 => do
      let next ← nextUnseen program seen queue
      match next with
      | none => pure (.complete {
          seedKeys, specializations, callEdges, referenceEdges })
      | some (request, specialized, rest) =>
          pure (.budgetExhausted {
            seedKeys, specializations, callEdges, referenceEdges }
            specialized.key (request :: rest))
  | remaining + 1 => do
      let next ← nextUnseen program seen queue
      match next with
      | none => pure (.complete {
          seedKeys, specializations, callEdges, referenceEdges })
      | some (_, specialized, rest) =>
          let source := specialized.function.typedBody
          let (requests, edges, references) ←
            collectAllReferences program specialized.key source
          runAux program seedKeys (rest ++ requests) (specialized.key :: seen)
            (specializations ++ [specialized]) (callEdges ++ edges)
            (referenceEdges ++ references) remaining

/-- Build a finite FIFO specialization plan from raw seed requests. -/
def run (program : CheckedProgram) (seeds : List Request) (budget : Nat) :
    Except Error Outcome := do
  let seedKeys ← canonicalSeedKeys program seeds
  runAux program seedKeys seeds [] [] [] [] budget

end Solcore.Frontend.SourceSpecializationWorklist

/-!
## Consolidated module: `Solcore.Frontend.SourceSpecializationWorklistProperties`
-/

/-! Small checked laws for finite specialization-worklist boundaries. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceSpecializationWorklist

/-- Canonical specialization identities retained by a worklist plan. -/
def Plan.specializationKeys (plan : Plan) :
    List SourceSpecialization.SpecializationKey :=
  plan.specializations.map (·.key)

/-- Recover the accumulated plan from either finite worklist outcome. -/
def Outcome.plan : Outcome → Plan
  | .complete plan => plan
  | .budgetExhausted plan _ _ => plan

@[simp] theorem Outcome.plan_complete (plan : Plan) :
    (Outcome.complete plan).plan = plan := rfl

@[simp] theorem Outcome.plan_budgetExhausted (plan : Plan)
    (next : SourceSpecialization.SpecializationKey) (pending : List Request) :
    (Outcome.budgetExhausted plan next pending).plan = plan := rfl

private theorem except_bind_ok {Error Value Result : Type}
    (source : Except Error Value) (continuation : Value → Except Error Result)
    (result : Result)
    (success : (do
      let value ← source
      continuation value) = .ok result) :
    ∃ value, source = .ok value ∧ continuation value = .ok result := by
  cases source with
  | error error => simp [bind, Except.bind] at success
  | ok value =>
      exact ⟨value, rfl, by simpa [bind, Except.bind] using success⟩

private def RequestResolvesTo (program : CheckedProgram) (request : Request)
    (key : SourceSpecialization.SpecializationKey) : Prop :=
  ∃ specialized, resolveRequest program request = .ok specialized ∧
    specialized.key = key

private def CoveredKey (program : CheckedProgram)
    (seen : List SourceSpecialization.SpecializationKey)
    (queue : List Request) (key : SourceSpecialization.SpecializationKey) : Prop :=
  key ∈ seen ∨ ∃ request ∈ queue, RequestResolvesTo program request key

private theorem any_key_eq_true_iff
    (seen : List SourceSpecialization.SpecializationKey)
    (key : SourceSpecialization.SpecializationKey) :
    (seen.any fun candidate => decide (candidate = key)) = true ↔
      key ∈ seen := by
  simp [List.any_eq_true]

private theorem nodup_reverse {α : Type} (values : List α)
    (unique : values.Nodup) : values.reverse.Nodup := by
  change List.Pairwise (fun left right : α => left ≠ right) values.reverse
  rw [List.pairwise_reverse]
  exact unique.imp fun notEqual equal => notEqual equal.symm

private theorem nextUnseen_some_key_not_mem (program : CheckedProgram)
    (seen : List SourceSpecialization.SpecializationKey) (queue : List Request)
    (request : Request) (specialized : SourceSpecialization.SpecializedFunction)
    (rest : List Request)
    (result : nextUnseen program seen queue =
      .ok (some (request, specialized, rest))) :
    specialized.key ∉ seen := by
  induction queue generalizing request specialized with
  | nil =>
      simp [nextUnseen, pure, Pure.pure, Except.pure] at result
  | cons current tail ih =>
      simp only [nextUnseen] at result
      cases resolved : resolveRequest program current with
      | error error =>
          simp [resolved, bind, Except.bind] at result
      | ok currentSpecialized =>
          by_cases present : currentSpecialized.key ∈ seen
          · have selected :
                (seen.any fun key => decide (key = currentSpecialized.key)) =
                  true :=
              (any_key_eq_true_iff seen currentSpecialized.key).2 present
            simp [resolved, selected, bind, Except.bind] at result
            exact ih (request := request) (specialized := specialized) result
          · have selected :
                (seen.any fun key => decide (key = currentSpecialized.key)) =
                  false := by
              cases choice :
                  (seen.any fun key => decide (key = currentSpecialized.key)) with
              | false => rfl
              | true =>
                  exact False.elim (present
                    ((any_key_eq_true_iff seen currentSpecialized.key).1 choice))
            simp [resolved, selected, bind, Except.bind] at result
            cases result
            exact present

private theorem nextUnseen_none_resolved_mem (program : CheckedProgram)
    (seen : List SourceSpecialization.SpecializationKey) (queue : List Request)
    (result : nextUnseen program seen queue = .ok none)
    (request : Request) (requestMember : request ∈ queue)
    (specialized : SourceSpecialization.SpecializedFunction)
    (resolvedRequest : resolveRequest program request = .ok specialized) :
    specialized.key ∈ seen := by
  induction queue generalizing request specialized with
  | nil => simp at requestMember
  | cons current tail ih =>
      simp only [nextUnseen] at result
      cases resolved : resolveRequest program current with
      | error error =>
          simp [resolved, bind, Except.bind] at result
      | ok currentSpecialized =>
          by_cases present : currentSpecialized.key ∈ seen
          · have selected :
                (seen.any fun key => decide (key = currentSpecialized.key)) =
                  true :=
              (any_key_eq_true_iff seen currentSpecialized.key).2 present
            simp [resolved, selected, bind, Except.bind] at result
            simp only [List.mem_cons] at requestMember
            rcases requestMember with rfl | requestMember
            · rw [resolved] at resolvedRequest
              cases resolvedRequest
              exact present
            · exact ih (request := request) (specialized := specialized) result
                requestMember resolvedRequest
          · have selected :
                (seen.any fun key => decide (key = currentSpecialized.key)) =
                  false := by
              cases choice :
                  (seen.any fun key => decide (key = currentSpecialized.key)) with
              | false => rfl
              | true =>
                  exact False.elim (present
                    ((any_key_eq_true_iff seen currentSpecialized.key).1 choice))
            simp [resolved, selected, bind, Except.bind, pure, Pure.pure,
              Except.pure] at result

private theorem nextUnseen_none_covers (program : CheckedProgram)
    (seen : List SourceSpecialization.SpecializationKey) (queue : List Request)
    (result : nextUnseen program seen queue = .ok none)
    (key : SourceSpecialization.SpecializationKey)
    (covered : CoveredKey program seen queue key) :
    key ∈ seen := by
  rcases covered with seenMember | ⟨request, requestMember, specialized,
      resolved, rfl⟩
  · exact seenMember
  · exact nextUnseen_none_resolved_mem program seen queue result request
      requestMember specialized resolved

private theorem nextUnseen_some_resolved_covered (program : CheckedProgram)
    (seen : List SourceSpecialization.SpecializationKey) (queue : List Request)
    (selectedRequest : Request)
    (selected : SourceSpecialization.SpecializedFunction) (rest : List Request)
    (result : nextUnseen program seen queue =
      .ok (some (selectedRequest, selected, rest)))
    (request : Request) (requestMember : request ∈ queue)
    (specialized : SourceSpecialization.SpecializedFunction)
    (resolvedRequest : resolveRequest program request = .ok specialized) :
    CoveredKey program (selected.key :: seen) rest specialized.key := by
  induction queue generalizing request specialized with
  | nil => simp at requestMember
  | cons current tail ih =>
      simp only [nextUnseen] at result
      cases resolved : resolveRequest program current with
      | error error =>
          simp [resolved, bind, Except.bind] at result
      | ok currentSpecialized =>
          by_cases present : currentSpecialized.key ∈ seen
          · have chosen :
                (seen.any fun key => decide (key = currentSpecialized.key)) =
                  true :=
              (any_key_eq_true_iff seen currentSpecialized.key).2 present
            simp [resolved, chosen, bind, Except.bind] at result
            simp only [List.mem_cons] at requestMember
            rcases requestMember with rfl | requestMember
            · rw [resolved] at resolvedRequest
              cases resolvedRequest
              exact .inl (.tail _ present)
            · exact ih (request := request) (specialized := specialized) result
                requestMember resolvedRequest
          · have chosen :
                (seen.any fun key => decide (key = currentSpecialized.key)) =
                  false := by
              cases choice :
                  (seen.any fun key => decide (key = currentSpecialized.key)) with
              | false => rfl
              | true =>
                  exact False.elim (present
                    ((any_key_eq_true_iff seen currentSpecialized.key).1 choice))
            simp [resolved, chosen, bind, Except.bind] at result
            cases result
            simp only [List.mem_cons] at requestMember
            rcases requestMember with rfl | requestMember
            · rw [resolved] at resolvedRequest
              cases resolvedRequest
              exact .inl (.head _)
            · exact .inr ⟨request, requestMember, specialized,
                resolvedRequest, rfl⟩

private theorem nextUnseen_some_preserves_covered (program : CheckedProgram)
    (seen : List SourceSpecialization.SpecializationKey) (queue : List Request)
    (request : Request) (specialized : SourceSpecialization.SpecializedFunction)
    (rest : List Request)
    (result : nextUnseen program seen queue =
      .ok (some (request, specialized, rest)))
    (key : SourceSpecialization.SpecializationKey)
    (covered : CoveredKey program seen queue key) :
    CoveredKey program (specialized.key :: seen) rest key := by
  rcases covered with seenMember | ⟨queued, queuedMember, resolved,
      resolvedOk, rfl⟩
  · exact .inl (.tail _ seenMember)
  · exact nextUnseen_some_resolved_covered program seen queue request
      specialized rest result queued queuedMember resolved resolvedOk

private theorem coveredKey_append_queue (program : CheckedProgram)
    (seen : List SourceSpecialization.SpecializationKey)
    (left right : List Request) (key : SourceSpecialization.SpecializationKey)
    (covered : CoveredKey program seen left key) :
    CoveredKey program seen (left ++ right) key := by
  rcases covered with seenMember | ⟨request, member, resolved⟩
  · exact .inl seenMember
  · exact .inr ⟨request, List.mem_append_left right member, resolved⟩

private theorem canonicalSeedKeys_cover (program : CheckedProgram)
    (seeds : List Request)
    (seedKeys : List SourceSpecialization.SpecializationKey)
    (result : canonicalSeedKeys program seeds = .ok seedKeys) :
    ∀ key ∈ seedKeys, CoveredKey program [] seeds key := by
  induction seeds generalizing seedKeys with
  | nil =>
      simp [canonicalSeedKeys, pure, Pure.pure, Except.pure] at result
      subst seedKeys
      simp
  | cons request rest ih =>
      simp only [canonicalSeedKeys] at result
      obtain ⟨specialized, resolved, continuation⟩ :=
        except_bind_ok _ _ _ result
      obtain ⟨restKeys, recursive, shape⟩ :=
        except_bind_ok _ _ _ continuation
      have seedShape : specialized.key :: restKeys = seedKeys := by
        simpa [pure, Pure.pure, Except.pure] using shape
      subst seedKeys
      intro key member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact .inr ⟨request, .head _, specialized, resolved, rfl⟩
      · have covered := ih restKeys recursive key member
        rcases covered with seenMember | ⟨queued, queuedMember, resolved⟩
        · simp at seenMember
        · exact .inr ⟨queued, .tail _ queuedMember, resolved⟩

@[simp] theorem run_empty (program : CheckedProgram) (budget : Nat) :
    run program [] budget = .ok (.complete {
      seedKeys := []
      specializations := []
      callEdges := []
    }) := by
  cases budget <;> rfl

theorem run_zero_single (program : CheckedProgram) (request : Request)
    (specialized : SourceSpecialization.SpecializedFunction)
    (resolved : resolveRequest program request = .ok specialized) :
    run program [request] 0 = .ok (.budgetExhausted {
      seedKeys := [specialized.key]
      specializations := []
      callEdges := []
    } specialized.key [request]) := by
  simp [run, canonicalSeedKeys, runAux, nextUnseen, resolved]
  rfl

theorem runAux_preserves_seedKeys (program : CheckedProgram)
    (seedKeys : List SourceSpecialization.SpecializationKey)
    (queue : List Request)
    (seen : List SourceSpecialization.SpecializationKey)
    (specializations : List SourceSpecialization.SpecializedFunction)
    (callEdges : List CallEdge) (referenceEdges : List ReferenceEdge)
    (budget : Nat) (outcome : Outcome)
    (result : runAux program seedKeys queue seen specializations callEdges
      referenceEdges budget = .ok outcome) :
    outcome.plan.seedKeys = seedKeys := by
  induction budget generalizing queue seen specializations callEdges
      referenceEdges outcome with
  | zero =>
      simp only [runAux] at result
      obtain ⟨next, _, continuation⟩ := except_bind_ok _ _ _ result
      cases next with
      | none =>
          have shape : Outcome.complete {
              seedKeys, specializations, callEdges, referenceEdges } = outcome := by
            simpa [pure, Pure.pure, Except.pure] using continuation
          rw [← shape]
          rfl
      | some entry =>
          rcases entry with ⟨request, specialized, rest⟩
          have shape : Outcome.budgetExhausted {
              seedKeys, specializations, callEdges, referenceEdges }
              specialized.key (request :: rest) = outcome := by
            simpa [pure, Pure.pure, Except.pure] using continuation
          rw [← shape]
          rfl
  | succ budget ih =>
      simp only [runAux] at result
      obtain ⟨next, _, continuation⟩ := except_bind_ok _ _ _ result
      cases next with
      | none =>
          have shape : Outcome.complete {
              seedKeys, specializations, callEdges, referenceEdges } = outcome := by
            simpa [pure, Pure.pure, Except.pure] using continuation
          rw [← shape]
          rfl
      | some entry =>
          rcases entry with ⟨request, specialized, rest⟩
          obtain ⟨found, _, recursive⟩ :=
            except_bind_ok _ _ _ continuation
          rcases found with ⟨requests, edges, references⟩
          exact ih _ _ _ _ _ _ recursive

theorem runAux_specializationKeys_nodup (program : CheckedProgram)
    (seedKeys : List SourceSpecialization.SpecializationKey)
    (queue : List Request)
    (seen : List SourceSpecialization.SpecializationKey)
    (specializations : List SourceSpecialization.SpecializedFunction)
    (callEdges : List CallEdge) (referenceEdges : List ReferenceEdge)
    (budget : Nat) (outcome : Outcome)
    (aligned : specializations.map (·.key) = seen.reverse)
    (unique : seen.Nodup)
    (result : runAux program seedKeys queue seen specializations callEdges
      referenceEdges budget = .ok outcome) :
    outcome.plan.specializationKeys.Nodup := by
  induction budget generalizing queue seen specializations callEdges
      referenceEdges outcome with
  | zero =>
      simp only [runAux] at result
      obtain ⟨next, _, continuation⟩ := except_bind_ok _ _ _ result
      have currentUnique : (specializations.map (·.key)).Nodup := by
        rw [aligned]
        exact nodup_reverse seen unique
      cases next with
      | none =>
          have shape : Outcome.complete {
              seedKeys, specializations, callEdges, referenceEdges } = outcome := by
            simpa [pure, Pure.pure, Except.pure] using continuation
          rw [← shape]
          exact currentUnique
      | some entry =>
          rcases entry with ⟨request, specialized, rest⟩
          have shape : Outcome.budgetExhausted {
              seedKeys, specializations, callEdges, referenceEdges }
              specialized.key (request :: rest) = outcome := by
            simpa [pure, Pure.pure, Except.pure] using continuation
          rw [← shape]
          exact currentUnique
  | succ budget ih =>
      simp only [runAux] at result
      obtain ⟨next, nextResult, continuation⟩ :=
        except_bind_ok _ _ _ result
      cases next with
      | none =>
          have shape : Outcome.complete {
              seedKeys, specializations, callEdges, referenceEdges } = outcome := by
            simpa [pure, Pure.pure, Except.pure] using continuation
          rw [← shape]
          change (specializations.map (·.key)).Nodup
          rw [aligned]
          exact nodup_reverse seen unique
      | some entry =>
          rcases entry with ⟨request, specialized, rest⟩
          have fresh : specialized.key ∉ seen :=
            nextUnseen_some_key_not_mem program seen queue request specialized
              rest nextResult
          obtain ⟨found, _, recursive⟩ :=
            except_bind_ok _ _ _ continuation
          rcases found with ⟨requests, edges, references⟩
          have nextAligned :
              (specializations ++ [specialized]).map (·.key) =
                (specialized.key :: seen).reverse := by
            simp [aligned]
          have nextUnique : (specialized.key :: seen).Nodup :=
            List.nodup_cons.mpr ⟨fresh, unique⟩
          exact ih _ _ _ _ _ _ nextAligned nextUnique recursive

private theorem runAux_complete_seedKeys_mem (program : CheckedProgram)
    (seedKeys : List SourceSpecialization.SpecializationKey)
    (queue : List Request)
    (seen : List SourceSpecialization.SpecializationKey)
    (specializations : List SourceSpecialization.SpecializedFunction)
    (callEdges : List CallEdge) (referenceEdges : List ReferenceEdge)
    (budget : Nat) (plan : Plan)
    (aligned : specializations.map (·.key) = seen.reverse)
    (covered : ∀ key ∈ seedKeys, CoveredKey program seen queue key)
    (result : runAux program seedKeys queue seen specializations callEdges
      referenceEdges budget = .ok (.complete plan)) :
    ∀ key ∈ seedKeys, key ∈ plan.specializationKeys := by
  induction budget generalizing queue seen specializations callEdges
      referenceEdges plan with
  | zero =>
      simp only [runAux] at result
      obtain ⟨next, nextResult, continuation⟩ :=
        except_bind_ok _ _ _ result
      cases next with
      | none =>
          have shape : {
              seedKeys, specializations, callEdges, referenceEdges } = plan := by
            simpa [pure, Pure.pure, Except.pure] using continuation
          subst plan
          intro key member
          change key ∈ specializations.map (·.key)
          rw [aligned]
          simpa using nextUnseen_none_covers program seen queue nextResult key
            (covered key member)
      | some entry =>
          rcases entry with ⟨request, specialized, rest⟩
          simp [pure, Pure.pure, Except.pure] at continuation
  | succ budget ih =>
      simp only [runAux] at result
      obtain ⟨next, nextResult, continuation⟩ :=
        except_bind_ok _ _ _ result
      cases next with
      | none =>
          have shape : {
              seedKeys, specializations, callEdges, referenceEdges } = plan := by
            simpa [pure, Pure.pure, Except.pure] using continuation
          subst plan
          intro key member
          change key ∈ specializations.map (·.key)
          rw [aligned]
          simpa using nextUnseen_none_covers program seen queue nextResult key
            (covered key member)
      | some entry =>
          rcases entry with ⟨request, specialized, rest⟩
          obtain ⟨found, _, recursive⟩ :=
            except_bind_ok _ _ _ continuation
          rcases found with ⟨requests, edges, references⟩
          have nextAligned :
              (specializations ++ [specialized]).map (·.key) =
                (specialized.key :: seen).reverse := by
            simp [aligned]
          have nextCovered : ∀ key ∈ seedKeys,
              CoveredKey program (specialized.key :: seen)
                (rest ++ requests) key := by
            intro key member
            exact coveredKey_append_queue program (specialized.key :: seen)
              rest requests key
              (nextUnseen_some_preserves_covered program seen queue request
                specialized rest nextResult key (covered key member))
          exact ih _ _ _ _ _ _ nextAligned nextCovered recursive

theorem runAux_specializations_length_le (program : CheckedProgram)
    (seedKeys : List SourceSpecialization.SpecializationKey)
    (queue : List Request)
    (seen : List SourceSpecialization.SpecializationKey)
    (specializations : List SourceSpecialization.SpecializedFunction)
    (callEdges : List CallEdge) (referenceEdges : List ReferenceEdge)
    (budget : Nat) (outcome : Outcome)
    (result : runAux program seedKeys queue seen specializations callEdges
      referenceEdges budget = .ok outcome) :
    outcome.plan.specializations.length ≤ specializations.length + budget := by
  induction budget generalizing queue seen specializations callEdges
      referenceEdges outcome with
  | zero =>
      simp only [runAux] at result
      obtain ⟨next, _, continuation⟩ := except_bind_ok _ _ _ result
      cases next with
      | none =>
          have shape : Outcome.complete {
              seedKeys, specializations, callEdges, referenceEdges } = outcome := by
            simpa [pure, Pure.pure, Except.pure] using continuation
          rw [← shape]
          simp
      | some entry =>
          rcases entry with ⟨request, specialized, rest⟩
          have shape : Outcome.budgetExhausted {
              seedKeys, specializations, callEdges, referenceEdges }
              specialized.key (request :: rest) = outcome := by
            simpa [pure, Pure.pure, Except.pure] using continuation
          rw [← shape]
          simp
  | succ budget ih =>
      simp only [runAux] at result
      obtain ⟨next, _, continuation⟩ := except_bind_ok _ _ _ result
      cases next with
      | none =>
          have shape : Outcome.complete {
              seedKeys, specializations, callEdges, referenceEdges } = outcome := by
            simpa [pure, Pure.pure, Except.pure] using continuation
          rw [← shape]
          simp only [Outcome.plan_complete]
          omega
      | some entry =>
          rcases entry with ⟨request, specialized, rest⟩
          obtain ⟨found, _, recursive⟩ :=
            except_bind_ok _ _ _ continuation
          rcases found with ⟨requests, edges, references⟩
          have bound := ih _ _ _ _ _ _ recursive
          simp only [List.length_append, List.length_singleton] at bound
          omega

theorem run_preserves_seedKeys (program : CheckedProgram)
    (seeds : List Request) (budget : Nat) (outcome : Outcome)
    (seedKeys : List SourceSpecialization.SpecializationKey)
    (canonical : canonicalSeedKeys program seeds = .ok seedKeys)
    (result : run program seeds budget = .ok outcome) :
    outcome.plan.seedKeys = seedKeys := by
  simp only [run, canonical] at result
  exact runAux_preserves_seedKeys program seedKeys seeds [] [] [] [] budget
    outcome result

/-- Successful worklist execution admits each canonical specialization key at
most once, independently of whether the finite frontier closes. -/
theorem run_specializationKeys_nodup (program : CheckedProgram)
    (seeds : List Request) (budget : Nat) (outcome : Outcome)
    (result : run program seeds budget = .ok outcome) :
    outcome.plan.specializationKeys.Nodup := by
  simp only [run] at result
  obtain ⟨seedKeys, _, recursive⟩ := except_bind_ok _ _ _ result
  exact runAux_specializationKeys_nodup program seedKeys seeds [] [] [] []
    budget outcome (by simp) (by simp) recursive

theorem run_complete_specializationKeys_nodup (program : CheckedProgram)
    (seeds : List Request) (budget : Nat) (plan : Plan)
    (result : run program seeds budget = .ok (.complete plan)) :
    plan.specializationKeys.Nodup := by
  simpa using run_specializationKeys_nodup program seeds budget
    (.complete plan) result

theorem run_budgetExhausted_specializationKeys_nodup
    (program : CheckedProgram) (seeds : List Request) (budget : Nat)
    (plan : Plan) (next : SourceSpecialization.SpecializationKey)
    (pending : List Request)
    (result : run program seeds budget =
      .ok (.budgetExhausted plan next pending)) :
    plan.specializationKeys.Nodup := by
  simpa using run_specializationKeys_nodup program seeds budget
    (.budgetExhausted plan next pending) result

/-- A closed worklist plan contains every eagerly canonicalized seed key.  Seed
order and duplicates remain in `seedKeys`; admission itself is unique. -/
theorem run_complete_seedKeys_mem (program : CheckedProgram)
    (seeds : List Request) (budget : Nat) (plan : Plan)
    (result : run program seeds budget = .ok (.complete plan)) :
    ∀ key ∈ plan.seedKeys, key ∈ plan.specializationKeys := by
  simp only [run] at result
  obtain ⟨seedKeys, canonical, recursive⟩ := except_bind_ok _ _ _ result
  have preserved := runAux_preserves_seedKeys program seedKeys seeds [] [] [] []
    budget (.complete plan) recursive
  have included := runAux_complete_seedKeys_mem program seedKeys seeds [] [] [] []
    budget plan (by simp) (canonicalSeedKeys_cover program seeds seedKeys canonical)
    recursive
  simp only [Outcome.plan_complete] at preserved
  rw [preserved]
  exact included

/-- A successful public run records exactly the eagerly canonicalized seeds. -/
theorem run_seedKeys_eq_canonical (program : CheckedProgram)
    (seeds : List Request) (budget : Nat) (outcome : Outcome)
    (result : run program seeds budget = .ok outcome) :
    canonicalSeedKeys program seeds = .ok outcome.plan.seedKeys := by
  simp only [run] at result
  obtain ⟨seedKeys, canonical, recursive⟩ := except_bind_ok _ _ _ result
  have preserved := runAux_preserves_seedKeys program seedKeys seeds [] [] [] []
    budget outcome recursive
  simpa [preserved] using canonical

/-- Every ordinary worklist outcome respects the distinct-specialization
budget, independently of whether the frontier closes. -/
theorem run_specializations_length_le (program : CheckedProgram)
    (seeds : List Request) (budget : Nat) (outcome : Outcome)
    (result : run program seeds budget = .ok outcome) :
    outcome.plan.specializations.length ≤ budget := by
  simp only [run] at result
  obtain ⟨seedKeys, _, recursive⟩ := except_bind_ok _ _ _ result
  simpa using
    runAux_specializations_length_le program seedKeys seeds [] [] [] []
      budget outcome recursive

theorem run_complete_specializations_length_le (program : CheckedProgram)
    (seeds : List Request) (budget : Nat) (plan : Plan)
    (result : run program seeds budget = .ok (.complete plan)) :
    plan.specializations.length ≤ budget := by
  simpa using run_specializations_length_le program seeds budget
    (.complete plan) result

theorem run_budgetExhausted_specializations_length_le
    (program : CheckedProgram) (seeds : List Request) (budget : Nat)
    (plan : Plan) (next : SourceSpecialization.SpecializationKey)
    (pending : List Request)
    (result : run program seeds budget =
      .ok (.budgetExhausted plan next pending)) :
    plan.specializations.length ≤ budget := by
  simpa using run_specializations_length_le program seeds budget
    (.budgetExhausted plan next pending) result

end Solcore.Frontend.SourceSpecializationWorklist
