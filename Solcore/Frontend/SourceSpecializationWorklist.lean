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
  | duplicatePlanSpecializations
      (key : SourceSpecialization.SpecializationKey) (count : Nat)
  | existingSpecializationMismatch
      (key : SourceSpecialization.SpecializationKey)
  | outerEdgeCalleeMismatch
      (root edge : SourceSpecialization.SpecializationKey)
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

/-- A generalized ordinary let whose initializer is directly a lambda.
Stable binder and expression identities are retained from typed source. -/
structure LocalLambdaBinding where
  binder : TypedBinder
  initializer : ExpressionId
  deriving Repr, BEq, DecidableEq

/-- One reachable local template context. Equality includes the entire
cumulative flexible substitution, not only the lambda's resulting type. -/
structure LocalLambdaInstance where
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

private def deduplicateRequirementLists
    (candidates : List (List RequirementId)) : List (List RequirementId) :=
  candidates.foldl (fun unique candidate =>
    if unique.contains candidate then unique else unique ++ [candidate]) []

/-- A declaration use owns the instantiated signature requirements between a
possible overload-result coercion prefix and a contextual coercion suffix.
References have only the suffix case, which is the split at zero. -/
private def declarationRequirementCandidates (expression : ExpressionNode)
    (predicateCount : Nat) : List (List RequirementId) :=
  let splits := match expression.form with
    | .call _ _ (.declaration _) =>
        List.range (expression.coercions.length + 1)
    | .reference _ (.declaration _) => [0]
    | _ => []
  deduplicateRequirementLists <|
    splits.filterMap fun split =>
      let before := coercionRequirements (expression.coercions.take split)
      let after := coercionRequirements (expression.coercions.drop split)
      let middleAndAfter := expression.requirements.drop before.length
      let middle := middleAndAfter.take predicateCount
      if expression.requirements.take before.length = before &&
          middle.length = predicateCount &&
          middleAndAfter.drop predicateCount = after then
        some middle
      else
        none

private def exactDeclarationRequirementIds (expression : ExpressionNode)
    (instantiation : DeclarationInstantiation) :
    Except Error (List RequirementId) := do
  if expression.coercions.isEmpty &&
      expression.requirements.length != instantiation.predicates.length then
    throw (.localSchemeCallRequirementCountMismatch expression.id
      instantiation.predicates.length expression.requirements.length)
  match firstDuplicateRequirement expression.requirements with
  | some requirement =>
      let count := (expression.requirements.filter fun candidate =>
        candidate == requirement).length
      throw (.localSchemeRequirementIdMultiplicity expression.id requirement count)
  | none => pure ()
  match declarationRequirementCandidates expression
      instantiation.predicates.length with
  | [requirements] => pure requirements
  | _ => throw (.localSchemeCallRequirementCountMismatch expression.id
      instantiation.predicates.length expression.requirements.length)

private def validateQualifiedLocalDeclarationUse
    (localInstance : LocalLambdaInstance) (expression : ExpressionNode)
    (instantiation : DeclarationInstantiation) : Except Error Unit := do
  let requirements ← exactDeclarationRequirementIds expression instantiation
  let owned := localInstance.binding.binder.schemeRequirements.filter fun owned =>
    requirements.contains owned.templateRequirement
  for requirement in owned do
    let count := (requirements.filter fun candidate =>
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
  let declarationUses := nodes.filterMap fun
    | .expression node =>
        match declarationInstantiation? node with
        | some _ => some node
        | none => none
    | .statement _ => none
  for requirement in own do
    let count := declarationUses.foldl (fun count declarationUse =>
      count + (declarationUse.requirements.filter fun candidate =>
        candidate == requirement).length) 0
    if count != 1 then
      throw (.localSchemeRequirementIdMultiplicity
        localInstance.binding.initializer requirement count)
  for declarationUse in declarationUses do
    match declarationUse.requirements.find? fun requirement =>
        all.contains requirement && !own.contains requirement with
    | some requirement =>
        throw (.foreignLocalSchemeRequirement declarationUse.id requirement)
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
                        validateQualifiedLocalDeclarationUse localInstance
                          expression instantiation
                    | .reference _ (.declaration _) =>
                        if directCallees.contains expression.id then
                          pure ()
                        else
                          validateQualifiedLocalDeclarationUse localInstance
                            expression instantiation
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

/-- Expose the same ordered local-template contexts used by declaration-edge
discovery. Exact binding/substitution duplicates are retained once, in first
discovery order. The optional fuel is a diagnostic override of the existing
compile-time context closure; normal planning uses the unchanged derived bound.
Success validates the existing open-declaration policy, not runtime semantics
or completeness of specialization for a wider source language. -/
def localLambdaInstances (source : TypedSource) (contextFuel : Option Nat := none) :
    Except Error (List LocalLambdaInstance) := do
  let bindings := directPolymorphicLambdaBindings source
  let initialInstances ← rootLocalLambdaInstances source bindings
  let instances ← match contextFuel with
    | none => closeLocalLambdaInstances source bindings initialInstances
    | some fuel =>
        closeLocalLambdaInstancesAux source bindings initialInstances initialInstances fuel
  validateOpenDeclarationsCovered source bindings instances
  pure instances

/-- Original typed nodes in one lambda's direct lexical body, in source-node
order. Nested generalized lambdas remain boundaries, as in edge discovery.
Metadata is retained before the instance's cumulative substitution is applied. -/
def localLambdaBodyNodes (source : TypedSource) (localInstance : LocalLambdaInstance) :
    Except Error (List Node) := do
  let ids ← localLambdaBodyNodeIds source (directPolymorphicLambdaBindings source)
    localInstance.binding
  pure (selectedNodes ids source.nodes)

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
  let instances ← localLambdaInstances source
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

private def firstDuplicatePlanSpecialization :
    List SourceSpecialization.SpecializedFunction →
      Option (SourceSpecialization.SpecializationKey × Nat)
  | [] => none
  | specialized :: rest =>
      let duplicates := rest.filter fun candidate =>
        decide (candidate.key = specialized.key)
      if duplicates.isEmpty then
        firstDuplicatePlanSpecialization rest
      else
        some (specialized.key, duplicates.length + 1)

/-- Reject the first duplicate specialization key in plan order. Shared by
plan extension and evaluator-independent local-instance catalog preparation. -/
def validatePlanSpecializationsUnique (plan : Plan) :
    Except Error Unit :=
  match firstDuplicatePlanSpecialization plan.specializations with
  | none => pure ()
  | some (key, count) => throw (.duplicatePlanSpecializations key count)

/-- Extend an already complete plan with one pre-resolved, detached callable
root and the synthetic direct-call edge by which an existing specialization
invokes it.  The supplied root itself is already admitted and therefore does
not consume `budget`; the budget counts only previously unseen helpers found
while closing its ordinary direct-call and declaration-reference frontier.

`seedKeys` remains the original public-root list.  Existing exact edges are
normalized and every newly collected edge is merged idempotently.  An existing
root key must name exactly the supplied carrier, and every specialization key
in the input plan must already be unique.  The root body is rescanned even when
the root is already present, so applying this operation again is idempotent and
can also repair a plan whose detached-root frontier was not yet merged. -/
def extendCompletePlan (program : CheckedProgram) (plan : Plan)
    (root : SourceSpecialization.SpecializedFunction) (outerEdge : CallEdge)
    (budget : Nat) : Except Error Outcome := do
  validatePlanSpecializationsUnique plan
  if outerEdge.callee != root.key then
    throw (.outerEdgeCalleeMismatch root.key outerEdge.callee)
  let existingRoot := plan.specializations.find? fun specialized =>
    decide (specialized.key = root.key)
  let specializations ← match existingRoot with
    | none => pure (plan.specializations ++ [root])
    | some existing =>
        if existing == root then
          pure plan.specializations
        else
          throw (.existingSpecializationMismatch root.key)
  let seen := specializations.map (fun specialized => specialized.key)
  let callEdges := appendCallEdges [] plan.callEdges
  let referenceEdges := appendReferenceEdges [] plan.referenceEdges
  let callEdges := appendCallEdge callEdges outerEdge
  let (requests, rootCalls, rootReferences) ←
    collectAllReferences program root.key root.function.typedBody
  runAux program plan.seedKeys requests seen specializations
    (appendCallEdges callEdges rootCalls)
    (appendReferenceEdges referenceEdges rootReferences) budget

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
            have selectedResult :
                (current, currentSpecialized, tail) =
                  (request, specialized, rest) := by
              simpa [resolved, selected, bind, Except.bind] using result
            cases selectedResult
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
            have selectedResult :
                (current, currentSpecialized, tail) =
                  (selectedRequest, selected, rest) := by
              simpa [resolved, chosen, bind, Except.bind] using result
            cases selectedResult
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

namespace Solcore.Frontend.SourceSpecializationWorklist

open SourceInference TypeSystem

/-- Every discovered localInstance retains the original local read which selected
its exact binder and cumulative substitution. Contextual reads retain the
already discovered parent, so the receipt follows actual worklist ancestry. -/
inductive LocalLambdaInstance.ReadOrigin (source : TypedSource) : LocalLambdaInstance → Prop where
  | root {localInstance : LocalLambdaInstance} (expression : ExpressionNode)
      (present : Node.expression expression ∈ source.nodes) (name : String)
      (form : expression.form = .reference name (.local localInstance.binding.binder.id))
      (matched : SourceSpecialization.matchClosedSchemeInstance?
        localInstance.binding.binder.scheme expression.rawType = some localInstance.substitution) :
      ReadOrigin source localInstance
  | contextual {localInstance parent : LocalLambdaInstance}
      (parentOrigin : ReadOrigin source parent) (expression : ExpressionNode)
      (present : Node.expression expression ∈ source.nodes) (name : String)
      (form : expression.form = .reference name (.local localInstance.binding.binder.id))
      (child : Substitution)
      (matched : SourceSpecialization.matchClosedSchemeInstance?
        (Scheme.apply parent.substitution localInstance.binding.binder.scheme)
        (parent.substitution.apply expression.rawType) = some child)
      (cumulative : localInstance.substitution = child.compose parent.substitution) :
      ReadOrigin source localInstance

private theorem selectedNodes_subset (ids : List NodeId) (nodes : List Node) :
    ∀ node ∈ selectedNodes ids nodes, node ∈ nodes := by
  induction nodes with
  | nil => simp [selectedNodes]
  | cons head tail ih =>
      simp only [selectedNodes]
      split
      · intro node member
        rcases List.mem_cons.mp member with rfl | member
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih node member)
      · exact fun node member => List.mem_cons_of_mem _ (ih node member)

private theorem insertLocalLambdaInstance_origin {source : TypedSource}
    {instances : List LocalLambdaInstance} {localInstance : LocalLambdaInstance}
    (prior : ∀ value ∈ instances, LocalLambdaInstance.ReadOrigin source value)
    (current : LocalLambdaInstance.ReadOrigin source localInstance) :
    ∀ value ∈ insertLocalLambdaInstance instances localInstance, LocalLambdaInstance.ReadOrigin source value := by
  unfold insertLocalLambdaInstance
  split
  · exact prior
  · intro value member
    rcases List.mem_append.mp member with old | added
    · exact prior value old
    · cases List.mem_singleton.mp added
      exact current

private theorem exactLocalLambdaBinding_id {bindings : List LocalLambdaBinding}
    {id : Resolved.LocalId} {binding : LocalLambdaBinding}
    (accepted : exactLocalLambdaBinding? bindings id = some binding) : binding.binder.id = id := by
  unfold exactLocalLambdaBinding? at accepted
  split at accepted <;> try contradiction
  rename_i only selected
  cases Option.some.inj accepted
  have member : binding ∈ bindings.filter (fun value => value.binder.id == id) := by
    rw [selected]
    exact List.mem_cons_self
  exact of_decide_eq_true (List.mem_filter.mp member).2

private theorem collectGroundLocalLambdaInstances_origins
    {source : TypedSource} (bindings : List LocalLambdaBinding) (nodes : List Node)
    (contained : ∀ node ∈ nodes, node ∈ source.nodes)
    (prior result : List LocalLambdaInstance)
    (origins : ∀ value ∈ prior, LocalLambdaInstance.ReadOrigin source value)
    (accepted : collectGroundLocalLambdaInstances bindings nodes prior = .ok result) :
    ∀ value ∈ result, LocalLambdaInstance.ReadOrigin source value := by
  induction nodes generalizing prior with
  | nil =>
      cases Except.ok.inj accepted
      exact origins
  | cons head tail ih =>
      have rest := fun node member => contained node (List.mem_cons_of_mem head member)
      have current := contained head List.mem_cons_self
      cases head with
      | statement statement => exact ih rest prior origins accepted
      | expression expression =>
        cases form : expression.form <;>
          simp only [collectGroundLocalLambdaInstances, form] at accepted
        all_goals try exact ih rest prior origins accepted
        rename_i name resolution
        cases resolution <;> simp only at accepted
        all_goals try exact ih rest prior origins accepted
        rename_i id
        cases found : exactLocalLambdaBinding? bindings id with
        | none =>
            simp only [found] at accepted
            exact ih rest prior origins accepted
        | some binding =>
            simp only [found] at accepted
            split at accepted
            · exact ih rest prior origins accepted
            · cases matched : SourceSpecialization.matchClosedSchemeInstance? binding.binder.scheme expression.rawType with
              | none => simp [matched, bind, Except.bind, throw] at accepted
              | some substitution =>
                  simp only [matched, pure, Pure.pure, Except.pure, bind, Except.bind] at accepted
                  apply ih rest _ (insertLocalLambdaInstance_origin origins ?_) accepted
                  exact .root expression current name
                    (by rw [exactLocalLambdaBinding_id found]; exact form) matched

private theorem collectContextualLocalLambdaInstances_origins
    {source : TypedSource} (bindings : List LocalLambdaBinding) (parent : LocalLambdaInstance)
    (parentOrigin : LocalLambdaInstance.ReadOrigin source parent)
    (nodes : List Node) (contained : ∀ node ∈ nodes, node ∈ source.nodes)
    (prior result : List LocalLambdaInstance)
    (origins : ∀ value ∈ prior, LocalLambdaInstance.ReadOrigin source value)
    (accepted : collectContextualLocalLambdaInstances bindings parent nodes prior = .ok result) :
    ∀ value ∈ result, LocalLambdaInstance.ReadOrigin source value := by
  induction nodes generalizing prior with
  | nil =>
      cases Except.ok.inj accepted
      exact origins
  | cons head tail ih =>
      have rest := fun node member => contained node (List.mem_cons_of_mem head member)
      have current := contained head List.mem_cons_self
      cases head with
      | statement statement => exact ih rest prior origins accepted
      | expression expression =>
        cases form : expression.form <;>
          simp only [collectContextualLocalLambdaInstances, form] at accepted
        all_goals try exact ih rest prior origins accepted
        rename_i name resolution
        cases resolution <;> simp only at accepted
        all_goals try exact ih rest prior origins accepted
        rename_i id
        cases found : exactLocalLambdaBinding? bindings id with
        | none =>
            simp only [found] at accepted
            exact ih rest prior origins accepted
        | some binding =>
            simp only [found] at accepted
            split at accepted
            · exact ih rest prior origins accepted
            · cases matched : SourceSpecialization.matchClosedSchemeInstance?
                  (Scheme.apply parent.substitution binding.binder.scheme)
                  (parent.substitution.apply expression.rawType) with
              | none => simp [matched, bind, Except.bind, throw] at accepted
              | some substitution =>
                  simp only [matched, pure, Pure.pure, Except.pure, bind, Except.bind] at accepted
                  apply ih rest _ (insertLocalLambdaInstance_origin origins ?_) accepted
                  exact .contextual parentOrigin expression current name
                    (by rw [exactLocalLambdaBinding_id found]; exact form) substitution matched rfl

private theorem rootLocalLambdaInstances_origins {source : TypedSource}
    {bindings : List LocalLambdaBinding} {result : List LocalLambdaInstance}
    (accepted : rootLocalLambdaInstances source bindings = .ok result) :
    ∀ value ∈ result, LocalLambdaInstance.ReadOrigin source value := by
  unfold rootLocalLambdaInstances at accepted
  cases selected : directLexicalNodeIds source (bindings.map (·.initializer)) source.roots with
  | error error => simp [selected, bind, Except.bind] at accepted
  | ok ids =>
      simp only [selected, bind, Except.bind] at accepted
      exact collectGroundLocalLambdaInstances_origins bindings (selectedNodes ids source.nodes)
        (selectedNodes_subset ids source.nodes) [] result (by simp) accepted

private theorem appendLocalLambdaInstances_origins {source : TypedSource}
    (left right : List LocalLambdaInstance)
    (prior : ∀ value ∈ left, LocalLambdaInstance.ReadOrigin source value)
    (added : ∀ value ∈ right, LocalLambdaInstance.ReadOrigin source value) :
    ∀ value ∈ appendLocalLambdaInstances left right, LocalLambdaInstance.ReadOrigin source value := by
  unfold appendLocalLambdaInstances
  induction right generalizing left with
  | nil => exact prior
  | cons head tail ih =>
      simp only [List.foldl_cons]
      exact ih _ (insertLocalLambdaInstance_origin prior (added head List.mem_cons_self))
        (fun value member => added value (List.mem_cons_of_mem _ member))

private theorem closeLocalLambdaInstancesAux_origins {source : TypedSource}
    (bindings : List LocalLambdaBinding) (fuel : Nat)
    (seen frontier result : List LocalLambdaInstance)
    (known : ∀ value ∈ seen, LocalLambdaInstance.ReadOrigin source value)
    (queued : ∀ value ∈ frontier, LocalLambdaInstance.ReadOrigin source value)
    (accepted : closeLocalLambdaInstancesAux source bindings seen frontier fuel = .ok result) :
    ∀ value ∈ result, LocalLambdaInstance.ReadOrigin source value := by
  induction fuel generalizing seen frontier with
  | zero =>
      cases frontier with
      | nil => cases Except.ok.inj accepted; exact known
      | cons head rest => simp [closeLocalLambdaInstancesAux, throw] at accepted
  | succ fuel ih =>
      cases frontier with
      | nil => cases Except.ok.inj accepted; exact known
      | cons parent rest =>
          simp only [closeLocalLambdaInstancesAux] at accepted
          cases bodyIds : localLambdaBodyNodeIds source bindings parent.binding with
          | error error => simp [bodyIds, bind, Except.bind] at accepted
          | ok ids =>
              simp only [bodyIds, bind, Except.bind] at accepted
              cases discovered : collectContextualLocalLambdaInstances bindings parent
                  (selectedNodes ids source.nodes) [] with
              | error error => simp [discovered] at accepted
              | ok found =>
                  simp only [discovered] at accepted
                  have foundOrigins := collectContextualLocalLambdaInstances_origins bindings parent
                    (queued parent List.mem_cons_self) (selectedNodes ids source.nodes)
                    (selectedNodes_subset ids source.nodes) [] found (by simp) discovered
                  have freshOrigins : ∀ value ∈ found.filter (fun value => !seen.contains value),
                      LocalLambdaInstance.ReadOrigin source value :=
                    fun value member => foundOrigins value (List.mem_filter.mp member).1
                  apply ih _ _
                    (appendLocalLambdaInstances_origins _ _ known freshOrigins) ?_ accepted
                  intro value member
                  rcases List.mem_append.mp member with old | fresh
                  · exact queued value (List.mem_cons_of_mem _ old)
                  · exact freshOrigins value fresh

/-- Successful actual discovery cannot invent a local instantiation from its
type alone: each ordered output has an original local-read origin and exact
scheme matching through its complete parent substitution chain. -/
theorem localLambdaInstances_read_origin {source : TypedSource} {contextFuel : Option Nat}
    {result : List LocalLambdaInstance}
    (accepted : localLambdaInstances source contextFuel = .ok result) :
    ∀ value ∈ result, LocalLambdaInstance.ReadOrigin source value := by
  cases contextFuel <;> simp only [localLambdaInstances] at accepted
  all_goals
    obtain ⟨roots, initial, afterInitial⟩ := except_bind_ok _ _ _ accepted
    obtain ⟨values, closed, afterClosed⟩ := except_bind_ok _ _ _ afterInitial
    obtain ⟨_, _, completed⟩ := except_bind_ok _ _ _ afterClosed
    have same : values = result := by simpa only [pure, Pure.pure, Except.pure, Except.ok.injEq] using completed
    subst result
    have rootsOrigin := rootLocalLambdaInstances_origins initial
    exact closeLocalLambdaInstancesAux_origins _ _ _ _ _ rootsOrigin rootsOrigin closed

private theorem collectAllReferences_local_instances
    {program : CheckedProgram} {caller : SourceSpecialization.SpecializationKey}
    {source : TypedSource} {result : List Request × List CallEdge × List ReferenceEdge}
    (accepted : collectAllReferences program caller source = .ok result) :
    ∃ instances, localLambdaInstances source = .ok instances := by
  unfold collectAllReferences at accepted
  obtain ⟨_, _, afterDirect⟩ := except_bind_ok _ _ _ accepted
  obtain ⟨instances, discovered, _⟩ := except_bind_ok _ _ _ afterDirect
  exact ⟨instances, discovered⟩

private theorem runAux_local_instances (program : CheckedProgram)
    (seedKeys : List SourceSpecialization.SpecializationKey) (budget : Nat)
    (queue : List Request) (seen : List SourceSpecialization.SpecializationKey)
    (specializations : List SourceSpecialization.SpecializedFunction)
    (calls : List CallEdge) (references : List ReferenceEdge) (outcome : Outcome)
    (known : ∀ row ∈ specializations, ∃ instances,
      localLambdaInstances row.function.typedBody = .ok instances)
    (accepted : runAux program seedKeys queue seen specializations calls references budget = .ok outcome) :
    ∀ row ∈ outcome.plan.specializations, ∃ instances,
      localLambdaInstances row.function.typedBody = .ok instances := by
  induction budget generalizing queue seen specializations calls references outcome with
  | zero =>
      simp only [runAux] at accepted
      obtain ⟨next, _, finished⟩ := except_bind_ok _ _ _ accepted
      cases next with
      | none => cases Except.ok.inj finished; exact known
      | some entry =>
          rcases entry with ⟨request, specialized, rest⟩
          cases Except.ok.inj finished
          exact known
  | succ budget ih =>
      simp only [runAux] at accepted
      obtain ⟨next, _, continuation⟩ := except_bind_ok _ _ _ accepted
      cases next with
      | none => cases Except.ok.inj continuation; exact known
      | some entry =>
          rcases entry with ⟨request, specialized, rest⟩
          obtain ⟨found, discovered, recursive⟩ := except_bind_ok _ _ _ continuation
          rcases found with ⟨requests, edges, targets⟩
          apply ih _ _ _ _ _ _ ?_ recursive
          intro row member
          rcases List.mem_append.mp member with old | added
          · exact known row old
          · cases List.mem_singleton.mp added
            exact collectAllReferences_local_instances discovered

/-- Every actually processed specialization has its successful local-instance
discovery receipt. The conclusion concerns selected worklist rows only. -/
theorem run_local_instances {program : CheckedProgram} {seeds : List Request}
    {budget : Nat} {outcome : Outcome}
    (accepted : run program seeds budget = .ok outcome)
    {row : SourceSpecialization.SpecializedFunction}
    (member : row ∈ outcome.plan.specializations) :
    ∃ instances, localLambdaInstances row.function.typedBody = .ok instances ∧
      ∀ value ∈ instances, LocalLambdaInstance.ReadOrigin row.function.typedBody value := by
  unfold run at accepted
  obtain ⟨seedKeys, _, completed⟩ := except_bind_ok _ _ _ accepted
  obtain ⟨instances, discovered⟩ := runAux_local_instances program seedKeys budget
    seeds [] [] [] [] outcome (by simp) completed row member
  exact ⟨instances, discovered, localLambdaInstances_read_origin discovered⟩

private theorem exactFunction_member {program : CheckedProgram}
    {declaration : Resolved.DeclarationId} {function : CheckedFunction}
    (accepted : exactFunction program declaration = .ok function) :
    function ∈ program.functions := by
  unfold exactFunction at accepted
  generalize filtered : program.functions.filter (fun value => decide (value.declaration = declaration)) = candidates at accepted
  cases candidates with
  | nil => cases accepted
  | cons first rest =>
      cases rest with
      | nil =>
          cases Except.ok.inj accepted
          exact (List.mem_filter.mp (show function ∈ program.functions.filter
            (fun value => decide (value.declaration = declaration)) by rw [filtered]; exact List.mem_cons_self)).1
      | cons second tail => cases accepted

/-- An actual request retains the original checked function and the exact
specialization computation; equal types alone do not identify that source. -/
theorem resolveRequest_original {program : CheckedProgram} {request : Request}
    {specialized : SourceSpecialization.SpecializedFunction}
    (accepted : resolveRequest program request = .ok specialized) :
    ∃ original ∈ program.functions, ∃ signature,
      SourceSpecialization.specializeFunction signature original request.parameterSubstitution = .ok specialized := by
  unfold resolveRequest at accepted
  obtain ⟨declaration, _, afterDeclaration⟩ := except_bind_ok _ _ _ accepted
  split at afterDeclaration
  · cases afterDeclaration
  · obtain ⟨signature, _, afterSignature⟩ := except_bind_ok _ _ _ afterDeclaration
    obtain ⟨original, selected, afterOriginal⟩ := except_bind_ok _ _ _ afterSignature
    cases lowered : SourceSpecialization.specializeFunction signature original request.parameterSubstitution with
    | error error => simp [lowered, throw, throwThe, MonadExceptOf.throw] at afterOriginal
    | ok result =>
        simp only [lowered, pure, Except.pure, Except.ok.injEq] at afterOriginal
        subst result
        exact ⟨original, exactFunction_member selected, signature, lowered⟩

private theorem nextUnseen_resolved {program : CheckedProgram}
    {seen : List SourceSpecialization.SpecializationKey} {queue rest : List Request}
    {request : Request} {specialized : SourceSpecialization.SpecializedFunction}
    (accepted : nextUnseen program seen queue = .ok (some (request, specialized, rest))) :
    resolveRequest program request = .ok specialized := by
  induction queue with
  | nil => cases accepted
  | cons current tail ih =>
      simp only [nextUnseen] at accepted
      obtain ⟨value, resolved, following⟩ := except_bind_ok _ _ _ accepted
      split at following
      · exact ih following
      · have same : (current, value, tail) = (request, specialized, rest) := by
          simpa only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] using following
        cases same
        exact resolved

private theorem runAux_originals (program : CheckedProgram)
    (seedKeys : List SourceSpecialization.SpecializationKey) (budget : Nat)
    (queue : List Request) (seen : List SourceSpecialization.SpecializationKey)
    (specializations : List SourceSpecialization.SpecializedFunction)
    (calls : List CallEdge) (references : List ReferenceEdge) (outcome : Outcome)
    (known : ∀ row ∈ specializations, ∃ request, resolveRequest program request = .ok row)
    (accepted : runAux program seedKeys queue seen specializations calls references budget = .ok outcome) :
    ∀ row ∈ outcome.plan.specializations, ∃ request, resolveRequest program request = .ok row := by
  induction budget generalizing queue seen specializations calls references outcome with
  | zero =>
      simp only [runAux] at accepted
      obtain ⟨next, _, finished⟩ := except_bind_ok _ _ _ accepted
      cases next with
      | none => cases Except.ok.inj finished; exact known
      | some entry =>
          rcases entry with ⟨request, specialized, rest⟩
          cases Except.ok.inj finished
          exact known
  | succ budget ih =>
      simp only [runAux] at accepted
      obtain ⟨next, selected, continuation⟩ := except_bind_ok _ _ _ accepted
      cases next with
      | none => cases Except.ok.inj continuation; exact known
      | some entry =>
          rcases entry with ⟨request, specialized, rest⟩
          obtain ⟨found, _, recursive⟩ := except_bind_ok _ _ _ continuation
          rcases found with ⟨requests, edges, targets⟩
          apply ih _ _ _ _ _ _ ?_ recursive
          intro row member
          rcases List.mem_append.mp member with old | added
          · exact known row old
          · cases List.mem_singleton.mp added
            exact ⟨request, nextUnseen_resolved selected⟩

/-- Each processed selected row is the result of a genuine request against an
original entry of the checked program. -/
theorem run_original {program : CheckedProgram} {seeds : List Request}
    {budget : Nat} {outcome : Outcome}
    (accepted : run program seeds budget = .ok outcome)
    {row : SourceSpecialization.SpecializedFunction}
    (member : row ∈ outcome.plan.specializations) :
    ∃ original ∈ program.functions, ∃ signature supplied,
      SourceSpecialization.specializeFunction signature original supplied = .ok row := by
  unfold run at accepted
  obtain ⟨seedKeys, _, completed⟩ := except_bind_ok _ _ _ accepted
  obtain ⟨request, resolved⟩ := runAux_originals program seedKeys budget seeds [] [] [] [] outcome
    (by simp) completed row member
  obtain ⟨original, originalMember, signature, specialized⟩ := resolveRequest_original resolved
  exact ⟨original, originalMember, signature, request.parameterSubstitution, specialized⟩

end Solcore.Frontend.SourceSpecializationWorklist

namespace Solcore.Frontend.SourceSpecializationWorklist
open SourceInference TypeSystem

/-- The actual ordered declaration-use list examined by template validation. -/
def localDeclarationUses (nodes : List Node) : List ExpressionNode :=
  nodes.filterMap fun
    | .expression node =>
        match declarationInstantiation? node with
        | some _ => some node
        | none => none
    | .statement _ => none

/-- The original generalized lambda bindings used by the real discovery pass. -/
def localLambdaBindings (source : TypedSource) : List LocalLambdaBinding :=
  directPolymorphicLambdaBindings source

structure LocalTemplateUses (bindings : List LocalLambdaBinding)
    (localInstance : LocalLambdaInstance) (nodes : List Node) : Prop where
  owned : ∀ requirement ∈ localInstance.binding.binder.schemeRequirements.map
      (·.templateRequirement),
    (localDeclarationUses nodes).foldl (fun count declarationUse =>
      count + (declarationUse.requirements.filter fun candidate =>
        candidate == requirement).length) 0 = 1
  foreign : ∀ declarationUse ∈ localDeclarationUses nodes,
    declarationUse.requirements.find? (fun requirement =>
      (bindings.flatMap fun binding => binding.binder.schemeRequirements.map
        (·.templateRequirement)).contains requirement &&
      !(localInstance.binding.binder.schemeRequirements.map
        (·.templateRequirement)).contains requirement) = none

private theorem forIn_yield_success {alpha : Type} (values : List alpha)
    (check : alpha → Except Error (ForInStep PUnit))
    (yieldOnly : ∀ value result, check value = .ok result → result = .yield PUnit.unit)
    {final : PUnit}
    (accepted : forIn values PUnit.unit (fun value _ => check value) = .ok final) :
    ∀ value ∈ values, check value = .ok (.yield PUnit.unit) := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      simp only [List.forIn_cons] at accepted
      cases tested : check head with
      | error error => simp [tested, bind, Except.bind] at accepted
      | ok step =>
          have same := yieldOnly head step tested
          subst step
          simp only [tested, bind, Except.bind] at accepted
          intro value member
          rcases List.mem_cons.mp member with rfl | later
          · exact tested
          · exact ih accepted value later

private theorem validateLocalSchemeTemplateUses_receipt
    {bindings : List LocalLambdaBinding} {localInstance : LocalLambdaInstance}
    {nodes : List Node}
    (accepted : validateLocalSchemeTemplateUses bindings localInstance nodes = .ok ()) :
    LocalTemplateUses bindings localInstance nodes := by
  unfold validateLocalSchemeTemplateUses at accepted
  obtain ⟨first, own, rest⟩ := except_bind_ok _ _ _ accepted
  obtain ⟨second, foreign, _⟩ := except_bind_ok _ _ _ rest
  have checkedOwn := forIn_yield_success _ _ (by
    intro value result checked
    try dsimp at checked
    split at checked
    · simp [bind, Except.bind, throw, throwThe] at checked
    · exact (Except.ok.inj checked).symm) own
  have checkedForeign := forIn_yield_success _ _ (by
    intro value result checked
    try dsimp at checked
    split at checked
    · simp [bind, Except.bind, throw, throwThe] at checked
    · exact (Except.ok.inj checked).symm) foreign
  constructor
  · intro requirement member
    have checked := checkedOwn requirement member
    try dsimp only at checked
    split at checked
    · simp [bind, Except.bind, throw, throwThe] at checked
    · rename_i countGood
      apply Classical.byContradiction
      intro denied
      apply countGood
      simpa only [bne_iff_ne, localDeclarationUses] using denied
  · intro declarationUse member
    have checked := checkedForeign declarationUse member
    try dsimp only at checked
    split at checked
    · simp [bind, Except.bind, throw, throwThe] at checked
    · assumption


private theorem validateReachableOpenDeclarations_template_receipts
    {source : TypedSource} {bindings : List LocalLambdaBinding}
    {instances : List LocalLambdaInstance}
    (accepted : validateReachableOpenDeclarations source bindings instances = .ok ()) :
    ∀ localInstance ∈ instances, ∃ ids,
      localLambdaBodyNodeIds source bindings localInstance.binding = .ok ids ∧
      LocalTemplateUses bindings localInstance (selectedNodes ids source.nodes) := by
  induction instances with
  | nil => simp
  | cons head tail ih =>
      simp only [validateReachableOpenDeclarations] at accepted
      obtain ⟨ids, body, afterBody⟩ := except_bind_ok _ _ _ accepted
      obtain ⟨checked, templates, afterTemplates⟩ := except_bind_ok _ _ _ afterBody
      cases checked
      obtain ⟨_, _, afterNodes⟩ := except_bind_ok _ _ _ afterTemplates
      intro localInstance member
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨ids, body, validateLocalSchemeTemplateUses_receipt templates⟩
      · exact ih afterNodes localInstance later

/-- Actual accepted discovery retains the exact direct lexical body used by
validation. Each owned template occurs once, and that body uses no template
owned by a different generalized binding. -/
theorem localLambdaInstances_template_receipts
    {source : TypedSource} {contextFuel : Option Nat}
    {instances : List LocalLambdaInstance}
    (accepted : localLambdaInstances source contextFuel = .ok instances) :
    ∀ localInstance ∈ instances, ∃ nodes,
      localLambdaBodyNodes source localInstance = .ok nodes ∧
      nodes ⊆ source.nodes ∧
      LocalTemplateUses (localLambdaBindings source) localInstance nodes := by
  have validated : validateOpenDeclarationsCovered source
      (directPolymorphicLambdaBindings source) instances = .ok () := by
    cases contextFuel <;> simp only [localLambdaInstances] at accepted
    all_goals
      obtain ⟨_, _, afterRoots⟩ := except_bind_ok _ _ _ accepted
      obtain ⟨values, _, afterClosed⟩ := except_bind_ok _ _ _ afterRoots
      obtain ⟨checked, validated, finished⟩ := except_bind_ok _ _ _ afterClosed
      cases checked
      have same : values = instances := by
        simpa only [pure, Except.pure, Except.ok.injEq] using finished
      subst instances
      exact validated
  unfold validateOpenDeclarationsCovered at validated
  obtain ⟨_, _, reachable⟩ := except_bind_ok _ _ _ validated
  intro localInstance member
  obtain ⟨ids, body, templates⟩ :=
    validateReachableOpenDeclarations_template_receipts reachable localInstance member
  refine ⟨selectedNodes ids source.nodes, ?_, selectedNodes_subset ids source.nodes, templates⟩
  simp only [localLambdaBodyNodes, body, bind, Except.bind, pure, Except.pure]

/-- Template ownership is exposed as membership, without assuming an
independent coverage property. It follows from the actual failed-search
check retained in the receipt. -/
theorem LocalTemplateUses.foreign_mem
    {bindings : List LocalLambdaBinding} {localInstance : LocalLambdaInstance}
    {nodes : List Node} (receipt : LocalTemplateUses bindings localInstance nodes)
    {expression : ExpressionNode} (used : expression ∈ localDeclarationUses nodes)
    {requirement : RequirementId} (present : requirement ∈ expression.requirements)
    (known : requirement ∈ bindings.flatMap fun binding =>
      binding.binder.schemeRequirements.map (·.templateRequirement)) :
    requirement ∈ localInstance.binding.binder.schemeRequirements.map (·.templateRequirement) := by
  letI : LawfulBEq RequirementId := by
    exact {
      eq_of_beq := by
        intro left right same
        cases left with
        | mk left =>
          cases right with
          | mk right =>
            change (left == right) = true at same
            have equal : left = right := eq_of_beq same
            cases equal
            rfl
      rfl := by
        intro value
        cases value with
        | mk index =>
          change (index == index) = true
          simp }
  have checked := receipt.foreign expression used
  have excluded := List.find?_eq_none.mp checked requirement present
  apply Classical.byContradiction
  intro absent
  apply excluded
  simp only [Bool.and_eq_true]
  constructor
  · exact List.contains_iff_mem.mpr known
  · have no := Bool.eq_false_iff.mpr (fun yes => absent (List.contains_iff_mem.mp yes))
    rw [no]
    rfl

end Solcore.Frontend.SourceSpecializationWorklist

namespace Solcore.Frontend.SourceSpecializationWorklist
open SourceInference TypeSystem

/-- One direct edge retains the exact successful compiler action, including
its concrete source node and declaration instantiation. -/
structure CallEdge.DirectReceipt (program : CheckedProgram)
    (caller : SourceSpecialization.SpecializationKey) (source : TypedSource)
    (edge : CallEdge) where
  node : ExpressionNode
  callee : ExpressionId
  arguments : List ExpressionId
  instantiation : DeclarationInstantiation
  request : Request
  form : node.form = .call callee arguments (.declaration instantiation)
  closed : hasOpenDeclarationInstantiation node = false
  accepted : directCall program caller source node callee instantiation = .ok (request, edge)

/-- Edge discovery distinguishes the original closed node from an actual
reachable local-template instance. The latter retains the ordered discovery
and exact contextual selection used by the compiler. -/
inductive CallEdge.SourceOrigin (program : CheckedProgram)
    (caller : SourceSpecialization.SpecializationKey) (source : TypedSource)
    (edge : CallEdge) : Prop where
  | direct (receipt : CallEdge.DirectReceipt program caller source edge)
      (member : .expression receipt.node ∈ source.nodes)
  | contextual (instances : List LocalLambdaInstance)
      (discovered : localLambdaInstances source = .ok instances)
      (localInstance : LocalLambdaInstance) (member : localInstance ∈ instances)
      (ids : List NodeId)
      (selected : openDeclarationNodeIdsFor source (localLambdaBindings source) localInstance = .ok ids)
      (receipt : CallEdge.DirectReceipt program caller
        (source.applySubstitution localInstance.substitution) edge)
      (nodeMember : .expression receipt.node ∈ selectedNodes ids
        (source.applySubstitution localInstance.substitution).nodes)

private theorem appendCallEdge_subset (left : List CallEdge) (right : CallEdge) :
    appendCallEdge left right ⊆ left ++ [right] := by
  unfold appendCallEdge
  split
  · exact List.subset_append_left _ _
  · exact List.Subset.refl _

private theorem appendCallEdges_subset (left right : List CallEdge) :
    appendCallEdges left right ⊆ left ++ right := by
  unfold appendCallEdges
  induction right generalizing left with
  | nil => simp
  | cons first rest ih =>
      simp only [List.foldl_cons]
      intro edge member
      have expanded := ih (appendCallEdge left first) member
      rcases List.mem_append.mp expanded with earlier | later
      · have inserted := appendCallEdge_subset left first earlier
        rcases List.mem_append.mp inserted with old | current
        · exact List.mem_append_left _ old
        · exact List.mem_append_right _ (List.mem_cons.mpr (.inl (List.mem_singleton.mp current)))
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ later)

private theorem collectReferences_call_receipts
    {program : CheckedProgram} {caller : SourceSpecialization.SpecializationKey}
    {source : TypedSource} {directCallees : List ExpressionId} {nodes : List Node}
    {result : List Request × List CallEdge × List ReferenceEdge}
    (accepted : collectReferences program caller source directCallees nodes = .ok result) :
    ∀ edge ∈ result.2.1, ∃ receipt : CallEdge.DirectReceipt program caller source edge,
      .expression receipt.node ∈ nodes := by
  induction nodes generalizing result with
  | nil => cases accepted; simp
  | cons node rest ih =>
      cases node with
      | statement statement =>
          intro edge member
          obtain ⟨receipt, present⟩ := ih accepted edge member
          exact ⟨receipt, List.mem_cons_of_mem _ present⟩
      | expression expression =>
          simp only [collectReferences] at accepted
          obtain ⟨_, _, continuation⟩ := except_bind_ok _ _ _ accepted
          split at continuation
          · obtain ⟨_, _, recursive⟩ := except_bind_ok _ _ _ continuation
            intro edge member
            obtain ⟨receipt, present⟩ := ih recursive edge member
            exact ⟨receipt, List.mem_cons_of_mem _ present⟩
          · rename_i callee arguments instantiation form
            split at continuation
            · obtain ⟨_, _, recursive⟩ := except_bind_ok _ _ _ continuation
              intro edge member
              obtain ⟨receipt, present⟩ := ih recursive edge member
              exact ⟨receipt, List.mem_cons_of_mem _ present⟩
            · rename_i closed
              obtain ⟨⟨request, added⟩, emitted, remaining⟩ := except_bind_ok _ _ _ continuation
              obtain ⟨⟨requests, calls, references⟩, recursive, finished⟩ := except_bind_ok _ _ _ remaining
              cases Except.ok.inj finished
              intro edge member
              rcases List.mem_cons.mp member with rfl | later
              · exact ⟨⟨expression, callee, arguments, instantiation, request, form,
                  Bool.eq_false_iff.mpr closed, emitted⟩, List.mem_cons_self⟩
              · obtain ⟨receipt, present⟩ := ih recursive edge later
                exact ⟨receipt, List.mem_cons_of_mem _ present⟩
          · split at continuation
            · intro edge member
              obtain ⟨receipt, present⟩ := ih continuation edge member
              exact ⟨receipt, List.mem_cons_of_mem _ present⟩
            · split at continuation
              · split at continuation
                · intro edge member
                  obtain ⟨receipt, present⟩ := ih continuation edge member
                  exact ⟨receipt, List.mem_cons_of_mem _ present⟩
                · cases continuation
              · obtain ⟨⟨request, selected⟩, _, remaining⟩ := except_bind_ok _ _ _ continuation
                obtain ⟨⟨requests, calls, references⟩, recursive, finished⟩ := except_bind_ok _ _ _ remaining
                cases Except.ok.inj finished
                intro edge member
                obtain ⟨receipt, present⟩ := ih recursive edge member
                exact ⟨receipt, List.mem_cons_of_mem _ present⟩
          · intro edge member
            obtain ⟨receipt, present⟩ := ih continuation edge member
            exact ⟨receipt, List.mem_cons_of_mem _ present⟩

/-- The receipt's caller and occurrence come from the actual edge emitter. -/
theorem CallEdge.DirectReceipt.emitted {program : CheckedProgram}
    {caller : SourceSpecialization.SpecializationKey} {source : TypedSource} {edge : CallEdge}
    (receipt : CallEdge.DirectReceipt program caller source edge) :
    edge.caller = caller ∧ edge.occurrence = receipt.node.id ∧
      ∃ selected, resolveRequest program receipt.request = .ok selected ∧ edge.callee = selected.key := by
  have accepted := receipt.accepted
  unfold directCall at accepted
  obtain ⟨calleeType, _, remaining⟩ := except_bind_ok _ _ _ accepted
  obtain ⟨⟨request, selected⟩, canonical, finished⟩ := except_bind_ok _ _ _ remaining
  have same := Prod.mk.inj (Except.ok.inj finished)
  obtain ⟨requestSame, edgeSame⟩ := same
  refine ⟨congrArg CallEdge.caller edgeSame.symm, congrArg CallEdge.occurrence edgeSame.symm,
    selected, ?_, congrArg CallEdge.callee edgeSame.symm⟩
  unfold canonicalReference at canonical
  split at canonical <;> try contradiction
  obtain ⟨value, resolved, remaining⟩ := except_bind_ok _ _ _ canonical
  try dsimp only at remaining
  split at remaining <;> try contradiction
  try dsimp only at remaining
  split at remaining <;> try contradiction
  try dsimp only at remaining
  split at remaining <;> try contradiction
  try dsimp only at remaining
  split at remaining <;> try contradiction
  have same := Prod.mk.inj (Except.ok.inj remaining)
  obtain ⟨emittedRequest, rfl⟩ := same
  rw [← requestSame, ← emittedRequest]
  exact resolved

private theorem collectInstantiatedReferences_call_receipts
    {program : CheckedProgram} {caller : SourceSpecialization.SpecializationKey}
    {source : TypedSource} {bindings : List LocalLambdaBinding} {instances : List LocalLambdaInstance}
    {result : List Request × List CallEdge × List ReferenceEdge}
    (accepted : collectInstantiatedReferences program caller source bindings instances = .ok result) :
    ∀ edge ∈ result.2.1, ∃ localInstance ∈ instances, ∃ ids,
      openDeclarationNodeIdsFor source bindings localInstance = .ok ids ∧
      ∃ receipt : CallEdge.DirectReceipt program caller
        (source.applySubstitution localInstance.substitution) edge,
        .expression receipt.node ∈ selectedNodes ids
          (source.applySubstitution localInstance.substitution).nodes := by
  induction instances generalizing result with
  | nil => cases accepted; simp
  | cons localInstance rest ih =>
      simp only [collectInstantiatedReferences] at accepted
      obtain ⟨ids, selected, remaining⟩ := except_bind_ok _ _ _ accepted
      obtain ⟨⟨requests, calls, references⟩, current, remaining⟩ := except_bind_ok _ _ _ remaining
      obtain ⟨⟨restRequests, restCalls, restReferences⟩, recursive, finished⟩ := except_bind_ok _ _ _ remaining
      cases Except.ok.inj finished
      intro edge member
      rcases List.mem_append.mp (appendCallEdges_subset calls restCalls member) with own | later
      · obtain ⟨receipt, present⟩ := collectReferences_call_receipts current edge own
        exact ⟨localInstance, List.mem_cons_self, ids, selected, receipt, present⟩
      · obtain ⟨localValue, present, ids, selected, receipt, nodeMember⟩ := ih recursive edge later
        exact ⟨localValue, List.mem_cons_of_mem _ present, ids, selected, receipt, nodeMember⟩

private theorem collectAllReferences_call_origins
    {program : CheckedProgram} {caller : SourceSpecialization.SpecializationKey}
    {source : TypedSource} {result : List Request × List CallEdge × List ReferenceEdge}
    (accepted : collectAllReferences program caller source = .ok result) :
    ∀ edge ∈ result.2.1, CallEdge.SourceOrigin program caller source edge := by
  unfold collectAllReferences at accepted
  obtain ⟨⟨requests, calls, references⟩, direct, remaining⟩ := except_bind_ok _ _ _ accepted
  obtain ⟨instances, discovered, remaining⟩ := except_bind_ok _ _ _ remaining
  obtain ⟨⟨localRequests, localCalls, localReferences⟩, contextual, finished⟩ := except_bind_ok _ _ _ remaining
  cases Except.ok.inj finished
  intro edge member
  rcases List.mem_append.mp (appendCallEdges_subset calls localCalls member) with own | contextualMember
  · obtain ⟨receipt, present⟩ := collectReferences_call_receipts direct edge own
    exact .direct receipt present
  · obtain ⟨localValue, present, ids, selected, receipt, nodeMember⟩ :=
      collectInstantiatedReferences_call_receipts contextual edge contextualMember
    exact .contextual instances discovered localValue present ids selected receipt nodeMember

private theorem runAux_rows_retained {program : CheckedProgram}
    {seedKeys seen : List SourceSpecialization.SpecializationKey} {queue : List Request}
    {specializations : List SourceSpecialization.SpecializedFunction}
    {calls : List CallEdge} {references : List ReferenceEdge} {budget : Nat} {outcome : Outcome}
    (accepted : runAux program seedKeys queue seen specializations calls references budget = .ok outcome) :
    specializations ⊆ outcome.plan.specializations := by
  induction budget generalizing queue seen specializations calls references outcome with
  | zero =>
      simp only [runAux] at accepted
      obtain ⟨next, _, finished⟩ := except_bind_ok _ _ _ accepted
      cases next with
      | none => cases Except.ok.inj finished; exact List.Subset.refl _
      | some entry =>
          rcases entry with ⟨request, row, rest⟩
          cases Except.ok.inj finished
          exact List.Subset.refl _
  | succ budget ih =>
      simp only [runAux] at accepted
      obtain ⟨next, _, remaining⟩ := except_bind_ok _ _ _ accepted
      cases next with
      | none => cases Except.ok.inj remaining; exact List.Subset.refl _
      | some entry =>
          rcases entry with ⟨request, row, rest⟩
          obtain ⟨⟨requests, edges, targets⟩, _, recursive⟩ := except_bind_ok _ _ _ remaining
          exact (List.subset_append_left _ _).trans (ih recursive)

/-- Queue closure preserves the originating processed row for every collected
call. Previously supplied edges are retained as an explicit alternative. -/
theorem runAux_call_origins {program : CheckedProgram}
    {seedKeys seen : List SourceSpecialization.SpecializationKey} {queue : List Request}
    {specializations : List SourceSpecialization.SpecializedFunction}
    {calls : List CallEdge} {references : List ReferenceEdge} {budget : Nat} {outcome : Outcome}
    (accepted : runAux program seedKeys queue seen specializations calls references budget = .ok outcome) :
    ∀ edge ∈ outcome.plan.callEdges, edge ∈ calls ∨
      ∃ row ∈ outcome.plan.specializations,
        CallEdge.SourceOrigin program row.key row.function.typedBody edge := by
  induction budget generalizing queue seen specializations calls references outcome with
  | zero =>
      simp only [runAux] at accepted
      obtain ⟨next, _, finished⟩ := except_bind_ok _ _ _ accepted
      cases next with
      | none => cases Except.ok.inj finished; exact fun _ member => .inl member
      | some entry =>
          rcases entry with ⟨request, row, rest⟩
          cases Except.ok.inj finished
          exact fun _ member => .inl member
  | succ budget ih =>
      simp only [runAux] at accepted
      obtain ⟨next, _, remaining⟩ := except_bind_ok _ _ _ accepted
      cases next with
      | none => cases Except.ok.inj remaining; exact fun _ member => .inl member
      | some entry =>
          rcases entry with ⟨request, row, rest⟩
          obtain ⟨⟨requests, edges, targets⟩, discovered, recursive⟩ := except_bind_ok _ _ _ remaining
          intro edge member
          rcases ih recursive edge member with previous | origin
          · rcases List.mem_append.mp previous with old | added
            · exact .inl old
            · right
              refine ⟨row, ?_, collectAllReferences_call_origins discovered edge added⟩
              exact runAux_rows_retained recursive (List.mem_append_right _ List.mem_cons_self)
          · exact .inr origin

/-- Every edge in an actual fresh worklist run has an actual processed source
row and its exact closed-call or local-instance origin. -/
theorem run_call_origins {program : CheckedProgram} {seeds : List Request}
    {budget : Nat} {outcome : Outcome}
    (accepted : run program seeds budget = .ok outcome)
    {edge : CallEdge} (member : edge ∈ outcome.plan.callEdges) :
    ∃ row ∈ outcome.plan.specializations,
      CallEdge.SourceOrigin program row.key row.function.typedBody edge := by
  unfold run at accepted
  obtain ⟨seedKeys, _, completed⟩ := except_bind_ok _ _ _ accepted
  rcases runAux_call_origins completed edge member with absent | origin
  · cases absent
  · exact origin

/-- Extending a plan admits exactly inherited edges, the explicitly supplied
outer call, the supplied root's real scan, or another actually processed row.
The synthetic outer call is never classified as a source-emitted edge. -/
theorem extendCompletePlan_call_origins {program : CheckedProgram} {plan : Plan}
    {root : SourceSpecialization.SpecializedFunction} {outerEdge : CallEdge}
    {budget : Nat} {outcome : Outcome}
    (accepted : extendCompletePlan program plan root outerEdge budget = .ok outcome)
    {edge : CallEdge} (member : edge ∈ outcome.plan.callEdges) :
    edge ∈ plan.callEdges ∨ edge = outerEdge ∨
      CallEdge.SourceOrigin program root.key root.function.typedBody edge ∨
      ∃ row ∈ outcome.plan.specializations,
        CallEdge.SourceOrigin program row.key row.function.typedBody edge := by
  unfold extendCompletePlan at accepted
  obtain ⟨checked, _, remaining⟩ := except_bind_ok _ _ _ accepted
  cases checked
  split at remaining <;> try contradiction
  dsimp only at remaining
  split at remaining
  · simp only [pure, Except.pure, bind, Except.bind] at remaining
    obtain ⟨⟨requests, calls, references⟩, discovered, completed⟩ := except_bind_ok _ _ _ remaining
    rcases runAux_call_origins completed edge member with previous | origin
    · rcases List.mem_append.mp (appendCallEdges_subset _ _ previous) with old | current
      · rcases List.mem_append.mp (appendCallEdge_subset _ _ old) with inherited | supplied
        · left
          simpa only [List.nil_append] using appendCallEdges_subset [] plan.callEdges inherited
        · exact .inr (.inl (List.mem_singleton.mp supplied))
      · exact .inr (.inr (.inl (collectAllReferences_call_origins discovered edge current)))
    · exact .inr (.inr (.inr origin))
  · split at remaining <;> try contradiction
    simp only [pure, Except.pure, bind, Except.bind] at remaining
    obtain ⟨⟨requests, calls, references⟩, discovered, completed⟩ := except_bind_ok _ _ _ remaining
    rcases runAux_call_origins completed edge member with previous | origin
    · rcases List.mem_append.mp (appendCallEdges_subset _ _ previous) with old | current
      · rcases List.mem_append.mp (appendCallEdge_subset _ _ old) with inherited | supplied
        · left
          simpa only [List.nil_append] using appendCallEdges_subset [] plan.callEdges inherited
        · exact .inr (.inl (List.mem_singleton.mp supplied))
      · exact .inr (.inr (.inl (collectAllReferences_call_origins discovered edge current)))
    · exact .inr (.inr (.inr origin))

/-- A direct receipt requests exactly the declaration and parameter
substitution retained by its actual source occurrence. -/
theorem CallEdge.DirectReceipt.request_exact {program : CheckedProgram}
    {caller : SourceSpecialization.SpecializationKey} {source : TypedSource} {edge : CallEdge}
    (receipt : CallEdge.DirectReceipt program caller source edge) :
    receipt.request = {
      declaration := receipt.instantiation.declaration
      parameterSubstitution := receipt.instantiation.parameterSubstitution } := by
  have accepted := receipt.accepted
  unfold directCall at accepted
  obtain ⟨calleeType, _, remaining⟩ := except_bind_ok _ _ _ accepted
  obtain ⟨⟨request, selected⟩, canonical, finished⟩ := except_bind_ok _ _ _ remaining
  have requestSame := (Prod.mk.inj (Except.ok.inj finished)).1
  unfold canonicalReference at canonical
  split at canonical <;> try contradiction
  obtain ⟨value, _, remaining⟩ := except_bind_ok _ _ _ canonical
  try dsimp only at remaining
  split at remaining <;> try contradiction
  try dsimp only at remaining
  split at remaining <;> try contradiction
  try dsimp only at remaining
  split at remaining <;> try contradiction
  try dsimp only at remaining
  split at remaining <;> try contradiction
  exact requestSame.symm.trans ((Prod.mk.inj (Except.ok.inj remaining)).1.symm)

/-- Source-emitted edges retain the actual calling specialization key. -/
theorem CallEdge.SourceOrigin.caller_eq {program : CheckedProgram}
    {caller : SourceSpecialization.SpecializationKey} {source : TypedSource} {edge : CallEdge}
    (origin : CallEdge.SourceOrigin program caller source edge) : edge.caller = caller := by
  cases origin with
  | direct receipt _ => exact receipt.emitted.1
  | contextual _ _ _ _ _ _ receipt _ => exact receipt.emitted.1

private theorem substituted_expression_original {source : TypedSource} {substitution : Substitution}
    {expression : ExpressionNode}
    (member : .expression expression ∈ (source.applySubstitution substitution).nodes) :
    ∃ original : ExpressionNode, .expression original ∈ source.nodes ∧
      original.applySubstitution substitution = expression := by
  obtain ⟨node, present, same⟩ := List.mem_map.mp member
  cases node with
  | statement statement => cases same
  | expression original =>
      exact ⟨original, present, Node.expression.inj same⟩

/-- Contextual scanning never invents an occurrence: the emitted occurrence
is one of the original caller's typed expression nodes. -/
theorem CallEdge.SourceOrigin.original_occurrence {program : CheckedProgram}
    {caller : SourceSpecialization.SpecializationKey} {source : TypedSource} {edge : CallEdge}
    (origin : CallEdge.SourceOrigin program caller source edge) :
    ∃ original : ExpressionNode, .expression original ∈ source.nodes ∧ original.id = edge.occurrence := by
  cases origin with
  | direct receipt present => exact ⟨receipt.node, present, receipt.emitted.2.1.symm⟩
  | contextual instances discovered localInstance member ids selected receipt present =>
      obtain ⟨original, originalMember, transformed⟩ := substituted_expression_original
        (selectedNodes_subset ids _ _ present)
      refine ⟨original, originalMember, ?_⟩
      have unchanged := congrArg ExpressionNode.id transformed
      change original.id = receipt.node.id at unchanged
      exact unchanged.trans receipt.emitted.2.1.symm

end Solcore.Frontend.SourceSpecializationWorklist

namespace Solcore.Frontend.SourceSpecializationWorklist
open SourceInference TypeSystem

private theorem insertLocalLambdaInstance_bindings {bindings : List LocalLambdaBinding}
    {instances : List LocalLambdaInstance} {localInstance : LocalLambdaInstance}
    (prior : ∀ value ∈ instances, value.binding ∈ bindings)
    (current : localInstance.binding ∈ bindings) :
    ∀ value ∈ insertLocalLambdaInstance instances localInstance, value.binding ∈ bindings := by
  unfold insertLocalLambdaInstance
  split
  · exact prior
  · intro value member
    rcases List.mem_append.mp member with old | added
    · exact prior value old
    · cases List.mem_singleton.mp added
      exact current

private theorem exactLocalLambdaBinding_member {bindings : List LocalLambdaBinding}
    {id : Resolved.LocalId} {binding : LocalLambdaBinding}
    (accepted : exactLocalLambdaBinding? bindings id = some binding) : binding ∈ bindings := by
  unfold exactLocalLambdaBinding? at accepted
  split at accepted <;> try contradiction
  rename_i only selected
  cases Option.some.inj accepted
  have member : binding ∈ bindings.filter (fun value => value.binder.id == id) := by
    rw [selected]
    exact List.mem_cons_self
  exact (List.mem_filter.mp member).1

private theorem collectGroundLocalLambdaInstances_bindings
    (bindings : List LocalLambdaBinding) (nodes : List Node)
    (prior result : List LocalLambdaInstance)
    (origins : ∀ value ∈ prior, value.binding ∈ bindings)
    (accepted : collectGroundLocalLambdaInstances bindings nodes prior = .ok result) :
    ∀ value ∈ result, value.binding ∈ bindings := by
  induction nodes generalizing prior with
  | nil =>
      cases Except.ok.inj accepted
      exact origins
  | cons head tail ih =>
      cases head with
      | statement statement => exact ih prior origins accepted
      | expression expression =>
        cases form : expression.form <;>
          simp only [collectGroundLocalLambdaInstances, form] at accepted
        all_goals try exact ih prior origins accepted
        rename_i name resolution
        cases resolution <;> simp only at accepted
        all_goals try exact ih prior origins accepted
        rename_i id
        cases found : exactLocalLambdaBinding? bindings id with
        | none =>
            simp only [found] at accepted
            exact ih prior origins accepted
        | some binding =>
            simp only [found] at accepted
            split at accepted
            · exact ih prior origins accepted
            · cases matched : SourceSpecialization.matchClosedSchemeInstance? binding.binder.scheme expression.rawType with
              | none => simp [matched, bind, Except.bind, throw] at accepted
              | some substitution =>
                  simp only [matched, pure, Pure.pure, Except.pure, bind, Except.bind] at accepted
                  apply ih _ (insertLocalLambdaInstance_bindings origins ?_) accepted
                  exact exactLocalLambdaBinding_member found

private theorem collectContextualLocalLambdaInstances_bindings
    (bindings : List LocalLambdaBinding) (parent : LocalLambdaInstance)
    (nodes : List Node)
    (prior result : List LocalLambdaInstance)
    (origins : ∀ value ∈ prior, value.binding ∈ bindings)
    (accepted : collectContextualLocalLambdaInstances bindings parent nodes prior = .ok result) :
    ∀ value ∈ result, value.binding ∈ bindings := by
  induction nodes generalizing prior with
  | nil =>
      cases Except.ok.inj accepted
      exact origins
  | cons head tail ih =>
      cases head with
      | statement statement => exact ih prior origins accepted
      | expression expression =>
        cases form : expression.form <;>
          simp only [collectContextualLocalLambdaInstances, form] at accepted
        all_goals try exact ih prior origins accepted
        rename_i name resolution
        cases resolution <;> simp only at accepted
        all_goals try exact ih prior origins accepted
        rename_i id
        cases found : exactLocalLambdaBinding? bindings id with
        | none =>
            simp only [found] at accepted
            exact ih prior origins accepted
        | some binding =>
            simp only [found] at accepted
            split at accepted
            · exact ih prior origins accepted
            · cases matched : SourceSpecialization.matchClosedSchemeInstance?
                  (Scheme.apply parent.substitution binding.binder.scheme)
                  (parent.substitution.apply expression.rawType) with
              | none => simp [matched, bind, Except.bind, throw] at accepted
              | some substitution =>
                  simp only [matched, pure, Pure.pure, Except.pure, bind, Except.bind] at accepted
                  apply ih _ (insertLocalLambdaInstance_bindings origins ?_) accepted
                  exact exactLocalLambdaBinding_member found

private theorem rootLocalLambdaInstances_bindings {source : TypedSource}
    {bindings : List LocalLambdaBinding} {result : List LocalLambdaInstance}
    (accepted : rootLocalLambdaInstances source bindings = .ok result) :
    ∀ value ∈ result, value.binding ∈ bindings := by
  unfold rootLocalLambdaInstances at accepted
  cases selected : directLexicalNodeIds source (bindings.map (·.initializer)) source.roots with
  | error error => simp [selected, bind, Except.bind] at accepted
  | ok ids =>
      simp only [selected, bind, Except.bind] at accepted
      exact collectGroundLocalLambdaInstances_bindings bindings (selectedNodes ids source.nodes)
        [] result (by simp) accepted

private theorem appendLocalLambdaInstances_bindings {bindings : List LocalLambdaBinding}
    (left right : List LocalLambdaInstance)
    (prior : ∀ value ∈ left, value.binding ∈ bindings)
    (added : ∀ value ∈ right, value.binding ∈ bindings) :
    ∀ value ∈ appendLocalLambdaInstances left right, value.binding ∈ bindings := by
  unfold appendLocalLambdaInstances
  induction right generalizing left with
  | nil => exact prior
  | cons head tail ih =>
      simp only [List.foldl_cons]
      exact ih _ (insertLocalLambdaInstance_bindings prior (added head List.mem_cons_self))
        (fun value member => added value (List.mem_cons_of_mem _ member))

private theorem closeLocalLambdaInstancesAux_bindings {source : TypedSource}
    (bindings : List LocalLambdaBinding) (fuel : Nat)
    (seen frontier result : List LocalLambdaInstance)
    (known : ∀ value ∈ seen, value.binding ∈ bindings)
    (accepted : closeLocalLambdaInstancesAux source bindings seen frontier fuel = .ok result) :
    ∀ value ∈ result, value.binding ∈ bindings := by
  induction fuel generalizing seen frontier with
  | zero =>
      cases frontier with
      | nil => cases Except.ok.inj accepted; exact known
      | cons head rest => simp [closeLocalLambdaInstancesAux, throw] at accepted
  | succ fuel ih =>
      cases frontier with
      | nil => cases Except.ok.inj accepted; exact known
      | cons parent rest =>
          simp only [closeLocalLambdaInstancesAux] at accepted
          cases bodyIds : localLambdaBodyNodeIds source bindings parent.binding with
          | error error => simp [bodyIds, bind, Except.bind] at accepted
          | ok ids =>
              simp only [bodyIds, bind, Except.bind] at accepted
              cases discovered : collectContextualLocalLambdaInstances bindings parent
                  (selectedNodes ids source.nodes) [] with
              | error error => simp [discovered] at accepted
              | ok found =>
                  simp only [discovered] at accepted
                  have foundOrigins := collectContextualLocalLambdaInstances_bindings bindings parent
                    (selectedNodes ids source.nodes) [] found (by simp) discovered
                  have freshOrigins : ∀ value ∈ found.filter (fun value => !seen.contains value),
                      value.binding ∈ bindings :=
                    fun value member => foundOrigins value (List.mem_filter.mp member).1
                  apply ih _ _
                    (appendLocalLambdaInstances_bindings _ _ known freshOrigins) accepted

/-- Every discovered instance uses a binding from the actual source collector. -/
theorem localLambdaInstances_bindings {source : TypedSource} {contextFuel : Option Nat}
    {result : List LocalLambdaInstance}
    (accepted : localLambdaInstances source contextFuel = .ok result) :
    ∀ value ∈ result, value.binding ∈ localLambdaBindings source := by
  cases contextFuel <;> simp only [localLambdaInstances] at accepted
  all_goals
    obtain ⟨roots, initial, afterInitial⟩ := except_bind_ok _ _ _ accepted
    obtain ⟨values, closed, afterClosed⟩ := except_bind_ok _ _ _ afterInitial
    obtain ⟨_, _, completed⟩ := except_bind_ok _ _ _ afterClosed
    have same : values = result := by simpa only [pure, Pure.pure, Except.pure, Except.ok.injEq] using completed
    subst result
    have rootsOrigin := rootLocalLambdaInstances_bindings initial
    exact closeLocalLambdaInstancesAux_bindings _ _ _ _ _ rootsOrigin closed

/-- The actual collector retains the complete original binder and initializer. -/
theorem localLambdaBindings_statement_origin {source : TypedSource} {binding : LocalLambdaBinding}
    (member : binding ∈ localLambdaBindings source) :
    ∃ statement : StatementNode, Node.statement statement ∈ source.nodes ∧
      statement.form = .letDecl binding.binder (some binding.initializer) := by
  change binding ∈ directPolymorphicLambdaBindings source at member
  obtain ⟨node, present, found⟩ := List.mem_filterMap.mp member
  cases node with
  | expression expression => simp at found
  | statement statement =>
    cases statement with
    | mk id span type form =>
      cases form
      all_goals try contradiction
      rename_i binder initializer
      cases initializer with
      | none => contradiction
      | some initializer =>
        change (if binder.scheme.quantified.isEmpty ||
          !SourceSpecialization.isDirectLambdaInitializer source initializer then none
          else some { binder, initializer }) = some binding at found
        split at found
        · contradiction
        · cases Option.some.inj found
          exact ⟨⟨id,span,type,.letDecl binder (some initializer)⟩, present, rfl⟩

end Solcore.Frontend.SourceSpecializationWorklist
