import Solcore.Frontend.SourceInference.Expression

/-!
# Whole-program inference

Public expression, body and whole-program entry points of inference. Main declarations:
`SourceInference.checkFunctionBody`, `SourceInference.Detail.finalize`.
-/

/-! Public expression, body, and whole-program source-checking entry points. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceInference

open TypeSystem

namespace Detail

/-- Validate declaration ownership and category-erased occurrence uniqueness
while accumulating the occurrences already present in the node table. -/
def validateOccurrenceTableFrom (owner : Resolved.DeclarationId) :
    List OccurrenceId → List Node → Except Error Unit
  | _, [] => .ok ()
  | seen, node :: rest => do
      let occurrence := node.occurrenceId
      if occurrence.owner != owner then
        throw (.nodeOwnerMismatch owner occurrence)
      if seen.contains occurrence then
        throw (.duplicateOccurrence occurrence)
      validateOccurrenceTableFrom owner (occurrence :: seen) rest

/-- Validate the declaration ownership and global occurrence uniqueness of a
typed source's heterogeneous node table. -/
def validateOccurrenceTable (source : TypedSource) : Except Error Unit :=
  validateOccurrenceTableFrom source.owner [] source.nodes

/-- Executable membership for declaration-local binder identities. -/
def localIdMember (ids : List Resolved.LocalId) (id : Resolved.LocalId) : Bool :=
  ids.any fun candidate => decide (candidate = id)

/-- Validate declaration ownership and global uniqueness for the canonical
local-definition inventory while accumulating identities already seen. -/
def validateLocalIdentitiesFrom (owner : Resolved.DeclarationId) :
    List Resolved.LocalId → List Resolved.LocalId → Except Error Unit
  | _, [] => .ok ()
  | seen, id :: rest => do
      if _ownerMismatch : id.owner ≠ owner then
        throw (.localIdentityOwnerMismatch owner id)
      if localIdMember seen id then
        throw (.duplicateLocalIdentity id)
      validateLocalIdentitiesFrom owner (id :: seen) rest

/-- Validate every declaration input and source-node binder in one shared
stable-identity namespace. -/
def validateSourceLocalIdentities (source : TypedSource) : Except Error Unit :=
  validateLocalIdentitiesFrom source.owner [] source.definedLocalIds

/-- Executable membership for stable requirement identities. -/
def requirementIdMember (ids : List RequirementId) (id : RequirementId) : Bool :=
  ids.any fun candidate => decide (candidate = id)

/-- Reject duplicates in one requirement-ID inventory while retaining the
caller-selected diagnostic for its ownership role. -/
def validateRequirementIdsUniqueFrom (duplicateError : RequirementId → Error) :
    List RequirementId → List RequirementId → Except Error Unit
  | _, [] => .ok ()
  | seen, id :: rest => do
      if requirementIdMember seen id then
        throw (duplicateError id)
      validateRequirementIdsUniqueFrom duplicateError (id :: seen) rest

/-- Check that every requested requirement identity occurs in the available
inventory, retaining the caller-selected diagnostic for the missing side. -/
def validateRequirementIdsContained (missingError : RequirementId → Error)
    (available : List RequirementId) : List RequirementId → Except Error Unit
  | [] => .ok ()
  | id :: rest => do
      if !requirementIdMember available id then
        throw (missingError id)
      validateRequirementIdsContained missingError available rest

/-- Validate the exact, order-insensitive bijection between primary source
attachments and the raw solver ledger.  Both sides must be duplicate-free. -/
def validateSourceRequirementOwnership (source : TypedSource)
    (requirements : List Requirement) : Except Error Unit := do
  let primary := source.primaryRequirementIds
  let ledger := requirements.map (fun requirement => requirement.id)
  validateRequirementIdsUniqueFrom Error.duplicatePrimaryRequirement [] primary
  validateRequirementIdsUniqueFrom Error.duplicateRequirementLedgerRow [] ledger
  validateRequirementIdsContained Error.missingRequirementLedgerRow ledger primary
  validateRequirementIdsContained Error.unattachedRequirementLedgerRow primary ledger

/-- Validate the exact executable classification of qualified local-scheme
templates and ensure every classified template has a raw requirement row. -/
def validateSourceTemplateTracking (source : TypedSource) (state : State) :
    Except Error Unit := do
  let templates := source.localSchemeTemplateIds
  let classified := state.localSchemeAssumptions
  let ledger := state.requirements.map (fun requirement => requirement.id)
  validateRequirementIdsUniqueFrom Error.duplicateLocalSchemeTemplate [] templates
  validateRequirementIdsUniqueFrom Error.duplicateLocalSchemeAssumption []
    classified
  validateRequirementIdsContained Error.missingLocalSchemeAssumption classified
    templates
  validateRequirementIdsContained Error.unownedLocalSchemeAssumption templates
    classified
  validateRequirementIdsContained Error.missingLocalSchemeRequirement ledger
    classified

/-- Whether the table contains a node at the exact category-preserving ID. -/
def sourceContainsNodeId (source : TypedSource) (id : NodeId) : Bool :=
  source.nodes.any fun node => decide (node.id = id)

/-- Validate exact category-preserving existence for a list of source roots. -/
def validateSourceRootsFrom (source : TypedSource) :
    List NodeId → Except Error Unit
  | [] => .ok ()
  | root :: rest => do
      unless sourceContainsNodeId source root do
        throw (.missingRoot root)
      validateSourceRootsFrom source rest

/-- Validate every root retained by a typed source. -/
def validateSourceRoots (source : TypedSource) : Except Error Unit :=
  validateSourceRootsFrom source source.roots

/-- Validate exact category-preserving existence for one node's child edges. -/
def validateSourceReferencesFrom (source : TypedSource) (parent : NodeId) :
    List NodeId → Except Error Unit
  | [] => .ok ()
  | child :: rest => do
      unless sourceContainsNodeId source child do
        throw (.missingChild parent child)
      validateSourceReferencesFrom source parent rest

/-- Validate all direct child edges retained by one source node. -/
def validateSourceNodeChildren (source : TypedSource)
    (node : Node) : Except Error Unit :=
  validateSourceReferencesFrom source node.id node.references

/-- Validate child edges for a list of source-table nodes. -/
def validateSourceChildrenFrom (source : TypedSource) :
    List Node → Except Error Unit
  | [] => .ok ()
  | node :: rest => do
      validateSourceNodeChildren source node
      validateSourceChildrenFrom source rest

/-- Validate every direct child edge retained by a typed source. -/
def validateSourceChildren (source : TypedSource) : Except Error Unit :=
  validateSourceChildrenFrom source source.nodes

/-- Executable membership for category-preserving source-node identities. -/
def nodeIdMember (ids : List NodeId) (id : NodeId) : Bool :=
  ids.any fun candidate => decide (candidate = id)

/-- Reject a repeated category-preserving incoming position.  Roots and child
slots share one inventory so this excludes repeated roots, repeated operand
slots, shared children, and roots which are also retained as children. -/
def validateIncomingNodeIdsFrom :
    List NodeId → List NodeId → Except Error Unit
  | _, [] => .ok ()
  | seen, id :: rest => do
      if nodeIdMember seen id then
        throw (.duplicateIncomingNode id)
      validateIncomingNodeIdsFrom (id :: seen) rest

/-- Follow a bounded exact-ID worklist, skipping identities already collected
and malformed missing lookups.  Exact root and child validation runs before
this collector at the final graph-validation boundary. -/
def collectReachableNodeIdsFuel (source : TypedSource) :
    Nat → List NodeId → List NodeId → List NodeId
  | 0, _, visited => visited
  | Nat.succ _, [], visited => visited
  | Nat.succ fuel, id :: rest, visited =>
      if nodeIdMember visited id then
        collectReachableNodeIdsFuel source fuel rest visited
      else
        match source.lookupNodeId? id with
        | none => collectReachableNodeIdsFuel source fuel rest visited
        | some node =>
            collectReachableNodeIdsFuel source fuel
              (node.references ++ rest) (id :: visited)

/-- Exact category-preserving identities reached from the declaration roots.
The incoming-position inventory bounds every well-formed forest traversal. -/
def sourceReachableNodeIds (source : TypedSource) : List NodeId :=
  collectReachableNodeIdsFuel source (source.incomingNodeIds.length + 1)
    source.roots []

/-- Exact identities collected below one arbitrary occurrence root.  Final
graph validation guarantees the initializer exists; the bounded collector is
shared with whole-source reachability. -/
def sourceSubtreeNodeIds (source : TypedSource) (root : NodeId) : List NodeId :=
  sourceReachableNodeIds { source with roots := [root] }

/-- Validate one initialized local-scheme template against its raw ledger row
and unique primary source attachment. -/
def validateSourceTemplateScope (source : TypedSource) (state : State)
    (site : LocalSchemeTemplateSite) : Except Error Unit :=
  let id := site.requirement.templateRequirement
  match state.requirements.find? fun requirement =>
      decide (requirement.id = id) with
  | none => .error (.missingLocalSchemeRequirement id)
  | some requirement =>
      let expected := site.requirement.predicate
      let actual := applyPredicate state requirement.predicate
      if _predicateEq : expected = actual then
        match source.primaryRequirementSites.find? fun primary =>
            decide (primary.requirement = id) with
        | none => .error (.missingLocalSchemePrimaryRequirement id)
        | some primary =>
            if nodeIdMember (sourceSubtreeNodeIds source site.initializer)
                primary.occurrence then
              .ok ()
            else
              .error (.localSchemeTemplateOutOfScope id site.initializer
                primary.occurrence)
      else
        .error (.localSchemeTemplatePredicateMismatch id expected actual)

/-- Validate a source-ordered suffix of qualified template sites. -/
def validateSourceTemplateScopesFrom (source : TypedSource) (state : State) :
    List LocalSchemeTemplateSite → Except Error Unit
  | [] => .ok ()
  | site :: rest => do
      validateSourceTemplateScope source state site
      validateSourceTemplateScopesFrom source state rest

/-- Validate predicate agreement and initializer-local primary ownership for
every qualified local-scheme template retained by a typed source. -/
def validateSourceTemplateScopes (source : TypedSource) (state : State) :
    Except Error Unit :=
  validateSourceTemplateScopesFrom source state source.localSchemeTemplateSites

/-- Ensure every retained table node was collected by the root worklist. -/
def validateAllSourceNodesReachedFrom (reached : List NodeId) :
    List Node → Except Error Unit
  | [] => .ok ()
  | node :: rest => do
      if nodeIdMember reached node.id then
        validateAllSourceNodesReachedFrom reached rest
      else
        throw (.unreachableNode node.id)

/-- Validate the unique-incoming and whole-table-reachability conditions which
turn an existing-node graph into a rooted occurrence forest. -/
def validateSourceForest (source : TypedSource) : Except Error Unit := do
  validateIncomingNodeIdsFrom [] source.incomingNodeIds
  validateAllSourceNodesReachedFrom (sourceReachableNodeIds source) source.nodes

/-- Reject malformed occurrence tables, dangling graph entry/child edges, and
non-forest occurrence structure before finalization exposes the typed source
to semantic consumers. -/
def validateSourceGraph (source : TypedSource) : Except Error Unit := do
  validateOccurrenceTable source
  validateSourceRoots source
  validateSourceChildren source
  validateSourceForest source

/-- Validate one retained expression result type in the declaration's rigid,
nominal, and residual-flexible formation scope. -/
def validateExpressionNodeTypeFormation (context : Context)
    (node : ExpressionNode) : Except Error Unit :=
  match validateInferenceTypeFormation context.signatures
      context.scope.genericOwner context.typeParameters
      node.type.freeVariables node.type with
  | .ok () => .ok ()
  | .error error => .error (.typeFormation error)

/-- Validate expression result types in one suffix of a heterogeneous source
node table.  Statement nodes carry inferred control-flow summaries rather
than expression result types and are intentionally skipped here. -/
def validateSourceExpressionTypeFormationFrom (context : Context) :
    List Node → Except Error Unit
  | [] => .ok ()
  | .expression node :: rest => do
      validateExpressionNodeTypeFormation context node
      validateSourceExpressionTypeFormationFrom context rest
  | .statement _ :: rest =>
      validateSourceExpressionTypeFormationFrom context rest

/-- Validate the structural formation of every expression type retained by a
typed source before the final inference substitution is applied. -/
def validateSourceExpressionTypeFormation (context : Context)
    (source : TypedSource) : Except Error Unit :=
  validateSourceExpressionTypeFormationFrom context source.nodes

/-- Executable first-match range check used to protect one generalized local
scheme from capture by the final inference substitution.  Only substitution
entries selected by variables occurring in `type` are relevant. -/
def substitutionRangeAvoidsVariablesOn (substitution : Substitution)
    (protectedVariables : List TypeVarId) (type : Ty) : Bool :=
  type.freeVariables.all fun sourceVariable =>
    match substitution.lookup? sourceVariable with
    | none => true
    | some replacement =>
        replacement.freeVariables.all fun rangeVariable =>
          !protectedVariables.contains rangeVariable

/-- Decidable binder-local side condition needed to commute final inference
substitution through a fresh instantiation of a generalized local scheme. -/
def localBinderInstantiationNoCapture (substitution : Substitution)
    (binder : TypedBinder) : Bool :=
  (binder.scheme.quantified.all fun metavariable =>
      !substitution.domain.contains metavariable) &&
    substitutionRangeAvoidsVariablesOn substitution binder.scheme.quantified
      binder.scheme.body &&
    (binder.schemeRequirements.all fun requirement =>
      substitutionRangeAvoidsVariablesOn substitution binder.scheme.quantified
          requirement.predicate.subject &&
        requirement.predicate.arguments.all fun argument =>
          substitutionRangeAvoidsVariablesOn substitution
            binder.scheme.quantified argument)

/-- Reject the first initialized local scheme whose quantified binders could
be captured by the final substitution. -/
def validateLocalSchemeBindersNoCapture (substitution : Substitution) :
    List TypedBinder → Except Error Unit
  | [] => .ok ()
  | binder :: rest =>
      if localBinderInstantiationNoCapture substitution binder then
        validateLocalSchemeBindersNoCapture substitution rest
      else
        .error (.localSchemeInstantiationCapture binder.id)

/-- Validate every initialized local scheme retained by a typed source.  The
inventory includes generalized binders with an empty qualified-predicate
spine. -/
def validateSourceLocalSchemeNoCapture (source : TypedSource)
    (substitution : Substitution) : Except Error Unit :=
  validateLocalSchemeBindersNoCapture substitution source.initializedLetBinders

/-- Validate every replacement retained by the final inference substitution
in the declaration's rigid and nominal formation scope.  Flexible variables
remain open because finalized source bodies permit residual inference types. -/
def validateFinalSubstitutionRangeFormation (context : Context)
    (substitution : Substitution) : Except Error Unit :=
  match validateInferenceSubstitutionRangeFormation context.signatures
      context.scope.genericOwner context.typeParameters substitution with
  | .ok () => .ok ()
  | .error error => .error (.typeFormation error)

/-- Validate that every retained origin names a metavariable already allocated
by the supplied inference counter. -/
def validateNumericOriginsBelow {α : Type} (next : Nat)
    (metavariable : α → TypeVarId) : List α → Except Error Unit
  | [] => .ok ()
  | origin :: rest =>
      let metavariableId := metavariable origin
      if metavariableId.index < next then
        validateNumericOriginsBelow next metavariable rest
      else
        .error (.numericOriginOutOfBounds metavariableId next)

/-- Validate the allocator bound required by both numeric-defaulting passes. -/
def validateNumericOriginsBelowNext (state : State) : Except Error Unit := do
  validateNumericOriginsBelow state.inference.next
    (fun origin : IntegerPatternOrigin => origin.metavariable)
    state.integerPatterns
  validateNumericOriginsBelow state.inference.next
    (fun origin : IntegerLiteralOrigin => origin.metavariable)
    state.integerLiterals

/-- An open numeric pattern defaults to `uint256`. -/
def defaultIntegerPatternTarget (state : State)
    (origin : IntegerPatternOrigin) : Except Error State :=
  match state.resolve (.variable origin.metavariable) with
  | .variable _ => unify state (.variable origin.metavariable) (.fixed .uint256)
  | _ => pure state

def defaultIntegerPatternTargets :
    List IntegerPatternOrigin → State → Except Error State
  | [], state => .ok state
  | origin :: rest, state => do
      let state ← defaultIntegerPatternTarget state origin
      defaultIntegerPatternTargets rest state

/-- The source of the integer-literal node at one expression identity. -/
def literalSourceAt? (state : State) (expression : ExpressionId) :
    Option Syntax.CoreLiteralValue :=
  state.nodes.findSome? fun node =>
    match node with
    | .expression node =>
        match node.form with
        | .integerLiteral source _ => if node.id = expression then some source else none
        | _ => none
    | .statement _ => none

/-- The resolved type of the expression node at one identity. -/
def expressionTypeAt? (state : State) (expression : ExpressionId) : Option Ty :=
  state.nodes.findSome? fun node =>
    match node with
    | .expression node => if node.id = expression then some (state.resolve node.type) else none
    | .statement _ => none

/-- The indexes of a place's elements of memory arrays, in order. -/
def placeElementIndexes (place : PlaceResolution) : List ExpressionId :=
  place.projections.filterMap fun
    | .element index => some index
    | .index _ | .member _ _ => none

/-- Whether a type variable occurs in the type of one of a place's element indexes,
which waits for its type as a read's index does. -/
def placeIndexMentions (state : State) (typeVar : TypeVarId) (place : PlaceResolution) : Bool :=
  (placeElementIndexes place).any fun index =>
    match expressionTypeAt? state index with
    | some type => type.freeVariables.contains typeVar
    | none => false

/-- Whether a type variable occurs in a compound assignment's target type, for
an operator that takes its target's type (`compoundTakesTargetType`), in a
compound shift's amount type: upstream reads `x <<= n` as `x = x << n`, whose
value and amount are both a shift's operands; or in one of the target's element
indexes' types. -/
def assignmentMentions (state : State) (typeVar : TypeVarId)
    (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp)
    (value : ExpressionId) : Bool :=
  (compoundTakesTargetType operator &&
    (state.resolve assignment.target.type).freeVariables.contains typeVar) ||
  (isShiftAssign operator &&
    match expressionTypeAt? state value with
    | some type => type.freeVariables.contains typeVar
    | none => false) ||
  placeIndexMentions state typeVar assignment.target

/-- Whether a type variable occurs in an in-place `~` target's type: upstream
reads `x ~=` as `x = ~x`, whose operand is the target; or in one of its element
indexes' types. -/
def bitNotMentions (state : State) (typeVar : TypeVarId)
    (assignment : AssignmentResolution) : Bool :=
  (state.resolve assignment.target.type).freeVariables.contains typeVar ||
    placeIndexMentions state typeVar assignment.target

/-- Whether a type variable occurs in a `for` item's compound or in-place `~`
target type. -/
def forItemMentions (state : State) (typeVar : TypeVarId) : ForItemForm → Bool
  | .assignValue assignment operator value => assignmentMentions state typeVar assignment operator value
  | .assignBitNot assignment => bitNotMentions state typeVar assignment
  | _ => false

/-- Whether a type variable occurs in an operand type of a unary or binary
operator (a builtin operator deferred on an open literal, or a comparison), in
the index type of a memory array read or of `lidx(a, i)`, or the type of a
memory array literal's element, or in the target type of a compound assignment
that takes its target's type or of an in-place `~`, a statement's or a `for`
item's: upstream reads `x op= e` as `x = x op e` and `x ~=` as `x = ~x`, and
gives a literal in `lidx`'s generic bound `uint256`. -/
def operatorMentions (state : State) (typeVar : TypeVarId) : Bool :=
  let mentions (operand : ExpressionId) : Bool :=
    match expressionTypeAt? state operand with
    | some type => type.freeVariables.contains typeVar
    | none => false
  state.nodes.any fun node =>
    match node with
    | .expression node =>
        match node.form with
        | .unary _ operand => mentions operand
        | .binary left _ right => mentions left || mentions right
        | .arrayIndex _ index => mentions index
        | .elementRef _ index => mentions index
        | .arrayLiteral _ elements => elements.any mentions
        | _ => false
    | .statement node =>
        match node.form with
        | .assignValue assignment operator value =>
            assignmentMentions state typeVar assignment operator value
        | .assignBitNot assignment => bitNotMentions state typeVar assignment
        | .forLoop initializer _ post _ =>
            initializer.any (forItemMentions state typeVar) ||
              post.any (forItemMentions state typeVar)
        | _ => false

/-- Whether a type variable occurs in a pending requirement other than a
literal's own builtin `Int`. -/
def requirementMentions (state : State) (typeVar : TypeVarId) : Bool :=
  state.requirements.any fun requirement =>
    requirement.predicate.trait != ProgramTraitId.builtin .int &&
      let predicate := applyPredicate state requirement.predicate
      (predicate.subject.freeVariables.contains typeVar ||
        predicate.arguments.any fun argument => argument.freeVariables.contains typeVar)

/-- An open literal defaults to `uint256` when its type occurs in an operator
or comparison obligation or a requirement other than its own `Int`, or when it
is negative (`-1`, as upstream, then fails `uint256`'s range). Numeric patterns
default before literals, so a literal matched by one is `uint256` already. -/
def literalDefaultsToUint256 (state : State) (origin : IntegerLiteralOrigin)
    (typeVar : TypeVarId) : Bool :=
  (match literalSourceAt? state origin.expression with
    | some source => Frontend.isNegativeLiteral source
    | none => false) ||
    operatorMentions state typeVar || requirementMentions state typeVar

/-- An open literal defaults to `uint256`, never to `word`; one that nothing
constrains is rejected as ambiguous. -/
def defaultIntegerLiteralTarget (state : State)
    (origin : IntegerLiteralOrigin) : Except Error State :=
  match state.resolve (.variable origin.metavariable) with
  | .variable typeVar =>
      if literalDefaultsToUint256 state origin typeVar then
        unify state (.variable origin.metavariable) (.fixed .uint256)
      else throw (.ambiguousIntegerLiteral origin.expression)
  | _ => pure state

def defaultIntegerLiteralTargets :
    List IntegerLiteralOrigin → State → Except Error State
  | [], state => .ok state
  | origin :: rest, state => do
      let state ← defaultIntegerLiteralTarget state origin
      defaultIntegerLiteralTargets rest state

/-- Integer carriers currently supported by both the declarative source
semantics and runtime materialization. -/
def supportedIntegerTarget : Ty → Bool
  | .constructor (.builtin .word)
  | .constructor (.builtin .integer) => true
  | _ => false

/-- Numeric pattern carriers: `word`, `integer` and `uint256`. The other
eleven fixed-width types keep rejecting numeric patterns. -/
def supportedIntegerPatternTarget : Ty → Bool
  | .constructor (.builtin (.fixed ⟨false, .w256⟩)) => true
  | type => supportedIntegerTarget type

/-- A literal's value fits its target: at a fixed-width integer type it is at
most the type's greatest value, and the other carriers take every literal. -/
def literalFitsTarget (type : Ty) (raw : Nat) : Bool :=
  match type with
  | .constructor (.builtin (.fixed fixed)) => decide (raw ≤ fixed.maxNat)
  | _ => true

/-- A numeric pattern's final type is a pattern carrier, and its value is in
that type's range. Only `uint256` has a range among the carriers, and it is
checked whether the pattern defaulted to it or was declared at it, as
upstream's `check_integer_literal_pattern_range` does; the compiler checks it
again. -/
def validateIntegerPatternTarget (origin : IntegerPatternOrigin)
    (state : State) : Except Error Unit := do
  let type := state.resolve (.variable origin.metavariable)
  if supportedIntegerPatternTarget type then
    if literalFitsTarget type origin.rawValue then pure ()
    else throw (.integerPatternOutOfRange origin.span type origin.rawValue)
  else throw (.nonNumericPatternType origin.span type)

def validateIntegerPatternTargets (state : State) :
    List IntegerPatternOrigin → Except Error Unit
  | [] => .ok ()
  | origin :: rest => do
      validateIntegerPatternTarget origin state
      validateIntegerPatternTargets state rest

/-- Integer-literal carriers: the two primitive carriers and the twelve
fixed-width integer types. Integer patterns keep `supportedIntegerTarget`. -/
def supportedIntegerLiteralTarget : Ty → Bool
  | .constructor (.builtin (.fixed _)) => true
  | type => supportedIntegerTarget type

/-- A negative literal's magnitude fits its target: at a fixed-width integer
type it is at most the magnitude of the type's least value, so only `-0` fits
an unsigned type, and the other carriers take every negative literal. -/
def negativeLiteralFitsTarget (type : Ty) (magnitude : Nat) : Bool :=
  match type with
  | .constructor (.builtin (.fixed fixed)) => decide (magnitude ≤ fixed.minMagnitude)
  | _ => true

/-- A literal of either sign fits its target. The sign is the spelling's
(`Frontend.isNegativeLiteral`), and `raw` is the magnitude. -/
def signedLiteralFitsTarget (source : Syntax.CoreLiteralValue) (type : Ty) (raw : Nat) : Bool :=
  if Frontend.isNegativeLiteral source then negativeLiteralFitsTarget type raw
  else literalFitsTarget type raw

/-- A literal's value: its magnitude, negated for a negative spelling. -/
def signedLiteralValue (source : Syntax.CoreLiteralValue) (raw : Nat) : Int :=
  if Frontend.isNegativeLiteral source then -(raw : Int) else raw

/-- Every integer-literal node at one expression identity fits the target. -/
def literalNodesFit (state : State) (expression : ExpressionId) (type : Ty) : Bool :=
  state.nodes.all fun node =>
    match node with
    | .expression node =>
        match node.form with
        | .integerLiteral source resolution =>
            !(decide (node.id = expression)) ||
              signedLiteralFitsTarget source type resolution.rawValue
        | _ => true
    | .statement _ => true

/-- The value of the integer-literal node at one expression identity, for
diagnostics. -/
def literalValueAt? (state : State) (expression : ExpressionId) : Option Int :=
  state.nodes.findSome? fun node =>
    match node with
    | .expression node =>
        match node.form with
        | .integerLiteral source resolution =>
            if node.id = expression then some (signedLiteralValue source resolution.rawValue)
            else none
        | _ => none
    | .statement _ => none

def validateIntegerLiteralTarget (origin : IntegerLiteralOrigin)
    (state : State) : Except Error Unit := do
  let type := state.resolve (.variable origin.metavariable)
  if supportedIntegerLiteralTarget type then
    if literalNodesFit state origin.expression type then pure ()
    else throw (.integerLiteralOutOfRange origin.expression type
      ((literalValueAt? state origin.expression).getD 0))
  else throw (.unsupportedIntegerLiteralTarget origin.expression type)

def validateIntegerLiteralTargets (state : State) :
    List IntegerLiteralOrigin → Except Error Unit
  | [] => .ok ()
  | origin :: rest => do
      validateIntegerLiteralTarget origin state
      validateIntegerLiteralTargets state rest

/-- Whether a node is an expression at one identity whose resolved type does
not fit. -/
def operandMisfits (state : State) (operand : ExpressionId) (fits : Ty → Bool) :
    Node → Bool
  | .expression candidate =>
      decide (candidate.id = operand) && !fits (state.resolve candidate.type)
  | .statement _ => false

/-- A compound shift's amount has `word` or an unsigned type, as a binary
shift's does (`validateShiftOperands`): upstream reads `x <<= n` as
`x = x << n`. Other assignments are not checked here. -/
def validateShiftAmount (state : State) (operator : Syntax.ValueAssignOp)
    (value : ExpressionId) : Except Error Unit :=
  if isShiftAssign operator && state.nodes.any (operandMisfits state value shiftAmountFits) then
    throw (.operatorNotSupported (match operator with | .shiftLeft => "shl" | _ => "shr")
      ((expressionTypeAt? state value).getD .word))
  else .ok ()

/-- An element place's indexes, once the defaults are in, have `word` or one of
the twelve types, as a read's index does (`validateArrayIndex`). -/
def validatePlaceIndexes (state : State) (place : PlaceResolution) : Except Error Unit :=
  match (placeElementIndexes place).find? fun index =>
      state.nodes.any (operandMisfits state index arrayIndexFits) with
  | some index =>
      throw (.operatorNotSupported "Typedef" ((expressionTypeAt? state index).getD .word))
  | none => .ok ()

/-- Check one value assignment's target type once the defaults are in
(`compoundTargetFits`), naming the assigned value, and a compound shift's amount
(`validateShiftAmount`). -/
def validateAssignmentTarget (state : State) (assignment : AssignmentResolution)
    (operator : Syntax.ValueAssignOp) (value : ExpressionId) : Except Error Unit :=
  let type := state.resolve assignment.target.type
  if compoundTargetFits operator type then validateShiftAmount state operator value
  else throw (.compoundTargetNotSupported value operator type)

/-- Check one in-place `~` target's type once the defaults are in
(`bitNotTargetFits`): upstream reads `x ~=` as `x = ~x`, and defines `BitNot` on
`word` and the twelve types only, so an `integer` target, one that nothing
fixes, and any other type are rejected with the trait's name, as an unchecked
operator's `integer` operand is. -/
def validateBitNotTarget (state : State) (assignment : AssignmentResolution) :
    Except Error Unit :=
  let type := state.resolve assignment.target.type
  if bitNotTargetFits type then .ok () else throw (.operatorNotSupported "BitNot" type)

/-- Check the value and in-place `~` assignments among a `for` header's
items. -/
def validateForItemAssignmentTargets (state : State) :
    List ForItemForm → Except Error Unit
  | [] => .ok ()
  | .assignValue assignment operator value :: rest => do
      validateAssignmentTarget state assignment operator value
      validateForItemAssignmentTargets state rest
  | .assignBitNot assignment :: rest => do
      validateBitNotTarget state assignment
      validateForItemAssignmentTargets state rest
  | _ :: rest => validateForItemAssignmentTargets state rest

/-- The name a binary operator's diagnostics give it: its trait's, or its
function's. -/
def binaryOperatorName (operator : Syntax.BinaryOp) : String :=
  match binaryOperatorDispatch operator with
  | .traitMethod name _ => name
  | .function name => name

/-- An unchecked operator that waited for an open literal operand (it owns no
requirement besides its coercions') never takes `integer`, for which upstream
defines no unchecked instance: once the defaults are in, its left operand's
type must not be `integer`. One that dispatched to a program's own trait owns
that trait's requirement and is not checked here. -/
def validateUncheckedOperand (state : State) (node : ExpressionNode) : Except Error Unit :=
  match node.form with
  | .binary left operator _ =>
      if isUncheckedOperator operator && decide (node.requirements = coercionRequirements node.coercions) &&
          state.nodes.any (fun candidate => match candidate with
            | .expression candidateNode =>
                decide (candidateNode.id = left) && decide (state.resolve candidateNode.type = .integer)
            | .statement _ => false) then
        throw (.operatorNotSupported (binaryOperatorName operator) .integer)
      else .ok ()
  | _ => .ok ()

/-- A shift types its value and its amount on their own and waits for both
(`inferBinaryOperator`): once the defaults are in, its value must have `word` or
one of the twelve types, and its amount `word` or an unsigned one, as upstream's
`Shl` and `Shr` instances take them. A signed, `integer` or `bool` amount is
rejected, as upstream's `shift_by_signed_amount` fixture has it. -/
def validateShiftOperands (state : State) (node : ExpressionNode) : Except Error Unit :=
  match node.form with
  | .binary left operator right =>
      if isShiftOperator operator then
        if state.nodes.any (operandMisfits state left shiftValueFits) then
          throw (.operatorNotSupported (binaryOperatorName operator)
            ((expressionTypeAt? state left).getD .word))
        else if state.nodes.any (operandMisfits state right shiftAmountFits) then
          throw (.operatorNotSupported (binaryOperatorName operator)
            ((expressionTypeAt? state right).getD .word))
        else .ok ()
      else .ok ()
  | _ => .ok ()

/-- A memory array read infers its index on its own and waits for its type
(`inferExprFuel`): once the defaults are in, the index must have `word` or one
of the twelve types, as upstream's read takes it as `Typedef<word>`. Another
type, such as `bool` or `integer`, is rejected with `operatorNotSupported
"Typedef"`, as upstream's `bool: Typedef<word>` fails. `lidx(a, i)`'s index is
checked the same way, as std's `LValueIdxAccess` takes it, and an open literal
index takes `uint256` as a read's does (`operatorMentions`). -/
def validateArrayIndex (state : State) (node : ExpressionNode) : Except Error Unit :=
  match node.form with
  | .arrayIndex _ index | .elementRef _ index =>
      if state.nodes.any (operandMisfits state index arrayIndexFits) then
        throw (.operatorNotSupported "Typedef" ((expressionTypeAt? state index).getD .word))
      else .ok ()
  | _ => .ok ()

/-- A memory array literal unifies its elements' types with one element type
and waits for it (`inferExprFuel`): once the defaults are in, a memory array
must hold it (`Ty.arrayElementAllowed`), as upstream's array of it needs
`Typedef<word>`. Another type, such as `bool`, is rejected with
`operatorNotSupported "Typedef"`, as upstream's `bool: Typedef<word>` fails. -/
def validateArrayLiteral (state : State) (node : ExpressionNode) : Except Error Unit :=
  match node.form with
  | .arrayLiteral element _ =>
      if (state.resolve element).arrayElementAllowed then .ok ()
      else throw (.operatorNotSupported "Typedef" (state.resolve element))
  | _ => .ok ()

/-- The finalization checks of one expression node: an unchecked operator's
operand type, a shift's operand types, a memory array read's index type and a
memory array literal's element type. -/
def validateExpressionNode (state : State) (node : ExpressionNode) : Except Error Unit := do
  validateUncheckedOperand state node
  validateShiftOperands state node
  validateArrayIndex state node
  validateArrayLiteral state node

/-- The finalization checks of one node: an assignment statement's value
assignment or in-place `~`, a `for` loop's header items, an unchecked operator's
operand type and a shift's operand types. -/
def validateAssignmentTargetNode (state : State) : Node → Except Error Unit
  | .statement node =>
      match node.form with
      | .assignValue assignment operator value =>
          validateAssignmentTarget state assignment operator value
      | .assignBitNot assignment => validateBitNotTarget state assignment
      | .forLoop initializer _ post _ => do
          validateForItemAssignmentTargets state initializer
          validateForItemAssignmentTargets state post
      | _ => .ok ()
  | .expression node => validateExpressionNode state node

/-- Check every value assignment's and in-place `~`'s target type, every
unchecked operator that waited for a literal operand, and every shift's operand
types. An open compound or in-place `~` target or operand waits for its type
(`compoundOperandType`, `bitNotTargetType`, `binaryDefers`, a shift), so a
literal it holds may default to `uint256` first. -/
def validateAssignmentTargets (state : State) : List Node → Except Error Unit
  | [] => .ok ()
  | node :: rest => do
      validateAssignmentTargetNode state node
      validateAssignmentTargets state rest

/-- The element places among a `for` header's items: an element place's indexes are
checked as a read's (`validatePlaceIndexes`), whether a plain write, a compound
assignment, one of its unchecked forms or an in-place `~` takes it. -/
def validateForItemElements (state : State) : List ForItemForm → Except Error Unit
  | [] => .ok ()
  | .assignValue assignment _ _ :: rest => do
      validatePlaceIndexes state assignment.target
      validateForItemElements state rest
  | .assignBitNot assignment :: rest => do
      validatePlaceIndexes state assignment.target
      validateForItemElements state rest
  | _ :: rest => validateForItemElements state rest

/-- The element places of one node: an assignment statement's, an in-place `~`'s
and a `for` header's items. -/
def validatePlaceElementNode (state : State) : Node → Except Error Unit
  | .statement node =>
      match node.form with
      | .assignValue assignment _ _ => validatePlaceIndexes state assignment.target
      | .assignBitNot assignment => validatePlaceIndexes state assignment.target
      | .forLoop initializer _ post _ => do
          validateForItemElements state initializer
          validateForItemElements state post
      | _ => .ok ()
  | .expression _ => .ok ()

/-- Check every element place once the defaults are in. -/
def validatePlaceElements (state : State) : List Node → Except Error Unit
  | [] => .ok ()
  | node :: rest => do
      validatePlaceElementNode state node
      validatePlaceElements state rest

/-- Whether Lean's operators are builtins at a type: `word` and the twelve fixed-width types. -/
def builtinOperatorOperand (type : Ty) : Bool :=
  match type with
  | .constructor (.builtin .word) => true
  | .constructor (.builtin (.fixed _)) => true
  | _ => false

/-- The binary operator a compound assignment applies, as upstream reads `x op= e` as
`x = x op e`; none for `=` and the shifts, whose traits are refused where they are implemented at
a builtin type (`shiftImplementationAtBuiltinType`). -/
def compoundBinaryOperator? : Syntax.ValueAssignOp → Option Syntax.BinaryOp
  | .add => some .add
  | .subtract => some .subtract
  | .multiply => some .multiply
  | .divide => some .divide
  | .modulo => some .modulo
  | .bitAnd => some .bitAnd
  | .bitXor => some .bitXor
  | .bitOr => some .bitOr
  | .uncheckedAdd => some .uncheckedAdd
  | .uncheckedSubtract => some .uncheckedSubtract
  | .uncheckedMultiply => some .uncheckedMultiply
  | .uncheckedDivide => some .uncheckedDivide
  | .uncheckedModulo => some .uncheckedModulo
  | .equal | .shiftLeft | .shiftRight => none

/-- Whether a module's scope sees a trait under a name: declared there with it, or bound there
under it by an import, an alias among them. -/
def traitInModuleScope (environment : ProgramEnvironment) (module : Workspace.ModuleId)
    (trait : Resolved.DeclarationId) (declaredName name : String) : Bool :=
  (decide (trait.moduleId = module) && declaredName == name) ||
    match buildProgramImports environment module with
    | .ok visibility => (visibility.traitsNamed name).any fun declaration =>
        decide (declaration.id = trait)
    | .error _ => false

/-- Whether upstream's lookup of an operator's trait method under the operator's trait name
reaches a trait from a module (`lookup_operator_class_method`): the module's own scope, else the
scope of each module it imports, whatever the import's form
(`lookup_imported_operator_class_method`), together with the modules that one imports, whose
names its imports qualify (`unique_visible_class_method`). A trait counts under the name a scope
sees it by, so an alias does. -/
def operatorTraitReachable (environment : ProgramEnvironment) (module : Workspace.ModuleId)
    (trait : Resolved.DeclarationId) (declaredName name : String) : Bool :=
  traitInModuleScope environment module trait declaredName name ||
    (environment.importedModules module).any fun imported =>
      traitInModuleScope environment imported trait declaredName name ||
        (environment.importedModules imported).any fun further =>
          decide (trait.moduleId = further) && declaredName == name

/-- The implementation that meets an operator's builtin at `operand`, if any: one at `operand`
or at a type parameter, of a trait that declares `methodName` and that upstream's lookup reaches
from the module being checked under the name `traitName` (`operatorTraitReachable`), declared so
or imported under it. A trait of that name without the method gives the operator no second
meaning. -/
def builtinOperatorMeeting? (context : Context) (traitName methodName : String) (operand : Ty) :
    Option ProgramImplementationSignature :=
  if !builtinOperatorOperand operand then none
  else
    context.signatures.implementations.find? fun implementation =>
      let atOperand := (match implementation.head.subject with
        | .parameter _ => true
        | subject => decide (subject = operand))
      atOperand && (match implementation.head.trait with
        | .builtin _ => false
        | .declaration trait =>
            (context.signatures.traits.find? fun signature => decide (signature.id = trait)).any
              fun signature => signature.methods.any (·.name == methodName) &&
                operatorTraitReachable context.environment context.scope.currentModule trait
                  signature.name traitName)

/-- Refuse a use that took an operator's builtin at `operand` where a program's implementation
meets it (`builtinOperatorMeeting?`). -/
def validateBuiltinOperatorUse (context : Context) (traitName methodName : String)
    (operand : Ty) : Except Error Unit :=
  match builtinOperatorMeeting? context traitName methodName operand with
  | some implementation =>
      throw (.builtinOperatorMeetsImplementation traitName implementation.id operand)
  | none => .ok ()

/-- The builtin use of one value assignment: a compound operator at its target's type, which
Lean always takes as the builtin there (`compoundOperandType`). -/
def validateBuiltinCompoundUse (context : Context) (state : State)
    (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp) : Except Error Unit :=
  match compoundBinaryOperator? operator with
  | some binary =>
      match binaryOperatorDispatch binary with
      | .traitMethod traitName methodName =>
          validateBuiltinOperatorUse context traitName methodName
            (state.resolve assignment.target.type)
      | .function _ => .ok ()
  | none => .ok ()

/-- The builtin uses among a `for` header's items. -/
def validateBuiltinOperatorForItems (context : Context) (state : State) :
    List ForItemForm → Except Error Unit
  | [] => .ok ()
  | .assignValue assignment operator _ :: rest => do
      validateBuiltinCompoundUse context state assignment operator
      validateBuiltinOperatorForItems context state rest
  | .assignBitNot assignment :: rest => do
      validateBuiltinOperatorUse context "BitNot" "bnot" (state.resolve assignment.target.type)
      validateBuiltinOperatorForItems context state rest
  | _ :: rest => validateBuiltinOperatorForItems context state rest

/-- The builtin uses of one node: a binary or unary trait-method operator that took its builtin,
its node owning no requirement but its coercions', as an unchecked operator's builtin is told
apart (`validateUncheckedOperand`); a compound assignment; an in-place `~`, which upstream reads
as `x = ~x`; and a `for` header's items. -/
def validateBuiltinOperatorNode (context : Context) (state : State) : Node → Except Error Unit
  | .expression node =>
      let builtin := decide (node.requirements = coercionRequirements node.coercions)
      match node.form with
      | .binary left operator _ =>
          match binaryOperatorDispatch operator, expressionTypeAt? state left with
          | .traitMethod traitName methodName, some operand =>
              if builtin then validateBuiltinOperatorUse context traitName methodName operand
              else .ok ()
          | _, _ => .ok ()
      | .unary operator inner =>
          match unaryOperatorDispatch operator, expressionTypeAt? state inner with
          | .traitMethod traitName methodName, some operand =>
              if builtin then validateBuiltinOperatorUse context traitName methodName operand
              else .ok ()
          | _, _ => .ok ()
      | _ => .ok ()
  | .statement node =>
      match node.form with
      | .assignValue assignment operator _ =>
          validateBuiltinCompoundUse context state assignment operator
      | .assignBitNot assignment =>
          validateBuiltinOperatorUse context "BitNot" "bnot" (state.resolve assignment.target.type)
      | .forLoop initializer _ post _ => do
          validateBuiltinOperatorForItems context state initializer
          validateBuiltinOperatorForItems context state post
      | _ => .ok ()

/-- Refuse every use where an operator's builtin at `word` or a fixed-width type meets a
program's implementation of its trait there, the user's rule of 2026-11-23 ("使用箇所に絞る"),
checked after the element places. Generic code, which runs the implementation as upstream does,
and a trait of the operator's name without its method refuse nothing. -/
def validateBuiltinOperatorUses (context : Context) (state : State) :
    List Node → Except Error Unit
  | [] => .ok ()
  | node :: rest => do
      validateBuiltinOperatorNode context state node
      validateBuiltinOperatorUses context state rest

/-- Check the source spelling and exact inference metadata retained by one
integer-literal expression node. -/
def validateIntegerLiteralNode (state : State) : Node → Except Error Unit
  | .expression node =>
      match node.form with
      | .integerLiteral source resolution =>
          if Frontend.literalMagnitude? source = some resolution.rawValue then
            match state.integerLiterals.find? fun origin =>
                decide (origin.expression = node.id ∧
                  resolution.targetType = .variable origin.metavariable ∧
                  origin.requirement = resolution.requirement) with
            | none => .error (.missingIntegerLiteralRequirement node.id
                resolution.requirement)
            | some _origin =>
                match state.requirements.find? fun requirement =>
                    decide (requirement.id = resolution.requirement) with
                | none => .error (.missingIntegerLiteralRequirement node.id
                    resolution.requirement)
                | some requirement =>
                    if requirement.predicate = resolution.predicate then
                      .ok ()
                    else
                      .error (.integerLiteralRequirementPredicateMismatch node.id
                        resolution.requirement resolution.predicate
                        requirement.predicate)
          else
            .error (.unsupportedLiteral
              "inconsistent integer literal metadata")
      | _ => .ok ()
  | .statement _ => .ok ()

/-- Validate integer-literal metadata for every retained source node. -/
def validateIntegerLiteralNodes (state : State) :
    List Node → Except Error Unit
  | [] => .ok ()
  | node :: rest => do
      validateIntegerLiteralNode state node
      validateIntegerLiteralNodes state rest

/-- Validate the complete node-to-origin-to-requirement correspondence before
finalization mutates inference substitutions. -/
def validateIntegerLiteralLedger (state : State) : Except Error Unit :=
  validateIntegerLiteralNodes state state.nodes

/-- The arguments that an implementation rule's head gives a goal whose subject the head
matches one way, as upstream's `match_pred` matches a main type and unifies the other
arguments: the rule is freshened, its subject unified with the goal's without binding a goal
variable, and its arguments taken under that unifier. A head of another trait or arity, one
whose subject does not match, and one whose arguments keep a variable of the rule give none;
the coverage condition (`SC0212`) leaves none of the last kind among a program's own. -/
def weakRuleArguments? (goal : ProgramPredicate) (rule : ProgramImplRule) :
    Option (List Ty) := do
  if rule.head.trait != goal.trait then none else pure ()
  if rule.head.arguments.length != goal.arguments.length then none else pure ()
  let freshened := TypedTraitResolution.freshenRuleFor rule goal
  let substitution ← (Unification.unify [{
    left := freshened.head.subject
    right := goal.subject
  }]).toOption
  if substitution.domain.any goal.subject.freeVariables.contains then none else pure ()
  let arguments := freshened.head.arguments.map substitution.apply
  if arguments.all fun argument => argument.freeVariables.isEmpty then pure arguments
  else none

/-- The one source of a goal's other arguments, in resolution's order: a given of its trait
and subject, which resolution takes first; else the one ordinary rule whose head subject
matches; else, when none does, the one default. Two sources of one kind give none. -/
def weakArgumentSource? (context : Context) (state : State) (goal : ProgramPredicate) :
    Option (List Ty) :=
  let givens := ((context.assumptions.map (applyPredicate state)).filter fun given =>
      given.trait == goal.trait && given.subject == goal.subject &&
        given.arguments.length == goal.arguments.length).eraseDups
  match givens with
  | [given] =>
      if given.arguments.all fun argument => argument.freeVariables.isEmpty then
        some given.arguments
      else none
  | _ :: _ :: _ => none
  | [] =>
      let rules := context.signatures.resolutionRules
      match ((rules.filter fun rule => !rule.isDefault).filterMap
          (weakRuleArguments? goal)).eraseDups with
      | [arguments] => some arguments
      | [] =>
          match ((rules.filter fun rule => rule.isDefault).filterMap
              (weakRuleArguments? goal)).eraseDups with
          | [arguments] => some arguments
          | _ => none
      | _ => none

/-- Unify each source argument, which has no metavariable, with the goal's, in order. The
closed side is the left operand, so no protected variable is bound
(`unify_closed_left_private`). -/
def unifyWeakArguments : State → List (Ty × Ty) → Except Error State
  | state, [] => .ok state
  | state, (source, target) :: rest => do
      let state ← unify state source target
      unifyWeakArguments state rest

/-- Whether every metavariable of a type lies below the allocator (`Ty.VariablesBelow`). -/
def variablesBelowNext (next : Nat) (type : Ty) : Bool :=
  type.freeVariables.all fun metavariable => decide (metavariable.index < next)

/-- Fix one requirement's open arguments from its one source, as upstream fixes a weak trait
argument: only a requirement whose trait is not the conventional `Coerce`, that is not a local
scheme's assumption (finalization keeps those as assumptions), whose subject has no
metavariable, and whose arguments hold one, all below the allocator. A requirement with no one
source, or whose arguments do not unify with it, is left as it is, so resolution refuses it as
before. -/
def fixWeakArgument (context : Context) (state : State) (requirement : Requirement) :
    Option State :=
  let goal := applyPredicate state requirement.predicate
  if state.localSchemeAssumptions.contains requirement.id ||
      isConventionalCoerce context.signatures.traits goal.trait ||
      !goal.subject.freeVariables.isEmpty ||
      goal.arguments.all (fun argument => argument.freeVariables.isEmpty) ||
      !goal.arguments.all (variablesBelowNext state.inference.next) then
    none
  else
    match weakArgumentSource? context state goal with
    | none => none
    | some arguments =>
        if arguments.length != goal.arguments.length ||
            !arguments.all (fun argument => argument.freeVariables.isEmpty) then none
        else
          match unifyWeakArguments state (arguments.zip goal.arguments) with
          | .ok next => some next
          | .error _ => none

/-- One round over the requirements, and whether it fixed any. -/
def weakArgumentRound (context : Context) : State → List Requirement → State × Bool
  | state, [] => (state, false)
  | state, requirement :: rest =>
      match fixWeakArgument context state requirement with
      | some next => ((weakArgumentRound context next rest).1, true)
      | none => weakArgumentRound context state rest

/-- Rounds until one fixes nothing, within `fuel` rounds: a chain of requirements, each fixing
the next one's subject (`t: Phantom<r>, r: Second<s>`), takes a round per link. -/
def weakArgumentPasses (context : Context) : Nat → State → State
  | 0, state => state
  | fuel + 1, state =>
      match weakArgumentRound context state state.requirements with
      | (next, true) => weakArgumentPasses context fuel next
      | (_, false) => state

/-- Upstream's weak trait arguments (`match_pred`): each requirement's open arguments are fixed
from the one given or implementation whose head subject matches its closed subject, for every
trait but Lean's own `Coerce`. Finalization runs this before a literal defaults and after, as
upstream fixes them on both sides. -/
def fixWeakArguments (context : Context) (state : State) : State :=
  weakArgumentPasses context (state.requirements.length + 1) state

/-- Finalization's defaulting: the weak trait arguments, the numeric patterns' and literals'
targets, and the weak arguments again, as upstream fixes a weak argument before a literal
defaults (`wa24`) and after (`wa26`). -/
def defaultTargets (context : Context) (state : State) : Except Error State := do
  let state := fixWeakArguments context state
  let state ← defaultIntegerPatternTargets state.integerPatterns state
  let state ← defaultIntegerLiteralTargets state.integerLiterals state
  pure (fixWeakArguments context state)

def finalize (context : Context) (type : Ty) (state : State)
    (roots : List NodeId) :
    Except Error Result := do
  validateNumericOriginsBelowNext state
  validateSourceGraph (state.toTypedSource roots)
  validateSourceExpressionTypeFormation context (state.toTypedSource roots)
  validateSourceLocalIdentities (state.toTypedSource roots)
  validateSourceTemplateTracking (state.toTypedSource roots) state
  validateIntegerLiteralLedger state
  let state ← defaultTargets context state
  validateIntegerPatternTargets state state.integerPatterns
  validateIntegerLiteralTargets state state.integerLiterals
  validateAssignmentTargets state state.nodes
  validatePlaceElements state state.nodes
  validateBuiltinOperatorUses context state state.nodes
  validateSourceRequirementOwnership (state.toTypedSource roots)
    state.requirements
  let substitution := state.inference.substitution
  validateFinalSubstitutionRangeFormation context substitution
  validateSourceLocalSchemeNoCapture (state.toTypedSource roots) substitution
  let typedSource := (state.toTypedSource roots).applySubstitution substitution
  validateSourceTemplateScopes typedSource state
  let solvedRequirements ← solveRequirements context state state.requirements
  pure {
    type := state.resolve type
    substitution
    solvedRequirements
    typedSource
  }

end Detail

/-- Infer one canonical source expression from an optional local environment.

The expression is its own root, and its type can stay open, unlike a named
function's, whose parameters and results are declared. An open literal that only
that root type constrains, such as a lone `7`, is rejected as ambiguous
(`Error.ambiguousIntegerLiteral`): upstream's `default_root_integer_literals`
would give it `uint256`. This is the one place the two differ, and nothing in
the repository calls this function. -/
def inferExpression (context : Context) (expression : Syntax.Expr)
    (locals : TypeSystem.Environment := []) (fuel : Nat := 1024) :
    Except Error Result := do
  let (expression, state) ← Detail.inferExprFuel fuel context expression none
    (.initial context.scope.genericOwner locals)
  Detail.finalize context expression.type state [.expression expression.id]

/-- Check one source expression against an expected semantic source type. -/
def checkExpression (context : Context) (expression : Syntax.Expr) (expected : Ty)
    (locals : TypeSystem.Environment := []) (fuel : Nat := 1024) :
    Except Error Result := do
  let (expression, state) ← Detail.inferExprFuel fuel context expression
    (some expected)
    (.initial context.scope.genericOwner locals)
  Detail.finalize context expression.type state [.expression expression.id]

private def functionLocals (signature : ProgramFunctionSignature) :
    TypeSystem.Environment :=
  (signature.parameterNames.zip signature.parameterTypes).map fun parameter =>
    (parameter.1, Scheme.mono parameter.2)

private def functionDeclaration?
    (environment : ProgramEnvironment) (signature : ProgramFunctionSignature) :
    Option ProgramDeclaration :=
  environment.declaration? signature.id

mutual
/-- Upstream's `SC0222` (`infer_stmt_sequence`): the first `return` statement that another
statement of its sequence follows. Every sequence is read, a body's and those of its blocks,
branches, loops, match arms and lambdas, whether or not anything runs it. A block that ends in a
`return` is not itself one, so statements after it stay. Fuel bounds the walk as it bounds
inference. -/
def nonFinalReturnInStatements : Nat → List Syntax.Statement → Option Syntax.SourceSpan
  | 0, _ => none
  | fuel + 1, statements =>
      match statements with
      | [] => none
      | statement :: rest =>
          match statement.value, rest with
          | .returnStmt _, _ :: _ => some statement.span
          | _, _ =>
              (nonFinalReturnInStatement fuel statement).orElse
                fun _ => nonFinalReturnInStatements fuel rest

/-- The first non-final `return` in the sequences that one statement holds. -/
def nonFinalReturnInStatement : Nat → Syntax.Statement → Option Syntax.SourceSpan
  | 0, _ => none
  | fuel + 1, statement =>
      match statement.value with
      | .letDecl _ _ initializer => initializer.bind (nonFinalReturnInExpr fuel)
      | .returnStmt value => value.bind (nonFinalReturnInExpr fuel)
      | .expression expression _ => nonFinalReturnInExpr fuel expression
      | .assignValue target _ value =>
          [target, value].findSome? (nonFinalReturnInExpr fuel)
      | .assignBitNot target _ => nonFinalReturnInExpr fuel target
      | .matchWith scrutinees arms =>
          (scrutinees.elements.toList.findSome? (nonFinalReturnInExpr fuel)).orElse fun _ =>
            (arms.value.cases.findSome? fun matchCase =>
                nonFinalReturnInStatements fuel matchCase.value.body.value).orElse fun _ =>
              arms.value.defaultBody.bind fun body => nonFinalReturnInStatements fuel body.value
      | .forLoop _ initializer condition post body =>
          ((initializer ++ post).findSome? fun item => match item.value with
            | .letDecl _ _ initializer => initializer.bind (nonFinalReturnInExpr fuel)
            | .expression expression => nonFinalReturnInExpr fuel expression
            | .assignValue target _ value =>
                [target, value].findSome? (nonFinalReturnInExpr fuel)
            | .assignBitNot target _ => nonFinalReturnInExpr fuel target).orElse fun _ =>
            (nonFinalReturnInExpr fuel condition).orElse fun _ =>
              nonFinalReturnInStatements fuel body.value
      | .whileLoop condition body =>
          (nonFinalReturnInExpr fuel condition).orElse fun _ =>
            nonFinalReturnInStatements fuel body.value
      | .ifThen condition thenBody elseBody =>
          (nonFinalReturnInExpr fuel condition).orElse fun _ =>
            (nonFinalReturnInStatements fuel thenBody.value).orElse fun _ =>
              elseBody.bind fun body => nonFinalReturnInStatements fuel body.value
      | .block body => nonFinalReturnInStatements fuel body
      | .assembly _ | .breakStmt | .continueStmt | .error => none

/-- The first non-final `return` in the bodies of the lambdas that one expression holds. -/
def nonFinalReturnInExpr : Nat → Syntax.Expr → Option Syntax.SourceSpan
  | 0, _ => none
  | fuel + 1, expression =>
      match expression.value with
      | .lambda _ _ _ body => nonFinalReturnInStatements fuel body.value
      | .dotConstructor _ _ arguments =>
          arguments.bind fun list => list.elements.findSome? (nonFinalReturnInExpr fuel)
      | .unary _ operand => nonFinalReturnInExpr fuel operand
      | .binary left _ right => [left, right].findSome? (nonFinalReturnInExpr fuel)
      | .index base _ index => [base, index].findSome? (nonFinalReturnInExpr fuel)
      | .call callee arguments =>
          (callee :: arguments.elements).findSome? (nonFinalReturnInExpr fuel)
      | .field base _ _ => nonFinalReturnInExpr fuel base
      | .conditional condition _ thenBranch _ elseBranch =>
          [condition, thenBranch, elseBranch].findSome? (nonFinalReturnInExpr fuel)
      | .group inner => nonFinalReturnInExpr fuel inner
      | .tuple elements => elements.elements.findSome? (nonFinalReturnInExpr fuel)
      | .array elements => elements.elements.findSome? (nonFinalReturnInExpr fuel)
      | .newArray _ _ length => nonFinalReturnInExpr fuel length
      | .slice base _ start _ stop =>
          (base :: start.toList ++ stop.toList).findSome? (nonFinalReturnInExpr fuel)
      | .literal _ | .identifier _ | .proxy _ _ | .error => none
end

private def checkFunctionBodyResult (environment : ProgramEnvironment)
    (signatures : ProgramSignatures) (signature : ProgramFunctionSignature)
    (fuel : Nat) : Except Error Result := do
  let declaration ← match functionDeclaration? environment signature with
    | some declaration => pure declaration
    | none => throw (.malformedFunctionType signature.id)
  -- Upstream's `SC0222`: a `return` that another statement of its sequence follows.
  if let some span := nonFinalReturnInStatements fuel signature.source.value.body.value then
    throw (.nonFinalReturn span)
  let context : Context := {
    environment
    signatures
    scope := .ofDeclaration declaration
    typeParameters := signature.scheme.parameters
    assumptions := signature.scheme.predicates
  }
  let expected := Ty.productMany signature.returnTypes
  let state := State.initial context.scope.genericOwner (functionLocals signature)
    signature.parameterComptime
  let body ← Detail.inferStatementsFuel fuel context signature.source.value.body.value
    expected state
  let state ← Detail.unify body.state body.type expected
  Detail.finalize context expected state
    (body.statements.map NodeId.statement)

private def checkedFunctionOfResult (signature : ProgramFunctionSignature)
    (result : Result) : CheckedFunction := {
    declaration := signature.id
    type := signature.scheme.body
    inferredBodyType := result.type
    returnComptime := signature.returnComptime
    substitution := result.substitution
    solvedRequirements := result.solvedRequirements
    typedBody := result.typedSource
    comptimeLets := signature.source.value.comptimeLets
  }

/-- Check the parsed body owned by one resolved top-level function signature. -/
def checkFunctionBody (environment : ProgramEnvironment)
    (signatures : ProgramSignatures) (signature : ProgramFunctionSignature)
    (fuel : Nat := 1024) : Except Error CheckedFunction := do
  let result ← checkFunctionBodyResult environment signatures signature fuel
  pure (checkedFunctionOfResult signature result)

/-- A successful body check retains the declaration identity of its input
signature. -/
theorem checkFunctionBody_success_declaration
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : CheckedFunction}
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked) :
    checked.declaration = signature.id := by
  unfold checkFunctionBody at success
  cases resultEq :
      checkFunctionBodyResult environment signatures signature fuel with
  | error error => simp [resultEq, bind, Except.bind] at success
  | ok result =>
      simp only [resultEq, bind, Except.bind] at success
      injection success with checkedEq
      subst checked
      rfl

/-- A successful body check exposes the declaration lookup, statement
inference, return-type unification, and finalization results which produced the
checked function. -/
theorem checkFunctionBody_success_witness
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : CheckedFunction}
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked) :
    ∃ declaration body finalState result,
      environment.declaration? signature.id = some declaration ∧
        Detail.inferStatementsFuel fuel
            {
              environment
              signatures
              scope := .ofDeclaration declaration
              typeParameters := signature.scheme.parameters
              assumptions := signature.scheme.predicates
            }
            signature.source.value.body.value
            (Ty.productMany signature.returnTypes)
            (State.initial declaration.id
              ((signature.parameterNames.zip signature.parameterTypes).map
                fun parameter => (parameter.1, Scheme.mono parameter.2))
              signature.parameterComptime) = .ok body ∧
          Detail.unify body.state body.type
              (Ty.productMany signature.returnTypes) = .ok finalState ∧
            Detail.finalize
                {
                  environment
                  signatures
                  scope := .ofDeclaration declaration
                  typeParameters := signature.scheme.parameters
                  assumptions := signature.scheme.predicates
                }
                (Ty.productMany signature.returnTypes) finalState
                (body.statements.map NodeId.statement) = .ok result ∧
              checked = {
                declaration := signature.id
                type := signature.scheme.body
                inferredBodyType := result.type
                returnComptime := signature.returnComptime
                substitution := result.substitution
                solvedRequirements := result.solvedRequirements
                typedBody := result.typedSource
                comptimeLets := signature.source.value.comptimeLets
              } := by
  unfold checkFunctionBody at success
  cases resultEq :
      checkFunctionBodyResult environment signatures signature fuel with
  | error error => simp [resultEq, bind, Except.bind] at success
  | ok result =>
      simp only [resultEq, bind, Except.bind] at success
      injection success with checkedEq
      unfold checkFunctionBodyResult at resultEq
      unfold functionDeclaration? at resultEq
      cases declarationEq : environment.declaration? signature.id with
      | none => simp [declarationEq, bind, Except.bind] at resultEq
      | some declaration =>
          simp [declarationEq, functionLocals, pure, Except.pure, bind,
            Except.bind] at resultEq
          cases returnEq : nonFinalReturnInStatements fuel
              signature.source.value.body.value with
          | some span => simp [returnEq] at resultEq
          | none =>
          simp only [returnEq] at resultEq
          cases bodyEq :
              Detail.inferStatementsFuel fuel
                {
                  environment
                  signatures
                  scope := .ofDeclaration declaration
                  typeParameters := signature.scheme.parameters
                  assumptions := signature.scheme.predicates
                }
                signature.source.value.body.value
                (Ty.productMany signature.returnTypes)
                (State.initial
                  (ProgramTypeScope.ofDeclaration declaration).genericOwner
                  ((signature.parameterNames.zip signature.parameterTypes).map
                    fun parameter => (parameter.1, Scheme.mono parameter.2))
                  signature.parameterComptime) with
          | error error =>
              rw [bodyEq] at resultEq
              contradiction
          | ok body =>
              rw [bodyEq] at resultEq
              simp only at resultEq
              cases unifyEq : Detail.unify body.state body.type
                  (Ty.productMany signature.returnTypes) with
              | error error =>
                  rw [unifyEq] at resultEq
                  contradiction
              | ok finalState =>
                  rw [unifyEq] at resultEq
                  simp only at resultEq
                  cases finalizeEq :
                      Detail.finalize
                        {
                          environment
                          signatures
                          scope := .ofDeclaration declaration
                          typeParameters := signature.scheme.parameters
                          assumptions := signature.scheme.predicates
                        }
                        (Ty.productMany signature.returnTypes) finalState
                        (body.statements.map NodeId.statement) with
                  | error error =>
                      rw [finalizeEq] at resultEq
                      contradiction
                  | ok finalResult =>
                      rw [finalizeEq] at resultEq
                      simp only [Except.ok.injEq] at resultEq
                      subst result
                      refine ⟨declaration, body, finalState, finalResult,
                        rfl, ?_, unifyEq, finalizeEq, ?_⟩
                      · simpa [ProgramTypeScope.ofDeclaration] using bodyEq
                      · simpa [checkedFunctionOfResult] using checkedEq.symm

/-- Source-ordered evidence that every retained checked function is exactly
the successful result of checking its corresponding catalog signature. -/
inductive FunctionBodiesChecked
    (environment : ProgramEnvironment)
    (signatures : ProgramSignatures)
    (fuel : Nat) :
    List ProgramFunctionSignature → List CheckedFunction → Prop where
  | nil : FunctionBodiesChecked environment signatures fuel [] []
  | cons
      {signature : ProgramFunctionSignature}
      {remaining : List ProgramFunctionSignature}
      {function : CheckedFunction}
      {functions : List CheckedFunction}
      (head : checkFunctionBody environment signatures signature fuel =
        .ok function)
      (tail : FunctionBodiesChecked environment signatures fuel remaining
        functions) :
      FunctionBodiesChecked environment signatures fuel
        (signature :: remaining) (function :: functions)

namespace FunctionBodiesChecked

/-- Every retained checked function has a catalog member whose exact
body-checking equation produced it. -/
theorem exists_signature_of_function_mem
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {fuel : Nat}
    {catalog : List ProgramFunctionSignature}
    {functions : List CheckedFunction}
    (checked : FunctionBodiesChecked environment signatures fuel catalog
      functions)
    {function : CheckedFunction}
    (member : function ∈ functions) :
    ∃ signature, signature ∈ catalog ∧
      checkFunctionBody environment signatures signature fuel = .ok function := by
  induction checked with
  | nil => simp at member
  | @cons signature remaining headFunction tailFunctions head tail induction =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨signature, by simp, head⟩
      · obtain ⟨found, foundMember, foundSuccess⟩ := induction member
        exact ⟨found, by simp [foundMember], foundSuccess⟩

end FunctionBodiesChecked

private def checkFunctionBodiesAux (environment : ProgramEnvironment)
    (signatures : ProgramSignatures) (fuel : Nat) :
    List ProgramFunctionSignature → List CheckedFunction → List FunctionError →
      List CheckedFunction × List FunctionError
  | [], checked, errors => (checked, errors)
  | signature :: rest, checked, errors =>
      match checkFunctionBody environment signatures signature fuel with
      | .ok result =>
          checkFunctionBodiesAux environment signatures fuel rest
            (checked ++ [result]) errors
      | .error error =>
          checkFunctionBodiesAux environment signatures fuel rest checked
            (errors ++ [{ declaration := signature.id, error }])

private theorem checkFunctionBodiesAux_success_declaration_ids
    (environment : ProgramEnvironment)
    (signatures : ProgramSignatures)
    (fuel : Nat) :
    ∀ remaining checked errors finalChecked,
      checkFunctionBodiesAux environment signatures fuel remaining checked
          errors = (finalChecked, []) →
        errors = [] ∧
          finalChecked.map (fun function => function.declaration) =
            checked.map (fun function => function.declaration) ++
              remaining.map (fun signature => signature.id) := by
  intro remaining
  induction remaining with
  | nil =>
      intro checked errors finalChecked success
      have checkedEq := congrArg Prod.fst success
      have errorsEq := congrArg Prod.snd success
      simp only [checkFunctionBodiesAux] at checkedEq errorsEq
      subst finalChecked
      exact ⟨errorsEq, by simp⟩
  | cons signature rest induction =>
      intro checked errors finalChecked success
      cases bodyResult :
          checkFunctionBody environment signatures signature fuel with
      | error error =>
          have tail := induction checked
            (errors ++ [{ declaration := signature.id, error }]) finalChecked (by
              simpa [checkFunctionBodiesAux, bodyResult] using success)
          simp at tail
      | ok result =>
          have tail := induction (checked ++ [result]) errors finalChecked (by
            simpa [checkFunctionBodiesAux, bodyResult] using success)
          refine ⟨tail.1, ?_⟩
          have resultId := checkFunctionBody_success_declaration bodyResult
          simpa [List.map_append, resultId, List.append_assoc] using tail.2

/-- Successful accumulation retains the exact per-signature body-checking
equation for every result appended after the input prefix. -/
private theorem checkFunctionBodiesAux_success_corresponds
    (environment : ProgramEnvironment)
    (signatures : ProgramSignatures)
    (fuel : Nat) :
    ∀ remaining checked errors finalChecked,
      checkFunctionBodiesAux environment signatures fuel remaining checked
          errors = (finalChecked, []) →
        errors = [] ∧
          ∃ produced,
            finalChecked = checked ++ produced ∧
              FunctionBodiesChecked environment signatures fuel remaining
                produced := by
  intro remaining
  induction remaining with
  | nil =>
      intro checked errors finalChecked success
      have checkedEq := congrArg Prod.fst success
      have errorsEq := congrArg Prod.snd success
      simp only [checkFunctionBodiesAux] at checkedEq errorsEq
      subst finalChecked
      exact ⟨errorsEq, [], by simp, .nil⟩
  | cons signature rest induction =>
      intro checked errors finalChecked success
      cases bodyResult :
          checkFunctionBody environment signatures signature fuel with
      | error error =>
          have tail := induction checked
            (errors ++ [{ declaration := signature.id, error }]) finalChecked (by
              simpa [checkFunctionBodiesAux, bodyResult] using success)
          simp at tail
      | ok result =>
          obtain ⟨errorsEq, produced, finalEq, corresponds⟩ :=
            induction (checked ++ [result]) errors finalChecked (by
              simpa [checkFunctionBodiesAux, bodyResult] using success)
          refine ⟨errorsEq, result :: produced, ?_, ?_⟩
          · simpa [List.append_assoc] using finalEq
          · exact .cons bodyResult corresponds

/-- Check every top-level source function, accumulating independent failures. -/
def checkFunctionBodies (environment : ProgramEnvironment)
    (signatures : ProgramSignatures) (fuel : Nat := 1024) :
    Except (List FunctionError) (List CheckedFunction) :=
  let (checked, errors) := checkFunctionBodiesAux environment signatures fuel
    signatures.functions [] []
  if errors.isEmpty then .ok checked else .error errors

/-- Successful whole-catalog body checking retains every function declaration
identity exactly once and in signature-catalog order. -/
theorem checkFunctionBodies_success_declaration_ids
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {fuel : Nat}
    {functions : List CheckedFunction}
    (success : checkFunctionBodies environment signatures fuel =
      .ok functions) :
    functions.map (fun function => function.declaration) =
      signatures.functions.map (fun signature => signature.id) := by
  unfold checkFunctionBodies at success
  cases resultEq :
      checkFunctionBodiesAux environment signatures fuel signatures.functions
        [] [] with
  | mk checked errors =>
      rw [resultEq] at success
      change (if errors.isEmpty then Except.ok checked else Except.error errors) =
        Except.ok functions at success
      by_cases errorsEmpty : errors.isEmpty = true
      · simp only [errorsEmpty, if_true, Except.ok.injEq] at success
        have errorsEq : errors = [] := List.isEmpty_iff.mp errorsEmpty
        subst checked
        subst errors
        have ids :=
          (checkFunctionBodiesAux_success_declaration_ids environment signatures
            fuel signatures.functions [] [] functions resultEq).2
        simpa using ids
      · simp [errorsEmpty] at success

/-- Successful whole-catalog checking preserves the exact body-checking
derivation for every function in catalog order, rather than only retaining
its declaration identity. -/
theorem checkFunctionBodies_success_corresponds
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {fuel : Nat}
    {functions : List CheckedFunction}
    (success : checkFunctionBodies environment signatures fuel =
      .ok functions) :
    FunctionBodiesChecked environment signatures fuel signatures.functions
      functions := by
  unfold checkFunctionBodies at success
  cases resultEq :
      checkFunctionBodiesAux environment signatures fuel signatures.functions
        [] [] with
  | mk checked errors =>
      rw [resultEq] at success
      change (if errors.isEmpty then Except.ok checked else Except.error errors) =
        Except.ok functions at success
      by_cases errorsEmpty : errors.isEmpty = true
      · simp only [errorsEmpty, if_true, Except.ok.injEq] at success
        have errorsEq : errors = [] := List.isEmpty_iff.mp errorsEmpty
        subst checked
        subst errors
        obtain ⟨_, produced, functionsEq, corresponds⟩ :=
          checkFunctionBodiesAux_success_corresponds environment signatures fuel
            signatures.functions [] [] functions resultEq
        simpa using functionsEq ▸ corresponds
      · simp [errorsEmpty] at success

/-- Resolve signatures and check all bodies of an already loaded program. -/
def checkLoadedProgram (loaded : LoadedProgram) (fuel : Nat := 1024) :
    Except (List ProgramCheckError) (List CheckedFunction) :=
  match buildProgramSignatures loaded.environment with
  | .error errors => .error (errors.map ProgramCheckError.signatures)
  | .ok signatures =>
      match checkFunctionBodies loaded.environment signatures fuel with
      | .ok checked => .ok checked
      | .error errors => .error (errors.map ProgramCheckError.body)

/-- Validate, parse, catalog, resolve, and type-check one whole workspace. -/
def loadAndCheckProgram (raw : Workspace.RawWorkspace) (fuel : Nat := 1024) :
    Except (List ProgramCheckError) (List CheckedFunction) :=
  match loadProgram raw with
  | .error errors => .error (errors.map ProgramCheckError.loading)
  | .ok loaded => checkLoadedProgram loaded fuel

end Solcore.Frontend.SourceInference
