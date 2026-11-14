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

/-- Whether a type variable occurs in a compound assignment's target type, for
an operator that takes its target's type (`compoundTakesTargetType`), or in a
compound shift's amount type: upstream reads `x <<= n` as `x = x << n`, whose
value and amount are both a shift's operands. -/
def assignmentMentions (state : State) (typeVar : TypeVarId)
    (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp)
    (value : ExpressionId) : Bool :=
  (compoundTakesTargetType operator &&
    (state.resolve assignment.target.type).freeVariables.contains typeVar) ||
  (isShiftAssign operator &&
    match expressionTypeAt? state value with
    | some type => type.freeVariables.contains typeVar
    | none => false)

/-- Whether a type variable occurs in an in-place `~` target's type: upstream
reads `x ~=` as `x = ~x`, whose operand is the target. -/
def bitNotMentions (state : State) (typeVar : TypeVarId)
    (assignment : AssignmentResolution) : Bool :=
  (state.resolve assignment.target.type).freeVariables.contains typeVar

/-- Whether a type variable occurs in a `for` item's compound or in-place `~`
target type. -/
def forItemMentions (state : State) (typeVar : TypeVarId) : ForItemForm → Bool
  | .assignValue assignment operator value => assignmentMentions state typeVar assignment operator value
  | .assignBitNot assignment => bitNotMentions state typeVar assignment
  | _ => false

/-- Whether a type variable occurs in an operand type of a unary or binary
operator (a builtin operator deferred on an open literal, or a comparison), in
the index type of a memory array read, or in the target type of a compound
assignment that takes its target's type or of an in-place `~`, a statement's or
a `for` item's: upstream reads `x op= e` as `x = x op e` and `x ~=` as
`x = ~x`. -/
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
"Typedef"`, as upstream's `bool: Typedef<word>` fails. -/
def validateArrayIndex (state : State) (node : ExpressionNode) : Except Error Unit :=
  match node.form with
  | .arrayIndex _ index =>
      if state.nodes.any (operandMisfits state index arrayIndexFits) then
        throw (.operatorNotSupported "Typedef" ((expressionTypeAt? state index).getD .word))
      else .ok ()
  | _ => .ok ()

/-- The finalization checks of one expression node: an unchecked operator's
operand type, a shift's operand types and a memory array read's index type. -/
def validateExpressionNode (state : State) (node : ExpressionNode) : Except Error Unit := do
  validateUncheckedOperand state node
  validateShiftOperands state node
  validateArrayIndex state node

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

def finalize (context : Context) (type : Ty) (state : State)
    (roots : List NodeId) :
    Except Error Result := do
  validateNumericOriginsBelowNext state
  validateSourceGraph (state.toTypedSource roots)
  validateSourceExpressionTypeFormation context (state.toTypedSource roots)
  validateSourceLocalIdentities (state.toTypedSource roots)
  validateSourceTemplateTracking (state.toTypedSource roots) state
  validateIntegerLiteralLedger state
  let state ← defaultIntegerPatternTargets state.integerPatterns state
  let state ← defaultIntegerLiteralTargets state.integerLiterals state
  validateIntegerPatternTargets state state.integerPatterns
  validateIntegerLiteralTargets state state.integerLiterals
  validateAssignmentTargets state state.nodes
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

private def checkFunctionBodyResult (environment : ProgramEnvironment)
    (signatures : ProgramSignatures) (signature : ProgramFunctionSignature)
    (fuel : Nat) : Except Error Result := do
  let declaration ← match functionDeclaration? environment signature with
    | some declaration => pure declaration
    | none => throw (.malformedFunctionType signature.id)
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
