import Solcore.Frontend.SourceInference.Expression

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

def defaultIntegerPatternTarget (state : State)
    (origin : IntegerPatternOrigin) : Except Error State :=
  match state.resolve (.variable origin.metavariable) with
  | .variable _ => unify state (.variable origin.metavariable) .word
  | _ => pure state

def defaultIntegerPatternTargets :
    List IntegerPatternOrigin → State → Except Error State
  | [], state => .ok state
  | origin :: rest, state => do
      let state ← defaultIntegerPatternTarget state origin
      defaultIntegerPatternTargets rest state

def defaultIntegerLiteralTarget (state : State)
    (origin : IntegerLiteralOrigin) : Except Error State :=
  match state.resolve (.variable origin.metavariable) with
  | .variable _ => unify state (.variable origin.metavariable) .word
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

def validateIntegerPatternTarget (origin : IntegerPatternOrigin)
    (state : State) : Except Error Unit := do
  let type := state.resolve (.variable origin.metavariable)
  if supportedIntegerTarget type then pure ()
  else throw (.nonNumericPatternType origin.span type)

def validateIntegerPatternTargets (state : State) :
    List IntegerPatternOrigin → Except Error Unit
  | [] => .ok ()
  | origin :: rest => do
      validateIntegerPatternTarget origin state
      validateIntegerPatternTargets state rest

def validateIntegerLiteralTarget (origin : IntegerLiteralOrigin)
    (state : State) : Except Error Unit := do
  let type := state.resolve (.variable origin.metavariable)
  if supportedIntegerTarget type then pure ()
  else throw (.unsupportedIntegerLiteralTarget origin.expression type)

def validateIntegerLiteralTargets (state : State) :
    List IntegerLiteralOrigin → Except Error Unit
  | [] => .ok ()
  | origin :: rest => do
      validateIntegerLiteralTarget origin state
      validateIntegerLiteralTargets state rest

/-- Check the source spelling and exact inference metadata retained by one
integer-literal expression node. -/
def validateIntegerLiteralNode (state : State) : Node → Except Error Unit
  | .expression node =>
      match node.form with
      | .integerLiteral source resolution =>
          if Frontend.numericLiteralValue? source = some resolution.rawValue then
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
  validateSourceGraph (state.toTypedSource roots)
  validateSourceLocalIdentities (state.toTypedSource roots)
  validateSourceTemplateTracking (state.toTypedSource roots) state
  validateIntegerLiteralLedger state
  let state ← defaultIntegerPatternTargets state.integerPatterns state
  let state ← defaultIntegerLiteralTargets state.integerLiterals state
  validateIntegerPatternTargets state state.integerPatterns
  validateIntegerLiteralTargets state state.integerLiterals
  validateSourceRequirementOwnership (state.toTypedSource roots)
    state.requirements
  let solvedRequirements ← solveRequirements context state state.requirements
  let substitution := state.inference.substitution
  pure {
    type := state.resolve type
    substitution
    solvedRequirements
    typedSource := (state.toTypedSource roots).applySubstitution substitution
  }

end Detail

/-- Infer one canonical source expression from an optional local environment. -/
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
