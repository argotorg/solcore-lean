import Solcore.Frontend.SourceCoreCallableAncestryPairedPreparation

/-! Cached raw principal and ordinary lambda headers for paired source states.
Native context selects compiler ownership; source state selects the observable
raw header and complete lexical source. These contexts need not be equal.
Runtime restoration selects prepared rows and preserves ordered captures and
the cached owner evidence. Actual frame lookup, native code authenticity and
capture/allocation provenance are supplied by the enclosing runtime adapter.
No runtime source traversal, substitution or witness construction occurs. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallablePairedHeaders
open SourceInference TypeSystem
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Base := SourceCoreCompatibleFunctions.Prepared
abbrev Graph := @SourceCoreCallableAncestryPairedPreparation.Prepared
abbrev State := SourceCoreCallableAncestryReadRecipes.State
abbrev Principal {checked : Checked} (base : Base checked) :=
  SourceCoreCallablePrincipals.Entry base.sourceProgram base.plan base.contexts
abbrev Principals {checked : Checked} (base : Base checked) :=
  SourceCoreCallablePrincipals.Table base.sourceProgram base.plan base.contexts
abbrev SourceValue := SourceTypedRuntime.Value

inductive Error where
  | principals (error : SourceCoreCallablePrincipals.Error)
  | missingContext (position : Nat)
  | missingDeclaration (position : Nat) (binder : Resolved.LocalId)
  | missingLambda (position : Nat) (initializer : ExpressionId)
  | invalidLambda (position : Nat) (initializer : ExpressionId)
  | missingPrincipal (position : Nat) (binder : Resolved.LocalId)
  | missingOrdinary (position : Nat) (descriptor : Core.Word)
  deriving Repr

structure PrincipalHeader {checked : Checked} {base : Base checked} (graph : Graph base)
    (principals : Principals base) where private mk ::
  position : Fin graph.table.states.length
  principal : Principal base
  owned : principal ∈ principals.entries
  owner : (graph.table.states[position]).metadata.owner = principal.context.owner
  native : (graph.table.states[position]).nativeActive = principal.context.active
  declaration : SourceCoreCallablePrincipals.Declaration
  declared : (SourceCoreCallablePrincipals.directDeclarations (graph.table.states[position]).metadata.source).find?
    (fun declaration => decide (declaration.binder.id = principal.principal.binder.id ∧
      declaration.initializer = principal.principal.declaration.initializer)) = some declaration
  node : ExpressionNode
  found : (graph.table.states[position]).metadata.source.lookupExpression? declaration.initializer = some node
  parameters : List TypedBinder
  resultType : Ty
  body : List StatementId
  shape : node.form = .lambda parameters resultType body
  parameterIds : parameters.map (·.id) = principal.principal.originalParameters.map (·.id)
  bodyIds : body = principal.principal.originalBody

def PrincipalHeader.state {checked : Checked} {base : Base checked} {graph : Graph base}
    {principals : Principals base} (header : PrincipalHeader graph principals) : State := graph.table.states[header.position]
def PrincipalHeader.sourceValue {checked : Checked} {base : Base checked} {graph : Graph base}
    {principals : Principals base} (header : PrincipalHeader graph principals)
    (captured : SourceTypedRuntime.Environment) : SourceValue :=
  .closure header.parameters header.resultType header.body header.state.metadata.source header.state.metadata.owner
    captured header.principal.context.evidence
def PrincipalHeader.cell {checked : Checked} {base : Base checked} {graph : Graph base}
    {principals : Principals base} (header : PrincipalHeader graph principals)
    (captured : SourceTypedRuntime.Environment) : SourceTypedRuntime.Cell :=
  ⟨header.declaration.binder.scheme.body, some (header.sourceValue captured)⟩

private def principalHeader {checked : Checked} {base : Base checked} (graph : Graph base) (principals : Principals base)
    (position : Fin graph.table.states.length) (principal : Principal base) (owned : principal ∈ principals.entries)
    (owner : (graph.table.states[position]).metadata.owner = principal.context.owner)
    (native : (graph.table.states[position]).nativeActive = principal.context.active) :
    Except Error (PrincipalHeader graph principals) := do
  match declared : (SourceCoreCallablePrincipals.directDeclarations (graph.table.states[position]).metadata.source).find?
      (fun declaration => decide (declaration.binder.id = principal.principal.binder.id ∧
        declaration.initializer = principal.principal.declaration.initializer)) with
  | none => throw (.missingDeclaration position.val principal.principal.binder.id)
  | some declaration =>
    match found : (graph.table.states[position]).metadata.source.lookupExpression? declaration.initializer with
    | none => throw (.missingLambda position.val declaration.initializer)
    | some node =>
      match shape : node.form with
      | .lambda parameters resultType body =>
        if parameterIds : parameters.map (·.id) = principal.principal.originalParameters.map (·.id) then
          if bodyIds : body = principal.principal.originalBody then
            pure ⟨position, principal, owned, owner, native, declaration, declared, node, found,
              parameters, resultType, body, shape, parameterIds, bodyIds⟩
          else throw (.invalidLambda position.val declaration.initializer)
        else throw (.invalidLambda position.val declaration.initializer)
      | _ => throw (.invalidLambda position.val declaration.initializer)

structure LambdaHeader {checked : Checked} {base : Base checked} (graph : Graph base)
    (principals : Principals base) where private mk ::
  position : Fin graph.table.states.length
  template : SourceCoreLambdaTemplates.Lambda
  owned : template ∈ graph.inputs.templates.lambdas
  owner : (graph.table.states[position]).metadata.owner = template.owner
  native : (graph.table.states[position]).nativeActive = template.active
  context : SourceCoreCallablePrincipals.Collected base.sourceProgram base.plan base.contexts
  contextOwned : context ∈ principals.collected
  contextSelected : context.context.owner = template.owner ∧ context.context.active = template.active
  node : ExpressionNode
  found : (graph.table.states[position]).metadata.source.lookupExpression? template.id = some node
  nativeHeader : node.form = template.node.form
  parameters : List TypedBinder
  resultType : Ty
  body : List StatementId
  shape : node.form = .lambda parameters resultType body

def LambdaHeader.state {checked : Checked} {base : Base checked} {graph : Graph base}
    {principals : Principals base} (header : LambdaHeader graph principals) : State := graph.table.states[header.position]
def LambdaHeader.sourceValue {checked : Checked} {base : Base checked} {graph : Graph base}
    {principals : Principals base} (header : LambdaHeader graph principals)
    (captured : SourceTypedRuntime.Environment) : SourceValue :=
  .closure header.parameters header.resultType header.body header.state.metadata.source header.state.metadata.owner
    captured header.context.context.evidence

private def lambdaHeader? {checked : Checked} {base : Base checked} (graph : Graph base) (principals : Principals base)
    (position : Fin graph.table.states.length) (template : SourceCoreLambdaTemplates.Lambda)
    (owned : template ∈ graph.inputs.templates.lambdas)
    (owner : (graph.table.states[position]).metadata.owner = template.owner)
    (native : (graph.table.states[position]).nativeActive = template.active) : Except Error (Option (LambdaHeader graph principals)) := do
  match found : (graph.table.states[position]).metadata.source.lookupExpression? template.id with
  | none => pure none
  | some node =>
    if nativeHeader : node.form = template.node.form then
      match shape : node.form with
      | .lambda parameters resultType body =>
        match contextFound : principals.collected.attach.find? (fun context => decide
            (context.val.context.owner = template.owner ∧ context.val.context.active = template.active)) with
        | none => throw (.missingContext position.val)
        | some context =>
          have tested : decide (context.val.context.owner = template.owner ∧ context.val.context.active = template.active) = true :=
            List.find?_some (p := fun (row : {row : SourceCoreCallablePrincipals.Collected base.sourceProgram base.plan base.contexts //
                row ∈ principals.collected}) => decide (row.val.context.owner = template.owner ∧ row.val.context.active = template.active)) contextFound
          have contextSelected := of_decide_eq_true tested
          pure (some ⟨position, template, owned, owner, native, context.val, context.property, contextSelected,
            node, found, nativeHeader, parameters, resultType, body, shape⟩)
      | _ => pure none
    else pure none

private def principalsAt {checked : Checked} {base : Base checked} (graph : Graph base) (principals : Principals base)
    (position : Fin graph.table.states.length) : Except Error (List (PrincipalHeader graph principals)) := do
  let groups ← principals.entries.attach.mapM fun principal => do
    if owner : (graph.table.states[position]).metadata.owner = principal.val.context.owner then
      if native : (graph.table.states[position]).nativeActive = principal.val.context.active then
        let header ← principalHeader graph principals position principal.val principal.property owner native
        pure [header]
      else pure []
    else pure []
  pure groups.flatten

private def lambdasAt {checked : Checked} {base : Base checked} (graph : Graph base) (principals : Principals base)
    (position : Fin graph.table.states.length) : Except Error (List (LambdaHeader graph principals)) := do
  let groups ← graph.inputs.templates.lambdas.attach.mapM fun template => do
    if owner : (graph.table.states[position]).metadata.owner = template.val.owner then
      if native : (graph.table.states[position]).nativeActive = template.val.active then
        let header ← lambdaHeader? graph principals position template.val template.property owner native
        pure header.toList
      else pure []
    else pure []
  pure groups.flatten

structure Prepared {checked : Checked} {base : Base checked} (graph : Graph base) where private mk ::
  principals : Principals base
  principalsPrepared : SourceCoreCallablePrincipals.prepare base = .ok principals
  principalHeaders : List (PrincipalHeader graph principals)
  private principalCollected : ∃ groups, (List.finRange graph.table.states.length).mapM (principalsAt graph principals) = .ok groups ∧
    principalHeaders = groups.flatten
  lambdaHeaders : List (LambdaHeader graph principals)
  private lambdaCollected : ∃ groups, (List.finRange graph.table.states.length).mapM (lambdasAt graph principals) = .ok groups ∧
    lambdaHeaders = groups.flatten

def prepare {checked : Checked} {base : Base checked} (graph : Graph base) : Except Error (Prepared graph) := do
  match principalsPrepared : SourceCoreCallablePrincipals.prepare base with
  | .error error => throw (.principals error)
  | .ok principals =>
    match principalCollected : (List.finRange graph.table.states.length).mapM (principalsAt graph principals) with
    | .error error => throw error
    | .ok principalGroups =>
      match lambdaCollected : (List.finRange graph.table.states.length).mapM (lambdasAt graph principals) with
      | .error error => throw error
      | .ok lambdaGroups => pure ⟨principals, principalsPrepared, principalGroups.flatten, ⟨principalGroups, principalCollected, rfl⟩,
        lambdaGroups.flatten, ⟨lambdaGroups, lambdaCollected, rfl⟩⟩

def Prepared.principalAt? {checked : Checked} {base : Base checked} {graph : Graph base} (prepared : Prepared graph)
    (position : Nat) (key : SourceCoreAllocationLayouts.Key) : Option (PrincipalHeader graph prepared.principals) :=
  prepared.principalHeaders.find? fun header => decide (header.position.val = position ∧ header.principal.matchesLayout key)
def Prepared.lambdaAt? {checked : Checked} {base : Base checked} {graph : Graph base} (prepared : Prepared graph)
    (position : Nat) (descriptor : Core.Word) : Option (LambdaHeader graph prepared.principals) :=
  prepared.lambdaHeaders.find? fun header => decide (header.position.val = position ∧ header.template.descriptor = descriptor)

theorem PrincipalHeader.raw_source {checked : Checked} {base : Base checked} {graph : Graph base} {principals : Principals base}
    (header : PrincipalHeader graph principals) (captured : SourceTypedRuntime.Environment) :
    header.sourceValue captured = .closure header.parameters header.resultType header.body header.state.metadata.source
      header.state.metadata.owner captured header.principal.context.evidence := rfl

end Solcore.Frontend.SourceCoreCallablePairedHeaders
