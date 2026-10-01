import Solcore.Frontend.SourceCoreCallableAncestryCache
import Solcore.Frontend.SourceCoreLambdaTemplates

/-! Reachable preparation of callable ancestry metadata. Only preparation runs
the pure local-witness factory. Runtime consumers receive the finite table and
perform table lookup; they do not inspect or evaluate source bodies.

The traversal bound is computed from owned contexts and requirement-profile
cardinality, not a caller-selected compilation/runtime fuel. The implementation
does not enumerate the Cartesian space of possible profiles. A successful
preparation retains its exact factory/traversal equations. The separate proof
layer must establish transition soundness, closure and impossibility of the
cardinality-exhausted branch before claiming acceptance for every artifact. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableAncestryPreparation
open SourceInference TypeSystem SourceCoreCallableAncestryCache
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Base := SourceCoreCompatibleFunctions.Prepared
abbrev State := SourceCoreCallableAncestryCache.State

inductive Error where
  | views (error : SourceCoreCallableViews.Error)
  | templates (error : SourceCoreLambdaTemplates.Error)
  | contractsUnavailable
  | invalidNamed (id : Core.Word)
  | inconsistentKey (key : Key)
  | cardinalityExhausted
  | invalidClosure
  deriving Repr

structure Inputs {checked : Checked} (base : Base checked) where private mk ::
  views : SourceCoreCallableViews.Table base.sourceProgram base.plan
  viewsPrepared : SourceCoreCallableViews.prepare base = .ok views
  templates : SourceCoreLambdaTemplates.Inventory checked
  templatesPrepared : SourceCoreLambdaTemplates.prepare base = .ok templates
  callable : SourceCoreGeneralFunctions.CallableContext
  callableSelected : base.callableContext = some callable

def prepareInputs {checked : Checked} (base : Base checked) : Except Error (Inputs base) := do
  match viewsPrepared : SourceCoreCallableViews.prepare base with
  | .error error => throw (.views error)
  | .ok views =>
    match templatesPrepared : SourceCoreLambdaTemplates.prepare base with
    | .error error => throw (.templates error)
    | .ok templates =>
      match callableSelected : base.callableContext with
      | none => throw .contractsUnavailable
      | some callable => pure ⟨views, viewsPrepared, templates, templatesPrepared, callable, callableSelected⟩

/-- The actual named source selected by the owned codebook and plan. -/
def named? {checked : Checked} {base : Base checked} (inputs : Inputs base)
    (id : Core.Word) : Option State := do
  let entry ← inputs.callable.table.entryAt? id
  let .named owner := entry.origin | none
  let caller ← (SourceCompilationPlan.exactSpecialization base.plan owner).toOption
  pure ⟨owner, [], caller.function.typedBody⟩

/-- Validate both the native lambda descriptor and its source occurrence. -/
def lambdaAllowed {checked : Checked} {base : Base checked} (inputs : Inputs base)
    (state : State) (id : Core.Word) : Bool := Id.run do
  let some template := inputs.templates.lambdaAt? id | return false
  let some entry := inputs.callable.table.entryAt? id | return false
  unless entry.origin = .lambda template.owner template.id template.active do return false
  unless state.owner = template.owner ∧ state.active = template.active do return false
  let some node := state.source.lookupExpression? template.id | return false
  unless node.form = template.node.form do return false
  match node.form with
  | .lambda .. => return true
  | _ => return false

/-- Recompute the occurrence-specific witness rename on the transported
metadata. This is a preparation operation, never a runtime reconstruction. -/
def view? {checked : Checked} {base : Base checked} (inputs : Inputs base)
    (state : State) (id target : Core.Word) : Option State := do
  let entry ← inputs.views.entryAt? id
  let template ← inputs.templates.lambdaAt? target
  let descriptor ← inputs.callable.table.entryAt? target
  if descriptor.origin ≠ .lambda template.owner template.id template.active then none else do
  if descriptor.origin ≠ .lambda entry.view.owner entry.view.principal.initializer entry.view.cumulative then none else do
  if entry.view.wrapsPrincipal ≠ true then none else do
  if state.owner ≠ entry.view.owner ∨ state.active ≠ entry.view.parentActive then none else do
  let caller ← (SourceCompilationPlan.exactSpecialization base.plan state.owner).toOption
  let node ← state.source.lookupExpression? entry.view.read
  let .reference _ (.local binderId) := node.form | none
  if binderId ≠ entry.view.binding.binder.id then none else do
  let binder := entry.view.binding.binder.applySubstitution state.active
  if (⟨binder, entry.view.principal.initializer⟩ : SourceCoreCallablePrincipals.Declaration) ∉
      SourceCoreCallablePrincipals.declarations state.source then none else do
  let requirements ← SourceCompilationPlan.ordinaryOwnedRequirements? node
  let (substitution, witnesses) ← (SourceCompilationPlan.localRequirementWitnesses caller
    entry.view.principal.evidence binder {node with type := node.rawType, requirements, coercions := []}).toOption
  if substitution ≠ entry.view.ownSubstitution then none else
    pure ⟨state.owner, substitution.compose state.active,
      SourceTypedRuntime.rewriteLocalRequirements witnesses (state.source.applySubstitution substitution)⟩

/-- An existing key may be reused only for exactly the same metadata. The
proof layer derives this equality from the owned transport invariants. -/
def intern (states : List State) (state : State) : Except Error (Nat × List State) :=
  match states.zipIdx.find? (fun row => decide (row.1.key = state.key)) with
  | none => .ok (states.length, states ++ [state])
  | some (previous, index) =>
      if previous = state then .ok (index, states) else .error (.inconsistentKey state.key)

def seed {checked : Checked} {base : Base checked} (inputs : Inputs base) : Except Error Table := do
  let mut table : Table := ⟨[], [], [], []⟩
  for entry in inputs.callable.table.entries do
    match entry.origin with
    | .named _ =>
      let state ← match named? inputs entry.id with
        | none => throw (.invalidNamed entry.id) | some state => pure state
      let (position, states) ← intern table.states state
      table := {table with states, named := table.named ++ [⟨entry.id, position⟩]}
    | _ => pure ()
  pure table

/-- Process one reached state. IDs range over actual owned finite tables.
Lambda edges never allocate a state; only successful view transitions do. -/
def expand {checked : Checked} {base : Base checked} (inputs : Inputs base)
    (position : Nat) (state : State) (initial : Table) : Except Error Table := do
  let mut table := initial
  for template in inputs.templates.lambdas do
    if lambdaAllowed inputs state template.descriptor then
      table := {table with lambdas := table.lambdas ++ [⟨position, template.descriptor⟩]}
  for entry in inputs.views.entries do
    for template in inputs.templates.lambdas do
      match view? inputs state entry.id template.descriptor with
      | none => pure ()
      | some next =>
        let (destination, states) ← intern table.states next
        table := {table with states, views := table.views ++ [⟨position, entry.id, template.descriptor, destination⟩]}
  pure table

/-- The processed prefix is indexed by `position`; newly discovered states
are appended. Only the reached suffix is visited. -/
def saturate {checked : Checked} {base : Base checked} (inputs : Inputs base) :
    Nat → Nat → Table → Except Error Table
  | fuel, position, table =>
    match table.stateAt? position with
    | none => .ok table
    | some state => match fuel with
      | 0 => .error .cardinalityExhausted
      | fuel + 1 => do
        let next ← expand inputs position state table
        saturate inputs fuel (position + 1) next

/-- Per-root profile cardinality is `alphabetSize ^ totalSpineLength`.
The duplicate-containing alphabet is a harmless overestimate. Each state has
either the empty substitution or a cumulative substitution from an owned view.
This number is calculated arithmetically; no profile list is constructed. -/
def capacity {checked : Checked} {base : Base checked} (inputs : Inputs base) (initial : Table) : Nat :=
  initial.states.foldl (fun total state =>
    let size := state.key.requirements.flatten.length
    total + (inputs.views.entries.length + 1) * size ^ size) 0

/-- A preparation-time closure check over finite rows and owned transition
IDs. It deliberately recomputes metadata transitions here, never at runtime.
This separates successful saturation coverage from the bound theorem. -/
def valid {checked : Checked} {base : Base checked} (inputs : Inputs base) (table : Table) : Bool :=
  let namedSound := table.named.all fun edge =>
    match named? inputs edge.origin with
    | none => false
    | some state => decide (table.stateAt? edge.destination = some state)
  let lambdaSound := table.lambdas.all fun edge =>
    match table.stateAt? edge.state with
    | none => false
    | some state => lambdaAllowed inputs state edge.origin
  let viewSound := table.views.all fun edge =>
    match table.stateAt? edge.state with
    | none => false
    | some state => match view? inputs state edge.view edge.target with
      | none => false
      | some result => decide (table.stateAt? edge.destination = some result)
  let namedClosed := inputs.callable.table.entries.all fun entry =>
    match named? inputs entry.id with
    | none => true
    | some state => match table.namedAt? entry.id with
      | none => false
      | some position => decide (table.stateAt? position = some state)
  let transitionsClosed := table.states.zipIdx.all fun row =>
    inputs.templates.lambdas.all (fun template =>
      !lambdaAllowed inputs row.1 template.descriptor || table.lambdaAllowed row.2 template.descriptor) &&
    inputs.views.entries.all (fun entry => inputs.templates.lambdas.all fun template =>
      match view? inputs row.1 entry.id template.descriptor with
      | none => true
      | some next => match table.viewAt? row.2 entry.id template.descriptor with
        | none => false
        | some position => decide (table.stateAt? position = some next))
  namedSound && lambdaSound && viewSound && namedClosed && transitionsClosed

structure Prepared {checked : Checked} (base : Base checked) where private mk ::
  inputs : Inputs base
  initial : Table
  seeded : seed inputs = .ok initial
  table : Table
  completed : saturate inputs (capacity inputs initial) 0 initial = .ok table
  validated : valid inputs table = true

def prepare {checked : Checked} (base : Base checked) : Except Error (Prepared base) := do
  let inputs ← prepareInputs base
  match seeded : seed inputs with
  | .error error => throw error
  | .ok initial =>
    match completed : saturate inputs (capacity inputs initial) 0 initial with
    | .error error => throw error
    | .ok table =>
      if validated : valid inputs table then pure ⟨inputs, initial, seeded, table, completed, validated⟩
      else throw .invalidClosure

end Solcore.Frontend.SourceCoreCallableAncestryPreparation
