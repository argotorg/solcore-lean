import Solcore.Frontend.SourceCoreCallableAncestryPairedCache

/-! Reached-state preparation for paired callable ancestry. Each applied-view
edge authenticates its read caller and lexical principal separately. Only
reached metadata states are interned; preparation never enumerates the full
finite profile space. Pure witness factories run here and are retained in a
sealed recipe cache. Runtime lookup uses that cache and ordinary frame data.

Successful preparation certifies actual factory equations and finite closure.
Acceptance for every compiler artifact, and coverage of every emitted runtime
snapshot, require separate totality and provenance proofs. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableAncestryPairedPreparation
open SourceInference TypeSystem SourceCoreCallableAncestryPairedCache
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Base := SourceCoreCompatibleFunctions.Prepared
abbrev Inputs := @SourceCoreCallableAncestryPreparation.Inputs
abbrev State := SourceCoreCallableAncestryReadRecipes.State

inductive Error where
  | inputs (error : SourceCoreCallableAncestryPreparation.Error)
  | invalidNamed (id : Core.Word)
  | inconsistentKey (key : Key)
  | cardinalityExhausted
  | invalidClosure
  | missingState (index : Nat)
  | read (error : SourceCoreCallableAncestryReadRecipes.Error)
  | wrongDestination
  deriving Repr

def named? {checked : Checked} {base : Base checked} (inputs : Inputs base) (id : Core.Word) : Option State :=
  (SourceCoreCallableAncestryPreparation.named? inputs id).map fun metadata => ⟨metadata, []⟩

def lambdaAllowed {checked : Checked} {base : Base checked} (inputs : Inputs base)
    (state : State) (id : Core.Word) : Bool := Id.run do
  let some template := inputs.templates.lambdaAt? id | return false
  let some descriptor := inputs.callable.table.entryAt? id | return false
  unless descriptor.origin = .lambda template.owner template.id template.active do return false
  unless state.metadata.owner = template.owner ∧ state.nativeActive = template.active do return false
  let some node := state.metadata.source.lookupExpression? template.id | return false
  unless node.form = template.node.form do return false
  match node.form with
  | .lambda .. => return true
  | _ => return false

def view? {checked : Checked} {base : Base checked} (inputs : Inputs base)
    (caller lexical : State) (id target : Core.Word) : Option State := do
  let read ← (SourceCoreCallableAncestryReadRecipes.prepareRead inputs caller id target).toOption
  let _ ← (SourceCoreCallableAncestryReadRecipes.applyRead read lexical).toOption
  pure (read.after lexical)

def intern (states : List State) (state : State) : Except Error (Nat × List State) :=
  match states.zipIdx.find? fun row => decide (stateKey row.1 = stateKey state) with
  | none => .ok (states.length, states ++ [state])
  | some (previous, index) =>
    if previous = state then .ok (index, states) else .error (.inconsistentKey (stateKey state))

def seed {checked : Checked} {base : Base checked} (inputs : Inputs base) : Except Error Table := do
  let mut table : Table := ⟨[], [], [], []⟩
  for entry in inputs.callable.table.entries do
    match entry.origin with
    | .named _ =>
      let state ← match named? inputs entry.id with
        | none => throw (.invalidNamed entry.id) | some state => pure state
      let (destination, states) ← intern table.states state
      table := {table with states, named := table.named ++ [⟨entry.id, destination⟩]}
    | _ => pure ()
  pure table

def addView {checked : Checked} {base : Base checked} (inputs : Inputs base)
    (table : Table) (caller lexical : Nat) (before principal : State) (id target : Core.Word) : Except Error Table := do
  match view? inputs before principal id target with
  | none => pure table
  | some state =>
    let (destination, states) ← intern table.states state
    let edge : ViewEdge := ⟨caller, lexical, id, target, destination⟩
    if table.views.any fun existing => decide (existing = edge) then pure {table with states}
    else pure {table with states, views := table.views ++ [edge]}

/-- A pair is considered when its later state is processed. New states are
queued at the end and will meet every previously reached state on their turn.
Processing both orientations keeps caller/principal roles in their own order. -/
def expand {checked : Checked} {base : Base checked} (inputs : Inputs base)
    (position : Nat) (state : State) (initial : Table) : Except Error Table := do
  let mut table := initial
  for template in inputs.templates.lambdas do
    if lambdaAllowed inputs state template.descriptor then
      let edge : LambdaEdge := ⟨position, template.descriptor⟩
      if !table.lambdas.contains edge then table := {table with lambdas := table.lambdas ++ [edge]}
  for entry in inputs.views.entries do
    match inputs.callable.table.idAt?
        (.lambda entry.view.owner entry.view.principal.initializer entry.view.cumulative) with
    | none => pure ()
    | some target =>
      for (other, index) in initial.states.zipIdx do
        table ← addView inputs table position index state other entry.id target
        table ← addView inputs table index position other state entry.id target
  pure table

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

def nativeContexts {checked : Checked} {base : Base checked} (inputs : Inputs base) : List Substitution :=
  [] :: (inputs.templates.lambdas.map (·.active) ++ inputs.views.entries.map (·.view.cumulative))

/-- This arithmetic bound equals the proof-facing ordered substitution key
space cardinality. It constructs neither substitution lists nor profiles. -/
def sourceActiveCapacity {checked : Checked} {base : Base checked} (inputs : Inputs base) : Nat :=
  let alphabet := inputs.views.entries.flatMap (·.view.ownSubstitution)
  let domainSize := (alphabet.map Prod.fst).eraseDups.length
  ((List.range (domainSize + 1)).map (alphabet.length ^ ·)).sum

def capacity {checked : Checked} {base : Base checked} (inputs : Inputs base) (initial : Table) : Nat :=
  initial.states.foldl (fun total state =>
    let size := (stateKey state).requirements.flatten.length
    total + sourceActiveCapacity inputs * (nativeContexts inputs).length * size ^ size) 0

def valid {checked : Checked} {base : Base checked} (inputs : Inputs base) (table : Table) : Bool :=
  let namedSound := table.named.all fun edge =>
    match named? inputs edge.origin with
    | none => false | some state => decide (table.stateAt? edge.destination = some state)
  let lambdaSound := table.lambdas.all fun edge =>
    match table.stateAt? edge.state with
    | none => false | some state => lambdaAllowed inputs state edge.origin
  let viewSound := table.views.all fun edge =>
    match table.stateAt? edge.caller, table.stateAt? edge.lexical with
    | some caller, some lexical => match view? inputs caller lexical edge.view edge.target with
      | none => false | some next => decide (table.stateAt? edge.destination = some next)
    | _, _ => false
  let namedClosed := inputs.callable.table.entries.all fun entry =>
    match named? inputs entry.id with
    | none => true | some state => match table.namedAt? entry.id with
      | none => false | some position => decide (table.stateAt? position = some state)
  let transitionsClosed := table.states.zipIdx.all fun caller =>
    inputs.templates.lambdas.all (fun template =>
      !lambdaAllowed inputs caller.1 template.descriptor || table.lambdaAllowed caller.2 template.descriptor) &&
    table.states.zipIdx.all (fun lexical => inputs.views.entries.all fun entry =>
      match inputs.callable.table.idAt?
          (.lambda entry.view.owner entry.view.principal.initializer entry.view.cumulative) with
      | none => true
      | some target => match view? inputs caller.1 lexical.1 entry.id target with
        | none => true
        | some next => match table.viewAt? caller.2 lexical.2 entry.id target with
          | none => false | some position => decide (table.stateAt? position = some next))
  namedSound && lambdaSound && viewSound && namedClosed && transitionsClosed

structure Recipe {checked : Checked} {base : Base checked} (inputs : Inputs base) (table : Table) where private mk ::
  edge : ViewEdge
  owned : edge ∈ table.views
  caller : State
  callerFound : table.stateAt? edge.caller = some caller
  lexical : State
  lexicalFound : table.stateAt? edge.lexical = some lexical
  read : SourceCoreCallableAncestryReadRecipes.Read inputs caller edge.view edge.target
  readPrepared : SourceCoreCallableAncestryReadRecipes.prepareRead inputs caller edge.view edge.target = .ok read
  applied : SourceCoreCallableAncestryReadRecipes.Applied read lexical
  appliedPrepared : SourceCoreCallableAncestryReadRecipes.applyRead read lexical = .ok applied
  destination : table.stateAt? edge.destination = some (read.after lexical)

def prepareRecipe {checked : Checked} {base : Base checked} (inputs : Inputs base) (table : Table)
    (edge : ViewEdge) (owned : edge ∈ table.views) : Except Error (Recipe inputs table) := do
  match callerFound : table.stateAt? edge.caller with
  | none => throw (.missingState edge.caller)
  | some caller =>
    match lexicalFound : table.stateAt? edge.lexical with
    | none => throw (.missingState edge.lexical)
    | some lexical =>
      match readPrepared : SourceCoreCallableAncestryReadRecipes.prepareRead inputs caller edge.view edge.target with
      | .error error => throw (.read error)
      | .ok read =>
        match appliedPrepared : SourceCoreCallableAncestryReadRecipes.applyRead read lexical with
        | .error error => throw (.read error)
        | .ok applied =>
          if destination : table.stateAt? edge.destination = some (read.after lexical) then
            pure ⟨edge, owned, caller, callerFound, lexical, lexicalFound, read, readPrepared, applied, appliedPrepared, destination⟩
          else throw .wrongDestination

structure Prepared {checked : Checked} (base : Base checked) where private mk ::
  inputs : Inputs base
  initial : Table
  seeded : seed inputs = .ok initial
  table : Table
  completed : saturate inputs (capacity inputs initial) 0 initial = .ok table
  validated : valid inputs table = true
  recipes : List (Recipe inputs table)
  recipesPrepared : table.views.attach.mapM (fun edge => prepareRecipe inputs table edge.val edge.property) = .ok recipes

def prepare {checked : Checked} (base : Base checked) : Except Error (Prepared base) := do
  let inputs ← (SourceCoreCallableAncestryPreparation.prepareInputs base).mapError Error.inputs
  match seeded : seed inputs with
  | .error error => throw error
  | .ok initial =>
    match completed : saturate inputs (capacity inputs initial) 0 initial with
    | .error error => throw error
    | .ok table =>
      if validated : valid inputs table = true then
        match recipesPrepared : table.views.attach.mapM (fun edge => prepareRecipe inputs table edge.val edge.property) with
        | .error error => throw error
        | .ok recipes => pure ⟨inputs, initial, seeded, table, completed, validated, recipes, recipesPrepared⟩
      else throw .invalidClosure

/-- Runtime selection touches only cached edge words/indices. The returned
receipt already contains caller witnesses, original lexical headers, and the
exact source-after metadata; no source lookup/substitution occurs here. -/
def Prepared.recipeAt? {checked : Checked} {base : Base checked} (prepared : Prepared base)
    (caller lexical : Nat) (view target : Core.Word) : Option (Recipe prepared.inputs prepared.table) :=
  prepared.recipes.find? fun recipe => decide
    (recipe.edge.caller = caller ∧ recipe.edge.lexical = lexical ∧ recipe.edge.view = view ∧ recipe.edge.target = target)

end Solcore.Frontend.SourceCoreCallableAncestryPairedPreparation
