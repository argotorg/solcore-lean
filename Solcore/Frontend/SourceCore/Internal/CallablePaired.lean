import Solcore.Frontend.SourceCore.Internal.CallableAncestry
import Solcore.Frontend.SourceCore.Internal.Carriers
import Solcore.Frontend.SourceCore.Internal.CallableViews
import Solcore.Frontend.SourceCore.Internal.CallablePrincipals
import Solcore.Frontend.SourceCore.Internal.Allocation

/-!
# Paired callable ancestry

Ancestry that keeps read-time callers and lexical creators: programs, templates, captures, views and
restoration.
-/

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallableAncestryPairedCache
/-! Table-only lookup for read-time caller and lexical creation snapshots.
Both parents of an applied view are retained. Native code context and source
substitution are distinct key fields. This data table does not itself certify
compiler ownership, closure/capture provenance, or runtime reachability. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableAncestryPairedCache
open SourceInference TypeSystem
abbrev State := SourceCoreCallableAncestryReadRecipes.State
abbrev Frame := SourceCoreCallablePairedFrames.Frame
abbrev Owner := SourceSpecialization.SpecializationKey

structure Key where
  owner : Owner
  sourceActive : Substitution
  nativeActive : Substitution
  requirements : List (List RequirementId)
  deriving DecidableEq, Repr

def stateKey (state : State) : Key :=
  ⟨state.metadata.owner, state.metadata.active, state.nativeActive, state.metadata.source.nodes.map fun
    | .expression node => node.requirements
    | .statement _ => []⟩

abbrev NamedEdge := SourceCoreCallableAncestryCache.NamedEdge
abbrev LambdaEdge := SourceCoreCallableAncestryCache.LambdaEdge

structure ViewEdge where
  caller : Nat
  lexical : Nat
  view : Core.Word
  target : Core.Word
  destination : Nat
  deriving DecidableEq, Repr

structure Table where
  states : List State
  named : List NamedEdge
  lambdas : List LambdaEdge
  views : List ViewEdge
  deriving DecidableEq, Repr

def Table.stateAt? (table : Table) (index : Nat) : Option State := table.states[index]?
def Table.namedAt? (table : Table) (origin : Core.Word) : Option Nat :=
  (table.named.find? fun edge => decide (edge.origin = origin)).map (·.destination)
def Table.lambdaAllowed (table : Table) (state : Nat) (origin : Core.Word) : Bool :=
  table.lambdas.any fun edge => decide (edge.state = state ∧ edge.origin = origin)
def Table.viewAt? (table : Table) (caller lexical : Nat) (view target : Core.Word) : Option Nat :=
  (table.views.find? fun edge => decide
    (edge.caller = caller ∧ edge.lexical = lexical ∧ edge.view = view ∧ edge.target = target)).map (·.destination)

/-- The transient read tag is installed only while invoking its underlying
lambda. It becomes an applied view when that lambda joins its own snapshot.
It has no principal execution-source state on its own. -/
def Table.lookupIndex? (table : Table) : Frame → Option (Option Nat)
  | .empty => some none
  | .named origin => (table.namedAt? origin).map some
  | .lambda origin lexical =>
    match table.lookupIndex? lexical with
    | some (some state) => if table.lambdaAllowed state origin then some (some state) else none
    | _ => none
  | .view .. => none
  | .appliedView view target caller lexical =>
    match table.lookupIndex? caller, table.lookupIndex? lexical with
    | some (some callerState), some (some lexicalState) =>
      (table.viewAt? callerState lexicalState view target).map some
    | _, _ => none

def Table.lookup? (table : Table) (frame : Frame) : Option (Option State) :=
  match table.lookupIndex? frame with
  | none => none
  | some none => some none
  | some (some position) => (table.stateAt? position).map some

end Solcore.Frontend.SourceCoreCallableAncestryPairedCache
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallableAncestryPairedPreparation
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
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallablePairedAncestry
/-! Paired dynamic callable ancestry uses one ordinary Core cell, placed after the
lexical source references and globals. A lambda snapshots that cell when it is
created. Calls enter its lexical frame and restore the caller, including on a
language failure. Owned read views snapshot the read caller independently of the original lambda's lexical creation frame, preserving identity/descriptor.

This is a compiler representation, not a source evaluator or a source-heap
exporter. Its cached metadata is prepared once. Reconstructing legacy source
closures still requires the artifact's allocation ledger and exact native
closure template authentication. Context snapshots add values to closure
environments; they do not allocate source cells.
-/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallablePairedAncestry
open SourceInference Core
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Base := SourceCoreCompatibleFunctions.Prepared
abbrev Key := SourceSpecialization.SpecializationKey
abbrev Active := TypeSystem.Substitution
abbrev Scope := SourceCoreFunctions.Scope
abbrev Frames := SourceCoreCallablePairedFrames.Frame

inductive Error where
  | invalidDefinitions
  | foreignDefinitions
  | templates (error : SourceCoreLambdaTemplates.Error)
  | views (error : SourceCoreCallableViews.Error)
  | principals (error : SourceCoreCallablePrincipals.Error)
  | viewLowering (error : SourceCoreCallableViewLowering.Error)
  | missingCallableContext
  | missingOrigin (origin : SourceCoreStageCodebook.Origin)
  | invalidLambda
  | invalidGlobals
  | missingInstance (read : ExpressionId)
  | unsupportedCarrier (type : Ty)
  | compilation (error : SourceCoreCompatibleMarkedFunctions.Error)
  | assembly (error : SourceCoreGeneralFunctions.Error)
  | native (error : SourceCoreGeneralEntry.NativeCompileError)
  deriving Repr

/-- The context definition occupies a certified suffix of the ambient table.
Further source marker definitions may be appended after it. -/
structure Layout where private mk ::
  ambient : DataEnvironment
  frame : SourceCoreCallablePairedFrames.Layout
  atEnd : frame.dataType.index = ambient.length
  definitionsTyped : (ambient ++ [frame.definition]).WellFormed

def Layout.definitions (layout : Layout) : DataEnvironment := layout.ambient ++ [layout.frame.definition]
def Layout.referenceType (layout : Layout) : Ty := .cell layout.frame.type

def Layout.prepare (ambient : DataEnvironment) : Except Error Layout :=
  let frame : SourceCoreCallablePairedFrames.Layout := ⟨⟨ambient.length⟩⟩
  if valid : (ambient ++ [frame.definition]).isWellFormed = true then
    .ok ⟨ambient, frame, rfl, DataEnvironment.isWellFormed_sound valid⟩
  else .error .invalidDefinitions

theorem Layout.registered (layout : Layout) : layout.frame.Registered layout.definitions := by
  constructor
  simp [Layout.definitions, layout.atEnd]

theorem Layout.prefix (layout : Layout) : layout.definitions.take layout.ambient.length = layout.ambient := by
  simp [Layout.definitions]

/-- No fake source-global key is introduced for the administrative reference. -/
def creationReferenceIndex (context : SourceCoreFunctions.Context) (scope : Scope) : Nat :=
  scope.length + context.administrativePrefix + context.globals.length

/-- Snapshot is slot 1 after the lambda argument; the existing lexical
references keep their order after it. The manifest, when present, is already
part of `body` and is shifted along with the other administrative variables. -/
def snapshotLambda (layout : SourceCoreCallablePairedFrames.Layout) (origin : Word)
    (referenceIndex : Nat) (parameter result : Ty) (body : Expr) : Expr :=
  .letE (.loadCell (.var referenceIndex))
    (.lambda parameter (LanguageResult.resultType result)
      (SourceCoreCallablePairedFrames.withFrame (.var (referenceIndex + 2))
        (SourceCoreCallablePairedFrames.lambdaFrame layout origin (.var 1)
          (.loadCell (.var (referenceIndex + 2)))) (body.weakenAt 1)))

theorem snapshotLambda_hasType {definitions : DataEnvironment} {layout : SourceCoreCallablePairedFrames.Layout}
    {context : Core.Context} {parameter result : Ty} {body : Expr} {referenceIndex : Nat}
    (registered : layout.Registered definitions) (origin : Word)
    (parameterWF : parameter.WellFormed definitions) (resultWF : result.WellFormed definitions)
    (reference : context[referenceIndex]? = some (.cell layout.type))
    (bodyTyped : HasType (parameter :: context) body (LanguageResult.resultType result) definitions) :
    HasType context (snapshotLambda layout origin referenceIndex parameter result body)
      (.function parameter (LanguageResult.resultType result)) definitions := by
  apply HasType.letE (.loadCell (.var reference))
  apply HasType.lambda parameterWF (LanguageResult.resultType_wellFormed resultWF)
  apply SourceCoreCallableContextFrames.withFrame_hasType
  · exact .var (by simpa [Nat.add_assoc] using reference)
  · apply SourceCoreCallablePairedFrames.lambdaFrame_hasType registered origin (.var rfl)
    exact .loadCell (.var (by simpa [Nat.add_assoc] using reference))
  · simpa [Context.insertAt] using bodyTyped.weakenAt (inserted := layout.type) 1

/-- Creation reads only the administrative cell and captures its exact finite
value. Application semantics use the existing `withFrame` laws. -/
theorem snapshotLambda_evaluates {layout : SourceCoreCallablePairedFrames.Layout}
    {environment : Environment} {store : Store} {parameter result : Ty} {body : Expr}
    {referenceIndex location : Nat} {snapshot : Core.Value} (origin : Word)
    (reference : environment[referenceIndex]? = some (.cellRef layout.type location))
    (read : store.read? location = some snapshot) :
    Evaluates environment store (snapshotLambda layout origin referenceIndex parameter result body)
      (.closure parameter (LanguageResult.resultType result)
        (SourceCoreCallablePairedFrames.withFrame (.var (referenceIndex + 2))
          (SourceCoreCallablePairedFrames.lambdaFrame layout origin (.var 1)
            (.loadCell (.var (referenceIndex + 2)))) (body.weakenAt 1))
        (snapshot :: environment)) store :=
  .letE (.loadCell (.var reference) read) .lambda

/-- Saved slot zero is the read-time caller frame; saved slot one is the
original carrier. The lambda argument adds a leading slot on application. -/
def viewBody (layout : SourceCoreCallablePairedFrames.Layout) (id target : Word)
    (referenceIndex : Nat) : Expr :=
  SourceCoreCallablePairedFrames.withFrame (.var (referenceIndex + 3))
    (SourceCoreCallablePairedFrames.view layout id target (.var 1))
    (.apply (.second (.first (.var 2))) (.var 0))

def viewRepack (layout : SourceCoreCallablePairedFrames.Layout) (parameter result : Ty)
    (id target : Word) (referenceIndex : Nat) : Expr :=
  .pair (.pair (.first (.first (.var 1)))
    (.lambda parameter (LanguageResult.resultType result) (viewBody layout id target referenceIndex)))
    (.second (.var 1))

/-- Snapshot is taken after the successful read, before returning its value.
A later named caller cannot replace the occurrence's witness context. -/
def viewLower (layout : SourceCoreCallablePairedFrames.Layout) (parameter result : Ty)
    (id target : Word) (referenceIndex : Nat) (read : Expr) : Expr :=
  LanguageResult.bind (CallableContract.functionType parameter result) read
    (.letE (.loadCell (.var (referenceIndex + 1)))
      (LanguageResult.success (viewRepack layout parameter result id target referenceIndex)))

theorem viewRepack_hasType {definitions : DataEnvironment} {layout : SourceCoreCallablePairedFrames.Layout}
    {context : Core.Context} {parameter result : Ty} {referenceIndex : Nat}
    (registered : layout.Registered definitions) (id target : Word)
    (parameterWF : parameter.WellFormed definitions) (resultWF : result.WellFormed definitions)
    (reference : context[referenceIndex]? = some (.cell layout.type)) :
    HasType (layout.type :: CallableContract.functionType parameter result :: context)
      (viewRepack layout parameter result id target referenceIndex)
      (CallableContract.functionType parameter result) definitions := by
  apply HasType.pair
  · apply HasType.pair (.first (.first (.var rfl)))
    apply HasType.lambda parameterWF (LanguageResult.resultType_wellFormed resultWF)
    apply SourceCoreCallableContextFrames.withFrame_hasType
    · exact .var (by simpa [Nat.add_assoc] using reference)
    · exact SourceCoreCallablePairedFrames.view_hasType registered id target (.var rfl)
    · exact .apply (.second (.first (.var rfl))) (.var rfl)
  · exact .second (.var rfl)

theorem viewLower_hasType {definitions : DataEnvironment} {layout : SourceCoreCallablePairedFrames.Layout}
    {context : Core.Context} {parameter result : Ty} {referenceIndex : Nat} {read : Expr}
    (registered : layout.Registered definitions) (id target : Word)
    (parameterWF : parameter.WellFormed definitions) (resultWF : result.WellFormed definitions)
    (reference : context[referenceIndex]? = some (.cell layout.type))
    (readTyped : HasType context read (LanguageResult.resultType (CallableContract.functionType parameter result)) definitions) :
    HasType context (viewLower layout parameter result id target referenceIndex read)
      (LanguageResult.resultType (CallableContract.functionType parameter result)) definitions := by
  apply LanguageResult.bind_hasType (CallableContract.functionType_wellFormed parameterWF resultWF) readTyped
  apply HasType.letE (.loadCell (.var (by simpa [Nat.add_assoc] using reference)))
  exact LanguageResult.success_hasType (viewRepack_hasType registered id target parameterWF resultWF reference)

/-- A language failure returns before the snapshot read or wrapper creation. -/
theorem viewLower_failure {layout : SourceCoreCallablePairedFrames.Layout} {environment : Environment}
    {before after : Store} {read : Expr} {parameter result : Ty} {id target reason : Word} {referenceIndex : Nat}
    (evaluated : Evaluates environment before read
      (.inLeft (CallableContract.functionType parameter result) (.word reason)) after) :
    Evaluates environment before (viewLower layout parameter result id target referenceIndex read)
      (.inLeft (CallableContract.functionType parameter result) (.word reason)) after :=
  LanguageResult.bind_failure (CallableContract.functionType parameter result) evaluated

/-- Successful creation captures the exact read-time frame and original
carrier. It adds no cells and preserves the read's final store. -/
theorem viewLower_evaluates {layout : SourceCoreCallablePairedFrames.Layout} {environment : Environment}
    {before after : Store} {read : Expr} {parameter result : Ty} {id target descriptor : Word}
    {referenceIndex location : Nat} {identity originalPayload snapshot : Value}
    (evaluated : Evaluates environment before read
      (.inRight .word (.pair (.pair identity originalPayload) (.word descriptor))) after)
    (reference : environment[referenceIndex]? = some (.cellRef layout.type location))
    (snapshotRead : after.read? location = some snapshot) :
    Evaluates environment before (viewLower layout parameter result id target referenceIndex read)
      (.inRight .word (.pair (.pair identity
        (.closure parameter (LanguageResult.resultType result) (viewBody layout id target referenceIndex)
          (snapshot :: .pair (.pair identity originalPayload) (.word descriptor) :: environment))) (.word descriptor))) after := by
  apply Evaluates.caseRight evaluated
  apply Evaluates.letE (.loadCell (.var (by simpa using reference)) snapshotRead)
  exact .inRight (.pair (.pair (.first (.first (.var rfl))) .lambda) (.second (.var rfl)))


structure Prepared {checked : Checked} (base : Base checked) where private mk ::
  layout : Layout
  layoutPrepared : Layout.prepare checked.catalog.definitions = .ok layout
  views : SourceCoreCallableViews.Table base.sourceProgram base.plan
  viewsPrepared : SourceCoreCallableViews.prepare base = .ok views
  principals : SourceCoreCallablePrincipals.Table base.sourceProgram base.plan base.contexts
  principalsPrepared : SourceCoreCallablePrincipals.prepare base = .ok principals
  templates : SourceCoreLambdaTemplates.Inventory checked
  templatesPrepared : SourceCoreLambdaTemplates.prepare base = .ok templates

def prepare {checked : Checked} (base : Base checked) : Except Error (Prepared base) := do
  let layout ← match accepted : Layout.prepare checked.catalog.definitions with
    | .error error => throw error
    | .ok layout => pure (⟨layout, accepted⟩ : {layout // Layout.prepare checked.catalog.definitions = .ok layout})
  let views ← match accepted : SourceCoreCallableViews.prepare base with
    | .error error => throw (.views error)
    | .ok views => pure (⟨views, accepted⟩ : {views // SourceCoreCallableViews.prepare base = .ok views})
  let principals ← match accepted : SourceCoreCallablePrincipals.prepare base with
    | .error error => throw (.principals error)
    | .ok principals => pure (⟨principals, accepted⟩ : {principals // SourceCoreCallablePrincipals.prepare base = .ok principals})
  let templates ← match accepted : SourceCoreLambdaTemplates.prepare base with
    | .error error => throw (.templates error)
    | .ok templates => pure (⟨templates, accepted⟩ : {templates // SourceCoreLambdaTemplates.prepare base = .ok templates})
  pure ⟨layout.val, layout.property, views.val, views.property, principals.val, principals.property,
    templates.val, templates.property⟩

private def fail (error : Error) : SourceCoreBasic.Error := .sourceAllocation (reprStr error)

def originId {checked : Checked} {base : Base checked} (_ : Prepared base)
    (origin : SourceCoreStageCodebook.Origin) : Except SourceCoreBasic.Error Word := do
  let native ← match base.callableContext with
    | some native => pure native | none => throw (fail .missingCallableContext)
  match native.table.idAt? origin with
  | some id => pure id | none => throw (fail (.missingOrigin origin))

def expressionHook {checked : Checked} {base : Base checked} (prepared : Prepared base)
    (owner : Key) (active : Active) : SourceCoreFunctions.RawLambdaExpressionHook :=
    fun context source scope node parameter result raw => do
  if context.owner != owner || context.globals != base.globals then throw (fail .invalidGlobals)
  let origin ← originId prepared (.lambda owner node.id active)
  let .lambda actualParameter actualResult body := raw | throw (fail .invalidLambda)
  if actualParameter != parameter || actualResult != LanguageResult.resultType result then throw (fail .invalidLambda)
  if source.owner != owner.declaration then throw (fail .invalidLambda)
  pure (snapshotLambda prepared.layout.frame origin (creationReferenceIndex context scope) parameter result body)

def namedBody {checked : Checked} {base : Base checked} (prepared : Prepared base)
    (function : SourceCoreGeneralFunctions.Function) (body : Expr) : Except SourceCoreBasic.Error Expr := do
  let origin ← originId prepared (.named function.signature.key)
  pure (SourceCoreCallablePairedFrames.withFrame (.var (base.globals.length + 1))
    (SourceCoreCallablePairedFrames.named prepared.layout.frame origin) body)

/-- The common contextual compiler currently uses one surviving packed-argument
administrative slot. Installation and loop helpers later rename this whole
expression, including the reference to the final context slot. -/
def lowerView {checked : Checked} {base : Base checked} (prepared : Prepared base)
    (owner : Key) (active : Active) (source : TypedSource) (scope : Scope)
    (read : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) : Except SourceCoreBasic.Error SourceCoreBasic.LoweredExpr := do
  let receipt ← (SourceCoreCallableViewLowering.lowerWithReceipt prepared.views owner active source read lowered)
    |>.mapError (fun error => fail (.viewLowering error))
  if !receipt.entry.view.wrapsPrincipal then return lowered
  let candidate ← match receipt.entry.view.selectedInstance with
    | some candidate => pure candidate | none => throw (fail (.missingInstance read))
  let target ← originId prepared (.lambda candidate.origin.caller candidate.origin.initializer candidate.origin.substitution)
  match lowered.type with
  | .product (.product (.sum .unit .word) (.function parameter (.sum .word result))) .word =>
    pure {lowered with expression := (viewLower prepared.layout.frame parameter result receipt.entry.id target
      (scope.length + 1 + base.globals.length) lowered.expression)}
  | type => throw (fail (.unsupportedCarrier type))

/-- Compose the manifest and snapshot hooks with the supplied data/allocator
profile. Compiler invocation retains its usual source traversal and ABI. -/
def representation {checked : Checked} {base : Base checked} (prepared : Prepared base)
    (original : SourceCoreGeneralFunctions.Representation) : SourceCoreGeneralFunctions.Representation :=
  {original with
    rawLambdaBodyAt := SourceCoreLambdaTemplates.hook prepared.templates
    rawLambdaExpressionAt := expressionHook prepared
    rawNamedBody := namedBody prepared
    localReadView := lowerView prepared}

structure Compiled {checked : Checked} {base : Base checked} (prepared : Prepared base)
    (original : SourceCoreGeneralFunctions.Representation) (fuel : Nat) where private mk ::
  compilation : SourceCoreCompatibleMarkedFunctions.Compilation base (representation prepared original) fuel

def compile {checked : Checked} {base : Base checked} (prepared : Prepared base)
    (original : SourceCoreGeneralFunctions.Representation) (fuel : Nat) :
    Except Error (Compiled prepared original fuel) := do
  let compiled ← (SourceCoreCompatibleMarkedFunctions.compileWithReceipt base (representation prepared original) fuel)
    |>.mapError Error.compilation
  pure ⟨compiled⟩

/-- Input expressions are already indexed under globals followed by the final
context reference. Native input-reference preparation is a later artifact
adapter; the common cached global/closure assembly is reused unchanged. -/
def assemble {checked : Checked} {base : Base checked} {prepared : Prepared base}
    {original : SourceCoreGeneralFunctions.Representation} {fuel : Nat}
    (compiled : Compiled prepared original fuel) (key : Key) (arguments : SourceCoreBasic.LoweredExpr) :
    Except Error Expr := do
  let body ← (SourceCoreGeneralFunctions.assembleCall base.globals base.functions compiled.compilation.closures key arguments)
    |>.mapError Error.assembly
  pure (SourceCoreCallablePairedFrames.allocate prepared.layout.frame body)

end Solcore.Frontend.SourceCoreCallablePairedAncestry
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallablePairedFrameCodec
/-! Exact paired-frame decoding. A decoded tree preserves read-caller and
lexical parents in order. This is a carrier law, not source-history authority.
-/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallablePairedFrameCodec
open Core SourceCoreCallablePairedFrames
abbrev PairedFrame := SourceCoreCallablePairedFrames.Frame

def decode (layout : Layout) : Value → Option PairedFrame
  | .constructed constructor .unit => if constructor = layout.empty then some .empty else none
  | .constructed constructor (.word origin) => if constructor = layout.named then some (.named origin) else none
  | .constructed constructor (.pair (.word first) second) =>
      if constructor = layout.lambda then (decode layout second).map (.lambda first)
      else if constructor = layout.view then
        match second with
        | .pair (.word target) caller => (decode layout caller).map (.view first target)
        | _ => none
      else if constructor = layout.appliedView then
        match second with
        | .pair (.word target) (.pair caller lexical) => do
            let caller ← decode layout caller
            let lexical ← decode layout lexical
            pure (.appliedView first target caller lexical)
        | _ => none
      else none
  | _ => none

theorem decode_encode (layout : Layout) (frame : PairedFrame) : decode layout (encode layout frame) = some frame := by
  induction frame with
  | empty => simp [decode, encode]
  | named origin => simp [decode, encode]
  | lambda origin captured ih =>
      rw [encode, decode.eq_def]
      simp only [↓reduceIte]
      rw [ih]
      rfl
  | view view target caller ih => simp [decode, encode, Layout.lambda, Layout.view, ih]
  | appliedView view target caller lexical callerIH lexicalIH =>
    simp [decode, encode, Layout.lambda, Layout.view, Layout.appliedView, callerIH, lexicalIH]

theorem decode_sound (layout : Layout) (value : Value) (frame : PairedFrame)
    (decoded : decode layout value = some frame) : value = encode layout frame := by
  revert frame
  induction value using decode.induct layout with
  | case1 => intro frame decoded; simp [decode] at decoded; subst frame; rfl
  | case2 constructor different => intro frame decoded; simp [decode, different] at decoded
  | case3 origin => intro frame decoded; simp [decode] at decoded; subst frame; rfl
  | case4 constructor origin different => intro frame decoded; simp [decode, different] at decoded
  | case5 first second ih =>
    intro frame decoded
    rw [decode.eq_def] at decoded
    simp only [↓reduceIte] at decoded
    cases observed : decode layout second with
    | none => simp [observed] at decoded
    | some captured =>
      simp [observed] at decoded
      subst frame
      rw [encode, ih captured observed]
  | case6 first target caller different ih =>
    intro frame decoded
    simp [decode, different] at decoded
    cases observed : decode layout caller with
    | none => simp [observed] at decoded
    | some captured =>
      simp [observed] at decoded
      subst frame
      rw [encode, ih captured observed]
  | case7 first second malformed different =>
    intro frame decoded
    rw [decode.eq_def] at decoded
    simp only [different, ↓reduceIte] at decoded
    contradiction
  | case8 first target caller lexical notLambda notView callerIH lexicalIH =>
    intro frame decoded
    simp only [decode, notLambda, notView, ↓reduceIte] at decoded
    cases callerFound : decode layout caller with
    | none => simp [callerFound] at decoded
    | some callerFrame =>
      cases lexicalFound : decode layout lexical with
      | none => simp [callerFound, lexicalFound] at decoded
      | some lexicalFrame =>
        simp [callerFound, lexicalFound] at decoded
        subst frame
        rw [encode, callerIH callerFrame callerFound, lexicalIH lexicalFrame lexicalFound]
  | case9 first second malformed notLambda notView =>
    intro frame decoded
    rw [decode.eq_def] at decoded
    simp only [notLambda, notView, ↓reduceIte] at decoded
    contradiction
  | case10 constructor first second notLambda notView notApplied =>
    intro frame decoded
    rw [decode.eq_def] at decoded
    simp [notLambda, notView, notApplied] at decoded
  | case11 value notEmpty notNamed notPair =>
    intro frame decoded
    rw [decode.eq_def] at decoded
    split at decoded <;> simp_all

theorem decode_iff (layout : Layout) (value : Value) (frame : PairedFrame) :
    decode layout value = some frame ↔ value = encode layout frame :=
  ⟨decode_sound layout value frame, fun same => same ▸ decode_encode layout frame⟩

end Solcore.Frontend.SourceCoreCallablePairedFrameCodec
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallablePairedAllocationFrames
/-! Keep allocation-time callable ancestry even for a generalized principal
whose native instance bundle is Unit. One ordinary administrative paired-frame cell
precedes each source marker. Its index is excluded from the source ledger.

The original allocator still authenticates the exact source/binder/layout.
The extra cell is emitted after the source initializer has produced its
successful value. The enclosing assembled checker validates its placement.
A decoded adjacent snapshot proves its shape, not execution history. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallablePairedAllocationFrames
open SourceInference Core
abbrev Request := SourceCoreSourceCells.Request
abbrev Allocator := SourceCoreSourceCells.Allocator
abbrev Layout := SourceCoreCallablePairedFrames.Layout
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Base := SourceCoreCompatibleFunctions.Prepared

/-- Named inputs bind the incoming argument through `request.references`.
Other sites retain the caller's original packed-argument slot. Binder IDs are
selected from the authenticated source; lambda IDs are distinct from inputs. -/
def isNamedInput (request : Request) : Bool :=
  request.source.inputs.any (fun binder => decide (binder.id = request.binder.id))

def referenceIndex (globals : Nat) (request : Request) : Nat :=
  request.references (request.scope.length + (if isNamedInput request then 0 else 1) + globals)

/-- Administrative lexical insertion moves every original allocation variable
with its expression, including its actual captures and initialized payload. -/
def snapshotBefore (layout : Layout) (reference allocation : Expr) : Expr :=
  .letE (.newCell layout.type (.loadCell reference)) (allocation.weakenAt 0)

theorem snapshotBefore_hasType {definitions : DataEnvironment} {context : Core.Context}
    {layout : Layout} {reference allocation : Expr} {result : Ty}
    (_registered : layout.Registered definitions)
    (referenceTyped : HasType context reference (.cell layout.type) definitions)
    (allocationTyped : HasType context allocation result definitions) :
    HasType context (snapshotBefore layout reference allocation) result definitions := by
  apply HasType.letE (.newCell (.loadCell referenceTyped))
  simpa [Context.insertAt] using allocationTyped.weakenAt (inserted := .cell layout.type) 0

structure Annotated (layout : Layout) (globals : Nat) (allocate : Allocator) (request : Request) where private mk ::
  original : Expr
  allocated : allocate request = .ok original
  expression : Expr
  exact : expression = snapshotBefore layout (.var (referenceIndex globals request)) original

def annotateWithReceipt (layout : Layout) (globals : Nat) (allocate : Allocator) (request : Request) :
    Except SourceCoreBasic.Error (Annotated layout globals allocate request) :=
  match allocated : allocate request with
  | .error error => .error error
  | .ok original => .ok ⟨original, allocated,
      snapshotBefore layout (.var (referenceIndex globals request)) original, rfl⟩

def allocator (layout : Layout) (globals : Nat) (allocate : Allocator) : Allocator :=
  fun request => (annotateWithReceipt layout globals allocate request).map (·.expression)

/-- Apply to the actual frame-aware representation after selecting its common
source-allocation profile. No new source binder or global key is introduced. -/
def representation {checked : Checked} {base : Base checked}
    (ancestry : SourceCoreCallablePairedAncestry.Prepared base)
    (original : SourceCoreGeneralFunctions.Representation) : SourceCoreGeneralFunctions.Representation :=
  {original with allocatorAt := fun owner active =>
    (original.allocatorAt owner active).map (allocator ancestry.layout.frame base.globals.length)}

inductive Error where
  | missingPredecessor
  | malformedSnapshot (index : Nat)
  deriving Repr

structure Snapshot {layouts : SourceCoreAllocationLayouts.Prepared} {store : Store}
    (layout : Layout) (row : SourceCoreAllocationLedger.Row layouts store) where private mk ::
  index : Nat
  preceding : index + 1 = row.markerIndex
  frame : SourceCoreCallablePairedFrames.Frame
  exact : store[index]? = some (SourceCoreCallablePairedFrames.encode layout frame)

def snapshot {layouts : SourceCoreAllocationLayouts.Prepared} {store : Store}
    (layout : Layout) (row : SourceCoreAllocationLedger.Row layouts store) : Except Error (Snapshot layout row) := do
  if preceding : row.markerIndex - 1 + 1 = row.markerIndex then
    match selected : store[row.markerIndex - 1]? with
    | none => throw (.malformedSnapshot (row.markerIndex - 1))
    | some value =>
      match decoded : SourceCoreCallablePairedFrameCodec.decode layout value with
      | none => throw (.malformedSnapshot (row.markerIndex - 1))
      | some frame =>
        have same := SourceCoreCallablePairedFrameCodec.decode_sound layout value frame decoded
        pure ⟨row.markerIndex - 1, preceding, frame, same ▸ selected⟩
  else throw .missingPredecessor

end Solcore.Frontend.SourceCoreCallablePairedAllocationFrames
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallablePairedPrograms
/-! Own one administrative paired callable frame alongside source-allocation markers.
Both passes use the actual common contextual compiler and the same cached
ancestry metadata. Native entries and resumable results retain the complete
frame/marker definition suffix. Public source inputs keep the original cached
admission plan. The source heap excludes the administrative frame cell.

This factory connects Core frame execution, not source closure reconstruction
or the complete source/Core meaning theorem. Those consume its owned receipts. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallablePairedPrograms
open SourceInference
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Base := SourceCoreCompatibleFunctions.Prepared
abbrev Key := SourceSpecialization.SpecializationKey
abbrev Layouts := SourceCoreAllocationLayouts.Prepared
abbrev Representation := SourceCoreGeneralFunctions.Representation

inductive Error where
  | contexts (error : SourceCoreAllocationContexts.Error)
  | discovery (error : SourceCoreAllocationDiscovery.Error)
  | layouts (error : SourceCoreAllocationLayouts.Error)
  | compilation (error : SourceCoreCompatibleMarkedFunctions.Error)
  | functions (error : SourceCoreGeneralFunctions.Error)
  | inputs (error : SourceCoreCompatibleInputs.Error)
  | native (error : SourceCoreGeneralEntry.NativeCompileError)
  | missingRoot (key : Key)
  | ancestry (error : SourceCoreCallablePairedAncestry.Error)
  deriving Repr

def discoveryRepresentation {checked : Checked} {base : Base checked}
    (ancestry : SourceCoreCallablePairedAncestry.Prepared base) (fuel : Nat)
    (discovery : SourceCoreAllocationDiscovery.Prepared) : Representation :=
  SourceCoreCallablePairedAllocationFrames.representation ancestry
    (SourceCoreCallablePairedAncestry.representation ancestry (SourceCoreCompatibleMarkedFunctions.discoveryRepresentation base fuel discovery))

def markedRepresentation {checked : Checked} {base : Base checked}
    (ancestry : SourceCoreCallablePairedAncestry.Prepared base) (fuel : Nat) (layouts : Layouts) : Representation :=
  SourceCoreCallablePairedAllocationFrames.representation ancestry
    (SourceCoreCallablePairedAncestry.representation ancestry (SourceCoreCompatibleMarkedFunctions.markedRepresentation checked fuel layouts))

def assembleCall {checked : Checked} {base : Base checked}
    (ancestry : SourceCoreCallablePairedAncestry.Prepared base) (closures : List Core.Expr)
    (key : Key) (arguments : SourceCoreBasic.LoweredExpr) : Except Error Core.Expr := do
  let body ← (SourceCoreGeneralFunctions.assembleCall base.globals base.functions closures key arguments).mapError Error.functions
  pure (SourceCoreCallablePairedFrames.allocate ancestry.layout.frame body)

structure Entry (layouts : Layouts) where private mk ::
  key : Key
  inputs : List TypedBinder
  sourceResultType : TypeSystem.Ty
  native : SourceCoreGeneralEntry.NativeEntry layouts.definitions

structure SourceInputs (checked : Checked) (layouts : Layouts) where private mk ::
  context : SourceCoreCompatibleInputs.Context
  valuesExact : context.values = SourceCoreCompatibleValues.Context.initial checked
  definitionsExact : context.definitions = layouts.definitions

private def prepareInputs (checked : Checked) (base : Base checked) (layouts : Layouts) :
    Except Error (SourceInputs checked layouts) :=
  match accepted : SourceCoreCompatibleInputs.prepare (.initial checked) base.plan base.globals
      (base.callableContext.map (·.table)) layouts.definitions Core.Word.zero (some base.validationPlan) with
  | .error error => .error (.inputs error)
  | .ok context => .ok ⟨context, SourceCoreCompatibleInputs.prepare_values accepted, by
      unfold SourceCoreCompatibleInputs.prepare at accepted
      split at accepted
      · contradiction
      · cases accepted; rfl⟩

structure Prepared (checked : Checked) where private mk ::
  base : Base checked
  fuel : Nat
  ancestry : SourceCoreCallablePairedAncestry.Prepared base
  ancestryPrepared : SourceCoreCallablePairedAncestry.prepare base = .ok ancestry
  contexts : SourceCoreAllocationContexts.Inventory base.plan base.contexts
  contextsPrepared : SourceCoreAllocationContexts.fromPrepared base.plan base.contexts = .ok contexts
  discovery : SourceCoreAllocationDiscovery.Prepared
  discoveryPrepared : SourceCoreAllocationDiscovery.prepare ancestry.layout.definitions contexts.contexts = .ok discovery
  firstPass : SourceCoreCompatibleMarkedFunctions.Compilation base (discoveryRepresentation ancestry fuel discovery) fuel
  discovered : SourceCoreAllocationDiscovery.Discovered discovery (SourceCoreCompatibleMarkedFunctions.scanBudget (SourceCoreCompatibleMarkedFunctions.packClosures firstPass.closures))
    (SourceCoreCompatibleMarkedFunctions.packClosures firstPass.closures)
  scanned : SourceCoreAllocationDiscovery.discover discovery (SourceCoreCompatibleMarkedFunctions.scanBudget (SourceCoreCompatibleMarkedFunctions.packClosures firstPass.closures))
    (SourceCoreCompatibleMarkedFunctions.packClosures firstPass.closures) = .ok discovered
  layouts : Layouts
  layoutsPrepared : SourceCoreAllocationLayouts.prepare discovered = .ok layouts
  secondPass : SourceCoreCompatibleMarkedFunctions.Compilation base (markedRepresentation ancestry fuel layouts) fuel
  sourceInputs : SourceInputs checked layouts
  entries : List (Entry layouts)

def prepare {checked : Checked} (base : Base checked) (fuel : Nat) : Except Error (Prepared checked) := do
  let ancestry ← match accepted : SourceCoreCallablePairedAncestry.prepare base with
    | .error error => throw (.ancestry error)
    | .ok ancestry => pure (⟨ancestry, accepted⟩ : {ancestry // SourceCoreCallablePairedAncestry.prepare base = .ok ancestry})
  let contexts ← match accepted : SourceCoreAllocationContexts.fromPrepared base.plan base.contexts with
    | .error error => throw (.contexts error)
    | .ok inventory => pure (⟨inventory, accepted⟩ : {inventory //
        SourceCoreAllocationContexts.fromPrepared base.plan base.contexts = .ok inventory})
  let discovery ← match accepted : SourceCoreAllocationDiscovery.prepare ancestry.val.layout.definitions contexts.val.contexts with
    | .error error => throw (.discovery error)
    | .ok discovery => pure (⟨discovery, accepted⟩ : {discovery //
        SourceCoreAllocationDiscovery.prepare ancestry.val.layout.definitions contexts.val.contexts = .ok discovery})
  let firstPass ← (SourceCoreCompatibleMarkedFunctions.compileWithReceipt base (discoveryRepresentation ancestry.val fuel discovery.val) fuel).mapError Error.compilation
  let discovered ← match accepted : SourceCoreAllocationDiscovery.discover discovery.val
      (SourceCoreCompatibleMarkedFunctions.scanBudget (SourceCoreCompatibleMarkedFunctions.packClosures firstPass.closures)) (SourceCoreCompatibleMarkedFunctions.packClosures firstPass.closures) with
    | .error error => throw (.discovery error)
    | .ok discovered => pure (⟨discovered, accepted⟩ : {discovered //
        SourceCoreAllocationDiscovery.discover discovery.val (SourceCoreCompatibleMarkedFunctions.scanBudget (SourceCoreCompatibleMarkedFunctions.packClosures firstPass.closures))
          (SourceCoreCompatibleMarkedFunctions.packClosures firstPass.closures) = .ok discovered})
  let layouts ← match accepted : SourceCoreAllocationLayouts.prepare discovered.val with
    | .error error => throw (.layouts error)
    | .ok layouts => pure (⟨layouts, accepted⟩ : {layouts //
        SourceCoreAllocationLayouts.prepare discovered.val = .ok layouts})
  let secondPass ← (SourceCoreCompatibleMarkedFunctions.compileWithReceipt base (markedRepresentation ancestry.val fuel layouts.val) fuel).mapError Error.compilation
  let sourceInputs ← prepareInputs checked base layouts.val
  let entries ← base.plan.seedKeys.mapM fun key => do
    let function ← match base.functions.find? (fun function => decide (function.signature.key = key)) with
      | none => throw (.missingRoot key)
      | some function => pure function
    let arguments := SourceCoreCalls.packArguments (function.inputs.zipIdx.map fun ((_, type), index) =>
      ⟨type, Core.OptionalCell.read type (.var (base.globals.length + 1 + function.inputs.length - 1 - index)) Core.Word.zero⟩)
    let body ← assembleCall ancestry.val secondPass.closures key arguments
    let native ← (SourceCoreGeneralEntry.NativeEntry.compile layouts.val.definitions (function.inputs.map Prod.snd)
      function.signature.resultType body).mapError Error.native
    pure (Entry.mk key (function.inputs.map Prod.fst) function.specialized.function.inferredBodyType native)
  pure ⟨base, fuel, ancestry.val, ancestry.property, contexts.val, contexts.property,
    discovery.val, discovery.property, firstPass, discovered.val, discovered.property,
    layouts.val, layouts.property, secondPass, sourceInputs, entries⟩

def Prepared.find? {checked : Checked} (prepared : Prepared checked) (key : Key) : Option (Entry prepared.layouts) :=
  prepared.entries.find? (fun entry => decide (entry.key = key))

inductive RunError where
  | missingEntry (key : Key)
  | input (error : SourceCoreCompatibleInputs.Error)
  | functions (error : SourceCoreGeneralFunctions.Error)
  | compile (error : SourceCoreGeneralEntry.NativeCompileError)
  | native (error : SourceCoreGeneralEntry.RunError)
  | diagnostics (error : SourceCoreCompatibleDataPlaceFaultSites.Error)
  deriving Repr

structure Result {checked : Checked} (prepared : Prepared checked) (entry : Entry prepared.layouts) where private mk ::
  context : SourceCoreCompatibleValues.Context
  contextOwner : context.checked = checked
  extension : SourceCoreRawMetadata.Extends checked.staticRegistry context.registry
  diagnostics : SourceCoreFaultSites.Table
  native : SourceCoreGeneralEntry.Result prepared.layouts.definitions entry.native.resultType

structure Completion {checked : Checked} (prepared : Prepared checked) where private mk ::
  entry : Entry prepared.layouts
  result : Result prepared entry

private def diagnosticTable {checked : Checked} (prepared : Prepared checked) (entry : Entry prepared.layouts)
    (registry : SourceCoreRawMetadata.Registry)
    (extension : SourceCoreRawMetadata.Extends checked.staticRegistry registry) : Except RunError SourceCoreFaultSites.Table := do
  let table ← match prepared.base.diagnostics with
    | some diagnostics => (diagnostics.tableForRegistry registry extension).mapError RunError.diagnostics
    | none => pure {
        owner := entry.key.declaration
        resultType := entry.sourceResultType
        reads := []
        escapedReason := Core.Word.zero }
  pure <| match prepared.base.callableDiagnostics with
    | none => table
    | some diagnostics => {table with additional := table.additional ++
        diagnostics.rootTable.additional.filter (fun item => diagnostics.unknown.val ≤ item.1.val)}

def Prepared.runSource {checked : Checked} (prepared : Prepared checked) (key : Key)
    (arguments : List SourceTypedRuntime.Value) (executionFuel : Nat) (validationFuel : Nat := 256) :
    Except RunError (Completion prepared) := do
  let entry ← match prepared.find? key with
    | none => throw (.missingEntry key)
    | some entry => pure entry
  let ready := prepared.sourceInputs
  let encoded ← (SourceCoreCompatibleInputs.encode ready.context (entry.inputs.map (·.scheme.body))
    arguments validationFuel).mapError RunError.input
  have extension : SourceCoreRawMetadata.Extends checked.staticRegistry encoded.values.registry := by
    change SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial checked).registry _
    rw [← ready.valuesExact]
    exact encoded.preserves
  let context := (SourceCoreCompatibleValues.Context.initial checked).extend encoded.values.registry extension
  let body ← (SourceCoreGeneralFunctions.assembleCall prepared.base.globals prepared.base.functions
    prepared.secondPass.closures key ⟨encoded.type, encoded.expression⟩).mapError RunError.functions
  let body := SourceCoreCallablePairedFrames.allocate prepared.ancestry.layout.frame body
  let native ← match accepted : SourceCoreGeneralEntry.NativeEntry.compile prepared.layouts.definitions []
      entry.native.resultType body with
    | .error error => throw (.compile error)
    | .ok runner =>
        let result ← (runner.run [] executionFuel).mapError RunError.native
        have resultType := (SourceCoreGeneralEntry.NativeEntry.compile_fields accepted).2.1
        pure (resultType ▸ result)
  let table ← diagnosticTable prepared entry encoded.values.registry extension
  pure ⟨entry, ⟨context, rfl, extension, table, native⟩⟩

def Completion.resume {checked : Checked} {prepared : Prepared checked}
    (completion : Completion prepared) (fuel : Nat) : Completion prepared :=
  match completion.result.native.checkpoint? with
  | none => completion
  | some checkpoint => ⟨completion.entry, {completion.result with native := checkpoint.resume fuel}⟩

end Solcore.Frontend.SourceCoreCallablePairedPrograms
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallablePairedLedger
/-! The actual frame-aware runner's typed store and source allocation ledger.
The context cell remains administrative. Decoding its finite carrier supplies
its exact shape, while ownership of the frame words and execution history
remain separate obligations. Observations never resume a checkpoint. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallablePairedLedger
open Core
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Prepared := SourceCoreCallablePairedPrograms.Prepared
abbrev Completion {checked : Checked} (prepared : Prepared checked) :=
  SourceCoreCallablePairedPrograms.Completion prepared
abbrev SourceHeap := SourceCoreAllocationLedger.SourceHeap

def store {checked : Checked} {prepared : Prepared checked} (completion : Completion prepared) : Store :=
  SourceCoreCompatibleMarkedLedger.observedStore completion.result.native.observation

def world {checked : Checked} {prepared : Prepared checked} (completion : Completion prepared) : StoreTyping :=
  (store completion).map Value.type

theorem store_typed {checked : Checked} {prepared : Prepared checked} (completion : Completion prepared) :
    RuntimeStoreHasTypes (world completion) (store completion) prepared.layouts.definitions :=
  SourceCoreCompatibleMarkedLedger.native_store_typed completion.result.native

abbrev Receipt {checked : Checked} {prepared : Prepared checked}
    (completion : Completion prepared) (initial : SourceHeap) :=
  SourceCoreAllocationLedger.TypedLedger prepared.layouts initial (world completion) (store completion)

def scan {checked : Checked} {prepared : Prepared checked}
    (completion : Completion prepared) (initial : SourceHeap := []) :
    Except SourceCoreAllocationLedger.Error (Receipt completion initial) :=
  SourceCoreAllocationLedger.scanTyped prepared.layouts initial (world completion) (store completion)
    (store_typed completion)

/-- Public runSource starts with the fresh context cell at location zero. A
checkpoint taken before that allocation has no frame yet. -/
def frame? {checked : Checked} {prepared : Prepared checked} (completion : Completion prepared) :
    Option SourceCoreCallablePairedFrames.Frame :=
  (store completion)[0]? >>= SourceCoreCallablePairedFrameCodec.decode prepared.ancestry.layout.frame

theorem frame_exact {checked : Checked} {prepared : Prepared checked} {completion : Completion prepared}
    {frame : SourceCoreCallablePairedFrames.Frame} (decoded : frame? completion = some frame) :
    (store completion)[0]? = some (SourceCoreCallablePairedFrames.encode prepared.ancestry.layout.frame frame) := by
  unfold frame? at decoded
  cases selected : (store completion)[0]? with
  | none => simp [selected] at decoded
  | some value =>
      simp only [selected] at decoded
      exact congrArg some (SourceCoreCallablePairedFrameCodec.decode_sound _ value frame decoded)

end Solcore.Frontend.SourceCoreCallablePairedLedger
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallablePairedTemplates
/-! Paired snapshot-bearing lambda templates from the artifact's actual second pass.
The scanner retains its compiler equation and installed syntax. Local inverse
renaming is accepted only when reconstructing the complete expression gives
exactly the original snapshot/withFrame carrier. Nested scanning uses the
original wrapped body, so outer administrative binders are never erased from
child capture indices.

Authentication establishes exact cached code, installed globals/context slot,
finite owned paired-frame words and world-typed source reference slots. The
read caller and lexical principal snapshots are not equated with a compiled
cumulative substitution. These facts
alone are not source execution history. The source allocation ledger must still
link each native location to its recorded source binder; source-value export
must consume actual produced values from the owning runner.
-/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallablePairedTemplates
open SourceInference Core
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Prepared := SourceCoreCallablePairedPrograms.Prepared
abbrev Scope := SourceCoreFunctions.Scope
abbrev Frame := SourceCoreCallablePairedFrames.Frame

inductive Error where
  | native (error : SourceCoreCallableNativeSlots.Error)
  | exhausted
  | malformedSnapshot
  | template (error : SourceCoreLambdaTemplates.Error)
  | manifestDepthMismatch
  | descriptorMismatch
  | globalsMismatch (location : Nat)
  | missingGlobal (index : Nat)
  | globalTemplateMismatch (index : Nat)
  | closureMismatch
  | snapshotMissing
  | snapshotMalformed
  | foreignFrame
  | contextReferenceMismatch
  | contextWorldMismatch
  | contextValueMalformed
  | missingCapture (index : Nat)
  | captureMismatch (index : Nat)
  | captureWorldMismatch (location : Nat)
  deriving Repr

private def removeInsertion (cutoff : Nat) (expression : Expr) : Expr :=
  expression.rename (fun index => if cutoff ≤ index then index - 1 else index)

/-- Extract only the body operand, without trusting the rest of the wrapper.
The complete snapshot expression is independently reconstructed below. -/
private def frameBody? : Expr → Option Expr
  | .letE _ (.letE _ (.letE body (.letE _ (.var 1)))) => some body
  | _ => none

private def captureIndices? : Scope → Expr → Option (List Nat)
  | [], .unit => some []
  | [_], .var index => some [index]
  | _ :: next :: rest, .pair (.var index) tail => (captureIndices? (next :: rest) tail).map (index :: ·)
  | _, _ => none

structure Template where private mk ::
  source : SourceCoreLambdaTemplates.Receipt
  creationReferenceIndex : Nat
  parameter : Ty
  result : Ty
  rawBody : Expr
  body : Expr
  carrier : Expr
  frame : SourceCoreCallablePairedFrames.Layout
  /-- Snapshot is the first value in the saved native closure environment. -/
  snapshotIndex : Nat := 0
  /-- Context reference follows the added snapshot in the saved environment. -/
  contextIndex : Nat
  /-- Manifest initialization runs under two withFrame binders and raw arg0.
  Snapshot belongs to the saved environment and is not subtracted here. -/
  manifestDepth : Nat := 3
  manifestIndices : List Nat
  references : List Nat
  nativeExact : carrier = .pair (.pair (.inLeft .word .unit)
    (.letE (.loadCell (.var creationReferenceIndex)) (.lambda parameter (LanguageResult.resultType result) body)))
    (.word source.lambda.descriptor)
  carrierExact : carrier = .pair (.pair (.inLeft .word .unit)
    (SourceCoreCallablePairedAncestry.snapshotLambda frame source.lambda.descriptor creationReferenceIndex parameter result rawBody))
    (.word source.lambda.descriptor)
  parameterExact : parameter = source.parameterType
  resultExact : result = source.resultType
  referenceExact : references = source.references.map (· + 1)
  manifestExact : references = manifestIndices.map (· - manifestDepth)
  snapshotExact : snapshotIndex = 0
  contextExact : contextIndex = creationReferenceIndex + 1

/-- Exact native body, including the lexical snapshot and restoration protocol.
The inverse scanner never supplies this equation from a manifest word alone. -/
theorem Template.bodyExact (template : Template) :
    template.body = SourceCoreCallablePairedFrames.withFrame
      (.var (template.creationReferenceIndex + 2))
      (SourceCoreCallablePairedFrames.lambdaFrame template.frame template.source.lambda.descriptor
        (.var 1) (.loadCell (.var (template.creationReferenceIndex + 2))))
      (template.rawBody.weakenAt 1) := by
  have exact := template.nativeExact.symm.trans template.carrierExact
  simpa only [SourceCoreCallablePairedAncestry.snapshotLambda, Expr.pair.injEq, Expr.letE.injEq,
    Expr.lambda.injEq, and_self, true_and, and_true] using exact

def decode {checked : Checked} (prepared : Prepared checked) (carrier : Expr) : Except Error Template := do
  let .pair (.pair identity payload) (.word descriptor) := carrier | throw .malformedSnapshot
  if identity != .inLeft .word .unit then throw .malformedSnapshot
  let .letE (.loadCell (.var referenceIndex)) (.lambda parameter (.sum .word result) body) := payload
    | throw .malformedSnapshot
  let shiftedBody ← match frameBody? body with | some body => pure body | none => throw .malformedSnapshot
  let rawBody := removeInsertion 1 (removeInsertion 0 (removeInsertion 0 shiftedBody))
  if payload != SourceCoreCallablePairedAncestry.snapshotLambda prepared.ancestry.layout.frame descriptor referenceIndex parameter result rawBody then
    throw .malformedSnapshot
  let source ← (SourceCoreLambdaTemplates.decode prepared.ancestry.templates
    (.pair (.pair identity (.lambda parameter (LanguageResult.resultType result) rawBody)) (.word descriptor)))
    |>.mapError Error.template
  let .letE (.pair (.word actual) (.pair _ captures)) _ := shiftedBody | throw .malformedSnapshot
  if actual != descriptor then throw .descriptorMismatch
  let manifestIndices ← match captureIndices? source.scope captures with
    | some indices => pure indices | none => throw .malformedSnapshot
  if manifestIndices.any (· < 4) then throw .manifestDepthMismatch
  let references := source.references.map (· + 1)
  if manifestExact : references = manifestIndices.map (· - 3) then
    if types : parameter = source.parameterType ∧ result = source.resultType then
      if carrierExact : carrier = .pair (.pair (.inLeft .word .unit)
          (SourceCoreCallablePairedAncestry.snapshotLambda prepared.ancestry.layout.frame source.lambda.descriptor referenceIndex parameter result rawBody))
          (.word source.lambda.descriptor) then
        if nativeExact : carrier = .pair (.pair (.inLeft .word .unit)
            (.letE (.loadCell (.var referenceIndex)) (.lambda parameter (LanguageResult.resultType result) body)))
            (.word source.lambda.descriptor) then
          pure ⟨source, referenceIndex, parameter, result, rawBody, body, carrier, prepared.ancestry.layout.frame, 0,
            referenceIndex + 1, 3, manifestIndices, references, nativeExact, carrierExact, types.1, types.2, rfl, manifestExact, rfl, rfl⟩
        else throw .descriptorMismatch
      else throw .descriptorMismatch
    else throw .malformedSnapshot
  else throw .manifestDepthMismatch

private def snapshotShape : Expr → Bool
  | .letE (.loadCell (.var _)) (.lambda _ _ body) => (frameBody? body).isSome
  | _ => false

mutual
  def scan {checked : Checked} (prepared : Prepared checked) : Nat → Expr → Except Error (List Template)
    | 0, _ => .error .exhausted
    | fuel + 1, expression => do
      match expression with
      | .pair (.pair identity payload) descriptor =>
        if snapshotShape payload then
          let template ← decode prepared expression
          -- Recurse through actual native binders, never the inverse-renamed
          -- synthetic source template. Child capture slots depend on them.
          pure (template :: (← scan prepared fuel template.body))
        else pure ((← scan prepared fuel (.pair identity payload)) ++ (← scan prepared fuel descriptor))
      | .letE (.loadCell (.var _)) (.lambda _ _ body) =>
        if (frameBody? body).isSome then throw .malformedSnapshot
        scan prepared fuel body
      | .unit | .bool _ | .word _ | .integer _ | .var _ => pure []
      | .lambda _ _ body => scan prepared fuel body
      | .pair left right | .apply left right | .storeCell left right | .binary _ left right | .letE left right =>
        pure ((← scan prepared fuel left) ++ (← scan prepared fuel right))
      | .first operand | .second operand | .loadCell operand | .inLeft _ operand | .inRight _ operand |
        .newCell _ operand | .construct _ operand | .unary _ operand => scan prepared fuel operand
      | .caseE first second third | .ifE first second third | .ternary _ first second third =>
        pure ((← scan prepared fuel first) ++ (← scan prepared fuel second) ++ (← scan prepared fuel third))
      | .matchData _ _ scrutinee branches => pure ((← scan prepared fuel scrutinee) ++ (← scanBranches prepared fuel branches))
  def scanBranches {checked : Checked} (prepared : Prepared checked) : Nat → List Expr → Except Error (List Template)
    | _, [] => pure []
    | 0, _ :: _ => .error .exhausted
    | fuel + 1, head :: tail => do pure ((← scan prepared fuel head) ++ (← scanBranches prepared fuel tail))
end

def globalEnvironment {checked : Checked} (prepared : Prepared checked) : Core.Environment :=
  SourceCoreLambdaTemplates.freshGlobals prepared.base.globals 1 ++
    [.cellRef prepared.ancestry.layout.frame.type 0]

private def globalSignatures {checked : Checked} (prepared : Prepared checked) : List (Ty × Ty) :=
  prepared.base.globals.map fun signature => (signature.parameterType, signature.resultType)

private def installedGlobals {checked : Checked} (prepared : Prepared checked) : List Expr :=
  prepared.secondPass.closures.zipIdx.map fun (closure, index) =>
    SourceCoreLambdaTemplates.installedTemplate index closure

structure Cache {checked : Checked} (prepared : Prepared checked) where private mk ::
  /-- Actual owned second pass, not a caller-supplied expression collection. -/
  compiled : SourceCoreCompatibleMarkedFunctions.compileClosures prepared.base
    (SourceCoreCallablePairedPrograms.markedRepresentation prepared.ancestry prepared.fuel prepared.layouts)
    prepared.fuel = .ok prepared.secondPass.closures
  groups : List (List Template)
  scanned : (prepared.secondPass.closures.zipIdx.mapM fun (closure, index) =>
    scan prepared (SourceCoreCompatibleMarkedFunctions.scanBudget (SourceCoreLambdaTemplates.installedTemplate index closure))
      (SourceCoreLambdaTemplates.installedTemplate index closure)) = .ok groups
  nativeGlobals : List (Nat × Core.Value)
  nativeGlobalsGenerated : SourceCoreCallableNativeSlots.expectedGlobals
    (globalSignatures prepared) (installedGlobals prepared) (globalEnvironment prepared) 1 = .ok nativeGlobals

def Cache.templates {checked : Checked} {prepared : Prepared checked} (cache : Cache prepared) : List Template :=
  cache.groups.flatten

def prepare {checked : Checked} (prepared : Prepared checked) : Except Error (Cache prepared) :=
  match scanned : prepared.secondPass.closures.zipIdx.mapM (fun (closure, index) =>
    scan prepared (SourceCoreCompatibleMarkedFunctions.scanBudget (SourceCoreLambdaTemplates.installedTemplate index closure))
      (SourceCoreLambdaTemplates.installedTemplate index closure)) with
  | .error error => .error error
  | .ok groups =>
    match generated : SourceCoreCallableNativeSlots.expectedGlobals (globalSignatures prepared)
        (installedGlobals prepared) (globalEnvironment prepared) 1 with
    | .error error => .error (.native error)
    | .ok slots => .ok ⟨prepared.secondPass.compiled, groups, scanned, slots, generated⟩

private def viewOwned {checked : Checked} (prepared : Prepared checked) (id target : Word) : Bool :=
  match prepared.ancestry.views.entries.find? (fun entry => decide (entry.id = id)) with
  | none => false
  | some entry => match entry.view.selectedInstance, prepared.base.callableContext with
    | some candidate, some native => entry.view.wrapsPrincipal && native.table.idAt?
        (.lambda candidate.origin.caller candidate.origin.initializer candidate.origin.substitution) == some target
    | _, _ => false

/-- Known words and exact view targets, checked against immutable receipts.
This verifies metadata ownership, not that this ancestry was actually visited. -/
def frameOwned {checked : Checked} (prepared : Prepared checked) : Frame → Bool
  | .empty => true
  | .named origin => match prepared.base.callableContext >>= (fun native => native.table.entryAt? origin) with
      | some entry => match entry.origin with | .named _ => true | _ => false
      | _ => false
  | .lambda origin parent =>
      (match prepared.base.callableContext >>= (fun native => native.table.entryAt? origin) with
        | some entry => match entry.origin with | .lambda _ _ _ => true | _ => false
        | _ => false) && frameOwned prepared parent
  | .view id target caller => viewOwned prepared id target && frameOwned prepared caller
  | .appliedView id target caller lexical =>
      viewOwned prepared id target && frameOwned prepared caller && frameOwned prepared lexical

structure Snapshot {checked : Checked} (prepared : Prepared checked) (value : Core.Value) where private mk ::
  frame : Frame
  decoded : SourceCoreCallablePairedFrameCodec.decode prepared.ancestry.layout.frame value = some frame
  exact : value = SourceCoreCallablePairedFrames.encode prepared.ancestry.layout.frame frame
  owned : frameOwned prepared frame = true

def decodeSnapshot {checked : Checked} (prepared : Prepared checked) (value : Core.Value) :
    Except Error (Snapshot prepared value) :=
  match decoded : SourceCoreCallablePairedFrameCodec.decode prepared.ancestry.layout.frame value with
  | none => .error .snapshotMalformed
  | some frame =>
      if owned : frameOwned prepared frame = true then
        .ok ⟨frame, decoded, SourceCoreCallablePairedFrameCodec.decode_sound _ value frame decoded, owned⟩
      else .error .foreignFrame

abbrev Globals {checked : Checked} (prepared : Prepared checked) (store : Store) :=
  SourceCoreCallableNativeSlots.Globals (globalSignatures prepared) (installedGlobals prepared)
    (globalEnvironment prepared) 1 store

private def checkGlobals {checked : Checked} {prepared : Prepared checked}
    (cache : Cache prepared) (store : Store) : Except Error (Globals prepared store) :=
  (SourceCoreCallableNativeSlots.checkPreparedGlobals cache.nativeGlobals cache.nativeGlobalsGenerated store).mapError Error.native

/-- Native reference slots are retained for the later source ledger join.
No source location or source binder allocation is inferred from type alone. -/
structure Capture (template : Template) (environment : Core.Environment) (world : StoreTyping) where private mk ::
  binder : Resolved.LocalId
  payloadType : Ty
  environmentIndex : Nat
  location : Nat
  sourceReference : (environmentIndex, (binder, payloadType)) ∈ template.references.zip template.source.scope
  sourceSlot : (binder, payloadType) ∈ template.source.scope
  referenceSlot : environmentIndex ∈ template.references
  exact : environment[environmentIndex]? = some (.cellRef (OptionalCell.cellType payloadType) location)
  worldExact : world[location]? = some (OptionalCell.cellType payloadType)

private def captures {template : Template} (environment : Core.Environment) (world : StoreTyping) :
    Except Error (List (Capture template environment world)) := do
  if template.source.scope.length != template.references.length then throw .manifestDepthMismatch
  (template.references.zip template.source.scope).attach.mapM fun ⟨(index, (binder, type)), member⟩ => do
    let native ← (SourceCoreCallableNativeSlots.reference environment world index type).mapError Error.native
    pure ⟨binder, type, index, native.location, member, (List.of_mem_zip member).2,
      (List.of_mem_zip member).1, native.exact, native.worldExact⟩

structure Authenticated {checked : Checked} {prepared : Prepared checked} (cache : Cache prepared)
    (world : StoreTyping) (store : Store) (value : Core.Value) where private mk ::
  template : Template
  member : template ∈ cache.templates
  environment : Core.Environment
  exact : value = .pair (.pair (.inLeft .word .unit)
    (.closure template.parameter (LanguageResult.resultType template.result) template.body environment))
    (.word template.source.lambda.descriptor)
  stored : RuntimeStoreHasTypes world store prepared.layouts.definitions
  typed : RuntimeValueHasType world value (CallableContract.functionType template.parameter template.result) prepared.layouts.definitions
  globals : Globals prepared store
  capturedGlobals : environment.drop (environment.length - (globalEnvironment prepared).length) = globalEnvironment prepared
  snapshotValue : Core.Value
  snapshotSlot : environment[template.snapshotIndex]? = some snapshotValue
  snapshot : Snapshot prepared snapshotValue
  contextSlot : environment[template.contextIndex]? = some (.cellRef prepared.ancestry.layout.frame.type 0)
  contextWorld : world[0]? = some prepared.ancestry.layout.frame.type
  contextValue : Core.Value
  contextRead : store.read? 0 = some contextValue
  current : Snapshot prepared contextValue
  sourceCaptures : List (Capture template environment world)
  capturesExact : sourceCaptures.map (fun capture => (capture.environmentIndex, (capture.binder, capture.payloadType))) =
    template.references.zip template.source.scope
  capturesComplete : sourceCaptures.length = template.source.scope.length

def authenticate {checked : Checked} {prepared : Prepared checked} (cache : Cache prepared)
    {world : StoreTyping} {store : Store} (stored : RuntimeStoreHasTypes world store prepared.layouts.definitions)
    (value : Core.Value) (parameter result : Ty)
    (typed : RuntimeValueHasType world value (CallableContract.functionType parameter result) prepared.layouts.definitions) :
    Except Error (Authenticated cache world store value) := do
  let globals ← checkGlobals cache store
  let .pair (.pair (.inLeft .word .unit) (.closure _ _ body environment)) (.word descriptor) := value | throw .closureMismatch
  let selected ← match cache.templates.attach.find? (fun item => decide
      (item.val.source.lambda.descriptor = descriptor ∧ item.val.body = body ∧
        item.val.parameter = parameter ∧ item.val.result = result)) with
    | some item => pure item | none => throw .closureMismatch
  let template := selected.val
  if types : template.parameter = parameter ∧ template.result = result then
    if exact : value = .pair (.pair (.inLeft .word .unit)
        (.closure template.parameter (LanguageResult.resultType template.result) template.body environment))
        (.word template.source.lambda.descriptor) then
      if capturedGlobals : environment.drop (environment.length - (globalEnvironment prepared).length) = globalEnvironment prepared then
        let snapshotValue ← match slot : environment[template.snapshotIndex]? with
          | none => throw .snapshotMissing
          | some value => pure (⟨value, slot⟩ : {value // environment[template.snapshotIndex]? = some value})
        let snapshot ← decodeSnapshot prepared snapshotValue.val
        if contextSlot : environment[template.contextIndex]? = some (.cellRef prepared.ancestry.layout.frame.type 0) then
          if contextWorld : world[0]? = some prepared.ancestry.layout.frame.type then
            let contextValue ← match read : store.read? 0 with
              | none => throw .contextValueMalformed
              | some value => pure (⟨value, read⟩ : {value // store.read? 0 = some value})
            let current ← decodeSnapshot prepared contextValue.val
            let sourceCaptures ← captures (template := template) environment world
            if capturesExact : sourceCaptures.map (fun capture => (capture.environmentIndex, (capture.binder, capture.payloadType))) =
                template.references.zip template.source.scope then
              if complete : sourceCaptures.length = template.source.scope.length then
                pure ⟨template, selected.property, environment, exact, stored,
                by simpa only [types.1, types.2] using typed,
                globals, capturedGlobals, snapshotValue.val, snapshotValue.property, snapshot,
                contextSlot, contextWorld, contextValue.val, contextValue.property, current, sourceCaptures, capturesExact, complete⟩
              else throw .manifestDepthMismatch
            else throw .manifestDepthMismatch
          else throw .contextWorldMismatch
        else throw .contextReferenceMismatch
      else throw .contextReferenceMismatch
    else throw .closureMismatch
  else throw .closureMismatch

end Solcore.Frontend.SourceCoreCallablePairedTemplates
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallablePairedCaptures
/-! Captured native references are joined to the actual allocation ledger by
physical Core location first. Binder identity, native payload type, owner,
complete native allocated context and contextual binder metadata are then
checked. Source metadata substitutions remain separate from these native
context checks; the source principal can have a different active context.
Repeated recursive allocations of the same binder remain different rows.

A produced receipt retains the owning completion and an exact successful
observation. Subvalue paths cover result data only, never closure environments.
The join preserves ordered source locations after the opaque prefix. It does
not reconstruct source lambda bodies or derive ancestry history from words.
-/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallablePairedCaptures
open SourceInference Core
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Prepared := SourceCoreCallablePairedPrograms.Prepared
abbrev Cache {checked : Checked} (prepared : Prepared checked) := SourceCoreCallablePairedTemplates.Cache prepared
abbrev Template := SourceCoreCallablePairedTemplates.Template
abbrev Capture := SourceCoreCallablePairedTemplates.Capture
abbrev Authenticated {checked : Checked} {prepared : Prepared checked} (cache : Cache prepared)
    (world : StoreTyping) (store : Store) (value : Value) := SourceCoreCallablePairedTemplates.Authenticated cache world store value
abbrev Completion {checked : Checked} (prepared : Prepared checked) := SourceCoreCallablePairedPrograms.Completion prepared
abbrev SourceHeap := SourceCoreAllocationLedger.SourceHeap
abbrev SourceEnvironment := SourceCoreAllocationLedger.SourceEnvironment
abbrev TypedLedger := SourceCoreAllocationLedger.TypedLedger
abbrev Row := SourceCoreAllocationLedger.Row

abbrev Subvalue (value : Value) := SourceCoreCallableNativeSlots.Subvalue value

structure Produced {checked : Checked} {prepared : Prepared checked} (cache : Cache prepared)
    (completion : Completion prepared) (world : StoreTyping) (store : Store) (value : Value) where private mk ::
  authenticated : Authenticated cache world store value
  result : Value
  observation : completion.result.native.observation = .succeeded result store
  subvalue : Subvalue value result

def Produced.of_success {checked : Checked} {prepared : Prepared checked} {cache : Cache prepared}
    {completion : Completion prepared} {world : StoreTyping} {store : Store} {value result : Value}
    (authenticated : Authenticated cache world store value)
    (observation : completion.result.native.observation = .succeeded result store)
    (subvalue : Subvalue value result) : Produced cache completion world store value :=
  ⟨authenticated, result, observation, subvalue⟩

/-- Composition can update older replacements; a literal list prefix would
incorrectly reject a completed flexible parent substitution. Domain order and
full composition, including every binding, are checked instead. -/
def ContextExtends (allocated selected : TypeSystem.Substitution) : Prop :=
  allocated.domain.IsPrefix selected.domain ∧ selected.compose allocated = selected
instance (allocated selected : TypeSystem.Substitution) : Decidable (ContextExtends allocated selected) :=
  inferInstanceAs (Decidable (_ ∧ _))

inductive Error where
  | unknownLocation (location : Nat)
  | binderMismatch (location : Nat) (expected actual : Resolved.LocalId)
  | payloadMismatch (location : Nat) (expected actual : Ty)
  | ownerMismatch (location : Nat)
  | contextMismatch (location : Nat)
  | unknownAllocatedContext (location : Nat)
  | allocatedBinderMismatch (location : Nat)
  | unknownExpectedBinder (id : Resolved.LocalId)
  | contextualBinderMismatch (location : Nat)
  deriving Repr

structure Slot {checked : Checked} {prepared : Prepared checked} {template : Template}
    {environment : Environment} {world : StoreTyping} {store : Store} {initial : SourceHeap}
    (ledger : TypedLedger prepared.layouts initial world store) (capture : Capture template environment world) where private mk ::
  ordinal : Fin ledger.ledger.rows.length
  locationExact : (ledger.ledger.rows[ordinal]).coreLocation = capture.location
  binderExact : (ledger.ledger.rows[ordinal]).entry.key.binder.id = capture.binder
  payloadExact : (ledger.ledger.rows[ordinal]).entry.key.payloadType = capture.payloadType
  ownerExact : (ledger.ledger.rows[ordinal]).entry.key.owner = template.source.lambda.owner
  activeExtends : ContextExtends (ledger.ledger.rows[ordinal]).entry.key.active template.source.lambda.active
  allocated : SourceCoreAllocationContexts.Certified prepared.base.plan prepared.base.contexts
  allocatedMember : allocated ∈ prepared.contexts.rows
  allocatedOwner : allocated.context.owner = (ledger.ledger.rows[ordinal]).entry.key.owner
  allocatedActive : allocated.context.active = (ledger.ledger.rows[ordinal]).entry.key.active
  allocatedBinder : (ledger.ledger.rows[ordinal]).entry.key.binder ∈ allocated.context.binders
  expected : SourceCoreAllocationCodebook.IndexedBinding
  expectedFound : template.source.lambda.context.bindingAt? capture.binder = some expected
  expectedIdentity : expected.binding.binder.id = capture.binder
  contextualBinder : (ledger.ledger.rows[ordinal]).entry.key.binder.applySubstitution template.source.lambda.active = expected.binding.binder

def Slot.row {checked : Checked} {prepared : Prepared checked} {template : Template}
    {environment : Environment} {world : StoreTyping} {store : Store} {initial : SourceHeap}
    {ledger : TypedLedger prepared.layouts initial world store} {capture : Capture template environment world}
    (slot : Slot ledger capture) : Row prepared.layouts store := ledger.ledger.rows[slot.ordinal]

def Slot.sourceLocation {checked : Checked} {prepared : Prepared checked} {template : Template}
    {environment : Environment} {world : StoreTyping} {store : Store} {initial : SourceHeap}
    {ledger : TypedLedger prepared.layouts initial world store} {capture : Capture template environment world}
    (slot : Slot ledger capture) : SourceTypedRuntime.Location := slot.row.sourceLocation

theorem Slot.prefixOffset {checked : Checked} {prepared : Prepared checked} {template : Template}
    {environment : Environment} {world : StoreTyping} {store : Store} {initial : SourceHeap}
    {ledger : TypedLedger prepared.layouts initial world store} {capture : Capture template environment world}
    (slot : Slot ledger capture) : slot.sourceLocation.index = initial.length + slot.ordinal.val :=
  ledger.ledger.sourceLocation_exact slot.ordinal

theorem Slot.nativeReference {checked : Checked} {prepared : Prepared checked} {template : Template}
    {environment : Environment} {world : StoreTyping} {store : Store} {initial : SourceHeap}
    {ledger : TypedLedger prepared.layouts initial world store} {capture : Capture template environment world}
    (slot : Slot ledger capture) :
    SourceCoreAllocationLedger.Reference ledger.ledger.locations capture.payloadType
      (.cellRef (OptionalCell.cellType capture.payloadType) capture.location) slot.sourceLocation := by
  rw [← slot.locationExact]
  apply SourceCoreAllocationLedger.Reference.intro (entry := slot.row.location)
  · exact List.mem_map_of_mem (by exact List.getElem_mem slot.ordinal.isLt)
  · exact slot.payloadExact

/-- The full contextual source binder comes from the actual cached allocation
inventory, rather than from a native reference's Core type. -/
theorem Slot.binderOrigin {checked : Checked} {prepared : Prepared checked} {template : Template}
    {environment : Environment} {world : StoreTyping} {store : Store} {initial : SourceHeap}
    {ledger : TypedLedger prepared.layouts initial world store} {capture : Capture template environment world}
    (slot : Slot ledger capture) :
    SourceCoreAllocationContexts.BinderOrigin slot.allocated.context.source slot.row.entry.key.binder :=
  slot.allocated.binder_origin slot.allocatedBinder

private theorem ledger_core_injective {checked : Checked} {prepared : Prepared checked}
    {world : StoreTyping} {store : Store} {initial : SourceHeap}
    (ledger : TypedLedger prepared.layouts initial world store) :
    Function.Injective (fun ordinal : Fin ledger.ledger.rows.length => (ledger.ledger.rows[ordinal]).coreLocation) := by
  have ordered : ∀ left right : Fin ledger.ledger.rows.length, left.val < right.val →
      (ledger.ledger.rows[left]).coreLocation < (ledger.ledger.rows[right]).coreLocation := by
    intro left right before
    have member : ledger.ledger.rows[left] ∈ ledger.ledger.rows.take right.val := by
      rw [List.mem_take_iff_getElem]
      exact ⟨left.val, by omega, rfl⟩
    have previous := List.all_eq_true.mp (ledger.ledger.aligned right).2.2 _ member
    have previous := of_decide_eq_true previous
    simp only [SourceCoreAllocationLedger.Row.coreLocation] at previous ⊢
    exact Nat.lt_trans previous (Nat.lt_succ_self _)
  intro left right same
  change (ledger.ledger.rows[left]).coreLocation = (ledger.ledger.rows[right]).coreLocation at same
  apply Fin.ext
  rcases Nat.lt_trichotomy left.val right.val with before | sameIndex | after
  · have tooSmall := ordered left right before
    rw [same] at tooSmall
    exact False.elim (Nat.lt_irrefl _ tooSmall)
  · exact sameIndex
  · have tooSmall := ordered right left after
    rw [same] at tooSmall
    exact False.elim (Nat.lt_irrefl _ tooSmall)

/-- Aliasing is determined by physical location, even when binder IDs recur. -/
theorem Slot.alias {checked : Checked} {prepared : Prepared checked}
    {leftTemplate rightTemplate : Template} {leftEnvironment rightEnvironment : Environment}
    {world : StoreTyping} {store : Store} {initial : SourceHeap}
    {ledger : TypedLedger prepared.layouts initial world store}
    {left : Capture leftTemplate leftEnvironment world} {right : Capture rightTemplate rightEnvironment world}
    (leftSlot : Slot ledger left) (rightSlot : Slot ledger right)
    (same : left.location = right.location) : leftSlot.sourceLocation = rightSlot.sourceLocation := by
  have ordinals : leftSlot.ordinal = rightSlot.ordinal :=
    ledger_core_injective ledger (leftSlot.locationExact.trans (same.trans rightSlot.locationExact.symm))
  exact congrArg (fun (ordinal : Fin ledger.ledger.rows.length) =>
    (ledger.ledger.rows[ordinal]).sourceLocation) ordinals

/-- Distinct native source cells remain distinct after prefix reindexing. -/
theorem Slot.alias_iff {checked : Checked} {prepared : Prepared checked}
    {leftTemplate rightTemplate : Template} {leftEnvironment rightEnvironment : Environment}
    {world : StoreTyping} {store : Store} {initial : SourceHeap}
    {ledger : TypedLedger prepared.layouts initial world store}
    {left : Capture leftTemplate leftEnvironment world} {right : Capture rightTemplate rightEnvironment world}
    (leftSlot : Slot ledger left) (rightSlot : Slot ledger right) :
    leftSlot.sourceLocation = rightSlot.sourceLocation ↔ left.location = right.location := by
  constructor
  · intro same
    have ordinals : leftSlot.ordinal = rightSlot.ordinal := ledger.ledger.sourceLocation_injective same
    exact leftSlot.locationExact.symm.trans
      ((congrArg (fun (ordinal : Fin ledger.ledger.rows.length) =>
        (ledger.ledger.rows[ordinal]).coreLocation) ordinals).trans rightSlot.locationExact)
  · exact leftSlot.alias rightSlot


private def joinSlot {checked : Checked} {prepared : Prepared checked} {template : Template}
    {environment : Environment} {world : StoreTyping} {store : Store} {initial : SourceHeap}
    (ledger : TypedLedger prepared.layouts initial world store) (capture : Capture template environment world) :
    Except Error (Slot ledger capture) := do
  let ordinal ← match (List.finRange ledger.ledger.rows.length).find? (fun ordinal =>
      decide ((ledger.ledger.rows[ordinal]).coreLocation = capture.location)) with
    | none => throw (.unknownLocation capture.location)
    | some ordinal => pure ordinal
  let row := ledger.ledger.rows[ordinal]
  if locationExact : row.coreLocation = capture.location then
    if binderExact : row.entry.key.binder.id = capture.binder then
      if payloadExact : row.entry.key.payloadType = capture.payloadType then
        if ownerExact : row.entry.key.owner = template.source.lambda.owner then
          if activeExtends : ContextExtends row.entry.key.active template.source.lambda.active then
            let allocated ← match prepared.contexts.rows.attach.find? (fun context => decide
                (context.val.context.owner = row.entry.key.owner ∧ context.val.context.active = row.entry.key.active)) with
              | none => throw (.unknownAllocatedContext capture.location)
              | some context => pure context
            if allocatedExact : allocated.val.context.owner = row.entry.key.owner ∧ allocated.val.context.active = row.entry.key.active then
              if allocatedBinder : row.entry.key.binder ∈ allocated.val.context.binders then
                match expectedFound : template.source.lambda.context.bindingAt? capture.binder with
                | none => throw (.unknownExpectedBinder capture.binder)
                | some expected =>
                  if expectedIdentity : expected.binding.binder.id = capture.binder then
                    if contextualBinder : row.entry.key.binder.applySubstitution template.source.lambda.active = expected.binding.binder then
                      pure ⟨ordinal, locationExact, binderExact, payloadExact, ownerExact, activeExtends,
                        allocated.val, allocated.property, allocatedExact.1, allocatedExact.2, allocatedBinder,
                        expected, expectedFound, expectedIdentity, contextualBinder⟩
                    else throw (.contextualBinderMismatch capture.location)
                  else throw (.unknownExpectedBinder capture.binder)
              else throw (.allocatedBinderMismatch capture.location)
            else throw (.unknownAllocatedContext capture.location)
          else throw (.contextMismatch capture.location)
        else throw (.ownerMismatch capture.location)
      else throw (.payloadMismatch capture.location capture.payloadType row.entry.key.payloadType)
    else throw (.binderMismatch capture.location capture.binder row.entry.key.binder.id)
  else throw (.unknownLocation capture.location)

inductive CaptureSourceEnv {checked : Checked} {prepared : Prepared checked} {template : Template}
    {environment : Environment} {world : StoreTyping} {store : Store} {initial : SourceHeap}
    (ledger : TypedLedger prepared.layouts initial world store) :
    List (Capture template environment world) → SourceEnvironment → Prop where
  | nil : CaptureSourceEnv ledger [] []
  | cons {capture : Capture template environment world} {tail : List (Capture template environment world)}
      {sourceTail : SourceEnvironment} (slot : Slot ledger capture)
      (following : CaptureSourceEnv ledger tail sourceTail) :
      CaptureSourceEnv ledger (capture :: tail) ((capture.binder, slot.sourceLocation) :: sourceTail)

namespace CaptureSourceEnv
variable {checked : Checked} {prepared : Prepared checked} {template : Template}
  {environment : Environment} {world : StoreTyping} {store : Store} {initial : SourceHeap}
  {ledger : TypedLedger prepared.layouts initial world store}
  {captures : List (Capture template environment world)} {source : SourceEnvironment}

theorem length (related : CaptureSourceEnv ledger captures source) : source.length = captures.length := by
  induction related with
  | nil => rfl
  | cons slot following ih => simp only [List.length_cons, ih]

theorem binders (related : CaptureSourceEnv ledger captures source) :
    source.map Prod.fst = captures.map (·.binder) := by
  induction related with
  | nil => rfl
  | cons slot following ih => simp only [List.map_cons, ih]

theorem lookup (related : CaptureSourceEnv ledger captures source) {index : Nat} {binder : Resolved.LocalId}
    {location : SourceTypedRuntime.Location} (found : source[index]? = some (binder, location)) :
    ∃ capture, captures[index]? = some capture ∧ capture.binder = binder ∧
      ∃ slot : Slot ledger capture, slot.sourceLocation = location := by
  induction related generalizing index with
  | nil => simp at found
  | cons slot following ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at found
      exact ⟨_, rfl, found.1, slot, found.2⟩
    | succ index =>
      obtain ⟨capture, captured, binderExact, slot, located⟩ := ih (by simpa using found)
      exact ⟨capture, by simpa using captured, binderExact, slot, located⟩

end CaptureSourceEnv

private structure EnvironmentReceipt {checked : Checked} {prepared : Prepared checked} {template : Template}
    {environment : Environment} {world : StoreTyping} {store : Store} {initial : SourceHeap}
    (ledger : TypedLedger prepared.layouts initial world store) (captures : List (Capture template environment world)) where
  source : SourceEnvironment
  related : CaptureSourceEnv ledger captures source

private def joinEnvironment {checked : Checked} {prepared : Prepared checked} {template : Template}
    {environment : Environment} {world : StoreTyping} {store : Store} {initial : SourceHeap}
    (ledger : TypedLedger prepared.layouts initial world store) :
    (captures : List (Capture template environment world)) → Except Error (EnvironmentReceipt ledger captures)
  | [] => .ok ⟨[], .nil⟩
  | capture :: tail => do
    let slot ← joinSlot ledger capture
    let following ← joinEnvironment ledger tail
    pure ⟨(capture.binder, slot.sourceLocation) :: following.source, .cons slot following.related⟩

/-- A metadata/location relation alone. Execution provenance is supplied by
`Produced` or `Stored`, and is deliberately not inferred from this receipt. -/
structure Captured {checked : Checked} {prepared : Prepared checked} {cache : Cache prepared}
    {world : StoreTyping} {store : Store} {value : Value}
    (authenticated : Authenticated cache world store value) {initial : SourceHeap}
    (ledger : TypedLedger prepared.layouts initial world store) where private mk ::
  environment : SourceEnvironment
  related : CaptureSourceEnv ledger authenticated.sourceCaptures environment

def joinAuthenticated {checked : Checked} {prepared : Prepared checked} {cache : Cache prepared}
    {world : StoreTyping} {store : Store} {value : Value}
    (authenticated : Authenticated cache world store value) {initial : SourceHeap}
    (ledger : TypedLedger prepared.layouts initial world store) : Except Error (Captured authenticated ledger) := do
  let receipt ← joinEnvironment ledger authenticated.sourceCaptures
  pure ⟨receipt.source, receipt.related⟩

abbrev Receipt {checked : Checked} {prepared : Prepared checked} {cache : Cache prepared}
    {completion : Completion prepared} {world : StoreTyping} {store : Store} {value : Value}
    (produced : Produced cache completion world store value) {initial : SourceHeap}
    (ledger : TypedLedger prepared.layouts initial world store) := Captured produced.authenticated ledger

def join {checked : Checked} {prepared : Prepared checked} {cache : Cache prepared}
    {completion : Completion prepared} {world : StoreTyping} {store : Store} {value : Value}
    (produced : Produced cache completion world store value) {initial : SourceHeap}
    (ledger : TypedLedger prepared.layouts initial world store) : Except Error (Receipt produced ledger) :=
  joinAuthenticated produced.authenticated ledger

/-- Heap payload provenance also covers failed and suspended invocations.
Only source ledger payloads are traversed, never an arbitrary closure's saved
Core environment or a compiler-only administrative cell. -/
structure Stored {checked : Checked} {prepared : Prepared checked} (cache : Cache prepared)
    (completion : Completion prepared) {world : StoreTyping} {store : Store} (value : Value)
    {initial : SourceHeap} (ledger : TypedLedger prepared.layouts initial world store) where private mk ::
  authenticated : Authenticated cache world store value
  observation : SourceCoreCallablePairedLedger.store completion = store
  ordinal : Fin ledger.ledger.rows.length
  payload : Value
  payloadFound : (ledger.ledger.rows[ordinal]).payload = some payload
  subvalue : Subvalue value payload

def Stored.of_payload {checked : Checked} {prepared : Prepared checked} {cache : Cache prepared}
    {completion : Completion prepared} {world : StoreTyping} {store : Store} {value payload : Value}
    {initial : SourceHeap} {ledger : TypedLedger prepared.layouts initial world store}
    (authenticated : Authenticated cache world store value)
    (observation : SourceCoreCallablePairedLedger.store completion = store)
    (ordinal : Fin ledger.ledger.rows.length)
    (payloadFound : (ledger.ledger.rows[ordinal]).payload = some payload)
    (subvalue : Subvalue value payload) : Stored cache completion value ledger :=
  ⟨authenticated, observation, ordinal, payload, payloadFound, subvalue⟩

def joinStored {checked : Checked} {prepared : Prepared checked} {cache : Cache prepared}
    {completion : Completion prepared} {world : StoreTyping} {store : Store} {value : Value}
    {initial : SourceHeap} {ledger : TypedLedger prepared.layouts initial world store}
    (stored : Stored cache completion value ledger) : Except Error (Captured stored.authenticated ledger) :=
  joinAuthenticated stored.authenticated ledger

namespace Captured
variable {checked : Checked} {prepared : Prepared checked} {cache : Cache prepared}
  {world : StoreTyping} {store : Store} {value : Value}
  {authenticated : Authenticated cache world store value} {initial : SourceHeap}
  {ledger : TypedLedger prepared.layouts initial world store}

theorem length (receipt : Captured authenticated ledger) :
    receipt.environment.length = authenticated.template.source.scope.length :=
  receipt.related.length.trans authenticated.capturesComplete

theorem binders (receipt : Captured authenticated ledger) :
    receipt.environment.map Prod.fst = authenticated.template.source.scope.map Prod.fst := by
  have lengths := congrArg List.length authenticated.capturesExact
  simp only [List.length_map, List.length_zip, authenticated.capturesComplete] at lengths
  have enough : authenticated.template.source.scope.length ≤ authenticated.template.references.length := by omega
  have exact := congrArg (List.map (fun entry : Nat × (Resolved.LocalId × Ty) => entry.2.1))
    authenticated.capturesExact
  have captureOrder : authenticated.sourceCaptures.map (·.binder) =
      authenticated.template.source.scope.map Prod.fst := by
    have zipped : (authenticated.template.references.zip authenticated.template.source.scope).map
        (fun entry => entry.2.1) = authenticated.template.source.scope.map Prod.fst := by
      simpa only [List.map_map, Function.comp_def] using congrArg (List.map Prod.fst) (List.map_snd_zip enough)
    simpa only [List.map_map, Function.comp_def] using exact.trans zipped
  exact receipt.related.binders.trans captureOrder

theorem lookup (receipt : Captured authenticated ledger) {index : Nat} {binder : Resolved.LocalId}
    {location : SourceTypedRuntime.Location} (found : receipt.environment[index]? = some (binder, location)) :
    ∃ capture, authenticated.sourceCaptures[index]? = some capture ∧ capture.binder = binder ∧
      ∃ slot : Slot ledger capture, slot.sourceLocation = location := receipt.related.lookup found

theorem outsidePrefix (receipt : Captured authenticated ledger) {index : Nat} {binder : Resolved.LocalId}
    {location : SourceTypedRuntime.Location} (found : receipt.environment[index]? = some (binder, location)) :
    initial.length ≤ location.index := by
  obtain ⟨_, _, _, slot, same⟩ := receipt.lookup found
  rw [← same, slot.prefixOffset]
  omega

end Captured
end Solcore.Frontend.SourceCoreCallablePairedCaptures
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallablePairedHeaders
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

/-- A read wrapper retains its original principal binder and initializer.
Its native target can have a cumulative context different from this lexical
header, so selection uses the cached lexical position and source identities. -/
def Prepared.principalBinderAt? {checked : Checked} {base : Base checked} {graph : Graph base}
    (prepared : Prepared graph) (position : Nat) (binder : Resolved.LocalId) (initializer : ExpressionId) :
    Option (PrincipalHeader graph prepared.principals) :=
  prepared.principalHeaders.find? fun header => decide (header.position.val = position ∧
    header.principal.principal.binder.id = binder ∧ header.declaration.initializer = initializer)

theorem PrincipalHeader.raw_source {checked : Checked} {base : Base checked} {graph : Graph base} {principals : Principals base}
    (header : PrincipalHeader graph principals) (captured : SourceTypedRuntime.Environment) :
    header.sourceValue captured = .closure header.parameters header.resultType header.body header.state.metadata.source
      header.state.metadata.owner captured header.principal.context.evidence := rfl

end Solcore.Frontend.SourceCoreCallablePairedHeaders
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallablePairedPrincipalAllocations
/-! Restore a raw principal from its actual allocation snapshot and cached
paired source header. The generic allocation row supplies the ordered source
captures and its physical location. The native bundle can be Unit.

The receipt keeps actual store adjacency, paired-table lookup, cached header
selection and the complete compiler principal key. A typed but fabricated
frame is not execution history; emitted-frame provenance remains a separate
artifact obligation. No source body is traversed or evaluated by restoration.
-/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallablePairedPrincipalAllocations
open SourceInference
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Program := SourceCoreCallablePairedPrograms.Prepared
abbrev Graph := @SourceCoreCallableAncestryPairedPreparation.Prepared
abbrev Headers := @SourceCoreCallablePairedHeaders.Prepared
abbrev Cell := SourceTypedRuntime.Cell

inductive Error where
  | absentPrincipal (binder : Resolved.LocalId)
  | snapshot (error : SourceCoreCallablePairedAllocationFrames.Error)
  | frameUnavailable (binder : Resolved.LocalId)
  | headerUnavailable (position : Nat) (binder : Resolved.LocalId)
  deriving Repr

structure Restored {checked : Checked} {program : Program checked} {graph : Graph program.base}
    (headers : Headers graph) {store : Core.Store}
    (row : SourceCoreAllocationLedger.Row program.layouts store) where private mk ::
  payload : Core.Value
  present : row.payload = some payload
  snapshot : SourceCoreCallablePairedAllocationFrames.Snapshot program.ancestry.layout.frame row
  position : Nat
  lookup : graph.table.lookupIndex? snapshot.frame = some (some position)
  header : SourceCoreCallablePairedHeaders.PrincipalHeader graph headers.principals
  selected : headers.principalAt? position row.entry.key = some header
  cell : Cell
  exact : cell = header.cell row.environment

def restore {checked : Checked} {program : Program checked} {graph : Graph program.base}
    (headers : Headers graph) {store : Core.Store}
    (row : SourceCoreAllocationLedger.Row program.layouts store) : Except Error (Restored headers row) := do
  match present : row.payload with
  | none => throw (.absentPrincipal row.entry.key.binder.id)
  | some payload =>
    let snapshot ← (SourceCoreCallablePairedAllocationFrames.snapshot program.ancestry.layout.frame row).mapError Error.snapshot
    match lookup : graph.table.lookupIndex? snapshot.frame with
    | some (some position) =>
      match selected : headers.principalAt? position row.entry.key with
      | none => throw (.headerUnavailable position row.entry.key.binder.id)
      | some header => pure ⟨payload, present, snapshot, position, lookup, header, selected, header.cell row.environment, rfl⟩
    | _ => throw (.frameUnavailable row.entry.key.binder.id)

theorem Restored.position_exact {checked : Checked} {program : Program checked} {graph : Graph program.base}
    {headers : Headers graph} {store : Core.Store} {row : SourceCoreAllocationLedger.Row program.layouts store}
    (restored : Restored headers row) : restored.header.position.val = restored.position := by
  have selected := restored.selected
  unfold SourceCoreCallablePairedHeaders.Prepared.principalAt? at selected
  have tested := List.find?_some selected
  exact (of_decide_eq_true tested).1

theorem Restored.native_key {checked : Checked} {program : Program checked} {graph : Graph program.base}
    {headers : Headers graph} {store : Core.Store} {row : SourceCoreAllocationLedger.Row program.layouts store}
    (restored : Restored headers row) : restored.header.principal.matchesLayout row.entry.key := by
  have selected := restored.selected
  unfold SourceCoreCallablePairedHeaders.Prepared.principalAt? at selected
  have tested := List.find?_some selected
  exact (of_decide_eq_true tested).2

theorem Restored.raw_type {checked : Checked} {program : Program checked} {graph : Graph program.base}
    {headers : Headers graph} {store : Core.Store} {row : SourceCoreAllocationLedger.Row program.layouts store}
    (restored : Restored headers row) : restored.cell.type = restored.header.declaration.binder.scheme.body := by
  rw [restored.exact]
  rfl

theorem Restored.original_closure {checked : Checked} {program : Program checked} {graph : Graph program.base}
    {headers : Headers graph} {store : Core.Store} {row : SourceCoreAllocationLedger.Row program.layouts store}
    (restored : Restored headers row) :
    restored.cell.value = some (.closure restored.header.parameters restored.header.resultType restored.header.body
      restored.header.state.metadata.source restored.header.state.metadata.owner row.environment restored.header.principal.context.evidence) := by
  rw [restored.exact]
  rfl

theorem Restored.capture_order {checked : Checked} {program : Program checked} {graph : Graph program.base}
    {headers : Headers graph} {store : Core.Store} {row : SourceCoreAllocationLedger.Row program.layouts store}
    (_restored : Restored headers row) :
    row.environment.map Prod.fst = row.entry.key.scope.map Prod.fst := row.captured.binders_exact

end Solcore.Frontend.SourceCoreCallablePairedPrincipalAllocations
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallablePairedReadViews
/-! Exact emitted generalized-read wrappers. The wrapper's original carrier
is retained in saved slot one, after the exact read-time caller snapshot,
with the same anonymous identity and contract ID. It is authenticated against actual snapshot templates before its captures
are joined to source allocation rows.

The cached read's parent/principal, own substitution/witnesses and cumulative
native instance remain separate. This unit never collapses an instantiated
source value to a ground closure. Dynamic principal headers must additionally be selected from the lexical
creation snapshot. Own substitutions and witnesses must come from the
separate read caller snapshot, through the prepared paired recipe table.
-/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallablePairedReadViews
open SourceInference Core
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Prepared := SourceCoreCallablePairedPrograms.Prepared
abbrev Templates {checked : Checked} (prepared : Prepared checked) := SourceCoreCallablePairedTemplates.Cache prepared
abbrev Instance := SourceCoreLocalPolymorphism.Instance
abbrev Completion {checked : Checked} (prepared : Prepared checked) := SourceCoreCallablePairedPrograms.Completion prepared
abbrev SourceHeap := SourceCoreAllocationLedger.SourceHeap
abbrev TypedLedger := SourceCoreAllocationLedger.TypedLedger

inductive Error where
  | exhausted
  | malformedWrapper
  | unknownView (id : Word)
  | monomorphicView (id : Word)
  | missingInstance (id : Word)
  | missingDescriptor (id : Word)
  | foreignOrigin (id : Word)
  | typeMismatch
  | closureMismatch
  | originalCarrierMismatch
  | contextReferenceMismatch
  | underlying (error : SourceCoreCallablePairedTemplates.Error)
  | caller (error : SourceCoreCallablePairedTemplates.Error)
  | captures (error : SourceCoreCallablePairedCaptures.Error)
  deriving Repr

private def bodyHeader? : Expr → Option (Nat × ConstructorId × Word × Word)
  | .letE (.loadCell (.var index)) (.letE (.storeCell _
      (.construct constructor (.pair (.word id) (.pair (.word target) _)))) _) =>
    some (index, constructor, id, target)
  | _ => none

structure Template {checked : Checked} (prepared : Prepared checked) where private mk ::
  entry : SourceCoreCallableViews.Entry prepared.base.sourceProgram prepared.base.plan
  found : prepared.ancestry.views.entryAt? entry.id = some entry
  wrapsPrincipal : entry.view.wrapsPrincipal = true
  candidate : Instance
  selected : entry.view.selectedInstance = some candidate
  target : Word
  targetFound : (prepared.base.callableContext >>= fun native => native.table.idAt?
    (.lambda candidate.origin.caller candidate.origin.initializer candidate.origin.substitution)) = some target
  parameter : Ty
  result : Ty
  parameterExact : parameter = candidate.parameterType
  resultExact : result = candidate.resultType
  /-- Index before the successful-read binder; installed syntax can rename it. -/
  referenceIndex : Nat
  body : Expr
  carrier : Expr
  bodyExact : body = SourceCoreCallablePairedAncestry.viewBody prepared.ancestry.layout.frame entry.id target referenceIndex
  carrierExact : carrier = SourceCoreCallablePairedAncestry.viewRepack prepared.ancestry.layout.frame
    parameter result entry.id target referenceIndex

def decode {checked : Checked} (prepared : Prepared checked) (carrier : Expr) : Except Error (Template prepared) := do
  let .pair (.pair _ (.lambda parameter (.sum .word result) body)) _ := carrier | throw .malformedWrapper
  let (index, constructor, id, target) ← match bodyHeader? body with
    | some header => pure header | none => throw .malformedWrapper
  if index < 3 || constructor != prepared.ancestry.layout.frame.view then throw .malformedWrapper
  match found : prepared.ancestry.views.entryAt? id with
  | none => throw (.unknownView id)
  | some entry =>
    have entryId : entry.id = id := by
      have matched := found
      unfold SourceCoreCallableViews.Table.entryAt? at matched
      have selected : decide (entry.id = id) = true :=
        List.find?_some (p := fun (candidate : SourceCoreCallableViews.Entry prepared.base.sourceProgram prepared.base.plan) =>
          decide (candidate.id = id)) matched
      exact of_decide_eq_true selected
    have ownedFound : prepared.ancestry.views.entryAt? entry.id = some entry := by simpa only [entryId] using found
    if wraps : entry.view.wrapsPrincipal = true then
      match selected : entry.view.selectedInstance with
      | none => throw (.missingInstance id)
      | some candidate =>
        if targetFound : (prepared.base.callableContext >>= fun native => native.table.idAt?
            (.lambda candidate.origin.caller candidate.origin.initializer candidate.origin.substitution)) = some target then
          if types : parameter = candidate.parameterType ∧ result = candidate.resultType then
            let referenceIndex := index - 3
            if bodyExact : body = SourceCoreCallablePairedAncestry.viewBody prepared.ancestry.layout.frame entry.id target referenceIndex then
              if carrierExact : carrier = SourceCoreCallablePairedAncestry.viewRepack prepared.ancestry.layout.frame parameter result entry.id target referenceIndex then
                pure ⟨entry, ownedFound, wraps, candidate, selected, target, targetFound, parameter, result,
                  types.1, types.2, referenceIndex, body, carrier, bodyExact, carrierExact⟩
              else throw .malformedWrapper
            else throw .malformedWrapper
          else throw .typeMismatch
        else throw (.missingDescriptor id)
    else throw (.monomorphicView id)

mutual
  def scan {checked : Checked} (prepared : Prepared checked) : Nat → Expr → Except Error (List (Template prepared))
    | 0, _ => .error .exhausted
    | fuel + 1, expression => do
      match expression with
      | .pair (.pair identity (.lambda parameter result body)) descriptor =>
        if (bodyHeader? body).isSome then
          let template ← decode prepared expression
          pure (template :: (← scan prepared fuel body))
        else pure ((← scan prepared fuel (.pair identity (.lambda parameter result body))) ++ (← scan prepared fuel descriptor))
      | .pair left right | .apply left right | .storeCell left right | .binary _ left right | .letE left right =>
        pure ((← scan prepared fuel left) ++ (← scan prepared fuel right))
      | .unit | .bool _ | .word _ | .integer _ | .var _ => pure []
      | .lambda _ _ body =>
        if (bodyHeader? body).isSome then throw .malformedWrapper
        scan prepared fuel body
      | .first operand | .second operand | .loadCell operand | .inLeft _ operand | .inRight _ operand |
        .newCell _ operand | .construct _ operand | .unary _ operand => scan prepared fuel operand
      | .caseE first second third | .ifE first second third | .ternary _ first second third =>
        pure ((← scan prepared fuel first) ++ (← scan prepared fuel second) ++ (← scan prepared fuel third))
      | .matchData _ _ scrutinee branches => pure ((← scan prepared fuel scrutinee) ++ (← scanBranches prepared fuel branches))
  def scanBranches {checked : Checked} (prepared : Prepared checked) : Nat → List Expr → Except Error (List (Template prepared))
    | _, [] => .ok []
    | 0, _ :: _ => .error .exhausted
    | fuel + 1, head :: tail => do pure ((← scan prepared fuel head) ++ (← scanBranches prepared fuel tail))
end

structure Cache {checked : Checked} {prepared : Prepared checked} (templates : Templates prepared) where private mk ::
  groups : List (List (Template prepared))
  scanned : (prepared.secondPass.closures.zipIdx.mapM fun (closure, index) =>
    scan prepared (SourceCoreCompatibleMarkedFunctions.scanBudget (SourceCoreLambdaTemplates.installedTemplate index closure))
      (SourceCoreLambdaTemplates.installedTemplate index closure)) = .ok groups

def Cache.wrappers {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    (cache : Cache templates) : List (Template prepared) := cache.groups.flatten

/-- Compilation provenance remains the actual snapshot cache's second pass. -/
theorem Cache.compiled {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    (_cache : Cache templates) : SourceCoreCompatibleMarkedFunctions.compileClosures prepared.base
      (SourceCoreCallablePairedPrograms.markedRepresentation prepared.ancestry prepared.fuel prepared.layouts)
      prepared.fuel = .ok prepared.secondPass.closures := templates.compiled

def prepare {checked : Checked} {prepared : Prepared checked} (templates : Templates prepared) : Except Error (Cache templates) :=
  match scanned : prepared.secondPass.closures.zipIdx.mapM (fun (closure, index) =>
    scan prepared (SourceCoreCompatibleMarkedFunctions.scanBudget (SourceCoreLambdaTemplates.installedTemplate index closure))
      (SourceCoreLambdaTemplates.installedTemplate index closure)) with
  | .error error => .error error
  | .ok groups => .ok ⟨groups, scanned⟩

private theorem original_typed {definitions : DataEnvironment} {world : StoreTyping}
    {identity callerSnapshot original : Value} {outer : Environment} {body : Expr}
    {descriptor : Word} {parameter result : Ty}
    (typed : RuntimeValueHasType world (.pair (.pair identity
      (.closure parameter (LanguageResult.resultType result) body (callerSnapshot :: original :: outer))) (.word descriptor))
      (CallableContract.functionType parameter result) definitions) :
    RuntimeValueHasType world original original.type definitions := by
  cases typed with
  | pair tagged _ =>
    cases tagged with
    | pair _ payload => exact SourceCoreCallableNativeSlots.saved_slot_typed (index := 1) payload rfl

private theorem caller_typed {definitions : DataEnvironment} {world : StoreTyping}
    {identity callerSnapshot original : Value} {outer : Environment} {body : Expr}
    {descriptor : Word} {parameter result : Ty}
    (typed : RuntimeValueHasType world (.pair (.pair identity
      (.closure parameter (LanguageResult.resultType result) body (callerSnapshot :: original :: outer))) (.word descriptor))
      (CallableContract.functionType parameter result) definitions) :
    RuntimeValueHasType world callerSnapshot callerSnapshot.type definitions := by
  cases typed with
  | pair tagged _ =>
    cases tagged with
    | pair _ payload => exact SourceCoreCallableNativeSlots.saved_slot_typed (index := 0) payload rfl

private theorem snapshot_type {checked : Checked} {prepared : Prepared checked} {value : Value}
    (snapshot : SourceCoreCallablePairedTemplates.Snapshot prepared value) : value.type = prepared.ancestry.layout.frame.type := by
  rw [snapshot.exact]
  cases snapshot.frame <;> rfl

structure Authenticated {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    (cache : Cache templates) (world : StoreTyping) (store : Store) (value : Value) where private mk ::
  wrapper : Template prepared
  member : wrapper ∈ cache.wrappers
  callerSnapshot : Value
  caller : SourceCoreCallablePairedTemplates.Snapshot prepared callerSnapshot
  callerTyped : RuntimeValueHasType world callerSnapshot prepared.ancestry.layout.frame.type prepared.layouts.definitions
  original : Value
  outer : Environment
  exact : value = .pair (.pair (.inLeft .word .unit)
    (.closure wrapper.parameter (LanguageResult.resultType wrapper.result) wrapper.body (callerSnapshot :: original :: outer))) (.word wrapper.target)
  typed : RuntimeValueHasType world value (CallableContract.functionType wrapper.parameter wrapper.result) prepared.layouts.definitions
  originalTyped : RuntimeValueHasType world original (CallableContract.functionType wrapper.parameter wrapper.result) prepared.layouts.definitions
  underlying : SourceCoreCallablePairedTemplates.Authenticated templates world store original
  targetExact : underlying.template.source.lambda.descriptor = wrapper.target
  originExact : underlying.template.source.lambda.owner = wrapper.entry.view.owner ∧
    underlying.template.source.lambda.id = wrapper.entry.view.binding.initializer ∧
    underlying.template.source.lambda.active = wrapper.entry.view.cumulative
  contextSlot : (callerSnapshot :: original :: outer)[wrapper.referenceIndex + 2]? =
    some (.cellRef prepared.ancestry.layout.frame.type 0)

def authenticate {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    (cache : Cache templates) {world : StoreTyping} {store : Store}
    (stored : RuntimeStoreHasTypes world store prepared.layouts.definitions) (value : Value) (parameter result : Ty)
    (typed : RuntimeValueHasType world value (CallableContract.functionType parameter result) prepared.layouts.definitions) :
    Except Error (Authenticated cache world store value) := do
  let .pair (.pair (.inLeft .word .unit) (.closure _ _ body (callerSnapshot :: original :: outer))) (.word descriptor) := value
    | throw .closureMismatch
  let chosen ← match cache.wrappers.attach.find? (fun wrapper => decide
      (wrapper.val.body = body ∧ wrapper.val.parameter = parameter ∧ wrapper.val.result = result ∧ wrapper.val.target = descriptor)) with
    | none => throw .closureMismatch | some wrapper => pure wrapper
  let wrapper := chosen.val
  if types : wrapper.parameter = parameter ∧ wrapper.result = result then
    if exact : value = .pair (.pair (.inLeft .word .unit)
        (.closure wrapper.parameter (LanguageResult.resultType wrapper.result) wrapper.body (callerSnapshot :: original :: outer))) (.word wrapper.target) then
      have typedWrapper : RuntimeValueHasType world value (CallableContract.functionType wrapper.parameter wrapper.result) prepared.layouts.definitions := by
        simpa only [types.1, types.2] using typed
      let caller ← (SourceCoreCallablePairedTemplates.decodeSnapshot prepared callerSnapshot).mapError Error.caller
      have callerTyped : RuntimeValueHasType world callerSnapshot prepared.ancestry.layout.frame.type prepared.layouts.definitions := by
        have own := caller_typed (exact ▸ typedWrapper)
        rw [snapshot_type caller] at own
        exact own
      have originalOwn : RuntimeValueHasType world original original.type prepared.layouts.definitions :=
        original_typed (exact ▸ typedWrapper)
      if originalType : original.type = CallableContract.functionType wrapper.parameter wrapper.result then
        have originalTyped : RuntimeValueHasType world original (CallableContract.functionType wrapper.parameter wrapper.result) prepared.layouts.definitions :=
          originalType ▸ originalOwn
        let underlying ← (SourceCoreCallablePairedTemplates.authenticate templates stored original wrapper.parameter wrapper.result originalTyped)
          |>.mapError Error.underlying
        if targetExact : underlying.template.source.lambda.descriptor = wrapper.target then
          if originExact : underlying.template.source.lambda.owner = wrapper.entry.view.owner ∧
              underlying.template.source.lambda.id = wrapper.entry.view.binding.initializer ∧
              underlying.template.source.lambda.active = wrapper.entry.view.cumulative then
            if contextSlot : (callerSnapshot :: original :: outer)[wrapper.referenceIndex + 2]? = some (.cellRef prepared.ancestry.layout.frame.type 0) then
              pure ⟨wrapper, chosen.property, callerSnapshot, caller, callerTyped, original, outer, exact, typedWrapper, originalTyped,
                underlying, targetExact, originExact, contextSlot⟩
            else throw .contextReferenceMismatch
          else throw (.foreignOrigin wrapper.entry.id)
        else throw .originalCarrierMismatch
      else throw .originalCarrierMismatch
    else throw .closureMismatch
  else throw .typeMismatch

structure Produced {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : StoreTyping} {store : Store} {value : Value}
    (authenticated : Authenticated cache world store value) (completion : Completion prepared) where private mk ::
  result : Value
  observation : completion.result.native.observation = .succeeded result store
  subvalue : SourceCoreCallablePairedCaptures.Subvalue value result

def Produced.of_success {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : StoreTyping} {store : Store} {value result : Value}
    {authenticated : Authenticated cache world store value} {completion : Completion prepared}
    (observation : completion.result.native.observation = .succeeded result store)
    (subvalue : SourceCoreCallablePairedCaptures.Subvalue value result) : Produced authenticated completion :=
  ⟨result, observation, subvalue⟩

structure Stored {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : StoreTyping} {store : Store} {value : Value}
    (authenticated : Authenticated cache world store value) (completion : Completion prepared)
    {initial : SourceHeap} (ledger : TypedLedger prepared.layouts initial world store) where private mk ::
  observation : SourceCoreCallablePairedLedger.store completion = store
  ordinal : Fin ledger.ledger.rows.length
  payload : Value
  payloadFound : (ledger.ledger.rows[ordinal]).payload = some payload
  subvalue : SourceCoreCallablePairedCaptures.Subvalue value payload

def Stored.of_payload {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : StoreTyping} {store : Store} {value payload : Value}
    {authenticated : Authenticated cache world store value} {completion : Completion prepared}
    {initial : SourceHeap} {ledger : TypedLedger prepared.layouts initial world store}
    (observation : SourceCoreCallablePairedLedger.store completion = store) (ordinal : Fin ledger.ledger.rows.length)
    (payloadFound : (ledger.ledger.rows[ordinal]).payload = some payload)
    (subvalue : SourceCoreCallablePairedCaptures.Subvalue value payload) : Stored authenticated completion ledger :=
  ⟨observation, ordinal, payload, payloadFound, subvalue⟩

structure JoinedProduced {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : StoreTyping} {store : Store} {value : Value}
    {authenticated : Authenticated cache world store value} {completion : Completion prepared}
    (produced : Produced authenticated completion) {initial : SourceHeap}
    (ledger : TypedLedger prepared.layouts initial world store) where private mk ::
  captures : SourceCoreCallablePairedCaptures.Captured authenticated.underlying ledger

structure JoinedStored {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : StoreTyping} {store : Store} {value : Value}
    {authenticated : Authenticated cache world store value} {completion : Completion prepared}
    {initial : SourceHeap} {ledger : TypedLedger prepared.layouts initial world store}
    (stored : Stored authenticated completion ledger) where private mk ::
  captures : SourceCoreCallablePairedCaptures.Captured authenticated.underlying ledger

def joinProduced {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : StoreTyping} {store : Store} {value : Value}
    {authenticated : Authenticated cache world store value} {completion : Completion prepared}
    (produced : Produced authenticated completion) {initial : SourceHeap}
    (ledger : TypedLedger prepared.layouts initial world store) : Except Error (JoinedProduced produced ledger) := do
  let captures ← (SourceCoreCallablePairedCaptures.joinAuthenticated authenticated.underlying ledger).mapError Error.captures
  pure ⟨captures⟩

def joinStored {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : StoreTyping} {store : Store} {value : Value}
    {authenticated : Authenticated cache world store value} {completion : Completion prepared}
    {initial : SourceHeap} {ledger : TypedLedger prepared.layouts initial world store}
    (stored : Stored authenticated completion ledger) : Except Error (JoinedStored stored) := do
  let captures ← (SourceCoreCallablePairedCaptures.joinAuthenticated authenticated.underlying ledger).mapError Error.captures
  pure ⟨captures⟩

theorem JoinedProduced.capture_order {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : StoreTyping} {store : Store} {value : Value}
    {authenticated : Authenticated cache world store value} {completion : Completion prepared}
    {produced : Produced authenticated completion} {initial : SourceHeap}
    {ledger : TypedLedger prepared.layouts initial world store} (joined : JoinedProduced produced ledger) :
    joined.captures.environment.map Prod.fst = authenticated.underlying.template.source.scope.map Prod.fst :=
  joined.captures.binders

theorem JoinedStored.capture_order {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : StoreTyping} {store : Store} {value : Value}
    {authenticated : Authenticated cache world store value} {completion : Completion prepared}
    {initial : SourceHeap} {ledger : TypedLedger prepared.layouts initial world store}
    {stored : Stored authenticated completion ledger} (joined : JoinedStored stored) :
    joined.captures.environment.map Prod.fst = authenticated.underlying.template.source.scope.map Prod.fst :=
  joined.captures.binders

/-- Canonical read metadata remains separate from dynamic principal headers.
Occurrence witnesses for a dynamically rewritten parent source must be supplied
by its prepared graph transition, rather than assumed equal to these rows. -/
def Authenticated.canonicalOwnSubstitution {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : StoreTyping} {store : Store} {value : Value}
    (authenticated : Authenticated cache world store value) : TypeSystem.Substitution :=
  authenticated.wrapper.entry.view.ownSubstitution

def Authenticated.canonicalOwnWitnesses {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : StoreTyping} {store : Store} {value : Value}
    (authenticated : Authenticated cache world store value) : List SourceCoreLocalEvidence.Witness :=
  authenticated.wrapper.entry.view.ownWitnesses

def Authenticated.parentActive {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : StoreTyping} {store : Store} {value : Value}
    (authenticated : Authenticated cache world store value) : TypeSystem.Substitution :=
  authenticated.wrapper.entry.view.parentActive

def Authenticated.cumulative {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : StoreTyping} {store : Store} {value : Value}
    (authenticated : Authenticated cache world store value) : TypeSystem.Substitution :=
  authenticated.wrapper.entry.view.cumulative

def Authenticated.canonicalPrincipalSource {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : StoreTyping} {store : Store} {value : Value}
    (authenticated : Authenticated cache world store value) : TypedSource :=
  authenticated.wrapper.entry.view.principal.source

end Solcore.Frontend.SourceCoreCallablePairedReadViews
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallablePairedRestoration
/-! Source closure restoration from the actual paired callable profile.
Code authenticity and physical capture joins are supplied by the owning native
receipts. Prepared positions select raw lexical headers and exact read recipes;
restoration performs no source traversal, substitution or evidence resolution.

The output retains the original closure for an instantiated read. Produced and
stored wrappers keep the corresponding completion provenance. These receipts
establish the reconstruction boundary; full source execution meaning still
requires the enclosing native emission/history theorem.
-/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallablePairedRestoration
open SourceInference
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Program := SourceCoreCallablePairedPrograms.Prepared
abbrev Graph := @SourceCoreCallableAncestryPairedPreparation.Prepared
abbrev Headers := @SourceCoreCallablePairedHeaders.Prepared
abbrev Templates := @SourceCoreCallablePairedTemplates.Cache
abbrev Views := @SourceCoreCallablePairedReadViews.Cache
abbrev Ledger := @SourceCoreAllocationLedger.TypedLedger
abbrev SourceValue := SourceTypedRuntime.Value

inductive Error where
  | captures (error : SourceCoreCallablePairedCaptures.Error)
  | lexicalUnavailable
  | callerUnavailable
  | lambdaHeaderUnavailable (position : Nat) (descriptor : Core.Word)
  | principalHeaderUnavailable (position : Nat) (binder : Resolved.LocalId)
  | readRecipeUnavailable (caller lexical : Nat) (view target : Core.Word)
  deriving Repr

structure Ordinary {checked : Checked} {program : Program checked} {graph : Graph program.base}
    (headers : Headers graph) {templates : Templates program}
    {world : Core.StoreTyping} {store : Core.Store} {value : Core.Value}
    (authenticated : SourceCoreCallablePairedTemplates.Authenticated templates world store value)
    {initial : List SourceTypedRuntime.Cell} (ledger : Ledger program.layouts initial world store) where private mk ::
  captures : SourceCoreCallablePairedCaptures.Captured authenticated ledger
  position : Nat
  lookup : graph.table.lookupIndex? authenticated.snapshot.frame = some (some position)
  header : SourceCoreCallablePairedHeaders.LambdaHeader graph headers.principals
  selected : headers.lambdaAt? position authenticated.template.source.lambda.descriptor = some header
  source : SourceValue
  exact : source = header.sourceValue captures.environment

def restoreOrdinary {checked : Checked} {program : Program checked} {graph : Graph program.base}
    (headers : Headers graph) {templates : Templates program}
    {world : Core.StoreTyping} {store : Core.Store} {value : Core.Value}
    (authenticated : SourceCoreCallablePairedTemplates.Authenticated templates world store value)
    {initial : List SourceTypedRuntime.Cell} (ledger : Ledger program.layouts initial world store) :
    Except Error (Ordinary headers authenticated ledger) := do
  let captures ← (SourceCoreCallablePairedCaptures.joinAuthenticated authenticated ledger).mapError Error.captures
  match lookup : graph.table.lookupIndex? authenticated.snapshot.frame with
  | some (some position) =>
    match selected : headers.lambdaAt? position authenticated.template.source.lambda.descriptor with
    | none => throw (.lambdaHeaderUnavailable position authenticated.template.source.lambda.descriptor)
    | some header => pure ⟨captures, position, lookup, header, selected, header.sourceValue captures.environment, rfl⟩
  | _ => throw .lexicalUnavailable

structure Read {checked : Checked} {program : Program checked} {graph : Graph program.base}
    (headers : Headers graph) {templates : Templates program} {views : Views templates}
    {world : Core.StoreTyping} {store : Core.Store} {value : Core.Value}
    (authenticated : SourceCoreCallablePairedReadViews.Authenticated views world store value)
    {initial : List SourceTypedRuntime.Cell} (ledger : Ledger program.layouts initial world store) where private mk ::
  captures : SourceCoreCallablePairedCaptures.Captured authenticated.underlying ledger
  caller : Nat
  callerLookup : graph.table.lookupIndex? authenticated.caller.frame = some (some caller)
  lexical : Nat
  lexicalLookup : graph.table.lookupIndex? authenticated.underlying.snapshot.frame = some (some lexical)
  recipe : SourceCoreCallableAncestryPairedPreparation.Recipe graph.inputs graph.table
  recipeSelected : graph.recipeAt? caller lexical authenticated.wrapper.entry.id authenticated.wrapper.target = some recipe
  header : SourceCoreCallablePairedHeaders.PrincipalHeader graph headers.principals
  headerSelected : headers.principalBinderAt? lexical authenticated.wrapper.entry.view.binding.binder.id
    authenticated.wrapper.entry.view.principal.initializer = some header
  source : SourceValue
  exact : source = recipe.applied.sourceValue captures.environment header.principal.context.evidence

def restoreRead {checked : Checked} {program : Program checked} {graph : Graph program.base}
    (headers : Headers graph) {templates : Templates program} {views : Views templates}
    {world : Core.StoreTyping} {store : Core.Store} {value : Core.Value}
    (authenticated : SourceCoreCallablePairedReadViews.Authenticated views world store value)
    {initial : List SourceTypedRuntime.Cell} (ledger : Ledger program.layouts initial world store) :
    Except Error (Read headers authenticated ledger) := do
  let captures ← (SourceCoreCallablePairedCaptures.joinAuthenticated authenticated.underlying ledger).mapError Error.captures
  match callerLookup : graph.table.lookupIndex? authenticated.caller.frame with
  | some (some caller) =>
    match lexicalLookup : graph.table.lookupIndex? authenticated.underlying.snapshot.frame with
    | some (some lexical) =>
      match recipeSelected : graph.recipeAt? caller lexical authenticated.wrapper.entry.id authenticated.wrapper.target with
      | none => throw (.readRecipeUnavailable caller lexical authenticated.wrapper.entry.id authenticated.wrapper.target)
      | some recipe =>
        match headerSelected : headers.principalBinderAt? lexical authenticated.wrapper.entry.view.binding.binder.id
            authenticated.wrapper.entry.view.principal.initializer with
        | none => throw (.principalHeaderUnavailable lexical authenticated.wrapper.entry.view.binding.binder.id)
        | some header => pure ⟨captures, caller, callerLookup, lexical, lexicalLookup, recipe, recipeSelected,
            header, headerSelected, recipe.applied.sourceValue captures.environment header.principal.context.evidence, rfl⟩
    | _ => throw .lexicalUnavailable
  | _ => throw .callerUnavailable

/-- Native result provenance is retained alongside the source reconstruction. -/
structure ProducedOrdinary {checked : Checked} {program : Program checked} {graph : Graph program.base}
    (headers : Headers graph) {templates : Templates program}
    {completion : SourceCoreCallablePairedPrograms.Completion program}
    {world : Core.StoreTyping} {store : Core.Store} {value : Core.Value}
    (produced : SourceCoreCallablePairedCaptures.Produced templates completion world store value)
    {initial : List SourceTypedRuntime.Cell} (ledger : Ledger program.layouts initial world store) where private mk ::
  restored : Ordinary headers produced.authenticated ledger

def restoreProducedOrdinary {checked : Checked} {program : Program checked} {graph : Graph program.base}
    (headers : Headers graph) {templates : Templates program}
    {completion : SourceCoreCallablePairedPrograms.Completion program}
    {world : Core.StoreTyping} {store : Core.Store} {value : Core.Value}
    (produced : SourceCoreCallablePairedCaptures.Produced templates completion world store value)
    {initial : List SourceTypedRuntime.Cell} (ledger : Ledger program.layouts initial world store) :
    Except Error (ProducedOrdinary headers produced ledger) := do
  pure ⟨← restoreOrdinary headers produced.authenticated ledger⟩

structure ProducedRead {checked : Checked} {program : Program checked} {graph : Graph program.base}
    (headers : Headers graph) {templates : Templates program} {views : Views templates}
    {world : Core.StoreTyping} {store : Core.Store} {value : Core.Value}
    {authenticated : SourceCoreCallablePairedReadViews.Authenticated views world store value}
    {completion : SourceCoreCallablePairedPrograms.Completion program}
    (produced : SourceCoreCallablePairedReadViews.Produced authenticated completion)
    {initial : List SourceTypedRuntime.Cell} (ledger : Ledger program.layouts initial world store) where private mk ::
  restored : Read headers authenticated ledger

def restoreProducedRead {checked : Checked} {program : Program checked} {graph : Graph program.base}
    (headers : Headers graph) {templates : Templates program} {views : Views templates}
    {world : Core.StoreTyping} {store : Core.Store} {value : Core.Value}
    {authenticated : SourceCoreCallablePairedReadViews.Authenticated views world store value}
    {completion : SourceCoreCallablePairedPrograms.Completion program}
    (produced : SourceCoreCallablePairedReadViews.Produced authenticated completion)
    {initial : List SourceTypedRuntime.Cell} (ledger : Ledger program.layouts initial world store) :
    Except Error (ProducedRead headers produced ledger) := do
  pure ⟨← restoreRead headers authenticated ledger⟩

/-- Failed and suspended native heaps retain stored-payload provenance. -/
structure StoredOrdinary {checked : Checked} {program : Program checked} {graph : Graph program.base}
    (headers : Headers graph) {templates : Templates program}
    {completion : SourceCoreCallablePairedPrograms.Completion program}
    {world : Core.StoreTyping} {store : Core.Store} {value : Core.Value}
    {initial : List SourceTypedRuntime.Cell} {ledger : Ledger program.layouts initial world store}
    (stored : SourceCoreCallablePairedCaptures.Stored templates completion value ledger) where private mk ::
  restored : Ordinary headers stored.authenticated ledger

def restoreStoredOrdinary {checked : Checked} {program : Program checked} {graph : Graph program.base}
    (headers : Headers graph) {templates : Templates program}
    {completion : SourceCoreCallablePairedPrograms.Completion program}
    {world : Core.StoreTyping} {store : Core.Store} {value : Core.Value}
    {initial : List SourceTypedRuntime.Cell} {ledger : Ledger program.layouts initial world store}
    (stored : SourceCoreCallablePairedCaptures.Stored templates completion value ledger) :
    Except Error (StoredOrdinary headers stored) := do
  pure ⟨← restoreOrdinary headers stored.authenticated ledger⟩

structure StoredRead {checked : Checked} {program : Program checked} {graph : Graph program.base}
    (headers : Headers graph) {templates : Templates program} {views : Views templates}
    {world : Core.StoreTyping} {store : Core.Store} {value : Core.Value}
    {authenticated : SourceCoreCallablePairedReadViews.Authenticated views world store value}
    {completion : SourceCoreCallablePairedPrograms.Completion program}
    {initial : List SourceTypedRuntime.Cell} {ledger : Ledger program.layouts initial world store}
    (stored : SourceCoreCallablePairedReadViews.Stored authenticated completion ledger) where private mk ::
  restored : Read headers authenticated ledger

def restoreStoredRead {checked : Checked} {program : Program checked} {graph : Graph program.base}
    (headers : Headers graph) {templates : Templates program} {views : Views templates}
    {world : Core.StoreTyping} {store : Core.Store} {value : Core.Value}
    {authenticated : SourceCoreCallablePairedReadViews.Authenticated views world store value}
    {completion : SourceCoreCallablePairedPrograms.Completion program}
    {initial : List SourceTypedRuntime.Cell} {ledger : Ledger program.layouts initial world store}
    (stored : SourceCoreCallablePairedReadViews.Stored authenticated completion ledger) :
    Except Error (StoredRead headers stored) := do
  pure ⟨← restoreRead headers authenticated ledger⟩

namespace Ordinary
variable {checked : Checked} {program : Program checked} {graph : Graph program.base}
  {headers : Headers graph} {templates : Templates program}
  {world : Core.StoreTyping} {store : Core.Store} {value : Core.Value}
  {authenticated : SourceCoreCallablePairedTemplates.Authenticated templates world store value}
  {initial : List SourceTypedRuntime.Cell} {ledger : Ledger program.layouts initial world store}

theorem raw_closure (restored : Ordinary headers authenticated ledger) :
    restored.source = .closure restored.header.parameters restored.header.resultType restored.header.body
      restored.header.state.metadata.source restored.header.state.metadata.owner restored.captures.environment
      restored.header.context.context.evidence := restored.exact

theorem capture_order (restored : Ordinary headers authenticated ledger) :
    restored.captures.environment.map Prod.fst = authenticated.template.source.scope.map Prod.fst := restored.captures.binders

end Ordinary
namespace Read
variable {checked : Checked} {program : Program checked} {graph : Graph program.base}
  {headers : Headers graph} {templates : Templates program} {views : Views templates}
  {world : Core.StoreTyping} {store : Core.Store} {value : Core.Value}
  {authenticated : SourceCoreCallablePairedReadViews.Authenticated views world store value}
  {initial : List SourceTypedRuntime.Cell} {ledger : Ledger program.layouts initial world store}

theorem original_closure (restored : Read headers authenticated ledger) :
    restored.source = .instantiated restored.recipe.read.substitution restored.recipe.read.witnesses
      (.closure restored.recipe.applied.parameters restored.recipe.applied.resultType restored.recipe.applied.body
        restored.recipe.lexical.metadata.source restored.recipe.lexical.metadata.owner restored.captures.environment
        restored.header.principal.context.evidence) := restored.exact

theorem capture_order (restored : Read headers authenticated ledger) :
    restored.captures.environment.map Prod.fst = authenticated.underlying.template.source.scope.map Prod.fst := restored.captures.binders

end Read
end Solcore.Frontend.SourceCoreCallablePairedRestoration
end
