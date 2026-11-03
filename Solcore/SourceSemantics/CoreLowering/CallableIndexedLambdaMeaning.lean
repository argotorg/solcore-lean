import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaValues
import Solcore.SourceSemantics.CoreLowering.CaptureCopiesMarked

/-! Lambda formation at the actual generated syntax, including arbitrary
administrative insertions. An ordinary lambda first copies the captured cells
of its creation environment through the marked allocator; the source lambda
copies the same bindings. The newly captured value is kept exactly as created
over the copies. A lambda whose policy does not snapshot it, a generalized
local's initializer, forms directly over its scope. Finite completion
reflection follows from the direct evaluation, not from an equality between
closures captured in different environments. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaValues
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality
open CallableIndexedHistory

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {actual : Core.Environment}

/-- The source location selected by a capture remains the same actual native
cell through the real embedding, including aliases. -/
theorem Captures.lookup (captured : Captures prepared mapping world scope function.captured actual)
    {binder : Resolved.LocalId} {location : Dynamic.Location}
    (found : Dynamic.Environment.LooksUp function.captured binder location) :
    ∃ index payload target, SourceCoreLocalCell.lookup? scope binder = some (index, payload) ∧
      actual[captured.embedding index]? = some (.cellRef (OptionalCell.cellType payload) target) ∧
      ReferenceRepresents mapping world location target payload := by
  obtain ⟨index, payload, target, selected, reference, represented⟩ := captured.represented.lookup_source found
  exact ⟨index, payload, target, selected, captured.agrees reference, represented⟩

/-- The decorated lambda forms over the actual environment after reading the
frame cell. -/
theorem expression_evaluates
    (captured : Captures prepared mapping world scope function.captured actual)
    (code : Code prepared function scope captured.administrative) (history : History code)
    {store : Store} {location : Location}
    (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
    (read : store.read? location = some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame history.native)) :
    Evaluates actual store (code.expression.rename captured.embedding)
      (.inRight .word (value code captured.embedding history.native actual)) store :=
  .inRight (.pair (.pair (.inLeft .unit) (.letE (.loadCell (.var (captured.agrees reference)) read) .lambda)) .word)

theorem formation_evaluates
    (captured : Captures prepared mapping world scope function.captured actual)
    (code : Code prepared function scope captured.administrative) (history : History code)
    (shared : code.policy.snapshotLambda code.id = false)
    {store : Store} {location : Location}
    (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
    (read : store.read? location = some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame history.native)) :
    Evaluates actual store (code.lowered.expression.rename captured.embedding)
      (.inRight .word (value code captured.embedding history.native actual)) store := by
  rw [code.emitted_shared shared]
  exact expression_evaluates captured code history reference read

/-- The actual emitted expression and store determine native output typing.
No future world is invented for a read-only formation step. -/
theorem formation_represents
    (captured : Captures prepared mapping world scope function.captured actual)
    (code : Code prepared function scope captured.administrative) (history : History code)
    (shared : code.policy.snapshotLambda code.id = false)
    {store : Store} {location : Location}
    (stored : RuntimeStoreHasTypes world store prepared.layouts.definitions)
    (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
    (read : store.read? location = some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame history.native)) :
    Represents prepared mapping world (FunctionValues.sourceType function) (.closure function)
      (value code captured.embedding history.native actual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) := by
  have evaluated := formation_evaluates captured code history shared reference read
  obtain ⟨future, _, finalStored, resultTyped⟩ :=
    evaluation_preserves_type evaluated (code.typed.rename captured.respects) captured.typed stored
  have same : future = world := finalStored.world_eq.trans stored.world_eq.symm
  subst future
  cases resultTyped with
  | inRight typed => exact .lambda captured code history typed

/-- Source formation copies the creation environment and stores exactly the
caller's raw source, context and evidence with the copies. These are semantic
inputs, not decoded guesses from a native descriptor. No body execution is
involved. -/
theorem source_formation {administrative : Core.Context}
    (code : Code prepared function scope administrative) (program : Program)
    {environment : Dynamic.Environment} {heap after : Dynamic.Heap}
    (snapshot : Dynamic.EnvironmentCopies function.source environment heap function.captured after)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    Dynamic.ExpressionEvaluates program function.context function.evidence function.source environment heap
      code.id (.closure function) after := by
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound code.sourceFound)
  · rw [code.sourceForm]
    exact .lambda ordinary snapshot
  · rw [coercions]
    exact .nil

/-- The closure an ordinary lambda forms over the copies of its creation
environment: the source copies, the closure's capture layout over the copied
cells, the extended heap relation with the frame cell unchanged, and the Core
evaluation of the emitted copies and lambda. Slots past the scope keep their
canonical values. -/
structure Formed {projects : GenericHeap.Projection}
    (model : GenericHeap.PayloadModel (storageCatalog checked.catalog) projects prepared.layouts.definitions)
    {environment : Dynamic.Environment}
    (current : Captures prepared mapping world scope environment actual)
    (code : Code prepared function scope current.administrative) (history : History code)
    (heap : Dynamic.Heap) (store : Store) (location : Location) where
  captured : Dynamic.Environment
  finalHeap : Dynamic.Heap
  finalStore : Store
  finalMap : LocationMap
  finalWorld : StoreTyping
  closureActual : Core.Environment
  canonical : Core.Environment
  actualContext : Core.Context
  embedding : Renaming
  copy : Dynamic.EnvironmentCopies function.source environment heap captured finalHeap
  represented : DataHeap.EnvRepresents (storageCatalog checked.catalog) finalMap finalWorld current.administrative
    scope captured canonical prepared.layouts.definitions
  agrees : ReadOnly.EnvironmentsAgree embedding canonical closureActual
  respects : Renaming.Respects embedding (SourceCoreLocalCell.coreContext scope ++ current.administrative) actualContext
  typed : RuntimeEnvironmentHasTypes finalWorld closureActual actualContext prepared.layouts.definitions
  slots : ∀ index, scope.length ≤ index → canonical[index]? = current.canonical[index]?
  heaps : GenericHeap.HeapRepresents model finalMap finalWorld finalHeap finalStore
  maps : LocationMap.Extends mapping finalMap
  worlds : WorldExtends world finalWorld
  frame : AdministrativePreserved mapping store finalMap finalStore
  read : finalStore.read? location = some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame history.native)
  evaluated : Evaluates actual store (code.lowered.expression.rename current.embedding)
    (.inRight .word (value code embedding history.native closureActual)) finalStore

namespace Formed
variable {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (storageCatalog checked.catalog) projects prepared.layouts.definitions}
  {environment : Dynamic.Environment} {current : Captures prepared mapping world scope environment actual}
  {code : Code prepared function scope current.administrative} {history : History code}
  {heap : Dynamic.Heap} {store : Store} {location : Location}

/-- The closure's capture layout over its copies. -/
def captures (formed : Formed model current code history heap store location) :
    Captures prepared formed.finalMap formed.finalWorld scope formed.captured formed.closureActual :=
  ⟨current.administrative, formed.canonical, formed.actualContext, formed.embedding, formed.represented,
    formed.agrees, formed.respects, formed.typed⟩

/-- The formed closure. -/
abbrev closure (formed : Formed model current code history heap store location) : Dynamic.Closure :=
  { function with captured := formed.captured }

/-- The same code, for the formed closure. -/
def closureCode (formed : Formed model current code history heap store location) :
    Code prepared formed.closure scope formed.captures.administrative :=
  code.recapture formed.captured

def closureHistory (formed : Formed model current code history heap store location) :
    History formed.closureCode :=
  history.recapture formed.captured

theorem value_eq (formed : Formed model current code history heap store location) :
    value formed.closureCode formed.captures.embedding history.native formed.closureActual =
      value code formed.embedding history.native formed.closureActual := rfl

theorem reference (formed : Formed model current code history heap store location)
    (referenceIndex : code.referenceIndex = scope.length + 1 + prepared.base.globals.length)
    (reference : current.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location)) :
    formed.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location) := by
  rw [formed.slots _ (by omega)]
  exact reference

/-- The source lambda forms the same closure over the same copies. -/
theorem source (formed : Formed model current code history heap store location) (program : Program)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    Dynamic.ExpressionEvaluates program function.context function.evidence function.source environment heap
      code.id (.closure formed.closure) formed.finalHeap :=
  source_formation formed.closureCode program formed.copy ordinary coercions

/-- The formed native closure, typed by the evaluation of the whole emitted
expression, represents the formed source closure. -/
theorem represents (formed : Formed model current code history heap store location)
    (stored : RuntimeStoreHasTypes world store prepared.layouts.definitions) :
    Represents prepared formed.finalMap formed.finalWorld (FunctionValues.sourceType function)
      (.closure formed.closure) (value code formed.embedding history.native formed.closureActual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) := by
  obtain ⟨future, _, finalStored, resultTyped⟩ :=
    evaluation_preserves_type formed.evaluated (code.typed.rename current.respects) current.typed stored
  have same : future = formed.finalWorld :=
    finalStored.world_eq.trans formed.heaps.runtime_hasTypes.world_eq.symm
  subst future
  cases resultTyped with
  | inRight typed =>
    have closureTyped : RuntimeValueHasType formed.finalWorld
        (value formed.closureCode formed.captures.embedding formed.closureHistory.native formed.closureActual)
        (CallableContract.functionType formed.closureCode.receipt.parameterCore formed.closureCode.receipt.resultCore)
        prepared.layouts.definitions := typed
    exact Represents.lambda (function := formed.closure) formed.captures formed.closureCode
      formed.closureHistory closureTyped

/-- A completed native formation is the formed closure in the formed store. -/
theorem reflects (formed : Formed model current code history heap store location)
    {result : Core.Value} {after : Store}
    (completed : Evaluates actual store (code.lowered.expression.rename current.embedding) result after) :
    result = .inRight .word (value code formed.embedding history.native formed.closureActual) ∧
      after = formed.finalStore :=
  evaluation_deterministic completed formed.evaluated

end Formed

/-- An ordinary lambda's formation: the marked creation copies of its scope,
then the decorated lambda over the copies. -/
theorem formation {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel (storageCatalog checked.catalog) projects prepared.layouts.definitions}
    {environment : Dynamic.Environment}
    (current : Captures prepared mapping world scope environment actual)
    (code : Code prepared function scope current.administrative) (history : History code)
    (copied : code.policy.snapshotLambda code.id = true)
    (referenceIndex : code.referenceIndex = scope.length + 1 + prepared.base.globals.length)
    {heap : Dynamic.Heap} {store : Store} {location : Location}
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (reference : current.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
    (read : store.read? location = some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame history.native)) :
    Nonempty (Formed model current code history heap store location) := by
  have accepted := code.emitted_copied copied
  have base : (fun index : Nat => index) = (· + ([] : Environment).length) := by
    funext index
    simp
  rw [base] at accepted
  rw [referenceIndex] at reference
  obtain ⟨captured, finalHeap, finalCanonical, finalActual, finalActualContext, finalStore, finalMap, finalWorld,
      finalEmbedding, copy, environments, slots, finalHeaps, maps, worlds, frame, finalRead, lookups, types,
      actualTyped, agreement⟩ :=
    CaptureCopies.marked_copies_prefix (pre := []) (preContext := []) accepted rfl
      (CallableIndexedAmbient.frame_registered prepared) current.represented heaps current.agrees rfl
      current.respects current.typed reference read
  have copy := copy.of_copiedBinder (LambdaMetadataViews.MetadataView.copiedBinder code.viewOfSource).symm
  let closure : Captures prepared finalMap finalWorld scope captured finalActual :=
    ⟨current.administrative, finalCanonical, finalActualContext, finalEmbedding, environments, lookups, types,
      actualTyped⟩
  have finalReference : closure.canonical[code.referenceIndex]? =
      some (.cellRef prepared.ancestry.layout.frame.type location) := by
    rw [referenceIndex, slots _ (by omega)]
    exact reference
  have formed := expression_evaluates (function := { function with captured := captured })
    (store := finalStore) (location := location) closure
    (code.recapture captured) (history.recapture captured) finalReference finalRead
  exact ⟨⟨captured, finalHeap, finalStore, finalMap, finalWorld, finalActual, finalCanonical, finalActualContext,
    finalEmbedding, copy, environments, lookups, types, actualTyped, slots, finalHeaps, maps, worlds, frame,
    finalRead, agreement.wrap formed⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaValues
