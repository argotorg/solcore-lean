import Solcore.Frontend.SourceCore.Internal.CallableViews
import Solcore.Frontend.SourceCore.Internal.CallablePrincipals
import Solcore.Frontend.SourceCore.Internal.Carriers
import Solcore.Frontend.SourceCore.Internal.Allocation

/-!
# Callable ancestry

Dynamic callable ancestry in one ordinary Core cell: programs, templates, captures, read recipes and
views.
-/

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallableAncestry
/-! Dynamic callable ancestry uses one ordinary Core cell, placed after the
lexical source references and globals. A lambda snapshots that cell when it is
created. Calls enter its lexical frame and restore the caller, including on a
language failure. Owned read views preserve the original identity/descriptor.

This is a compiler representation, not a source evaluator or a source-heap
exporter. Its cached metadata is prepared once. Reconstructing legacy source
closures still requires the artifact's allocation ledger and exact native
closure template authentication. Context snapshots add values to closure
environments; they do not allocate source cells.
-/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableAncestry
open SourceInference Core
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Base := SourceCoreCompatibleFunctions.Prepared
abbrev Key := SourceSpecialization.SpecializationKey
abbrev Active := TypeSystem.Substitution
abbrev Scope := SourceCoreFunctions.Scope
abbrev Frames := SourceCoreCallableContextFrames.Frame

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
  frame : SourceCoreCallableContextFrames.Layout
  atEnd : frame.dataType.index = ambient.length
  definitionsTyped : (ambient ++ [frame.definition]).WellFormed

def Layout.definitions (layout : Layout) : DataEnvironment := layout.ambient ++ [layout.frame.definition]
def Layout.referenceType (layout : Layout) : Ty := .cell layout.frame.type

def Layout.prepare (ambient : DataEnvironment) : Except Error Layout :=
  let frame : SourceCoreCallableContextFrames.Layout := ⟨⟨ambient.length⟩⟩
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
def snapshotLambda (layout : SourceCoreCallableContextFrames.Layout) (origin : Word)
    (referenceIndex : Nat) (parameter result : Ty) (body : Expr) : Expr :=
  .letE (.loadCell (.var referenceIndex))
    (.lambda parameter (LanguageResult.resultType result)
      (SourceCoreCallableContextFrames.withFrame (.var (referenceIndex + 2))
        (SourceCoreCallableContextFrames.lambdaFrame layout origin (.var 1)
          (.loadCell (.var (referenceIndex + 2)))) (body.weakenAt 1)))

theorem snapshotLambda_hasType {definitions : DataEnvironment} {layout : SourceCoreCallableContextFrames.Layout}
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
  · apply SourceCoreCallableContextFrames.lambdaFrame_hasType registered origin (.var rfl)
    exact .loadCell (.var (by simpa [Nat.add_assoc] using reference))
  · simpa [Context.insertAt] using bodyTyped.weakenAt (inserted := layout.type) 1

/-- Creation reads only the administrative cell and captures its exact finite
value. Application semantics use the existing `withFrame` laws. -/
theorem snapshotLambda_evaluates {layout : SourceCoreCallableContextFrames.Layout}
    {environment : Environment} {store : Store} {parameter result : Ty} {body : Expr}
    {referenceIndex location : Nat} {snapshot : Core.Value} (origin : Word)
    (reference : environment[referenceIndex]? = some (.cellRef layout.type location))
    (read : store.read? location = some snapshot) :
    Evaluates environment store (snapshotLambda layout origin referenceIndex parameter result body)
      (.closure parameter (LanguageResult.resultType result)
        (SourceCoreCallableContextFrames.withFrame (.var (referenceIndex + 2))
          (SourceCoreCallableContextFrames.lambdaFrame layout origin (.var 1)
            (.loadCell (.var (referenceIndex + 2)))) (body.weakenAt 1))
        (snapshot :: environment)) store :=
  .letE (.loadCell (.var reference) read) .lambda

/-- The read's original carrier occupies saved slot 0; the lambda argument
adds slot 0 on application. The context cell stays at the last lexical slot. -/
def viewBody (layout : SourceCoreCallableContextFrames.Layout) (id target : Word)
    (referenceIndex : Nat) : Expr :=
  SourceCoreCallableContextFrames.withFrame (.var (referenceIndex + 2))
    (SourceCoreCallableContextFrames.view layout id target (.loadCell (.var (referenceIndex + 2))))
    (.apply (.second (.first (.var 1))) (.var 0))

def viewRepack (layout : SourceCoreCallableContextFrames.Layout) (parameter result : Ty)
    (id target : Word) (referenceIndex : Nat) : Expr :=
  .pair (.pair (.first (.first (.var 0)))
    (.lambda parameter (LanguageResult.resultType result) (viewBody layout id target referenceIndex)))
    (.second (.var 0))

def viewLower (layout : SourceCoreCallableContextFrames.Layout) (parameter result : Ty)
    (id target : Word) (referenceIndex : Nat) (read : Expr) : Expr :=
  LanguageResult.bind (CallableContract.functionType parameter result) read
    (LanguageResult.success (viewRepack layout parameter result id target referenceIndex))

theorem viewRepack_hasType {definitions : DataEnvironment} {layout : SourceCoreCallableContextFrames.Layout}
    {context : Core.Context} {parameter result : Ty} {referenceIndex : Nat}
    (registered : layout.Registered definitions) (id target : Word)
    (parameterWF : parameter.WellFormed definitions) (resultWF : result.WellFormed definitions)
    (reference : context[referenceIndex]? = some (.cell layout.type)) :
    HasType (CallableContract.functionType parameter result :: context)
      (viewRepack layout parameter result id target referenceIndex)
      (CallableContract.functionType parameter result) definitions := by
  apply HasType.pair
  · apply HasType.pair (.first (.first (.var rfl)))
    apply HasType.lambda parameterWF (LanguageResult.resultType_wellFormed resultWF)
    apply SourceCoreCallableContextFrames.withFrame_hasType
    · exact .var (by simpa [Nat.add_assoc] using reference)
    · apply SourceCoreCallableContextFrames.view_hasType registered id target
      exact .loadCell (.var (by simpa [Nat.add_assoc] using reference))
    · exact .apply (.second (.first (.var rfl))) (.var rfl)
  · exact .second (.var rfl)

theorem viewLower_hasType {definitions : DataEnvironment} {layout : SourceCoreCallableContextFrames.Layout}
    {context : Core.Context} {parameter result : Ty} {referenceIndex : Nat} {read : Expr}
    (registered : layout.Registered definitions) (id target : Word)
    (parameterWF : parameter.WellFormed definitions) (resultWF : result.WellFormed definitions)
    (reference : context[referenceIndex]? = some (.cell layout.type))
    (readTyped : HasType context read (LanguageResult.resultType (CallableContract.functionType parameter result)) definitions) :
    HasType context (viewLower layout parameter result id target referenceIndex read)
      (LanguageResult.resultType (CallableContract.functionType parameter result)) definitions :=
  LanguageResult.bind_hasType (CallableContract.functionType_wellFormed parameterWF resultWF) readTyped
    (LanguageResult.success_hasType (viewRepack_hasType registered id target parameterWF resultWF reference))

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

private def originId {checked : Checked} {base : Base checked} (_ : Prepared base)
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
  pure (SourceCoreCallableContextFrames.withFrame (.var (base.globals.length + 1))
    (SourceCoreCallableContextFrames.named prepared.layout.frame origin) body)

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
  pure (SourceCoreCallableContextFrames.allocate prepared.layout.frame body)

end Solcore.Frontend.SourceCoreCallableAncestry
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreAncestryAllocationFrames
/-! Keep allocation-time callable ancestry even for a generalized principal
whose native instance bundle is Unit. One ordinary administrative frame cell
precedes each source marker. Its index is excluded from the source ledger.

The original allocator still authenticates the exact source/binder/layout.
The extra cell is emitted after the source initializer has produced its
successful value. The enclosing assembled checker validates its placement.
A decoded adjacent snapshot proves its shape, not execution history. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreAncestryAllocationFrames
open SourceInference Core
abbrev Request := SourceCoreSourceCells.Request
abbrev Allocator := SourceCoreSourceCells.Allocator
abbrev Layout := SourceCoreCallableContextFrames.Layout
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
    (ancestry : SourceCoreCallableAncestry.Prepared base)
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
  frame : SourceCoreCallableContextFrames.Frame
  exact : store[index]? = some (SourceCoreCallableContextFrames.encode layout frame)

def snapshot {layouts : SourceCoreAllocationLayouts.Prepared} {store : Store}
    (layout : Layout) (row : SourceCoreAllocationLedger.Row layouts store) : Except Error (Snapshot layout row) := do
  if preceding : row.markerIndex - 1 + 1 = row.markerIndex then
    match selected : store[row.markerIndex - 1]? with
    | none => throw (.malformedSnapshot (row.markerIndex - 1))
    | some value =>
      match decoded : SourceCoreCallableContextFrameCodec.decode layout value with
      | none => throw (.malformedSnapshot (row.markerIndex - 1))
      | some frame =>
        have same := SourceCoreCallableContextFrameCodec.decode_sound layout value frame decoded
        pure ⟨row.markerIndex - 1, preceding, frame, same ▸ selected⟩
  else throw .missingPredecessor

end Solcore.Frontend.SourceCoreAncestryAllocationFrames
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallableAncestryCache
/-! A finite table for callable ancestry metadata. Runtime lookup traverses the
finite frame and searches prepared rows; it does not substitute source types,
rewrite requirements, match schemes, resolve evidence, or evaluate source IR.

`Table` is a data carrier, not an ownership certificate. A compiler artifact
must retain both its preparation receipt and the completeness/meaning of its
rows. In particular, accepting a table's indices does not prove runtime
history, native closure code, or capture ownership. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableAncestryCache
open SourceInference TypeSystem
abbrev Frame := SourceCoreCallableContextFrames.Frame
abbrev Owner := SourceSpecialization.SpecializationKey

structure State where
  owner : Owner
  active : Substitution
  source : TypedSource
  deriving DecidableEq, Repr

structure Key where
  owner : Owner
  active : Substitution
  requirements : List (List RequirementId)
  deriving DecidableEq, Repr

def State.key (state : State) : Key :=
  ⟨state.owner, state.active, state.source.nodes.map fun
    | .expression node => node.requirements
    | .statement _ => []⟩

structure NamedEdge where
  origin : Core.Word
  destination : Nat
  deriving DecidableEq, Repr

structure LambdaEdge where
  state : Nat
  origin : Core.Word
  deriving DecidableEq, Repr

structure ViewEdge where
  state : Nat
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

def Table.viewAt? (table : Table) (state : Nat) (view target : Core.Word) : Option Nat :=
  (table.views.find? fun edge => decide (edge.state = state ∧ edge.view = view ∧ edge.target = target)).map (·.destination)

/-- `some none` is the empty frame. `none` rejects a missing transition. A
lambda transition preserves its parent's state, regardless of frame depth. -/
def Table.lookupIndex? (table : Table) : Frame → Option (Option Nat)
  | .empty => some none
  | .named origin => (table.namedAt? origin).map some
  | .lambda origin captured =>
      match table.lookupIndex? captured with
      | some (some state) => if table.lambdaAllowed state origin then some (some state) else none
      | _ => none
  | .view view target parent =>
      match table.lookupIndex? parent with
      | some (some state) => (table.viewAt? state view target).map some
      | _ => none

/-- Table-only reconstruction. With list-backed tables the time is bounded by
frame depth times the transition-table size, plus one final state lookup. No
work depends on the size of a source body or on an execution fuel budget. -/
def Table.lookup? (table : Table) (frame : Frame) : Option (Option State) :=
  match table.lookupIndex? frame with
  | none => none
  | some none => some none
  | some (some index) => (table.stateAt? index).map some

end Solcore.Frontend.SourceCoreCallableAncestryCache
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallableAncestryPrograms
/-! Own one administrative callable frame alongside source-allocation markers.
Both passes use the actual common contextual compiler and the same cached
ancestry metadata. Native entries and resumable results retain the complete
frame/marker definition suffix. Public source inputs keep the original cached
admission plan. The source heap excludes the administrative frame cell.

This factory connects Core frame execution, not source closure reconstruction
or the complete source/Core meaning theorem. Those consume its owned receipts. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableAncestryPrograms
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
  | ancestry (error : SourceCoreCallableAncestry.Error)
  deriving Repr

def discoveryRepresentation {checked : Checked} {base : Base checked}
    (ancestry : SourceCoreCallableAncestry.Prepared base) (fuel : Nat)
    (discovery : SourceCoreAllocationDiscovery.Prepared) : Representation :=
  SourceCoreAncestryAllocationFrames.representation ancestry
    (SourceCoreCallableAncestry.representation ancestry (SourceCoreCompatibleMarkedFunctions.discoveryRepresentation base fuel discovery))

def markedRepresentation {checked : Checked} {base : Base checked}
    (ancestry : SourceCoreCallableAncestry.Prepared base) (fuel : Nat) (layouts : Layouts) : Representation :=
  SourceCoreAncestryAllocationFrames.representation ancestry
    (SourceCoreCallableAncestry.representation ancestry (SourceCoreCompatibleMarkedFunctions.markedRepresentation checked fuel layouts))

def assembleCall {checked : Checked} {base : Base checked}
    (ancestry : SourceCoreCallableAncestry.Prepared base) (closures : List Core.Expr)
    (key : Key) (arguments : SourceCoreBasic.LoweredExpr) : Except Error Core.Expr := do
  let body ← (SourceCoreGeneralFunctions.assembleCall base.globals base.functions closures key arguments).mapError Error.functions
  pure (SourceCoreCallableContextFrames.allocate ancestry.layout.frame body)

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
  ancestry : SourceCoreCallableAncestry.Prepared base
  ancestryPrepared : SourceCoreCallableAncestry.prepare base = .ok ancestry
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
  let ancestry ← match accepted : SourceCoreCallableAncestry.prepare base with
    | .error error => throw (.ancestry error)
    | .ok ancestry => pure (⟨ancestry, accepted⟩ : {ancestry // SourceCoreCallableAncestry.prepare base = .ok ancestry})
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
  let body := SourceCoreCallableContextFrames.allocate prepared.ancestry.layout.frame body
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

end Solcore.Frontend.SourceCoreCallableAncestryPrograms
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallableAncestryLedger
/-! The actual frame-aware runner's typed store and source allocation ledger.
The context cell remains administrative. Decoding its finite carrier supplies
its exact shape, while ownership of the frame words and execution history
remain separate obligations. Observations never resume a checkpoint. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableAncestryLedger
open Core
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Prepared := SourceCoreCallableAncestryPrograms.Prepared
abbrev Completion {checked : Checked} (prepared : Prepared checked) :=
  SourceCoreCallableAncestryPrograms.Completion prepared
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
    Option SourceCoreCallableContextFrames.Frame :=
  (store completion)[0]? >>= SourceCoreCallableContextFrameCodec.decode prepared.ancestry.layout.frame

theorem frame_exact {checked : Checked} {prepared : Prepared checked} {completion : Completion prepared}
    {frame : SourceCoreCallableContextFrames.Frame} (decoded : frame? completion = some frame) :
    (store completion)[0]? = some (SourceCoreCallableContextFrames.encode prepared.ancestry.layout.frame frame) := by
  unfold frame? at decoded
  cases selected : (store completion)[0]? with
  | none => simp [selected] at decoded
  | some value =>
      simp only [selected] at decoded
      exact congrArg some (SourceCoreCallableContextFrameCodec.decode_sound _ value frame decoded)

end Solcore.Frontend.SourceCoreCallableAncestryLedger
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallableAncestryTemplates
/-! Snapshot-bearing lambda templates from the artifact's actual second pass.
The scanner retains its compiler equation and installed syntax. Local inverse
renaming is accepted only when reconstructing the complete expression gives
exactly the original snapshot/withFrame carrier. Nested scanning uses the
original wrapped body, so outer administrative binders are never erased from
child capture indices.

Authentication establishes exact cached code, installed globals/context slot,
finite owned frame words and world-typed source reference slots. These facts
alone are not source execution history. The source allocation ledger must still
link each native location to its recorded source binder; source-value export
must consume actual produced values from the owning runner.
-/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableAncestryTemplates
open SourceInference Core
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Prepared := SourceCoreCallableAncestryPrograms.Prepared
abbrev Scope := SourceCoreFunctions.Scope
abbrev Frame := SourceCoreCallableContextFrames.Frame

inductive Error where
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
  frame : SourceCoreCallableContextFrames.Layout
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
    (SourceCoreCallableAncestry.snapshotLambda frame source.lambda.descriptor creationReferenceIndex parameter result rawBody))
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
    template.body = SourceCoreCallableContextFrames.withFrame
      (.var (template.creationReferenceIndex + 2))
      (SourceCoreCallableContextFrames.lambdaFrame template.frame template.source.lambda.descriptor
        (.var 1) (.loadCell (.var (template.creationReferenceIndex + 2))))
      (template.rawBody.weakenAt 1) := by
  have exact := template.nativeExact.symm.trans template.carrierExact
  simpa only [SourceCoreCallableAncestry.snapshotLambda, Expr.pair.injEq, Expr.letE.injEq,
    Expr.lambda.injEq, and_self, true_and, and_true] using exact

def decode {checked : Checked} (prepared : Prepared checked) (carrier : Expr) : Except Error Template := do
  let .pair (.pair identity payload) (.word descriptor) := carrier | throw .malformedSnapshot
  if identity != .inLeft .word .unit then throw .malformedSnapshot
  let .letE (.loadCell (.var referenceIndex)) (.lambda parameter (.sum .word result) body) := payload
    | throw .malformedSnapshot
  let shiftedBody ← match frameBody? body with | some body => pure body | none => throw .malformedSnapshot
  let rawBody := removeInsertion 1 (removeInsertion 0 (removeInsertion 0 shiftedBody))
  if payload != SourceCoreCallableAncestry.snapshotLambda prepared.ancestry.layout.frame descriptor referenceIndex parameter result rawBody then
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
          (SourceCoreCallableAncestry.snapshotLambda prepared.ancestry.layout.frame source.lambda.descriptor referenceIndex parameter result rawBody))
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

structure Cache {checked : Checked} (prepared : Prepared checked) where private mk ::
  /-- Actual owned second pass, not a caller-supplied expression collection. -/
  compiled : SourceCoreCompatibleMarkedFunctions.compileClosures prepared.base
    (SourceCoreCallableAncestryPrograms.markedRepresentation prepared.ancestry prepared.fuel prepared.layouts)
    prepared.fuel = .ok prepared.secondPass.closures
  groups : List (List Template)
  scanned : (prepared.secondPass.closures.zipIdx.mapM fun (closure, index) =>
    scan prepared (SourceCoreCompatibleMarkedFunctions.scanBudget (SourceCoreLambdaTemplates.installedTemplate index closure))
      (SourceCoreLambdaTemplates.installedTemplate index closure)) = .ok groups

def Cache.templates {checked : Checked} {prepared : Prepared checked} (cache : Cache prepared) : List Template :=
  cache.groups.flatten

def prepare {checked : Checked} (prepared : Prepared checked) : Except Error (Cache prepared) :=
  match scanned : prepared.secondPass.closures.zipIdx.mapM (fun (closure, index) =>
    scan prepared (SourceCoreCompatibleMarkedFunctions.scanBudget (SourceCoreLambdaTemplates.installedTemplate index closure))
      (SourceCoreLambdaTemplates.installedTemplate index closure)) with
  | .error error => .error error
  | .ok groups => .ok ⟨prepared.secondPass.compiled, groups, scanned⟩

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
  | .view id target parent =>
      (match prepared.ancestry.views.entries.find? (fun entry => decide (entry.id = id)) with
        | none => false
        | some entry => match entry.view.selectedInstance, prepared.base.callableContext with
          | some candidate, some native =>
              entry.view.wrapsPrincipal && native.table.idAt?
                (.lambda candidate.origin.caller candidate.origin.initializer candidate.origin.substitution) == some target
          | _, _ => false) && frameOwned prepared parent

structure Snapshot {checked : Checked} (prepared : Prepared checked) (value : Core.Value) where private mk ::
  frame : Frame
  decoded : SourceCoreCallableContextFrameCodec.decode prepared.ancestry.layout.frame value = some frame
  exact : value = SourceCoreCallableContextFrames.encode prepared.ancestry.layout.frame frame
  owned : frameOwned prepared frame = true

def decodeSnapshot {checked : Checked} (prepared : Prepared checked) (value : Core.Value) :
    Except Error (Snapshot prepared value) :=
  match decoded : SourceCoreCallableContextFrameCodec.decode prepared.ancestry.layout.frame value with
  | none => .error .snapshotMalformed
  | some frame =>
      if owned : frameOwned prepared frame = true then
        .ok ⟨frame, decoded, SourceCoreCallableContextFrameCodec.decode_sound _ value frame decoded, owned⟩
      else .error .foreignFrame

def globalEnvironment {checked : Checked} (prepared : Prepared checked) : Core.Environment :=
  SourceCoreLambdaTemplates.freshGlobals prepared.base.globals 1 ++
    [.cellRef prepared.ancestry.layout.frame.type 0]

private def expectedGlobals {checked : Checked} (prepared : Prepared checked) : Except Error (List (Nat × Core.Value)) := do
  if prepared.secondPass.closures.length != prepared.base.globals.length then throw (.missingGlobal 0)
  prepared.base.globals.zipIdx.mapM fun (signature, index) => do
    let closure ← match prepared.secondPass.closures[index]? with
      | some closure => pure closure | none => throw (.missingGlobal index)
    let .lambda parameter result body := SourceCoreLambdaTemplates.installedTemplate index closure
      | throw (.globalTemplateMismatch index)
    if parameter != signature.parameterType || result != LanguageResult.resultType signature.resultType then
      throw (.globalTemplateMismatch index)
    pure (prepared.base.globals.length - index,
      .inRight .unit (.closure parameter result body (List.replicate index .unit ++ globalEnvironment prepared)))

structure Globals {checked : Checked} (prepared : Prepared checked) (store : Store) where private mk ::
  slots : List (Nat × Core.Value)
  generated : expectedGlobals prepared = .ok slots
  exact : slots.all (fun (location, value) => decide (store[location]? = some value)) = true

private def checkGlobals {checked : Checked} (prepared : Prepared checked) (store : Store) : Except Error (Globals prepared store) := do
  match generated : expectedGlobals prepared with
  | .error error => throw error
  | .ok slots =>
    if exact : slots.all (fun (location, value) => decide (store[location]? = some value)) = true then
      pure ⟨slots, generated, exact⟩
    else
      match slots.find? (fun (location, value) => decide (store[location]? != some value)) with
      | some (location, _) => throw (.globalsMismatch location)
      | none => throw (.globalsMismatch 0)

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
    let value ← match environment[index]? with
      | some value => pure value | none => throw (.missingCapture index)
    let .cellRef actual location := value | throw (.captureMismatch index)
    if actual != OptionalCell.cellType type then throw (.captureMismatch index)
    if world[location]? != some (OptionalCell.cellType type) then throw (.captureWorldMismatch location)
    if exact : environment[index]? = some (.cellRef (OptionalCell.cellType type) location) then
      if worldExact : world[location]? = some (OptionalCell.cellType type) then
        pure ⟨binder, type, index, location, member, (List.of_mem_zip member).2,
          (List.of_mem_zip member).1, exact, worldExact⟩
      else throw (.captureWorldMismatch location)
    else throw (.captureMismatch index)

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
  let globals ← checkGlobals prepared store
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

end Solcore.Frontend.SourceCoreCallableAncestryTemplates
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallableAncestryCaptures
/-! Captured native references are joined to the actual allocation ledger by
physical Core location first. Binder identity, native payload type, owner,
complete allocated context and contextual binder metadata are then checked.
Repeated recursive allocations of the same binder remain different rows.

A produced receipt retains the owning completion and an exact successful
observation. Subvalue paths cover result data only, never closure environments.
The join preserves ordered source locations after the opaque prefix. It does
not reconstruct source lambda bodies or derive ancestry history from words.
-/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableAncestryCaptures
open SourceInference Core
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Prepared := SourceCoreCallableAncestryPrograms.Prepared
abbrev Cache {checked : Checked} (prepared : Prepared checked) := SourceCoreCallableAncestryTemplates.Cache prepared
abbrev Template := SourceCoreCallableAncestryTemplates.Template
abbrev Capture := SourceCoreCallableAncestryTemplates.Capture
abbrev Authenticated {checked : Checked} {prepared : Prepared checked} (cache : Cache prepared)
    (world : StoreTyping) (store : Store) (value : Value) := SourceCoreCallableAncestryTemplates.Authenticated cache world store value
abbrev Completion {checked : Checked} (prepared : Prepared checked) := SourceCoreCallableAncestryPrograms.Completion prepared
abbrev SourceHeap := SourceCoreAllocationLedger.SourceHeap
abbrev SourceEnvironment := SourceCoreAllocationLedger.SourceEnvironment
abbrev TypedLedger := SourceCoreAllocationLedger.TypedLedger
abbrev Row := SourceCoreAllocationLedger.Row

/-- Native result paths stop at closures; captured values are not result data. -/
inductive Subvalue (value : Value) : Value → Prop where
  | root : Subvalue value value
  | pairLeft {left right : Value} (inside : Subvalue value left) : Subvalue value (.pair left right)
  | pairRight {left right : Value} (inside : Subvalue value right) : Subvalue value (.pair left right)
  | inLeft {type : Ty} {payload : Value} (inside : Subvalue value payload) : Subvalue value (.inLeft type payload)
  | inRight {type : Ty} {payload : Value} (inside : Subvalue value payload) : Subvalue value (.inRight type payload)
  | constructed {constructor : ConstructorId} {payload : Value} (inside : Subvalue value payload) :
      Subvalue value (.constructed constructor payload)

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
  observation : SourceCoreCallableAncestryLedger.store completion = store
  ordinal : Fin ledger.ledger.rows.length
  payload : Value
  payloadFound : (ledger.ledger.rows[ordinal]).payload = some payload
  subvalue : Subvalue value payload

def Stored.of_payload {checked : Checked} {prepared : Prepared checked} {cache : Cache prepared}
    {completion : Completion prepared} {world : StoreTyping} {store : Store} {value payload : Value}
    {initial : SourceHeap} {ledger : TypedLedger prepared.layouts initial world store}
    (authenticated : Authenticated cache world store value)
    (observation : SourceCoreCallableAncestryLedger.store completion = store)
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
end Solcore.Frontend.SourceCoreCallableAncestryCaptures
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallableAncestryPreparation
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
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallableAncestryPrincipalHeaders
/-! Principal closure headers are prepared for every supplied graph state.
Preparation validates the owned principal inventory and exact lambda form.
Runtime restoration selects a cached header by state index and the complete
allocation key, and retains the ledger's ordered source locations.

This module does not certify the graph's reachable-state closure or runtime
history. Its caller must supply the owning graph preparation receipt and the
actual allocation-frame lookup. No source body is evaluated or traversed while
restoring a value. A Unit native instance bundle still has a source principal.
-/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableAncestryPrincipalHeaders
open SourceInference TypeSystem
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Program := SourceCoreCallableAncestryPrograms.Prepared
abbrev Table := SourceCoreCallableAncestryCache.Table
abbrev Principal {checked : Checked} (program : Program checked) :=
  SourceCoreCallablePrincipals.Entry program.base.sourceProgram program.base.plan program.base.contexts
abbrev AllocationKey := SourceCoreAllocationLayouts.Key
abbrev SourceValue := SourceTypedRuntime.Value

def eraseRequirements (source : TypedSource) : TypedSource :=
  {source with nodes := source.nodes.map fun
    | .expression node => .expression {node with requirements := []}
    | .statement node => .statement node}

inductive Error where
  | sourceMismatch (index : Nat) (binder : Resolved.LocalId)
  | missingLambda (index : Nat) (initializer : ExpressionId)
  | lambdaMismatch (index : Nat) (initializer : ExpressionId)
  | missingHeader (index : Nat) (binder : Resolved.LocalId)
  | allocationMismatch (index : Nat) (binder : Resolved.LocalId)
  | absentPrincipal (binder : Resolved.LocalId)
  | snapshot (error : SourceCoreAncestryAllocationFrames.Error)
  | frameUnavailable (binder : Resolved.LocalId)
  deriving Repr

structure Header {checked : Checked} (program : Program checked) (table : Table) where private mk ::
  position : Fin table.states.length
  principal : Principal program
  owned : principal ∈ program.ancestry.principals.entries
  owner : (table.states[position]).owner = principal.context.owner
  active : (table.states[position]).active = principal.context.active
  sourceExact : eraseRequirements (table.states[position]).source = eraseRequirements principal.context.source
  node : ExpressionNode
  found : (table.states[position]).source.lookupExpression? principal.principal.declaration.initializer = some node
  form : node.form = .lambda principal.principal.parameters principal.principal.resultType principal.principal.body

def Header.state {checked : Checked} {program : Program checked} {table : Table}
    (header : Header program table) : SourceCoreCallableAncestryCache.State := table.states[header.position]

def Header.matches {checked : Checked} {program : Program checked} {table : Table}
    (header : Header program table) (key : AllocationKey) : Prop := header.principal.matchesLayout key
instance {checked : Checked} {program : Program checked} {table : Table}
    (header : Header program table) (key : AllocationKey) : Decidable (header.matches key) :=
  inferInstanceAs (Decidable (header.principal.matchesLayout key))

private def prepareHeader {checked : Checked} (program : Program checked) (table : Table)
    (position : Fin table.states.length) (principal : Principal program)
    (owned : principal ∈ program.ancestry.principals.entries)
    (owner : (table.states[position]).owner = principal.context.owner)
    (active : (table.states[position]).active = principal.context.active) : Except Error (Header program table) := do
  if sourceExact : eraseRequirements (table.states[position]).source = eraseRequirements principal.context.source then
    match found : (table.states[position]).source.lookupExpression? principal.principal.declaration.initializer with
    | none => throw (.missingLambda position.val principal.principal.declaration.initializer)
    | some node =>
      if form : node.form = .lambda principal.principal.parameters principal.principal.resultType principal.principal.body then
        pure ⟨position, principal, owned, owner, active, sourceExact, node, found, form⟩
      else throw (.lambdaMismatch position.val principal.principal.declaration.initializer)
  else throw (.sourceMismatch position.val principal.principal.binder.id)

private def headersAt {checked : Checked} (program : Program checked) (table : Table)
    (position : Fin table.states.length) : Except Error (List (Header program table)) := do
  let candidates ← program.ancestry.principals.entries.attach.mapM fun principal => do
    if owner : (table.states[position]).owner = principal.val.context.owner then
      if active : (table.states[position]).active = principal.val.context.active then
        let header ← prepareHeader program table position principal.val principal.property owner active
        pure [header]
      else pure []
    else pure []
  pure candidates.flatten

structure Prepared {checked : Checked} (program : Program checked) (table : Table) where private mk ::
  headers : List (Header program table)
  private collected : ∃ groups, (List.finRange table.states.length).mapM (headersAt program table) = .ok groups ∧
    headers = groups.flatten

def prepare {checked : Checked} (program : Program checked) (table : Table) : Except Error (Prepared program table) :=
  match collected : (List.finRange table.states.length).mapM (headersAt program table) with
  | .error error => .error error
  | .ok groups => .ok ⟨groups.flatten, ⟨groups, collected, rfl⟩⟩

def Prepared.headerAt? {checked : Checked} {program : Program checked} {table : Table}
    (prepared : Prepared program table) (position : Nat) (binder : Resolved.LocalId) : Option (Header program table) :=
  prepared.headers.find? fun header => decide (header.position.val = position ∧ header.principal.principal.binder.id = binder)

structure Restored {checked : Checked} {program : Program checked} {table : Table}
    (prepared : Prepared program table) (position : Nat) {store : Core.Store}
    (row : SourceCoreAllocationLedger.Row program.layouts store) where private mk ::
  header : Header program table
  selected : prepared.headerAt? position row.entry.key.binder.id = some header
  layoutMatches : header.matches row.entry.key
  value : SourceValue
  exact : value = .closure header.principal.principal.parameters header.principal.principal.resultType
    header.principal.principal.body header.state.source header.state.owner row.environment header.principal.context.evidence

/-- The state index must come from the separately owned graph lookup of the
actual allocation snapshot. This operation only selects prepared metadata. -/
def restoreAt {checked : Checked} {program : Program checked} {table : Table}
    (prepared : Prepared program table) (position : Nat) {store : Core.Store}
    (row : SourceCoreAllocationLedger.Row program.layouts store) : Except Error (Restored prepared position row) := do
  match selected : prepared.headerAt? position row.entry.key.binder.id with
  | none => throw (.missingHeader position row.entry.key.binder.id)
  | some header =>
    if layoutMatches : header.matches row.entry.key then
      pure ⟨header, selected, layoutMatches,
        .closure header.principal.principal.parameters header.principal.principal.resultType header.principal.principal.body
          header.state.source header.state.owner row.environment header.principal.context.evidence, rfl⟩
    else throw (.allocationMismatch position row.entry.key.binder.id)

theorem Restored.position_exact {checked : Checked} {program : Program checked} {table : Table}
    {prepared : Prepared program table} {position : Nat} {store : Core.Store}
    {row : SourceCoreAllocationLedger.Row program.layouts store} (restored : Restored prepared position row) :
    restored.header.position.val = position := by
  have selected := restored.selected
  simp only [Prepared.headerAt?] at selected
  have tested := List.find?_some selected
  exact (of_decide_eq_true tested).1

theorem Restored.binder_exact {checked : Checked} {program : Program checked} {table : Table}
    {prepared : Prepared program table} {position : Nat} {store : Core.Store}
    {row : SourceCoreAllocationLedger.Row program.layouts store} (restored : Restored prepared position row) :
    row.entry.key.binder = restored.header.principal.principal.binder := restored.layoutMatches.2.2

theorem Restored.binder_origin {checked : Checked} {program : Program checked} {table : Table}
    {prepared : Prepared program table} {position : Nat} {store : Core.Store}
    {row : SourceCoreAllocationLedger.Row program.layouts store} (restored : Restored prepared position row) :
    SourceCoreAllocationContexts.BinderOrigin restored.header.principal.context.compilerSource row.entry.key.binder :=
  restored.header.principal.layout_binder_origin restored.layoutMatches

theorem Restored.capture_order {checked : Checked} {program : Program checked} {table : Table}
    {prepared : Prepared program table} {position : Nat} {store : Core.Store}
    {row : SourceCoreAllocationLedger.Row program.layouts store} (_restored : Restored prepared position row) :
    row.environment.map Prod.fst = row.entry.key.scope.map Prod.fst := row.captured.binders_exact

structure AllocationRestored {checked : Checked} {program : Program checked} {table : Table}
    (prepared : Prepared program table) {store : Core.Store}
    (row : SourceCoreAllocationLedger.Row program.layouts store) where private mk ::
  payload : Core.Value
  present : row.payload = some payload
  snapshot : SourceCoreAncestryAllocationFrames.Snapshot program.ancestry.layout.frame row
  position : Nat
  selected : table.lookupIndex? snapshot.frame = some (some position)
  restored : Restored prepared position row

/-- The actual recorded frame determines the selected metadata state. An
absent optional payload is retained as absent by the heap decoder, so this
principal constructor requires an initialized allocation. -/
def restoreAllocation {checked : Checked} {program : Program checked} {table : Table}
    (prepared : Prepared program table) {store : Core.Store}
    (row : SourceCoreAllocationLedger.Row program.layouts store) : Except Error (AllocationRestored prepared row) := do
  match present : row.payload with
  | none => throw (.absentPrincipal row.entry.key.binder.id)
  | some payload =>
    let snapshot ← (SourceCoreAncestryAllocationFrames.snapshot program.ancestry.layout.frame row).mapError Error.snapshot
    match selected : table.lookupIndex? snapshot.frame with
    | some (some position) =>
      let restored ← restoreAt prepared position row
      pure ⟨payload, present, snapshot, position, selected, restored⟩
    | _ => throw (.frameUnavailable row.entry.key.binder.id)

end Solcore.Frontend.SourceCoreCallableAncestryPrincipalHeaders
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallableAncestryReadRecipes
/-! Read-time evidence and lexical source transport for generalized callables.
The caller supplies the occurrence's requirements; the stored principal
supplies the source graph to which its own substitution and witnesses apply.
Native compilation context and source substitution are separate fields.

These factories run during preparation. Their sealed receipts retain exact
owned view/template selection and the actual local-witness factory equation.
Runtime consumers select cached receipts and never invoke these factories.
Reachability, cache closure, native read snapshots, and heap provenance remain
obligations of the enclosing artifact. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableAncestryReadRecipes
open SourceInference TypeSystem
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Base := SourceCoreCompatibleFunctions.Prepared
abbrev Inputs := @SourceCoreCallableAncestryPreparation.Inputs
abbrev Metadata := SourceCoreCallableAncestryCache.State
abbrev Witness := SourceCoreLocalEvidence.Witness
abbrev View {checked : Checked} (base : Base checked) :=
  SourceCoreCallableViews.Entry base.sourceProgram base.plan

structure State where
  metadata : Metadata
  nativeActive : Substitution
  deriving DecidableEq, Repr

inductive Error where
  | unknownView (id : Core.Word)
  | unknownTarget (id : Core.Word)
  | invalidDescriptor (id : Core.Word)
  | monomorphicView (id : Core.Word)
  | wrongCaller (id : Core.Word)
  | missingRead (id : ExpressionId)
  | invalidRead (id : ExpressionId)
  | missingBinder (id : Resolved.LocalId)
  | invalidBinder (id : Resolved.LocalId)
  | unsupportedRequirements (id : ExpressionId)
  | plan (error : SourceCompilationPlan.Error)
  | substitutionMismatch (id : Core.Word)
  | wrongPrincipal (id : Core.Word)
  | missingLambda (id : ExpressionId)
  | invalidLambda (id : ExpressionId)
  | nativeHeaderMismatch (id : Core.Word)
  deriving Repr

/-- This receipt describes one read, independent of when or where the
resulting callable is applied. Its witnesses come from this exact caller. -/
structure Read {checked : Checked} {base : Base checked} (inputs : Inputs base)
    (caller : State) (id target : Core.Word) where private mk ::
  entry : View base
  selected : inputs.views.entryAt? id = some entry
  generalized : entry.view.wrapsPrincipal = true
  template : SourceCoreLambdaTemplates.Lambda
  targetSelected : inputs.templates.lambdaAt? target = some template
  descriptor : SourceCoreStageCodebook.Entry
  descriptorSelected : inputs.callable.table.entryAt? target = some descriptor
  templateOrigin : descriptor.origin = .lambda template.owner template.id template.active
  viewOrigin : descriptor.origin = .lambda entry.view.owner entry.view.principal.initializer entry.view.cumulative
  owner : caller.metadata.owner = entry.view.owner
  nativeParent : caller.nativeActive = entry.view.parentActive
  specialized : SourceSpecialization.SpecializedFunction
  specializedFound : SourceCompilationPlan.exactSpecialization base.plan caller.metadata.owner = .ok specialized
  available : SourceCompilationPlan.EvidenceEnvironment
  availableResolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment base.sourceProgram specialized.key
    specialized.assumptions = .ok available
  node : ExpressionNode
  found : caller.metadata.source.lookupExpression? entry.view.read = some node
  name : String
  reference : node.form = .reference name (.local entry.view.binding.binder.id)
  binder : TypedBinder
  detected : SourceCompilationPlan.directLambdaLetBinder? caller.metadata.source entry.view.binding.binder.id = some binder
  binderExact : binder = entry.view.binding.binder.applySubstitution caller.metadata.active
  requirements : List RequirementId
  requirementsSelected : SourceCompilationPlan.ordinaryOwnedRequirements? node = some requirements
  substitution : Substitution
  witnesses : List Witness
  factory : SourceCompilationPlan.localRequirementWitnesses specialized available binder
    {node with type := node.rawType, requirements, coercions := []} = .ok (substitution, witnesses)
  substitutionExact : substitution = entry.view.ownSubstitution

def prepareRead {checked : Checked} {base : Base checked} (inputs : Inputs base)
    (caller : State) (id target : Core.Word) : Except Error (Read inputs caller id target) := do
  match selected : inputs.views.entryAt? id with
  | none => throw (.unknownView id)
  | some entry =>
    if generalized : entry.view.wrapsPrincipal = true then
      match targetSelected : inputs.templates.lambdaAt? target with
      | none => throw (.unknownTarget target)
      | some template =>
        match descriptorSelected : inputs.callable.table.entryAt? target with
        | none => throw (.unknownTarget target)
        | some descriptor =>
          if templateOrigin : descriptor.origin = .lambda template.owner template.id template.active then
            if viewOrigin : descriptor.origin = .lambda entry.view.owner entry.view.principal.initializer entry.view.cumulative then
              if owner : caller.metadata.owner = entry.view.owner then
                if nativeParent : caller.nativeActive = entry.view.parentActive then
                  match specializedFound : SourceCompilationPlan.exactSpecialization base.plan caller.metadata.owner with
                  | .error error => throw (.plan error)
                  | .ok specialized =>
                    match availableResolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment base.sourceProgram specialized.key specialized.assumptions with
                    | .error error => throw (.plan error)
                    | .ok available =>
                    match found : caller.metadata.source.lookupExpression? entry.view.read with
                    | none => throw (.missingRead entry.view.read)
                    | some node =>
                      match reference : node.form with
                      | .reference name (.local binderId) =>
                        if same : binderId = entry.view.binding.binder.id then
                          match detected : SourceCompilationPlan.directLambdaLetBinder? caller.metadata.source entry.view.binding.binder.id with
                          | none => throw (.missingBinder entry.view.binding.binder.id)
                          | some binder =>
                            if binderExact : binder = entry.view.binding.binder.applySubstitution caller.metadata.active then
                              match requirementsSelected : SourceCompilationPlan.ordinaryOwnedRequirements? node with
                              | none => throw (.unsupportedRequirements node.id)
                              | some requirements =>
                                match factory : SourceCompilationPlan.localRequirementWitnesses specialized available binder
                                    {node with type := node.rawType, requirements, coercions := []} with
                                | .error error => throw (.plan error)
                                | .ok (substitution, witnesses) =>
                                  if substitutionExact : substitution = entry.view.ownSubstitution then
                                    pure ⟨entry, selected, generalized, template, targetSelected, descriptor, descriptorSelected,
                                      templateOrigin, viewOrigin, owner, nativeParent, specialized, specializedFound,
                                      available, availableResolved,
                                      node, found, name, by simpa only [same] using reference, binder, detected, binderExact,
                                      requirements, requirementsSelected, substitution, witnesses, factory, substitutionExact⟩
                                  else throw (.substitutionMismatch id)
                            else throw (.invalidBinder entry.view.binding.binder.id)
                        else throw (.invalidRead entry.view.read)
                      | _ => throw (.invalidRead entry.view.read)
                else throw (.wrongCaller id)
              else throw (.wrongCaller id)
            else throw (.invalidDescriptor target)
          else throw (.invalidDescriptor target)
    else throw (.monomorphicView id)

/-- Application transports the lexical source. The read caller is retained
in `read` and is never used as the replacement principal source. -/
def Read.after {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {caller : State} {id target : Core.Word} (read : Read inputs caller id target) (lexical : State) : State :=
  ⟨⟨lexical.metadata.owner, read.substitution.compose lexical.metadata.active,
    SourceTypedRuntime.rewriteLocalRequirements read.witnesses
      (lexical.metadata.source.applySubstitution read.substitution)⟩, read.entry.view.cumulative⟩

structure Applied {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {caller : State} {id target : Core.Word} (read : Read inputs caller id target) (lexical : State) where private mk ::
  owner : lexical.metadata.owner = read.entry.view.owner
  node : ExpressionNode
  found : lexical.metadata.source.lookupExpression? read.entry.view.principal.initializer = some node
  parameters : List TypedBinder
  resultType : Ty
  body : List StatementId
  shape : node.form = .lambda parameters resultType body
  nativeHeader : (ExpressionForm.lambda (parameters.map (TypedBinder.applySubstitution read.substitution))
    (read.substitution.apply resultType) body) = read.template.node.form

def applyRead {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {caller : State} {id target : Core.Word} (read : Read inputs caller id target) (lexical : State) :
    Except Error (Applied read lexical) := do
  if owner : lexical.metadata.owner = read.entry.view.owner then
    match found : lexical.metadata.source.lookupExpression? read.entry.view.principal.initializer with
    | none => throw (.missingLambda read.entry.view.principal.initializer)
    | some node =>
      match shape : node.form with
      | .lambda parameters resultType body =>
        if nativeHeader : ExpressionForm.lambda (parameters.map (TypedBinder.applySubstitution read.substitution))
            (read.substitution.apply resultType) body = read.template.node.form then
          pure ⟨owner, node, found, parameters, resultType, body, shape, nativeHeader⟩
        else throw (.nativeHeaderMismatch target)
      | _ => throw (.invalidLambda read.entry.view.principal.initializer)
  else throw (.wrongPrincipal id)

/-- Keep the observable instantiated constructor and the original lexical
header. Capture ownership must be supplied by the allocation/callable join. -/
def Applied.sourceValue {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {caller : State} {id target : Core.Word} {read : Read inputs caller id target} {lexical : State}
    (applied : Applied read lexical) (captured : SourceTypedRuntime.Environment)
    (evidence : SourceCompilationPlan.EvidenceEnvironment) : SourceTypedRuntime.Value :=
  .instantiated read.substitution read.witnesses
    (.closure applied.parameters applied.resultType applied.body lexical.metadata.source lexical.metadata.owner
      captured evidence)

theorem Read.after_native {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {caller : State} {id target : Core.Word} (read : Read inputs caller id target) (lexical : State) :
    (read.after lexical).nativeActive = read.entry.view.cumulative := rfl

theorem Read.after_source {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {caller : State} {id target : Core.Word} (read : Read inputs caller id target) (lexical : State) :
    (read.after lexical).metadata.source = SourceTypedRuntime.rewriteLocalRequirements read.witnesses
      (lexical.metadata.source.applySubstitution read.substitution) := rfl

theorem Applied.capture_order {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {caller : State} {id target : Core.Word} {read : Read inputs caller id target} {lexical : State}
    (applied : Applied read lexical) (captured : SourceTypedRuntime.Environment)
    (evidence : SourceCompilationPlan.EvidenceEnvironment) :
    applied.sourceValue captured evidence = .instantiated read.substitution read.witnesses
      (.closure applied.parameters applied.resultType applied.body lexical.metadata.source lexical.metadata.owner
        captured evidence) := rfl

end Solcore.Frontend.SourceCoreCallableAncestryReadRecipes
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallableAncestryReadViews
/-! Exact emitted generalized-read wrappers. The wrapper's original carrier
is retained in saved slot zero, with the same anonymous identity and contract
ID. It is authenticated against actual snapshot templates before its captures
are joined to source allocation rows.

The cached read's parent/principal, own substitution/witnesses and cumulative
native instance remain separate. This unit never collapses an instantiated
source value to a ground closure. Dynamic principal headers must additionally
be selected by the authenticated snapshot's prepared ancestry table.
-/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableAncestryReadViews
open SourceInference Core
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Prepared := SourceCoreCallableAncestryPrograms.Prepared
abbrev Templates {checked : Checked} (prepared : Prepared checked) := SourceCoreCallableAncestryTemplates.Cache prepared
abbrev Instance := SourceCoreLocalPolymorphism.Instance
abbrev Completion {checked : Checked} (prepared : Prepared checked) := SourceCoreCallableAncestryPrograms.Completion prepared
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
  | underlying (error : SourceCoreCallableAncestryTemplates.Error)
  | captures (error : SourceCoreCallableAncestryCaptures.Error)
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
  bodyExact : body = SourceCoreCallableAncestry.viewBody prepared.ancestry.layout.frame entry.id target referenceIndex
  carrierExact : carrier = SourceCoreCallableAncestry.viewRepack prepared.ancestry.layout.frame
    parameter result entry.id target referenceIndex

def decode {checked : Checked} (prepared : Prepared checked) (carrier : Expr) : Except Error (Template prepared) := do
  let .pair (.pair _ (.lambda parameter (.sum .word result) body)) _ := carrier | throw .malformedWrapper
  let (index, constructor, id, target) ← match bodyHeader? body with
    | some header => pure header | none => throw .malformedWrapper
  if index < 2 || constructor != prepared.ancestry.layout.frame.view then throw .malformedWrapper
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
            let referenceIndex := index - 2
            if bodyExact : body = SourceCoreCallableAncestry.viewBody prepared.ancestry.layout.frame entry.id target referenceIndex then
              if carrierExact : carrier = SourceCoreCallableAncestry.viewRepack prepared.ancestry.layout.frame parameter result entry.id target referenceIndex then
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
      (SourceCoreCallableAncestryPrograms.markedRepresentation prepared.ancestry prepared.fuel prepared.layouts)
      prepared.fuel = .ok prepared.secondPass.closures := templates.compiled

def prepare {checked : Checked} {prepared : Prepared checked} (templates : Templates prepared) : Except Error (Cache templates) :=
  match scanned : prepared.secondPass.closures.zipIdx.mapM (fun (closure, index) =>
    scan prepared (SourceCoreCompatibleMarkedFunctions.scanBudget (SourceCoreLambdaTemplates.installedTemplate index closure))
      (SourceCoreLambdaTemplates.installedTemplate index closure)) with
  | .error error => .error error
  | .ok groups => .ok ⟨groups, scanned⟩

private theorem original_typed {definitions : DataEnvironment} {world : StoreTyping}
    {identity original : Value} {outer : Environment} {body : Expr} {descriptor : Word} {parameter result : Ty}
    (typed : RuntimeValueHasType world (.pair (.pair identity
      (.closure parameter (LanguageResult.resultType result) body (original :: outer))) (.word descriptor))
      (CallableContract.functionType parameter result) definitions) :
    RuntimeValueHasType world original original.type definitions := by
  cases typed with
  | pair tagged _ =>
    cases tagged with
    | pair _ payload =>
      cases payload with
      | closure environment _ =>
        cases environment with
        | cons originalTyped _ =>
          rw [originalTyped.type_eq]
          exact originalTyped

structure Authenticated {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    (cache : Cache templates) (world : StoreTyping) (store : Store) (value : Value) where private mk ::
  wrapper : Template prepared
  member : wrapper ∈ cache.wrappers
  original : Value
  outer : Environment
  exact : value = .pair (.pair (.inLeft .word .unit)
    (.closure wrapper.parameter (LanguageResult.resultType wrapper.result) wrapper.body (original :: outer))) (.word wrapper.target)
  typed : RuntimeValueHasType world value (CallableContract.functionType wrapper.parameter wrapper.result) prepared.layouts.definitions
  originalTyped : RuntimeValueHasType world original (CallableContract.functionType wrapper.parameter wrapper.result) prepared.layouts.definitions
  underlying : SourceCoreCallableAncestryTemplates.Authenticated templates world store original
  targetExact : underlying.template.source.lambda.descriptor = wrapper.target
  originExact : underlying.template.source.lambda.owner = wrapper.entry.view.owner ∧
    underlying.template.source.lambda.id = wrapper.entry.view.binding.initializer ∧
    underlying.template.source.lambda.active = wrapper.entry.view.cumulative
  contextSlot : (original :: outer)[wrapper.referenceIndex + 1]? =
    some (.cellRef prepared.ancestry.layout.frame.type 0)

def authenticate {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    (cache : Cache templates) {world : StoreTyping} {store : Store}
    (stored : RuntimeStoreHasTypes world store prepared.layouts.definitions) (value : Value) (parameter result : Ty)
    (typed : RuntimeValueHasType world value (CallableContract.functionType parameter result) prepared.layouts.definitions) :
    Except Error (Authenticated cache world store value) := do
  let .pair (.pair (.inLeft .word .unit) (.closure _ _ body (original :: outer))) (.word descriptor) := value
    | throw .closureMismatch
  let chosen ← match cache.wrappers.attach.find? (fun wrapper => decide
      (wrapper.val.body = body ∧ wrapper.val.parameter = parameter ∧ wrapper.val.result = result ∧ wrapper.val.target = descriptor)) with
    | none => throw .closureMismatch | some wrapper => pure wrapper
  let wrapper := chosen.val
  if types : wrapper.parameter = parameter ∧ wrapper.result = result then
    if exact : value = .pair (.pair (.inLeft .word .unit)
        (.closure wrapper.parameter (LanguageResult.resultType wrapper.result) wrapper.body (original :: outer))) (.word wrapper.target) then
      have typedWrapper : RuntimeValueHasType world value (CallableContract.functionType wrapper.parameter wrapper.result) prepared.layouts.definitions := by
        simpa only [types.1, types.2] using typed
      have originalOwn : RuntimeValueHasType world original original.type prepared.layouts.definitions :=
        original_typed (exact ▸ typedWrapper)
      if originalType : original.type = CallableContract.functionType wrapper.parameter wrapper.result then
        have originalTyped : RuntimeValueHasType world original (CallableContract.functionType wrapper.parameter wrapper.result) prepared.layouts.definitions :=
          originalType ▸ originalOwn
        let underlying ← (SourceCoreCallableAncestryTemplates.authenticate templates stored original wrapper.parameter wrapper.result originalTyped)
          |>.mapError Error.underlying
        if targetExact : underlying.template.source.lambda.descriptor = wrapper.target then
          if originExact : underlying.template.source.lambda.owner = wrapper.entry.view.owner ∧
              underlying.template.source.lambda.id = wrapper.entry.view.binding.initializer ∧
              underlying.template.source.lambda.active = wrapper.entry.view.cumulative then
            if contextSlot : (original :: outer)[wrapper.referenceIndex + 1]? = some (.cellRef prepared.ancestry.layout.frame.type 0) then
              pure ⟨wrapper, chosen.property, original, outer, exact, typedWrapper, originalTyped,
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
  subvalue : SourceCoreCallableAncestryCaptures.Subvalue value result

def Produced.of_success {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : StoreTyping} {store : Store} {value result : Value}
    {authenticated : Authenticated cache world store value} {completion : Completion prepared}
    (observation : completion.result.native.observation = .succeeded result store)
    (subvalue : SourceCoreCallableAncestryCaptures.Subvalue value result) : Produced authenticated completion :=
  ⟨result, observation, subvalue⟩

structure Stored {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : StoreTyping} {store : Store} {value : Value}
    (authenticated : Authenticated cache world store value) (completion : Completion prepared)
    {initial : SourceHeap} (ledger : TypedLedger prepared.layouts initial world store) where private mk ::
  observation : SourceCoreCallableAncestryLedger.store completion = store
  ordinal : Fin ledger.ledger.rows.length
  payload : Value
  payloadFound : (ledger.ledger.rows[ordinal]).payload = some payload
  subvalue : SourceCoreCallableAncestryCaptures.Subvalue value payload

def Stored.of_payload {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : StoreTyping} {store : Store} {value payload : Value}
    {authenticated : Authenticated cache world store value} {completion : Completion prepared}
    {initial : SourceHeap} {ledger : TypedLedger prepared.layouts initial world store}
    (observation : SourceCoreCallableAncestryLedger.store completion = store) (ordinal : Fin ledger.ledger.rows.length)
    (payloadFound : (ledger.ledger.rows[ordinal]).payload = some payload)
    (subvalue : SourceCoreCallableAncestryCaptures.Subvalue value payload) : Stored authenticated completion ledger :=
  ⟨observation, ordinal, payload, payloadFound, subvalue⟩

structure JoinedProduced {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : StoreTyping} {store : Store} {value : Value}
    {authenticated : Authenticated cache world store value} {completion : Completion prepared}
    (produced : Produced authenticated completion) {initial : SourceHeap}
    (ledger : TypedLedger prepared.layouts initial world store) where private mk ::
  captures : SourceCoreCallableAncestryCaptures.Captured authenticated.underlying ledger

structure JoinedStored {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : StoreTyping} {store : Store} {value : Value}
    {authenticated : Authenticated cache world store value} {completion : Completion prepared}
    {initial : SourceHeap} {ledger : TypedLedger prepared.layouts initial world store}
    (stored : Stored authenticated completion ledger) where private mk ::
  captures : SourceCoreCallableAncestryCaptures.Captured authenticated.underlying ledger

def joinProduced {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : StoreTyping} {store : Store} {value : Value}
    {authenticated : Authenticated cache world store value} {completion : Completion prepared}
    (produced : Produced authenticated completion) {initial : SourceHeap}
    (ledger : TypedLedger prepared.layouts initial world store) : Except Error (JoinedProduced produced ledger) := do
  let captures ← (SourceCoreCallableAncestryCaptures.joinAuthenticated authenticated.underlying ledger).mapError Error.captures
  pure ⟨captures⟩

def joinStored {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : StoreTyping} {store : Store} {value : Value}
    {authenticated : Authenticated cache world store value} {completion : Completion prepared}
    {initial : SourceHeap} {ledger : TypedLedger prepared.layouts initial world store}
    (stored : Stored authenticated completion ledger) : Except Error (JoinedStored stored) := do
  let captures ← (SourceCoreCallableAncestryCaptures.joinAuthenticated authenticated.underlying ledger).mapError Error.captures
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

end Solcore.Frontend.SourceCoreCallableAncestryReadViews
end
