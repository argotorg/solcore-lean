import Solcore.Frontend.SourceCore.Internal.Carriers
import Solcore.Frontend.SourceCore.Internal.CallablePaired
import Solcore.Frontend.SourceCore.Internal.CallableViews
import Solcore.Frontend.SourceCore.Internal.CallablePrincipals
import Solcore.Frontend.SourceCore.Internal.Allocation

/-!
# Indexed callable ancestry

Constant-depth ancestry over a finite table: dispatch, programs, templates, captures, views and
restoration.
-/

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallableIndexedDispatch
/-! Finite, table-derived ordinary Core dispatch for indexed ancestry.
Generated expressions compare only native scalar IDs. The owned preparation
table retains all source metadata and read/application recipes; runtime
dispatch neither traverses source IR nor reconstructs a recursive frame.

An invalid carrier is a failed administrative lookup, not authenticated source
history and not a language failure. The execution adapter must reject it.
-/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableIndexedDispatch
open Core SourceCoreCallableIndexedFrames
abbrev Frame := SourceCoreCallableIndexedFrames.Frame
abbrev Table := SourceCoreCallableAncestryPairedCache.Table
abbrev State := SourceCoreCallableAncestryPairedCache.State
abbrev LambdaEdge := SourceCoreCallableAncestryPairedCache.LambdaEdge
abbrev ViewEdge := SourceCoreCallableAncestryPairedCache.ViewEdge
abbrev Graph := @SourceCoreCallableAncestryPairedPreparation.Prepared

def lookup? (table : Table) : Frame → Option (Option State)
  | .empty => some none
  | .state index => do
      let position ← naturalIndex? index
      let state ← table.stateAt? position
      pure (some state)
  | .view .. | .invalid => none

def checkedState (table : Table) (position : Nat) : Frame :=
  if (table.stateAt? position).isSome then .state (Int.ofNat position) else .invalid

def namedFrame (table : Table) (origin : Word) : Frame :=
  match table.namedAt? origin with
  | none => .invalid
  | some position => checkedState table position

def plainRows (table : Table) (origin : Word) (lexical : Int) : List LambdaEdge → Frame
  | [] => .invalid
  | edge :: rest =>
    if edge.origin = origin ∧ lexical = Int.ofNat edge.state then checkedState table edge.state
    else plainRows table origin lexical rest

def viewRows (table : Table) (origin id : Word) (caller lexical : Int) : List ViewEdge → Frame
  | [] => .invalid
  | edge :: rest =>
    if edge.target = origin ∧ edge.view = id ∧ caller = Int.ofNat edge.caller ∧ lexical = Int.ofNat edge.lexical then
      checkedState table edge.destination
    else viewRows table origin id caller lexical rest

def selectedFrame (table : Table) (origin : Word) (lexical current : Frame) : Frame :=
  match lexical with
  | .state index =>
    match current with
    | .view id target caller =>
      if target = origin then viewRows table origin id caller index table.views
      else plainRows table origin index table.lambdas
    | _ => plainRows table origin index table.lambdas
  | _ => .invalid

def literal (layout : Layout) : Frame → Expr
  | .empty => empty layout
  | .state index => state layout (.integer index)
  | .view id target caller => view layout id target (.integer caller)
  | .invalid => invalid layout

theorem literal_hasType {definitions : DataEnvironment} {layout : Layout} (context : Context)
    (registered : layout.Registered definitions) (frame : Frame) :
    HasType context (literal layout frame) layout.type definitions := by
  cases frame with
  | empty => exact empty_hasType context registered
  | state index => exact state_hasType registered .integer
  | view id target caller => exact view_hasType registered id target .integer
  | invalid => exact invalid_hasType context registered

def plainDispatch (table : Table) (layout : Layout) (origin : Word) (lexical : Expr) : List LambdaEdge → Expr
  | [] => invalid layout
  | edge :: rest =>
    if edge.origin = origin then
      .ifE (.binary .integerEq lexical (.integer (Int.ofNat edge.state)))
        (literal layout (checkedState table edge.state)) (plainDispatch table layout origin lexical rest)
    else plainDispatch table layout origin lexical rest

def viewDispatch (table : Table) (layout : Layout) (origin : Word) (id caller lexical : Expr) : List ViewEdge → Expr
  | [] => invalid layout
  | edge :: rest =>
    let tail := viewDispatch table layout origin id caller lexical rest
    if edge.target = origin then
      .ifE
        (.ifE (.binary .wordEq id (.word edge.view))
          (.ifE (.binary .integerEq caller (.integer (Int.ofNat edge.caller)))
            (.binary .integerEq lexical (.integer (Int.ofNat edge.lexical))) (.bool false)) (.bool false))
        (literal layout (checkedState table edge.destination)) tail
    else tail

/-- The lexical snapshot is decoded once. A matching transient view joins its
read-time caller index with that lexical index using the cached paired edges.
Other incoming frames use only an authenticated ordinary lambda edge. -/
def lambdaFrame (table : Table) (layout : Layout) (origin : Word) (lexical current : Expr) : Expr :=
  let plain := plainDispatch table layout origin (.var 1) table.lambdas
  .matchData layout.dataType layout.type lexical
    [invalid layout,
      .matchData layout.dataType layout.type (current.weakenAt 0)
        [plain, plain,
          .ifE (.binary .wordEq (.first (.second (.var 0))) (.word origin))
            (viewDispatch table layout origin (.first (.var 0)) (.second (.second (.var 0))) (.var 1) table.views)
            plain,
          plain],
      invalid layout, invalid layout]

/-- A read retains the current state index as a transient caller snapshot.
Empty/invalid/transient carriers cannot authenticate a source read context. -/
def readView (layout : Layout) (id target : Word) (current : Expr) : Expr :=
  .matchData layout.dataType layout.type current
    [invalid layout, view layout id target (.var 0), invalid layout, invalid layout]

def readFrame (id target : Word) : Frame → Frame
  | .state index => .view id target index
  | _ => .invalid

private theorem atFront {definitions : DataEnvironment} {context : Context} {expression : Expr} {type : Ty}
    (typed : HasType context expression type definitions) (inserted : Ty) :
    HasType (inserted :: context) (expression.weakenAt 0) type definitions := by
  simpa [Context.insertAt] using typed.weakenAt (inserted := inserted) 0

theorem plainDispatch_hasType {definitions : DataEnvironment} {layout : Layout} {context : Context}
    (registered : layout.Registered definitions) (table : Table) (origin : Word) {lexical : Expr}
    (typed : HasType context lexical .integer definitions) (rows : List LambdaEdge) :
    HasType context (plainDispatch table layout origin lexical rows) layout.type definitions := by
  induction rows with
  | nil => exact invalid_hasType context registered
  | cons edge rest ih =>
    simp only [plainDispatch]
    split
    · exact .ifE (.binary typed .integer) (literal_hasType context registered _) ih
    · exact ih

theorem viewDispatch_hasType {definitions : DataEnvironment} {layout : Layout} {context : Context}
    (registered : layout.Registered definitions) (table : Table) (origin : Word) {id caller lexical : Expr}
    (idTyped : HasType context id .word definitions)
    (callerTyped : HasType context caller .integer definitions)
    (lexicalTyped : HasType context lexical .integer definitions) (rows : List ViewEdge) :
    HasType context (viewDispatch table layout origin id caller lexical rows) layout.type definitions := by
  induction rows with
  | nil => exact invalid_hasType context registered
  | cons edge rest ih =>
    simp only [viewDispatch]
    split
    · exact .ifE (.ifE (.binary idTyped .word)
        (.ifE (.binary callerTyped .integer) (.binary lexicalTyped .integer) .bool) .bool)
        (literal_hasType context registered _) ih
    · exact ih

theorem lambdaFrame_hasType {definitions : DataEnvironment} {layout : Layout} {context : Context}
    (registered : layout.Registered definitions) (table : Table) (origin : Word) {lexical current : Expr}
    (lexicalTyped : HasType context lexical layout.type definitions)
    (currentTyped : HasType context current layout.type definitions) :
    HasType context (lambdaFrame table layout origin lexical current) layout.type definitions := by
  apply HasType.matchData registered.lookup registered.typeWellFormed lexicalTyped
  apply BranchesHaveType.cons (invalid_hasType _ registered)
  apply BranchesHaveType.cons
  · apply HasType.matchData registered.lookup registered.typeWellFormed (atFront currentTyped .integer)
    apply BranchesHaveType.cons (plainDispatch_hasType registered table origin (.var rfl) _)
    apply BranchesHaveType.cons (plainDispatch_hasType registered table origin (.var rfl) _)
    apply BranchesHaveType.cons
    · exact .ifE (.binary (.first (.second (.var rfl))) .word)
        (viewDispatch_hasType registered table origin (.first (.var rfl))
          (.second (.second (.var rfl))) (.var rfl) _)
        (plainDispatch_hasType registered table origin (.var rfl) _)
    · exact .cons (plainDispatch_hasType registered table origin (.var rfl) _) .nil
  · exact .cons (invalid_hasType _ registered) (.cons (invalid_hasType _ registered) .nil)

theorem readView_hasType {definitions : DataEnvironment} {layout : Layout} {context : Context}
    (registered : layout.Registered definitions) (id target : Word) {current : Expr}
    (typed : HasType context current layout.type definitions) :
    HasType context (readView layout id target current) layout.type definitions := by
  apply HasType.matchData registered.lookup registered.typeWellFormed typed
  exact .cons (invalid_hasType _ registered) (.cons (view_hasType registered id target (.var rfl))
    (.cons (invalid_hasType _ registered) (.cons (invalid_hasType _ registered) .nil)))

/-- This sealed recipe points to the existing checked metadata preparation.
It adds no independent source evidence and does not rebuild the graph. -/
structure Dispatch {checked : SourceCoreCompatibleCatalog.Checked}
    {base : SourceCoreCompatibleFunctions.Prepared checked} (graph : Graph base) where private mk ::
  table : Table
  tableOwner : table = graph.table

def prepare {checked : SourceCoreCompatibleCatalog.Checked}
    {base : SourceCoreCompatibleFunctions.Prepared checked} (graph : Graph base) : Dispatch graph :=
  ⟨graph.table, rfl⟩

end Solcore.Frontend.SourceCoreCallableIndexedDispatch
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallableIndexedAncestry
/-! Actual compiler hooks for constant-depth indexed callable ancestry.
The finite metadata graph is prepared before execution. Lambda creation and
read creation save scalar-state carriers separately; their application selects
an owned cached paired edge using ordinary Core dispatch. Manifests, source
allocations and native inputs keep the existing common compiler ABI.

This unit owns preparation and emission equations. It does not authenticate
arbitrary closure outputs or infer execution history from a numeric index. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableIndexedAncestry
open SourceInference Core
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Base := SourceCoreCompatibleFunctions.Prepared
abbrev Key := SourceSpecialization.SpecializationKey
abbrev Active := TypeSystem.Substitution
abbrev Scope := SourceCoreFunctions.Scope
abbrev Frames := SourceCoreCallableIndexedFrames.Frame

inductive Error where
  | graph (error : SourceCoreCallableAncestryPairedPreparation.Error)
  | invalidNamed (origin : Word)
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
  frame : SourceCoreCallableIndexedFrames.Layout
  atEnd : frame.dataType.index = ambient.length
  definitionsTyped : (ambient ++ [frame.definition]).WellFormed

def Layout.definitions (layout : Layout) : DataEnvironment := layout.ambient ++ [layout.frame.definition]
def Layout.referenceType (layout : Layout) : Ty := .cell layout.frame.type

def Layout.prepare (ambient : DataEnvironment) : Except Error Layout :=
  let frame : SourceCoreCallableIndexedFrames.Layout := ⟨⟨ambient.length⟩⟩
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
def snapshotLambda (table : SourceCoreCallableIndexedDispatch.Table) (layout : SourceCoreCallableIndexedFrames.Layout) (origin : Word)
    (referenceIndex : Nat) (parameter result : Ty) (body : Expr) : Expr :=
  .letE (.loadCell (.var referenceIndex))
    (.lambda parameter (LanguageResult.resultType result)
      (SourceCoreCallableIndexedFrames.withFrame (.var (referenceIndex + 2))
        (SourceCoreCallableIndexedDispatch.lambdaFrame table layout origin (.var 1)
          (.loadCell (.var (referenceIndex + 2)))) (body.weakenAt 1)))

theorem snapshotLambda_hasType {definitions : DataEnvironment} {layout : SourceCoreCallableIndexedFrames.Layout}
    {context : Core.Context} {parameter result : Ty} {body : Expr} {referenceIndex : Nat}
    (registered : layout.Registered definitions) (table : SourceCoreCallableIndexedDispatch.Table) (origin : Word)
    (parameterWF : parameter.WellFormed definitions) (resultWF : result.WellFormed definitions)
    (reference : context[referenceIndex]? = some (.cell layout.type))
    (bodyTyped : HasType (parameter :: context) body (LanguageResult.resultType result) definitions) :
    HasType context (snapshotLambda table layout origin referenceIndex parameter result body)
      (.function parameter (LanguageResult.resultType result)) definitions := by
  apply HasType.letE (.loadCell (.var reference))
  apply HasType.lambda parameterWF (LanguageResult.resultType_wellFormed resultWF)
  apply SourceCoreCallableContextFrames.withFrame_hasType
  · exact .var (by simpa [Nat.add_assoc] using reference)
  · apply SourceCoreCallableIndexedDispatch.lambdaFrame_hasType registered table origin (.var rfl)
    exact .loadCell (.var (by simpa [Nat.add_assoc] using reference))
  · simpa [Context.insertAt] using bodyTyped.weakenAt (inserted := layout.type) 1

/-- Creation reads only the administrative cell and captures its exact finite
value. Application semantics use the existing `withFrame` laws. -/
theorem snapshotLambda_evaluates {layout : SourceCoreCallableIndexedFrames.Layout}
    {environment : Environment} {store : Store} {parameter result : Ty} {body : Expr}
    {referenceIndex location : Nat} {snapshot : Core.Value} (table : SourceCoreCallableIndexedDispatch.Table) (origin : Word)
    (reference : environment[referenceIndex]? = some (.cellRef layout.type location))
    (read : store.read? location = some snapshot) :
    Evaluates environment store (snapshotLambda table layout origin referenceIndex parameter result body)
      (.closure parameter (LanguageResult.resultType result)
        (SourceCoreCallableIndexedFrames.withFrame (.var (referenceIndex + 2))
          (SourceCoreCallableIndexedDispatch.lambdaFrame table layout origin (.var 1)
            (.loadCell (.var (referenceIndex + 2)))) (body.weakenAt 1))
        (snapshot :: environment)) store :=
  .letE (.loadCell (.var reference) read) .lambda

/-- Saved slot zero is the read-time caller frame; saved slot one is the
original carrier. The lambda argument adds a leading slot on application. -/
def viewBody (layout : SourceCoreCallableIndexedFrames.Layout) (id target : Word)
    (referenceIndex : Nat) : Expr :=
  SourceCoreCallableIndexedFrames.withFrame (.var (referenceIndex + 3))
    (SourceCoreCallableIndexedDispatch.readView layout id target (.var 1))
    (.apply (.second (.first (.var 2))) (.var 0))

def viewRepack (layout : SourceCoreCallableIndexedFrames.Layout) (parameter result : Ty)
    (id target : Word) (referenceIndex : Nat) : Expr :=
  .pair (.pair (.first (.first (.var 1)))
    (.lambda parameter (LanguageResult.resultType result) (viewBody layout id target referenceIndex)))
    (.second (.var 1))

/-- Snapshot is taken after the successful read, before returning its value.
A later named caller cannot replace the occurrence's witness context. -/
def viewLower (layout : SourceCoreCallableIndexedFrames.Layout) (parameter result : Ty)
    (id target : Word) (referenceIndex : Nat) (read : Expr) : Expr :=
  LanguageResult.bind (CallableContract.functionType parameter result) read
    (.letE (.loadCell (.var (referenceIndex + 1)))
      (LanguageResult.success (viewRepack layout parameter result id target referenceIndex)))

theorem viewRepack_hasType {definitions : DataEnvironment} {layout : SourceCoreCallableIndexedFrames.Layout}
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
    · exact SourceCoreCallableIndexedDispatch.readView_hasType registered id target (.var rfl)
    · exact .apply (.second (.first (.var rfl))) (.var rfl)
  · exact .second (.var rfl)

theorem viewLower_hasType {definitions : DataEnvironment} {layout : SourceCoreCallableIndexedFrames.Layout}
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
theorem viewLower_failure {layout : SourceCoreCallableIndexedFrames.Layout} {environment : Environment}
    {before after : Store} {read : Expr} {parameter result : Ty} {id target reason : Word} {referenceIndex : Nat}
    (evaluated : Evaluates environment before read
      (.inLeft (CallableContract.functionType parameter result) (.word reason)) after) :
    Evaluates environment before (viewLower layout parameter result id target referenceIndex read)
      (.inLeft (CallableContract.functionType parameter result) (.word reason)) after :=
  LanguageResult.bind_failure (CallableContract.functionType parameter result) evaluated

/-- Successful creation captures the exact read-time frame and original
carrier. It adds no cells and preserves the read's final store. -/
theorem viewLower_evaluates {layout : SourceCoreCallableIndexedFrames.Layout} {environment : Environment}
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
  graph : SourceCoreCallableAncestryPairedPreparation.Prepared base
  graphPrepared : SourceCoreCallableAncestryPairedPreparation.prepare base = .ok graph
  dispatch : SourceCoreCallableIndexedDispatch.Dispatch graph
  principals : SourceCoreCallablePrincipals.Table base.sourceProgram base.plan base.contexts
  principalsPrepared : SourceCoreCallablePrincipals.prepare base = .ok principals

def Prepared.views {checked : Checked} {base : Base checked} (prepared : Prepared base) := prepared.graph.inputs.views
def Prepared.templates {checked : Checked} {base : Base checked} (prepared : Prepared base) := prepared.graph.inputs.templates

def prepare {checked : Checked} (base : Base checked) : Except Error (Prepared base) := do
  let layout ← match accepted : Layout.prepare checked.catalog.definitions with
    | .error error => throw error
    | .ok layout => pure (⟨layout, accepted⟩ : {layout // Layout.prepare checked.catalog.definitions = .ok layout})
  let graph ← match accepted : SourceCoreCallableAncestryPairedPreparation.prepare base with
    | .error error => throw (.graph error)
    | .ok graph => pure (⟨graph, accepted⟩ : {graph // SourceCoreCallableAncestryPairedPreparation.prepare base = .ok graph})
  let principals ← match accepted : SourceCoreCallablePrincipals.prepare base with
    | .error error => throw (.principals error)
    | .ok principals => pure (⟨principals, accepted⟩ : {principals // SourceCoreCallablePrincipals.prepare base = .ok principals})
  pure ⟨layout.val, layout.property, graph.val, graph.property,
    SourceCoreCallableIndexedDispatch.prepare graph.val, principals.val, principals.property⟩

private def fail (error : Error) : SourceCoreBasic.Error := .sourceAllocation (reprStr error)

def originId {checked : Checked} {base : Base checked} (prepared : Prepared base)
    (origin : SourceCoreStageCodebook.Origin) : Except SourceCoreBasic.Error Word := do
  let native := prepared.graph.inputs.callable
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
  pure (snapshotLambda prepared.dispatch.table prepared.layout.frame origin (creationReferenceIndex context scope) parameter result body)

def namedBody {checked : Checked} {base : Base checked} (prepared : Prepared base)
    (function : SourceCoreGeneralFunctions.Function) (body : Expr) : Except SourceCoreBasic.Error Expr := do
  let origin ← originId prepared (.named function.signature.key)
  let selected := SourceCoreCallableIndexedDispatch.namedFrame prepared.dispatch.table origin
  match selected with
  | .state _ => pure (SourceCoreCallableIndexedFrames.withFrame (.var (base.globals.length + 1))
      (SourceCoreCallableIndexedDispatch.literal prepared.layout.frame selected) body)
  | _ => throw (fail (.invalidNamed origin))

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
  pure (SourceCoreCallableIndexedFrames.allocate prepared.layout.frame body)

end Solcore.Frontend.SourceCoreCallableIndexedAncestry
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallableIndexedAllocationFrames
/-! Keep allocation-time indexed callable ancestry even for a generalized principal
whose native instance bundle is Unit. One ordinary administrative indexed-frame cell
precedes each source marker. Its index is excluded from the source ledger.

The original allocator still authenticates the exact source/binder/layout.
The extra cell is emitted after the source initializer has produced its
successful value. The enclosing assembled checker validates its placement.
A decoded adjacent snapshot proves its shape, not execution history. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableIndexedAllocationFrames
open SourceInference Core
abbrev Request := SourceCoreSourceCells.Request
abbrev Allocator := SourceCoreSourceCells.Allocator
abbrev Layout := SourceCoreCallableIndexedFrames.Layout
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
    (ancestry : SourceCoreCallableIndexedAncestry.Prepared base)
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
  frame : SourceCoreCallableIndexedFrames.Frame
  exact : store[index]? = some (SourceCoreCallableIndexedFrames.encode layout frame)

def snapshot {layouts : SourceCoreAllocationLayouts.Prepared} {store : Store}
    (layout : Layout) (row : SourceCoreAllocationLedger.Row layouts store) : Except Error (Snapshot layout row) := do
  if preceding : row.markerIndex - 1 + 1 = row.markerIndex then
    match selected : store[row.markerIndex - 1]? with
    | none => throw (.malformedSnapshot (row.markerIndex - 1))
    | some value =>
      match decoded : SourceCoreCallableIndexedFrames.decode layout value with
      | none => throw (.malformedSnapshot (row.markerIndex - 1))
      | some frame =>
        have same := SourceCoreCallableIndexedFrames.decode_sound layout value frame decoded
        pure ⟨row.markerIndex - 1, preceding, frame, same ▸ selected⟩
  else throw .missingPredecessor

end Solcore.Frontend.SourceCoreCallableIndexedAllocationFrames
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallableIndexedPrograms
/-! Own one administrative indexed callable frame alongside source-allocation markers.
Both passes use the actual common contextual compiler and the same cached
finite metadata graph. Native entries and resumable results retain the complete
frame/marker definition suffix. Public source inputs keep the original cached
admission plan. The source heap excludes the administrative frame cell.

This factory connects Core frame execution, not source closure reconstruction
or the complete source/Core meaning theorem. Those consume its owned receipts. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableIndexedPrograms
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
  | ancestry (error : SourceCoreCallableIndexedAncestry.Error)
  deriving Repr

def discoveryRepresentation {checked : Checked} {base : Base checked}
    (ancestry : SourceCoreCallableIndexedAncestry.Prepared base) (fuel : Nat)
    (discovery : SourceCoreAllocationDiscovery.Prepared) : Representation :=
  SourceCoreCallableIndexedAllocationFrames.representation ancestry
    (SourceCoreCallableIndexedAncestry.representation ancestry (SourceCoreCompatibleMarkedFunctions.discoveryRepresentation base fuel discovery))

def markedRepresentation {checked : Checked} {base : Base checked}
    (ancestry : SourceCoreCallableIndexedAncestry.Prepared base) (fuel : Nat) (layouts : Layouts) : Representation :=
  SourceCoreCallableIndexedAllocationFrames.representation ancestry
    (SourceCoreCallableIndexedAncestry.representation ancestry (SourceCoreCompatibleMarkedFunctions.markedRepresentation checked fuel layouts))

def assembleCall {checked : Checked} {base : Base checked}
    (ancestry : SourceCoreCallableIndexedAncestry.Prepared base) (closures : List Core.Expr)
    (key : Key) (arguments : SourceCoreBasic.LoweredExpr) : Except Error Core.Expr := do
  let body ← (SourceCoreGeneralFunctions.assembleCall base.globals base.functions closures key arguments).mapError Error.functions
  pure (SourceCoreCallableIndexedFrames.allocate ancestry.layout.frame body)

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
  ancestry : SourceCoreCallableIndexedAncestry.Prepared base
  ancestryPrepared : SourceCoreCallableIndexedAncestry.prepare base = .ok ancestry
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
  let ancestry ← match accepted : SourceCoreCallableIndexedAncestry.prepare base with
    | .error error => throw (.ancestry error)
    | .ok ancestry => pure (⟨ancestry, accepted⟩ : {ancestry // SourceCoreCallableIndexedAncestry.prepare base = .ok ancestry})
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
  let body := SourceCoreCallableIndexedFrames.allocate prepared.ancestry.layout.frame body
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

end Solcore.Frontend.SourceCoreCallableIndexedPrograms
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallableIndexedLedger
/-! The actual frame-aware runner's typed store and source allocation ledger.
The context cell remains administrative. Decoding its constant-depth carrier supplies
its exact shape, while ownership of the frame words and execution history
remain separate obligations. Observations never resume a checkpoint. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableIndexedLedger
open Core
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Prepared := SourceCoreCallableIndexedPrograms.Prepared
abbrev Completion {checked : Checked} (prepared : Prepared checked) :=
  SourceCoreCallableIndexedPrograms.Completion prepared
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
    Option SourceCoreCallableIndexedFrames.Frame :=
  (store completion)[0]? >>= SourceCoreCallableIndexedFrames.decode prepared.ancestry.layout.frame

theorem frame_exact {checked : Checked} {prepared : Prepared checked} {completion : Completion prepared}
    {frame : SourceCoreCallableIndexedFrames.Frame} (decoded : frame? completion = some frame) :
    (store completion)[0]? = some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame frame) := by
  unfold frame? at decoded
  cases selected : (store completion)[0]? with
  | none => simp [selected] at decoded
  | some value =>
      simp only [selected] at decoded
      exact congrArg some (SourceCoreCallableIndexedFrames.decode_sound _ value frame decoded)

/-- Lookup reads only the prepared finite table. This checks the scalar state
shape and range; actual ancestry history requires the emission proof boundary. -/
def state? {checked : Checked} {prepared : Prepared checked} (completion : Completion prepared) :
    Option (Option SourceCoreCallableAncestryPairedCache.State) :=
  frame? completion >>= SourceCoreCallableIndexedDispatch.lookup? prepared.ancestry.dispatch.table

end Solcore.Frontend.SourceCoreCallableIndexedLedger
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallableNativeSnapshotScanner
/-! Shared syntax inspection for snapshot-bearing native lambda templates.
The parser retains exact complete emission and manifest equations, actual
native body/capture indices and the sealed manifest receipt. It does not own a
compiler artifact, authenticate a runtime value, or infer source execution
history. Profile-specific caches must retain their actual compiler equation. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableNativeSnapshotScanner
open SourceInference Core
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Scope := SourceCoreFunctions.Scope

/-- A syntax strategy only. Its use in an owned compiler pass is certified
by the enclosing artifact cache, never by this public parameter alone. -/
structure Profile where
  frameType : Ty
  body : Word → Nat → Ty → Ty → Expr → Expr

def Profile.snapshotLambda (profile : Profile) (origin : Word) (referenceIndex : Nat)
    (parameter result : Ty) (rawBody : Expr) : Expr :=
  .letE (.loadCell (.var referenceIndex))
    (.lambda parameter (LanguageResult.resultType result)
      (profile.body origin referenceIndex parameter result rawBody))

inductive Error where
  | exhausted
  | malformedSnapshot
  | template (error : SourceCoreLambdaTemplates.Error)
  | manifestDepthMismatch
  | descriptorMismatch
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

structure Template (profile : Profile) where private mk ::
  source : SourceCoreLambdaTemplates.Receipt
  creationReferenceIndex : Nat
  parameter : Ty
  result : Ty
  rawBody : Expr
  body : Expr
  carrier : Expr
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
    (profile.snapshotLambda source.lambda.descriptor creationReferenceIndex parameter result rawBody))
    (.word source.lambda.descriptor)
  parameterExact : parameter = source.parameterType
  resultExact : result = source.resultType
  referenceExact : references = source.references.map (· + 1)
  manifestExact : references = manifestIndices.map (· - manifestDepth)
  snapshotExact : snapshotIndex = 0
  contextExact : contextIndex = creationReferenceIndex + 1

/-- Exact native body, including the lexical snapshot and restoration protocol.
The inverse scanner never supplies this equation from a manifest word alone. -/
theorem Template.bodyExact {profile : Profile} (template : Template profile) :
    template.body = profile.body template.source.lambda.descriptor
      template.creationReferenceIndex template.parameter template.result template.rawBody := by
  have exact := template.nativeExact.symm.trans template.carrierExact
  simpa only [Profile.snapshotLambda, Expr.pair.injEq, Expr.letE.injEq,
    Expr.lambda.injEq, and_self, true_and, and_true] using exact

def decode {checked : Checked} (inventory : SourceCoreLambdaTemplates.Inventory checked)
    (profile : Profile) (carrier : Expr) : Except Error (Template profile) := do
  let .pair (.pair identity payload) (.word descriptor) := carrier | throw .malformedSnapshot
  if identity != .inLeft .word .unit then throw .malformedSnapshot
  let .letE (.loadCell (.var referenceIndex)) (.lambda parameter (.sum .word result) body) := payload
    | throw .malformedSnapshot
  let shiftedBody ← match frameBody? body with | some body => pure body | none => throw .malformedSnapshot
  let rawBody := removeInsertion 1 (removeInsertion 0 (removeInsertion 0 shiftedBody))
  if payload != profile.snapshotLambda descriptor referenceIndex parameter result rawBody then
    throw .malformedSnapshot
  let source ← (SourceCoreLambdaTemplates.decode inventory
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
          (profile.snapshotLambda source.lambda.descriptor referenceIndex parameter result rawBody))
          (.word source.lambda.descriptor) then
        if nativeExact : carrier = .pair (.pair (.inLeft .word .unit)
            (.letE (.loadCell (.var referenceIndex)) (.lambda parameter (LanguageResult.resultType result) body)))
            (.word source.lambda.descriptor) then
          pure ⟨source, referenceIndex, parameter, result, rawBody, body, carrier, 0,
            referenceIndex + 1, 3, manifestIndices, references, nativeExact, carrierExact, types.1, types.2, rfl, manifestExact, rfl, rfl⟩
        else throw .descriptorMismatch
      else throw .descriptorMismatch
    else throw .malformedSnapshot
  else throw .manifestDepthMismatch

private def snapshotShape : Expr → Bool
  | .letE (.loadCell (.var _)) (.lambda _ _ body) => (frameBody? body).isSome
  | _ => false

mutual
  def scan {checked : Checked} (inventory : SourceCoreLambdaTemplates.Inventory checked) (profile : Profile) : Nat → Expr → Except Error (List (Template profile))
    | 0, _ => .error .exhausted
    | fuel + 1, expression => do
      match expression with
      | .pair (.pair identity payload) descriptor =>
        if snapshotShape payload then
          let template ← decode inventory profile expression
          -- Recurse through actual native binders, never the inverse-renamed
          -- synthetic source template. Child capture slots depend on them.
          pure (template :: (← scan inventory profile fuel template.body))
        else pure ((← scan inventory profile fuel (.pair identity payload)) ++ (← scan inventory profile fuel descriptor))
      | .letE (.loadCell (.var _)) (.lambda _ _ body) =>
        if (frameBody? body).isSome then throw .malformedSnapshot
        scan inventory profile fuel body
      | .unit | .bool _ | .word _ | .integer _ | .var _ => pure []
      | .lambda _ _ body => scan inventory profile fuel body
      | .pair left right | .apply left right | .storeCell left right | .binary _ left right | .letE left right =>
        pure ((← scan inventory profile fuel left) ++ (← scan inventory profile fuel right))
      | .first operand | .second operand | .loadCell operand | .inLeft _ operand | .inRight _ operand |
        .newCell _ operand | .construct _ operand | .unary _ operand => scan inventory profile fuel operand
      | .caseE first second third | .ifE first second third | .ternary _ first second third =>
        pure ((← scan inventory profile fuel first) ++ (← scan inventory profile fuel second) ++ (← scan inventory profile fuel third))
      | .matchData _ _ scrutinee branches => pure ((← scan inventory profile fuel scrutinee) ++ (← scanBranches inventory profile fuel branches))
  def scanBranches {checked : Checked} (inventory : SourceCoreLambdaTemplates.Inventory checked) (profile : Profile) : Nat → List Expr → Except Error (List (Template profile))
    | _, [] => pure []
    | 0, _ :: _ => .error .exhausted
    | fuel + 1, head :: tail => do pure ((← scan inventory profile fuel head) ++ (← scanBranches inventory profile fuel tail))
end


end Solcore.Frontend.SourceCoreCallableNativeSnapshotScanner
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallableNativeCaptureJoin
/-! Profile-independent typed reference collection and source ledger joins.
Physical Core locations select rows before exact binder/type/owner/native
context checks. This library proves order, alias and opaque-prefix laws; it
does not authenticate native closure code or infer execution provenance.
Owned profile caches and Produced/Stored receipts supply those boundaries. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableNativeCaptureJoin
open SourceInference Core
abbrev Plan := SourceSpecializationWorklist.Plan
abbrev Layouts := SourceCoreAllocationLayouts.Prepared
abbrev SourceHeap := SourceCoreAllocationLedger.SourceHeap
abbrev SourceEnvironment := SourceCoreAllocationLedger.SourceEnvironment
abbrev TypedLedger := SourceCoreAllocationLedger.TypedLedger
abbrev Row := SourceCoreAllocationLedger.Row

structure Spec where
  source : SourceCoreLambdaTemplates.Receipt
  references : List Nat
  referenceExact : references = source.references.map (· + 1)

def ofTemplate {profile : SourceCoreCallableNativeSnapshotScanner.Profile}
    (template : SourceCoreCallableNativeSnapshotScanner.Template profile) : Spec :=
  ⟨template.source, template.references, template.referenceExact⟩

structure Capture (spec : Spec) (environment : Core.Environment) (world : StoreTyping) where private mk ::
  binder : Resolved.LocalId
  payloadType : Ty
  environmentIndex : Nat
  location : Nat
  sourceReference : (environmentIndex, (binder, payloadType)) ∈ spec.references.zip spec.source.scope
  sourceSlot : (binder, payloadType) ∈ spec.source.scope
  referenceSlot : environmentIndex ∈ spec.references
  exact : environment[environmentIndex]? = some (.cellRef (OptionalCell.cellType payloadType) location)
  worldExact : world[location]? = some (OptionalCell.cellType payloadType)

inductive CollectionError where
  | native (error : SourceCoreCallableNativeSlots.Error)
  | countMismatch
  | orderMismatch
  deriving Repr

structure Collected (spec : Spec) (environment : Environment) (world : StoreTyping) where private mk ::
  captures : List (Capture spec environment world)
  exact : captures.map (fun capture => (capture.environmentIndex, (capture.binder, capture.payloadType))) =
    spec.references.zip spec.source.scope
  complete : captures.length = spec.source.scope.length

def collect (spec : Spec) (environment : Environment) (world : StoreTyping) :
    Except CollectionError (Collected spec environment world) := do
  let captures ← (spec.references.zip spec.source.scope).attach.mapM fun ⟨(index, (binder, type)), member⟩ => do
    let native ← (SourceCoreCallableNativeSlots.reference environment world index type).mapError CollectionError.native
    pure (Capture.mk binder type index native.location member (List.of_mem_zip member).2
      (List.of_mem_zip member).1 native.exact native.worldExact)
  if order : captures.map (fun capture => (capture.environmentIndex, (capture.binder, capture.payloadType))) =
      spec.references.zip spec.source.scope then
    if complete : captures.length = spec.source.scope.length then
      pure ⟨captures, order, complete⟩
    else throw .countMismatch
  else throw .orderMismatch

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

structure Slot {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared} {layouts : Layouts}
    {contexts : SourceCoreAllocationContexts.Inventory plan parents} {spec : Spec}
    {environment : Environment} {world : StoreTyping} {store : Store} {initial : SourceHeap}
    (ledger : TypedLedger layouts initial world store) (capture : Capture spec environment world) where private mk ::
  ordinal : Fin ledger.ledger.rows.length
  locationExact : (ledger.ledger.rows[ordinal]).coreLocation = capture.location
  binderExact : (ledger.ledger.rows[ordinal]).entry.key.binder.id = capture.binder
  payloadExact : (ledger.ledger.rows[ordinal]).entry.key.payloadType = capture.payloadType
  ownerExact : (ledger.ledger.rows[ordinal]).entry.key.owner = spec.source.lambda.owner
  activeExtends : ContextExtends (ledger.ledger.rows[ordinal]).entry.key.active spec.source.lambda.active
  allocated : SourceCoreAllocationContexts.Certified plan parents
  allocatedMember : allocated ∈ contexts.rows
  allocatedOwner : allocated.context.owner = (ledger.ledger.rows[ordinal]).entry.key.owner
  allocatedActive : allocated.context.active = (ledger.ledger.rows[ordinal]).entry.key.active
  allocatedBinder : (ledger.ledger.rows[ordinal]).entry.key.binder ∈ allocated.context.binders
  expected : SourceCoreAllocationCodebook.IndexedBinding
  expectedFound : spec.source.lambda.context.bindingAt? capture.binder = some expected
  expectedIdentity : expected.binding.binder.id = capture.binder
  contextualBinder : (ledger.ledger.rows[ordinal]).entry.key.binder.applySubstitution spec.source.lambda.active = expected.binding.binder

def Slot.row {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared} {layouts : Layouts}
    {contexts : SourceCoreAllocationContexts.Inventory plan parents} {spec : Spec}
    {environment : Environment} {world : StoreTyping} {store : Store} {initial : SourceHeap}
    {ledger : TypedLedger layouts initial world store} {capture : Capture spec environment world}
    (slot : Slot (contexts := contexts) ledger capture) : Row layouts store := ledger.ledger.rows[slot.ordinal]

def Slot.sourceLocation {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared} {layouts : Layouts}
    {contexts : SourceCoreAllocationContexts.Inventory plan parents} {spec : Spec}
    {environment : Environment} {world : StoreTyping} {store : Store} {initial : SourceHeap}
    {ledger : TypedLedger layouts initial world store} {capture : Capture spec environment world}
    (slot : Slot (contexts := contexts) ledger capture) : SourceTypedRuntime.Location := slot.row.sourceLocation

theorem Slot.prefixOffset {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared} {layouts : Layouts}
    {contexts : SourceCoreAllocationContexts.Inventory plan parents} {spec : Spec}
    {environment : Environment} {world : StoreTyping} {store : Store} {initial : SourceHeap}
    {ledger : TypedLedger layouts initial world store} {capture : Capture spec environment world}
    (slot : Slot (contexts := contexts) ledger capture) : slot.sourceLocation.index = initial.length + slot.ordinal.val :=
  ledger.ledger.sourceLocation_exact slot.ordinal

theorem Slot.nativeReference {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared} {layouts : Layouts}
    {contexts : SourceCoreAllocationContexts.Inventory plan parents} {spec : Spec}
    {environment : Environment} {world : StoreTyping} {store : Store} {initial : SourceHeap}
    {ledger : TypedLedger layouts initial world store} {capture : Capture spec environment world}
    (slot : Slot (contexts := contexts) ledger capture) :
    SourceCoreAllocationLedger.Reference ledger.ledger.locations capture.payloadType
      (.cellRef (OptionalCell.cellType capture.payloadType) capture.location) slot.sourceLocation := by
  rw [← slot.locationExact]
  apply SourceCoreAllocationLedger.Reference.intro (entry := slot.row.location)
  · exact List.mem_map_of_mem (by exact List.getElem_mem slot.ordinal.isLt)
  · exact slot.payloadExact

/-- The full contextual source binder comes from the actual cached allocation
inventory, rather than from a native reference's Core type. -/
theorem Slot.binderOrigin {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared} {layouts : Layouts}
    {contexts : SourceCoreAllocationContexts.Inventory plan parents} {spec : Spec}
    {environment : Environment} {world : StoreTyping} {store : Store} {initial : SourceHeap}
    {ledger : TypedLedger layouts initial world store} {capture : Capture spec environment world}
    (slot : Slot (contexts := contexts) ledger capture) :
    SourceCoreAllocationContexts.BinderOrigin slot.allocated.context.source slot.row.entry.key.binder :=
  slot.allocated.binder_origin slot.allocatedBinder

theorem ledger_core_injective {layouts : Layouts}
    {world : StoreTyping} {store : Store} {initial : SourceHeap}
    (ledger : TypedLedger layouts initial world store) :
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
theorem Slot.alias {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared} {layouts : Layouts}
    {contexts : SourceCoreAllocationContexts.Inventory plan parents}
    {leftTemplate rightTemplate : Spec} {leftEnvironment rightEnvironment : Environment}
    {world : StoreTyping} {store : Store} {initial : SourceHeap}
    {ledger : TypedLedger layouts initial world store}
    {left : Capture leftTemplate leftEnvironment world} {right : Capture rightTemplate rightEnvironment world}
    (leftSlot : Slot (contexts := contexts) ledger left) (rightSlot : Slot (contexts := contexts) ledger right)
    (same : left.location = right.location) : leftSlot.sourceLocation = rightSlot.sourceLocation := by
  have ordinals : leftSlot.ordinal = rightSlot.ordinal :=
    ledger_core_injective ledger (leftSlot.locationExact.trans (same.trans rightSlot.locationExact.symm))
  exact congrArg (fun (ordinal : Fin ledger.ledger.rows.length) =>
    (ledger.ledger.rows[ordinal]).sourceLocation) ordinals

/-- Distinct native source cells remain distinct after prefix reindexing. -/
theorem Slot.alias_iff {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared} {layouts : Layouts}
    {contexts : SourceCoreAllocationContexts.Inventory plan parents}
    {leftTemplate rightTemplate : Spec} {leftEnvironment rightEnvironment : Environment}
    {world : StoreTyping} {store : Store} {initial : SourceHeap}
    {ledger : TypedLedger layouts initial world store}
    {left : Capture leftTemplate leftEnvironment world} {right : Capture rightTemplate rightEnvironment world}
    (leftSlot : Slot (contexts := contexts) ledger left) (rightSlot : Slot (contexts := contexts) ledger right) :
    leftSlot.sourceLocation = rightSlot.sourceLocation ↔ left.location = right.location := by
  constructor
  · intro same
    have ordinals : leftSlot.ordinal = rightSlot.ordinal := ledger.ledger.sourceLocation_injective same
    exact leftSlot.locationExact.symm.trans
      ((congrArg (fun (ordinal : Fin ledger.ledger.rows.length) =>
        (ledger.ledger.rows[ordinal]).coreLocation) ordinals).trans rightSlot.locationExact)
  · exact leftSlot.alias rightSlot


def joinSlot {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared} {layouts : Layouts}
    {contexts : SourceCoreAllocationContexts.Inventory plan parents} {spec : Spec}
    {environment : Environment} {world : StoreTyping} {store : Store} {initial : SourceHeap}
    (ledger : TypedLedger layouts initial world store) (capture : Capture spec environment world) :
    Except Error (Slot (contexts := contexts) ledger capture) :=
  letI : BEq TypedBinder := instBEqOfDecidableEq
  do
    let ordinal ← match (List.finRange ledger.ledger.rows.length).find? (fun ordinal =>
        decide ((ledger.ledger.rows[ordinal]).coreLocation = capture.location)) with
      | none => throw (.unknownLocation capture.location)
      | some ordinal => pure ordinal
    let row := ledger.ledger.rows[ordinal]
    if locationExact : row.coreLocation = capture.location then
      if binderExact : row.entry.key.binder.id = capture.binder then
        if payloadExact : row.entry.key.payloadType = capture.payloadType then
          if ownerExact : row.entry.key.owner = spec.source.lambda.owner then
            if activeExtends : ContextExtends row.entry.key.active spec.source.lambda.active then
              let allocated : { certified : SourceCoreAllocationContexts.Certified plan parents // certified ∈ contexts.rows } ← match contexts.rows.attach.find? (fun context => decide
                  (context.val.context.owner = row.entry.key.owner ∧ context.val.context.active = row.entry.key.active)) with
                | none => throw (.unknownAllocatedContext capture.location)
                | some context => pure context
              if allocatedExact : allocated.val.context.owner = row.entry.key.owner ∧ allocated.val.context.active = row.entry.key.active then
                if allocatedBinder : (row.entry.key.binder : TypedBinder) ∈ (allocated.val.context.binders : List TypedBinder) then
                  match expectedFound : spec.source.lambda.context.bindingAt? capture.binder with
                  | none => throw (.unknownExpectedBinder capture.binder)
                  | some expected =>
                    if expectedIdentity : expected.binding.binder.id = capture.binder then
                      if contextualBinder : row.entry.key.binder.applySubstitution spec.source.lambda.active = expected.binding.binder then
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

inductive CaptureSourceEnv {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared} {layouts : Layouts}
    {contexts : SourceCoreAllocationContexts.Inventory plan parents} {spec : Spec}
    {environment : Environment} {world : StoreTyping} {store : Store} {initial : SourceHeap}
    (ledger : TypedLedger layouts initial world store) :
    List (Capture spec environment world) → SourceEnvironment → Prop where
  | nil : CaptureSourceEnv (contexts := contexts) ledger [] []
  | cons {capture : Capture spec environment world} {tail : List (Capture spec environment world)}
      {sourceTail : SourceEnvironment} (slot : Slot (contexts := contexts) ledger capture)
      (following : CaptureSourceEnv (contexts := contexts) ledger tail sourceTail) :
      CaptureSourceEnv (contexts := contexts) ledger (capture :: tail) ((capture.binder, slot.sourceLocation) :: sourceTail)

namespace CaptureSourceEnv
variable {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared} {layouts : Layouts}
    {contexts : SourceCoreAllocationContexts.Inventory plan parents} {spec : Spec}
  {environment : Environment} {world : StoreTyping} {store : Store} {initial : SourceHeap}
  {ledger : TypedLedger layouts initial world store}
  {captures : List (Capture spec environment world)} {source : SourceEnvironment}

theorem length (related : CaptureSourceEnv (contexts := contexts) ledger captures source) : source.length = captures.length := by
  induction related with
  | nil => rfl
  | cons slot following ih => simp only [List.length_cons, ih]

theorem binders (related : CaptureSourceEnv (contexts := contexts) ledger captures source) :
    source.map Prod.fst = captures.map (·.binder) := by
  induction related with
  | nil => rfl
  | cons slot following ih => simp only [List.map_cons, ih]

theorem lookup (related : CaptureSourceEnv (contexts := contexts) ledger captures source) {index : Nat} {binder : Resolved.LocalId}
    {location : SourceTypedRuntime.Location} (found : source[index]? = some (binder, location)) :
    ∃ capture, captures[index]? = some capture ∧ capture.binder = binder ∧
      ∃ slot : Slot (contexts := contexts) ledger capture, slot.sourceLocation = location := by
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

structure Joined {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared} {layouts : Layouts}
    {contexts : SourceCoreAllocationContexts.Inventory plan parents} {spec : Spec}
    {environment : Environment} {world : StoreTyping} {store : Store} {initial : SourceHeap}
    (ledger : TypedLedger layouts initial world store) (captures : List (Capture spec environment world)) where
  source : SourceEnvironment
  related : CaptureSourceEnv (contexts := contexts) ledger captures source

def join {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared} {layouts : Layouts}
    {contexts : SourceCoreAllocationContexts.Inventory plan parents} {spec : Spec}
    {environment : Environment} {world : StoreTyping} {store : Store} {initial : SourceHeap}
    (ledger : TypedLedger layouts initial world store) :
    (captures : List (Capture spec environment world)) → Except Error (Joined (contexts := contexts) ledger captures)
  | [] => .ok ⟨[], .nil⟩
  | capture :: tail => do
    let slot ← joinSlot (contexts := contexts) ledger capture
    let following ← join (contexts := contexts) ledger tail
    pure ⟨(capture.binder, slot.sourceLocation) :: following.source, .cons slot following.related⟩


end Solcore.Frontend.SourceCoreCallableNativeCaptureJoin
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallableIndexedTemplates
/-! Exact native lambda authentication for the owned indexed compiler pass.
Shared syntax/slot utilities provide no compiler authority. This cache retains
its actual second-pass equation and complete installed bodies; decoded frame
indices establish finite metadata membership, never execution history.
Source capture identity additionally requires the typed source ledger join. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableIndexedTemplates
open SourceInference Core
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Prepared := SourceCoreCallableIndexedPrograms.Prepared
abbrev Frame := SourceCoreCallableIndexedFrames.Frame

def profile {checked : Checked} (prepared : Prepared checked) : SourceCoreCallableNativeSnapshotScanner.Profile := {
  frameType := prepared.ancestry.layout.frame.type
  body := fun origin referenceIndex _ _ rawBody =>
    SourceCoreCallableIndexedFrames.withFrame (.var (referenceIndex + 2))
      (SourceCoreCallableIndexedDispatch.lambdaFrame prepared.ancestry.dispatch.table
        prepared.ancestry.layout.frame origin (.var 1) (.loadCell (.var (referenceIndex + 2))))
      (rawBody.weakenAt 1)
}

abbrev Template {checked : Checked} (prepared : Prepared checked) := SourceCoreCallableNativeSnapshotScanner.Template (profile prepared)

theorem snapshotExact {checked : Checked} (prepared : Prepared checked) (origin : Word)
    (referenceIndex : Nat) (parameter result : Ty) (rawBody : Expr) :
    (profile prepared).snapshotLambda origin referenceIndex parameter result rawBody =
    SourceCoreCallableIndexedAncestry.snapshotLambda prepared.ancestry.dispatch.table
      prepared.ancestry.layout.frame origin referenceIndex parameter result rawBody := rfl

inductive Error where
  | scanner (error : SourceCoreCallableNativeSnapshotScanner.Error)
  | native (error : SourceCoreCallableNativeSlots.Error)
  | captures (error : SourceCoreCallableNativeCaptureJoin.CollectionError)
  | closureMismatch
  | snapshotMissing
  | snapshotMalformed
  | foreignFrame
  | contextReferenceMismatch
  | contextWorldMismatch
  | contextValueMalformed
  deriving Repr

def decode {checked : Checked} (prepared : Prepared checked) (carrier : Expr) :
    Except Error (Template prepared) :=
  (SourceCoreCallableNativeSnapshotScanner.decode prepared.ancestry.templates (profile prepared) carrier).mapError Error.scanner

def scan {checked : Checked} (prepared : Prepared checked) (fuel : Nat) (body : Expr) :
    Except Error (List (Template prepared)) :=
  (SourceCoreCallableNativeSnapshotScanner.scan prepared.ancestry.templates (profile prepared) fuel body).mapError Error.scanner

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
    (SourceCoreCallableIndexedPrograms.markedRepresentation prepared.ancestry prepared.fuel prepared.layouts)
    prepared.fuel = .ok prepared.secondPass.closures
  groups : List (List (Template prepared))
  scanned : (prepared.secondPass.closures.zipIdx.mapM fun (closure, index) =>
    scan prepared (SourceCoreCompatibleMarkedFunctions.scanBudget (SourceCoreLambdaTemplates.installedTemplate index closure))
      (SourceCoreLambdaTemplates.installedTemplate index closure)) = .ok groups
  nativeGlobals : List (Nat × Core.Value)
  nativeGlobalsGenerated : SourceCoreCallableNativeSlots.expectedGlobals
    (globalSignatures prepared) (installedGlobals prepared) (globalEnvironment prepared) 1 = .ok nativeGlobals

def Cache.templates {checked : Checked} {prepared : Prepared checked} (cache : Cache prepared) : List (Template prepared) :=
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

/-- Constant-size index validation and owned view IDs. Neither numeric tokens
nor a well-typed frame establish that an execution visited this state. -/
def frameOwned {checked : Checked} (prepared : Prepared checked) : Frame → Bool
  | .empty => true
  | .state index => (SourceCoreCallableIndexedDispatch.lookup? prepared.ancestry.dispatch.table (.state index)).isSome
  | .view id target caller => viewOwned prepared id target &&
      (SourceCoreCallableIndexedDispatch.lookup? prepared.ancestry.dispatch.table (.state caller)).isSome
  | .invalid => false

structure Snapshot {checked : Checked} (prepared : Prepared checked) (value : Core.Value) where private mk ::
  frame : Frame
  decoded : SourceCoreCallableIndexedFrames.decode prepared.ancestry.layout.frame value = some frame
  exact : value = SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame frame
  owned : frameOwned prepared frame = true

def decodeSnapshot {checked : Checked} (prepared : Prepared checked) (value : Core.Value) :
    Except Error (Snapshot prepared value) :=
  match decoded : SourceCoreCallableIndexedFrames.decode prepared.ancestry.layout.frame value with
  | none => .error .snapshotMalformed
  | some frame =>
      if owned : frameOwned prepared frame = true then
        .ok ⟨frame, decoded, SourceCoreCallableIndexedFrames.decode_sound _ value frame decoded, owned⟩
      else .error .foreignFrame

abbrev Globals {checked : Checked} (prepared : Prepared checked) (store : Store) :=
  SourceCoreCallableNativeSlots.Globals (globalSignatures prepared) (installedGlobals prepared)
    (globalEnvironment prepared) 1 store

private def checkGlobals {checked : Checked} {prepared : Prepared checked}
    (cache : Cache prepared) (store : Store) : Except Error (Globals prepared store) :=
  (SourceCoreCallableNativeSlots.checkPreparedGlobals cache.nativeGlobals cache.nativeGlobalsGenerated store).mapError Error.native

structure Authenticated {checked : Checked} {prepared : Prepared checked} (cache : Cache prepared)
    (world : StoreTyping) (store : Store) (value : Core.Value) where private mk ::
  template : Template prepared
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
  collection : SourceCoreCallableNativeCaptureJoin.Collected (SourceCoreCallableNativeCaptureJoin.ofTemplate template) environment world

def Authenticated.sourceCaptures {checked : Checked} {prepared : Prepared checked} {cache : Cache prepared}
    {world : StoreTyping} {store : Store} {value : Value} (authenticated : Authenticated cache world store value) :=
  authenticated.collection.captures

theorem Authenticated.capturesExact {checked : Checked} {prepared : Prepared checked} {cache : Cache prepared}
    {world : StoreTyping} {store : Store} {value : Value} (authenticated : Authenticated cache world store value) :
    authenticated.sourceCaptures.map (fun capture => (capture.environmentIndex, (capture.binder, capture.payloadType))) =
      authenticated.template.references.zip authenticated.template.source.scope := authenticated.collection.exact

theorem Authenticated.capturesComplete {checked : Checked} {prepared : Prepared checked} {cache : Cache prepared}
    {world : StoreTyping} {store : Store} {value : Value} (authenticated : Authenticated cache world store value) :
    authenticated.sourceCaptures.length = authenticated.template.source.scope.length := authenticated.collection.complete

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
            let collection ← (SourceCoreCallableNativeCaptureJoin.collect (SourceCoreCallableNativeCaptureJoin.ofTemplate template) environment world).mapError Error.captures
            pure ⟨template, selected.property, environment, exact, stored,
              by simpa only [types.1, types.2] using typed,
              globals, capturedGlobals, snapshotValue.val, snapshotValue.property, snapshot,
              contextSlot, contextWorld, contextValue.val, contextValue.property, current, collection⟩
          else throw .contextWorldMismatch
        else throw .contextReferenceMismatch
      else throw .contextReferenceMismatch
    else throw .closureMismatch
  else throw .closureMismatch

end Solcore.Frontend.SourceCoreCallableIndexedTemplates
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallableIndexedCaptures
/-! Owned indexed callable provenance and source capture restoration.
Code authentication stays in IndexedTemplates. The profile-independent join
selects exact physical source rows and checks cached binder/type/owner/context.
Successful result provenance and failed/suspended heap provenance are separate. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableIndexedCaptures
open SourceInference Core
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Prepared := SourceCoreCallableIndexedPrograms.Prepared
abbrev Cache {checked : Checked} (prepared : Prepared checked) := SourceCoreCallableIndexedTemplates.Cache prepared
abbrev Authenticated {checked : Checked} {prepared : Prepared checked} (cache : Cache prepared)
    (world : StoreTyping) (store : Store) (value : Value) := SourceCoreCallableIndexedTemplates.Authenticated cache world store value
abbrev Completion {checked : Checked} (prepared : Prepared checked) := SourceCoreCallableIndexedPrograms.Completion prepared
abbrev SourceHeap := SourceCoreAllocationLedger.SourceHeap
abbrev SourceEnvironment := SourceCoreAllocationLedger.SourceEnvironment
abbrev TypedLedger := SourceCoreAllocationLedger.TypedLedger
abbrev Subvalue (value : Value) := SourceCoreCallableNativeSlots.Subvalue value
abbrev Error := SourceCoreCallableNativeCaptureJoin.Error

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

abbrev Slot {checked : Checked} {prepared : Prepared checked} {cache : Cache prepared}
    {world : StoreTyping} {store : Store} {value : Value}
    {authenticated : Authenticated cache world store value} {initial : SourceHeap}
    (ledger : TypedLedger prepared.layouts initial world store)
    (capture : SourceCoreCallableNativeCaptureJoin.Capture
      (SourceCoreCallableNativeCaptureJoin.ofTemplate authenticated.template) authenticated.environment world) :=
  SourceCoreCallableNativeCaptureJoin.Slot (contexts := prepared.contexts) ledger capture

/-- These are metadata/location facts. Produced or Stored retains the actual
owning completion; this receipt alone does not establish execution history. -/
structure Captured {checked : Checked} {prepared : Prepared checked} {cache : Cache prepared}
    {world : StoreTyping} {store : Store} {value : Value}
    (authenticated : Authenticated cache world store value) {initial : SourceHeap}
    (ledger : TypedLedger prepared.layouts initial world store) where private mk ::
  environment : SourceEnvironment
  slots : SourceCoreCallableNativeCaptureJoin.CaptureSourceEnv (contexts := prepared.contexts)
    ledger authenticated.sourceCaptures environment

theorem Captured.related {checked : Checked} {prepared : Prepared checked} {cache : Cache prepared}
    {world : StoreTyping} {store : Store} {value : Value}
    {authenticated : Authenticated cache world store value} {initial : SourceHeap}
    {ledger : TypedLedger prepared.layouts initial world store} (captured : Captured authenticated ledger) :
    SourceCoreCallableNativeCaptureJoin.CaptureSourceEnv (contexts := prepared.contexts)
      ledger authenticated.sourceCaptures captured.environment := captured.slots

def joinAuthenticated {checked : Checked} {prepared : Prepared checked} {cache : Cache prepared}
    {world : StoreTyping} {store : Store} {value : Value}
    (authenticated : Authenticated cache world store value) {initial : SourceHeap}
    (ledger : TypedLedger prepared.layouts initial world store) : Except Error (Captured authenticated ledger) := do
  let joined ← SourceCoreCallableNativeCaptureJoin.join (contexts := prepared.contexts) ledger authenticated.sourceCaptures
  pure ⟨joined.source, joined.related⟩

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
  observation : SourceCoreCallableIndexedLedger.store completion = store
  ordinal : Fin ledger.ledger.rows.length
  payload : Value
  payloadFound : (ledger.ledger.rows[ordinal]).payload = some payload
  subvalue : Subvalue value payload

def Stored.of_payload {checked : Checked} {prepared : Prepared checked} {cache : Cache prepared}
    {completion : Completion prepared} {world : StoreTyping} {store : Store} {value payload : Value}
    {initial : SourceHeap} {ledger : TypedLedger prepared.layouts initial world store}
    (authenticated : Authenticated cache world store value)
    (observation : SourceCoreCallableIndexedLedger.store completion = store)
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
end Solcore.Frontend.SourceCoreCallableIndexedCaptures
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallableIndexedPrincipalAllocations
/-! Restore a raw principal from its actual allocation snapshot and cached
source header. The generic allocation row supplies the ordered source
captures and its physical location. The native bundle can be Unit.

The receipt keeps actual store adjacency, constant-depth frame index, cached header
selection and the complete compiler principal key. A typed but fabricated
frame is not execution history; emitted-frame provenance remains a separate
artifact obligation. No source body is traversed or evaluated by restoration.
-/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableIndexedPrincipalAllocations
open SourceInference
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Program := SourceCoreCallableIndexedPrograms.Prepared
abbrev Graph := @SourceCoreCallableAncestryPairedPreparation.Prepared
abbrev Headers := @SourceCoreCallablePairedHeaders.Prepared
abbrev Cell := SourceTypedRuntime.Cell

inductive Error where
  | absentPrincipal (binder : Resolved.LocalId)
  | snapshot (error : SourceCoreCallableIndexedAllocationFrames.Error)
  | frameUnavailable (binder : Resolved.LocalId)
  | headerUnavailable (position : Nat) (binder : Resolved.LocalId)
  deriving Repr

structure Restored {checked : Checked} {program : Program checked} {graph : Graph program.base}
    (headers : Headers graph) {store : Core.Store}
    (row : SourceCoreAllocationLedger.Row program.layouts store) where private mk ::
  payload : Core.Value
  present : row.payload = some payload
  snapshot : SourceCoreCallableIndexedAllocationFrames.Snapshot program.ancestry.layout.frame row
  position : Nat
  lookup : snapshot.frame.index? = some position
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
    let snapshot ← (SourceCoreCallableIndexedAllocationFrames.snapshot program.ancestry.layout.frame row).mapError Error.snapshot
    match lookup : snapshot.frame.index? with
    | some position =>
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

end Solcore.Frontend.SourceCoreCallableIndexedPrincipalAllocations
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallableIndexedReadViews
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
namespace Solcore.Frontend.SourceCoreCallableIndexedReadViews
open SourceInference Core
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Prepared := SourceCoreCallableIndexedPrograms.Prepared
abbrev Templates {checked : Checked} (prepared : Prepared checked) := SourceCoreCallableIndexedTemplates.Cache prepared
abbrev Instance := SourceCoreLocalPolymorphism.Instance
abbrev Completion {checked : Checked} (prepared : Prepared checked) := SourceCoreCallableIndexedPrograms.Completion prepared
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
  | underlying (error : SourceCoreCallableIndexedTemplates.Error)
  | caller (error : SourceCoreCallableIndexedTemplates.Error)
  | captures (error : SourceCoreCallableIndexedCaptures.Error)
  deriving Repr

private def bodyHeader? : Expr → Option (Nat × ConstructorId × Word × Word)
  | .letE (.loadCell (.var index)) (.letE (.storeCell _
      (.matchData _ _ _ [_ ,
        .construct constructor (.pair (.word id) (.pair (.word target) _)), _, _])) _) =>
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
  bodyExact : body = SourceCoreCallableIndexedAncestry.viewBody prepared.ancestry.layout.frame entry.id target referenceIndex
  carrierExact : carrier = SourceCoreCallableIndexedAncestry.viewRepack prepared.ancestry.layout.frame
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
            if bodyExact : body = SourceCoreCallableIndexedAncestry.viewBody prepared.ancestry.layout.frame entry.id target referenceIndex then
              if carrierExact : carrier = SourceCoreCallableIndexedAncestry.viewRepack prepared.ancestry.layout.frame parameter result entry.id target referenceIndex then
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
      (SourceCoreCallableIndexedPrograms.markedRepresentation prepared.ancestry prepared.fuel prepared.layouts)
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
    (snapshot : SourceCoreCallableIndexedTemplates.Snapshot prepared value) : value.type = prepared.ancestry.layout.frame.type := by
  rw [snapshot.exact]
  cases snapshot.frame <;> rfl

structure Authenticated {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    (cache : Cache templates) (world : StoreTyping) (store : Store) (value : Value) where private mk ::
  wrapper : Template prepared
  member : wrapper ∈ cache.wrappers
  callerSnapshot : Value
  caller : SourceCoreCallableIndexedTemplates.Snapshot prepared callerSnapshot
  callerTyped : RuntimeValueHasType world callerSnapshot prepared.ancestry.layout.frame.type prepared.layouts.definitions
  original : Value
  outer : Environment
  exact : value = .pair (.pair (.inLeft .word .unit)
    (.closure wrapper.parameter (LanguageResult.resultType wrapper.result) wrapper.body (callerSnapshot :: original :: outer))) (.word wrapper.target)
  typed : RuntimeValueHasType world value (CallableContract.functionType wrapper.parameter wrapper.result) prepared.layouts.definitions
  originalTyped : RuntimeValueHasType world original (CallableContract.functionType wrapper.parameter wrapper.result) prepared.layouts.definitions
  underlying : SourceCoreCallableIndexedTemplates.Authenticated templates world store original
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
      let caller ← (SourceCoreCallableIndexedTemplates.decodeSnapshot prepared callerSnapshot).mapError Error.caller
      have callerTyped : RuntimeValueHasType world callerSnapshot prepared.ancestry.layout.frame.type prepared.layouts.definitions := by
        have own := caller_typed (exact ▸ typedWrapper)
        rw [snapshot_type caller] at own
        exact own
      have originalOwn : RuntimeValueHasType world original original.type prepared.layouts.definitions :=
        original_typed (exact ▸ typedWrapper)
      if originalType : original.type = CallableContract.functionType wrapper.parameter wrapper.result then
        have originalTyped : RuntimeValueHasType world original (CallableContract.functionType wrapper.parameter wrapper.result) prepared.layouts.definitions :=
          originalType ▸ originalOwn
        let underlying ← (SourceCoreCallableIndexedTemplates.authenticate templates stored original wrapper.parameter wrapper.result originalTyped)
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
  subvalue : SourceCoreCallableIndexedCaptures.Subvalue value result

def Produced.of_success {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : StoreTyping} {store : Store} {value result : Value}
    {authenticated : Authenticated cache world store value} {completion : Completion prepared}
    (observation : completion.result.native.observation = .succeeded result store)
    (subvalue : SourceCoreCallableIndexedCaptures.Subvalue value result) : Produced authenticated completion :=
  ⟨result, observation, subvalue⟩

structure Stored {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : StoreTyping} {store : Store} {value : Value}
    (authenticated : Authenticated cache world store value) (completion : Completion prepared)
    {initial : SourceHeap} (ledger : TypedLedger prepared.layouts initial world store) where private mk ::
  observation : SourceCoreCallableIndexedLedger.store completion = store
  ordinal : Fin ledger.ledger.rows.length
  payload : Value
  payloadFound : (ledger.ledger.rows[ordinal]).payload = some payload
  subvalue : SourceCoreCallableIndexedCaptures.Subvalue value payload

def Stored.of_payload {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : StoreTyping} {store : Store} {value payload : Value}
    {authenticated : Authenticated cache world store value} {completion : Completion prepared}
    {initial : SourceHeap} {ledger : TypedLedger prepared.layouts initial world store}
    (observation : SourceCoreCallableIndexedLedger.store completion = store) (ordinal : Fin ledger.ledger.rows.length)
    (payloadFound : (ledger.ledger.rows[ordinal]).payload = some payload)
    (subvalue : SourceCoreCallableIndexedCaptures.Subvalue value payload) : Stored authenticated completion ledger :=
  ⟨observation, ordinal, payload, payloadFound, subvalue⟩

structure JoinedProduced {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : StoreTyping} {store : Store} {value : Value}
    {authenticated : Authenticated cache world store value} {completion : Completion prepared}
    (produced : Produced authenticated completion) {initial : SourceHeap}
    (ledger : TypedLedger prepared.layouts initial world store) where private mk ::
  captures : SourceCoreCallableIndexedCaptures.Captured authenticated.underlying ledger

structure JoinedStored {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : StoreTyping} {store : Store} {value : Value}
    {authenticated : Authenticated cache world store value} {completion : Completion prepared}
    {initial : SourceHeap} {ledger : TypedLedger prepared.layouts initial world store}
    (stored : Stored authenticated completion ledger) where private mk ::
  captures : SourceCoreCallableIndexedCaptures.Captured authenticated.underlying ledger

def joinProduced {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : StoreTyping} {store : Store} {value : Value}
    {authenticated : Authenticated cache world store value} {completion : Completion prepared}
    (produced : Produced authenticated completion) {initial : SourceHeap}
    (ledger : TypedLedger prepared.layouts initial world store) : Except Error (JoinedProduced produced ledger) := do
  let captures ← (SourceCoreCallableIndexedCaptures.joinAuthenticated authenticated.underlying ledger).mapError Error.captures
  pure ⟨captures⟩

def joinStored {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : StoreTyping} {store : Store} {value : Value}
    {authenticated : Authenticated cache world store value} {completion : Completion prepared}
    {initial : SourceHeap} {ledger : TypedLedger prepared.layouts initial world store}
    (stored : Stored authenticated completion ledger) : Except Error (JoinedStored stored) := do
  let captures ← (SourceCoreCallableIndexedCaptures.joinAuthenticated authenticated.underlying ledger).mapError Error.captures
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

end Solcore.Frontend.SourceCoreCallableIndexedReadViews
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallableIndexedRestoration
/-! Source closure restoration from the actual indexed callable profile.
Code authenticity and physical capture joins are supplied by the owning native
receipts. Constant-depth saved indices select raw lexical headers and exact read recipes;
restoration performs no source traversal, substitution or evidence resolution.

The output retains the original closure for an instantiated read. Produced and
stored wrappers keep the corresponding completion provenance. These receipts
establish the reconstruction boundary; full source execution meaning still
requires the enclosing native emission/history theorem.
-/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableIndexedRestoration
open SourceInference
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Program := SourceCoreCallableIndexedPrograms.Prepared
abbrev Graph := @SourceCoreCallableAncestryPairedPreparation.Prepared
abbrev Headers := @SourceCoreCallablePairedHeaders.Prepared
abbrev Templates := @SourceCoreCallableIndexedTemplates.Cache
abbrev Views := @SourceCoreCallableIndexedReadViews.Cache
abbrev Ledger := @SourceCoreAllocationLedger.TypedLedger
abbrev SourceValue := SourceTypedRuntime.Value

inductive Error where
  | captures (error : SourceCoreCallableIndexedCaptures.Error)
  | lexicalUnavailable
  | callerUnavailable
  | lambdaHeaderUnavailable (position : Nat) (descriptor : Core.Word)
  | principalHeaderUnavailable (position : Nat) (binder : Resolved.LocalId)
  | readRecipeUnavailable (caller lexical : Nat) (view target : Core.Word)
  deriving Repr

structure Ordinary {checked : Checked} {program : Program checked} {graph : Graph program.base}
    (headers : Headers graph) {templates : Templates program}
    {world : Core.StoreTyping} {store : Core.Store} {value : Core.Value}
    (authenticated : SourceCoreCallableIndexedTemplates.Authenticated templates world store value)
    {initial : List SourceTypedRuntime.Cell} (ledger : Ledger program.layouts initial world store) where private mk ::
  captures : SourceCoreCallableIndexedCaptures.Captured authenticated ledger
  position : Nat
  lookup : authenticated.snapshot.frame.index? = some position
  header : SourceCoreCallablePairedHeaders.LambdaHeader graph headers.principals
  selected : headers.lambdaAt? position authenticated.template.source.lambda.descriptor = some header
  source : SourceValue
  exact : source = header.sourceValue captures.environment

def restoreOrdinary {checked : Checked} {program : Program checked} {graph : Graph program.base}
    (headers : Headers graph) {templates : Templates program}
    {world : Core.StoreTyping} {store : Core.Store} {value : Core.Value}
    (authenticated : SourceCoreCallableIndexedTemplates.Authenticated templates world store value)
    {initial : List SourceTypedRuntime.Cell} (ledger : Ledger program.layouts initial world store) :
    Except Error (Ordinary headers authenticated ledger) := do
  let captures ← (SourceCoreCallableIndexedCaptures.joinAuthenticated authenticated ledger).mapError Error.captures
  match lookup : authenticated.snapshot.frame.index? with
  | some position =>
    match selected : headers.lambdaAt? position authenticated.template.source.lambda.descriptor with
    | none => throw (.lambdaHeaderUnavailable position authenticated.template.source.lambda.descriptor)
    | some header => pure ⟨captures, position, lookup, header, selected, header.sourceValue captures.environment, rfl⟩
  | _ => throw .lexicalUnavailable

structure Read {checked : Checked} {program : Program checked} {graph : Graph program.base}
    (headers : Headers graph) {templates : Templates program} {views : Views templates}
    {world : Core.StoreTyping} {store : Core.Store} {value : Core.Value}
    (authenticated : SourceCoreCallableIndexedReadViews.Authenticated views world store value)
    {initial : List SourceTypedRuntime.Cell} (ledger : Ledger program.layouts initial world store) where private mk ::
  captures : SourceCoreCallableIndexedCaptures.Captured authenticated.underlying ledger
  caller : Nat
  callerLookup : authenticated.caller.frame.index? = some caller
  lexical : Nat
  lexicalLookup : authenticated.underlying.snapshot.frame.index? = some lexical
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
    (authenticated : SourceCoreCallableIndexedReadViews.Authenticated views world store value)
    {initial : List SourceTypedRuntime.Cell} (ledger : Ledger program.layouts initial world store) :
    Except Error (Read headers authenticated ledger) := do
  let captures ← (SourceCoreCallableIndexedCaptures.joinAuthenticated authenticated.underlying ledger).mapError Error.captures
  match callerLookup : authenticated.caller.frame.index? with
  | some caller =>
    match lexicalLookup : authenticated.underlying.snapshot.frame.index? with
    | some lexical =>
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

/-- The original lexical declaration and saved source captures are retained. -/
theorem Ordinary.raw_closure {checked : Checked} {program : Program checked} {graph : Graph program.base}
    {headers : Headers graph} {templates : Templates program} {world : Core.StoreTyping} {store : Core.Store} {value : Core.Value}
    {authenticated : SourceCoreCallableIndexedTemplates.Authenticated templates world store value}
    {initial : List SourceTypedRuntime.Cell} {ledger : Ledger program.layouts initial world store}
    (restored : Ordinary headers authenticated ledger) :
    restored.source = .closure restored.header.parameters restored.header.resultType restored.header.body
      restored.header.state.metadata.source restored.header.state.metadata.owner restored.captures.environment
      restored.header.context.context.evidence := by
  rw [restored.exact]
  rfl

/-- A read value keeps its own caller substitution and original lexical source. -/
theorem Read.original_closure {checked : Checked} {program : Program checked} {graph : Graph program.base}
    {headers : Headers graph} {templates : Templates program} {views : Views templates}
    {world : Core.StoreTyping} {store : Core.Store} {value : Core.Value}
    {authenticated : SourceCoreCallableIndexedReadViews.Authenticated views world store value}
    {initial : List SourceTypedRuntime.Cell} {ledger : Ledger program.layouts initial world store}
    (restored : Read headers authenticated ledger) :
    restored.source = restored.recipe.applied.sourceValue restored.captures.environment
      restored.header.principal.context.evidence := restored.exact

end Solcore.Frontend.SourceCoreCallableIndexedRestoration
end
