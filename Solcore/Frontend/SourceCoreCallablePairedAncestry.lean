import Solcore.Frontend.SourceCoreLambdaTemplates
import Solcore.Frontend.SourceCoreCallablePrincipals
import Solcore.Frontend.SourceCoreCallablePairedFrames

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
