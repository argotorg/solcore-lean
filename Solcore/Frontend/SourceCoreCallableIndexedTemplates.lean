import Solcore.Frontend.SourceCoreCallableIndexedPrograms
import Solcore.Frontend.SourceCoreCallableNativeCaptureJoin

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
