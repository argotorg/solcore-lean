import Solcore.Frontend.SourceCoreCallablePairedPrograms
import Solcore.Frontend.SourceCoreCallablePairedFrameCodec
import Solcore.Frontend.SourceCoreCallableNativeSlots

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
