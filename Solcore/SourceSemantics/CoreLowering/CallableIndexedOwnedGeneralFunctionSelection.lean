import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralLambdaValues

/-! Exact selection in the shared rich function relation retains the same
Source value, native carrier and all authentic static receipts. Old ranked and
method closures keep their actual caller prefix; stronger invocation prefixes
need the genuine capture/formation receipt. The unrestricted ordinary branch
already retains its full Header prefix and observed Globals1. This is finite
provenance inversion, with no execution premise or function-model inverse. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralFunctionSelection
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey NamedSourceAt NamedCapture NamedInstalledCode)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- Each alternative keeps the exact full constructor witness. In particular,
the prefix stored by an old or method closure is retained without strengthening. -/
inductive Selection (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping) : TypeSystem.Ty → Dynamic.Value → Value → Ty → Prop where
  | builtin {sourceType source native type}
      (related : CallableIndexedBuiltinValues.Represents compiled.indexed world sourceType source native type) :
      Selection headers keys registry faults mapping world sourceType source native type
  | named {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
      {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {source : Dynamic.GlobalFunction} {identity : Word}
      (owner : OwnedKey keys) (member : header ∈ headers)
      (sourceAt : NamedSourceAt header rawD source)
      (capture : NamedCapture headers owner.key header mapping world) (installed : NamedInstalledCode capture)
      (number : Word.ofNat? (header.slot + 1) = some identity)
      (projection : compiled.compatible.checked.catalog.project header.named.specialized.function.type = .ok
        (CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType))
      (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
        (.named header.named.signature.key))
      (typed : RuntimeValueHasType world (.closure header.named.signature.parameterType
        (LanguageResult.resultType header.named.signature.resultType) (header.code.rename capture.embedding.lift)
        capture.captured) header.named.signature.functionType compiled.indexed.layouts.definitions) :
      Selection headers keys registry faults mapping world header.named.specialized.function.type (.global source)
        (.pair (.pair (.inRight .unit (.word identity)) (.closure header.named.signature.parameterType
          (LanguageResult.resultType header.named.signature.resultType) (header.code.rename capture.embedding.lift)
          capture.captured)) (.word descriptor.id))
        (CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType)
  | ranked_lambda {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
      {actual : Environment} {callerPrefix : Nat}
      (owner : OwnedKey keys) (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code)
      (body : CallableIndexedOwnedFunctionValues.StaticSupport headers registry faults code)
      (origin : CallableIndexedOwnedFunctionValues.ActualSourceOrigin code history body)
      (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations callerPrefix scope captured.canonical owner.key.frameLocation)
      (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) compiled.indexed.layouts.definitions) :
      Selection headers keys registry faults mapping world (FunctionValues.sourceType function) (.closure function)
        (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)
  | method_lambda {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
      {actual : Environment} {callerPrefix : Nat}
      (owner : OwnedKey keys) (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code)
      (body : CallableIndexedOwnedMethodLambdaSupport.Support code registry faults)
      (origin : CallableIndexedOwnedMethodLambdaSupport.SourceOrigin body history)
      (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations callerPrefix scope captured.canonical owner.key.frameLocation)
      (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) compiled.indexed.layouts.definitions) :
      Selection headers keys registry faults mapping world (FunctionValues.sourceType function) (.closure function)
        (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)
  | ordinary_lambda {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
      (owner : OwnedKey keys) (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code)
      (body : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults)
      (origin : CallableIndexedOwnedOrdinaryLambdaSupport.SourceOrigin body history)
      (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
        (values := .initial compiled.compatible.checked) body.caller)
      (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
      (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) compiled.indexed.layouts.definitions) :
      Selection headers keys registry faults mapping world (FunctionValues.sourceType function) (.closure function)
        (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)

variable {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping}
  {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {native : Value} {type : Ty}

/-- Finite inversion keeps every receipt and the exact carrier from the
actual shared relation. No weaker projection is used to recover support. -/
theorem of_represents
    (related : CallableIndexedOwnedGeneralLambdaValues.Represents headers keys registry faults
      mapping world sourceType source native type) :
    Selection headers keys registry faults mapping world sourceType source native type := by
  cases related with
  | prior prior =>
    cases prior with
    | prior original =>
      cases original with
      | builtin related => exact .builtin related
      | named owner member sourceAt capture installed number projection descriptor typed =>
        exact .named owner member sourceAt capture installed number projection descriptor typed
      | lambda owner captured code history body origin globals referenceIndex typed =>
        exact .ranked_lambda owner captured code history body origin globals referenceIndex typed
    | method_lambda owner captured code history body origin globals referenceIndex typed =>
      exact .method_lambda owner captured code history body origin globals referenceIndex typed
  | ordinary_lambda owner captured code history body origin prefixContext globals referenceIndex typed =>
    exact .ordinary_lambda owner captured code history body origin prefixContext globals referenceIndex typed

/-- The retained receipts reconstruct exactly the same rich relation. This
uses the full witnesses in this selection, rather than a model inclusion. -/
theorem represents (selected : Selection headers keys registry faults mapping world sourceType source native type) :
    CallableIndexedOwnedGeneralLambdaValues.Represents headers keys registry faults mapping world sourceType source native type := by
  cases selected with
  | builtin related => exact .prior (.prior (.builtin related))
  | named owner member sourceAt capture installed number projection descriptor typed =>
    exact .prior (.prior (.named owner member sourceAt capture installed number projection descriptor typed))
  | ranked_lambda owner captured code history body origin globals referenceIndex typed =>
    exact .prior (.prior (.lambda owner captured code history body origin globals referenceIndex typed))
  | method_lambda owner captured code history body origin globals referenceIndex typed =>
    exact .prior (.method_lambda owner captured code history body origin globals referenceIndex typed)
  | ordinary_lambda owner captured code history body origin prefixContext globals referenceIndex typed =>
    exact .ordinary_lambda owner captured code history body origin prefixContext globals referenceIndex typed

/-- The exact model's actual value relation supplies finite selected provenance.
All heaps and maps remain those of the caller; no reverse inclusion is assumed. -/
theorem of_model (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {actualRegistry : SourceCoreRawMetadata.Registry}
    (related : (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile).Represents
      actualRegistry mapping world sourceType source native type) :
    Selection headers keys registry faults mapping world sourceType source native type := of_represents related

/-- Selection and the exact rich model describe the same full actual value. -/
theorem model_iff (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (actualRegistry : SourceCoreRawMetadata.Registry) :
    (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile).Represents
      actualRegistry mapping world sourceType source native type ↔
    Selection headers keys registry faults mapping world sourceType source native type :=
  ⟨of_represents, represents⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralFunctionSelection
