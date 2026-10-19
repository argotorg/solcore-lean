import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalClosureAssociation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryLambdaValues
import Solcore.SourceSemantics.CoreLowering.PreparedLambdaBodySupport

/-! A physical closure retains either its original legacy association or the
actual prepared body and all captured slots. The representation projection
retains the actual closure Code and does not require uniform diagnostics. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalClosureAssociation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport
variable {compiled : SourceCoreUnifiedCompilation.Compiled}

inductive Association
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping) :
    Dynamic.Closure → Value → List CallableIndexedParameterCertificates.Binding → Ty → Ty → Type where
  | legacy {function native bindings parameter result}
      (original : CallableIndexedOwnedPhysicalClosureAssociation.Association
        headers keys registry faults mapping world function native bindings parameter result) :
      Association headers keys registry faults mapping world function native bindings parameter result
  | preparedOrdinary {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
      (owner : OwnedKey keys)
      (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code)
      (support : Support code) (origin : SourceOrigin support history)
      (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
        (values := .initial compiled.compatible.checked) support.caller)
      (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
      (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) compiled.indexed.layouts.definitions)
      (prepared : PreparedAt code support)
      (slots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 1 scope captured.canonical)
      (callerReceipt : Nonempty (CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt
        support.caller function.context function.evidence)) :
      Association headers keys registry faults mapping world function
        (value code captured.embedding history.native actual) code.receipt.loweredParameters
        code.receipt.parameterCore code.receipt.resultCore

  | preparedBranching {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
      (owner : OwnedKey keys)
      (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code)
      (support : PreparedLambdaBodySupport.Support code)
      (origin : PreparedLambdaBodySupport.SourceOrigin support history)
      (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
        (values := .initial compiled.compatible.checked) support.caller)
      (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
      (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) compiled.indexed.layouts.definitions)
      (prepared : PreparedLambdaBodySupport.PreparedAt code support)
      (slots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 1 scope captured.canonical)
      (callerReceipt : Nonempty (CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt
        support.caller function.context function.evidence)) :
      Association headers keys registry faults mapping world function
        (value code captured.embedding history.native actual) code.receipt.loweredParameters
        code.receipt.parameterCore code.receipt.resultCore

variable {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
  {function : Dynamic.Closure} {native : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}

theorem Association.represents
    (member : Association headers keys registry faults mapping world function native bindings parameter result) :
    CallableIndexedLambdaValues.Represents compiled.indexed mapping world
      (FunctionValues.sourceType function) (.closure function) native
      (CallableContract.functionType parameter result) := by
  cases member with
  | legacy original => exact original.original.represents.forget
  | preparedOrdinary owner captured code history support origin prefixContext globals referenceIndex typed prepared slots callerReceipt =>
    exact .lambda captured code history typed

  | preparedBranching owner captured code history support origin prefixContext globals referenceIndex typed prepared slots callerReceipt =>
    exact .lambda captured code history typed

def Association.extend
    (member : Association headers keys registry faults mapping world function native bindings parameter result)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    Association headers keys registry faults futureMapping futureWorld function native bindings parameter result := by
  cases member with
  | legacy original => exact .legacy (original.extend maps worlds)
  | preparedOrdinary owner captured code history support origin prefixContext globals referenceIndex typed prepared slots callerReceipt =>
    exact .preparedOrdinary owner (captured.extend maps worlds) code history support origin prefixContext globals
      referenceIndex (typed.weaken worlds) prepared slots callerReceipt

  | preparedBranching owner captured code history support origin prefixContext globals referenceIndex typed prepared slots callerReceipt =>
    exact .preparedBranching owner (captured.extend maps worlds) code history support origin prefixContext globals
      referenceIndex (typed.weaken worlds) prepared slots callerReceipt

abbrev StaticMember
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping)
    (function : Dynamic.Closure) (native : Value)
    (bindings : List CallableIndexedParameterCertificates.Binding) (parameter result : Ty) : Prop :=
  Nonempty (Association headers keys registry faults mapping world function native bindings parameter result)

theorem StaticMember.represents
    (member : StaticMember headers keys registry faults mapping world function native bindings parameter result) :
    CallableIndexedLambdaValues.Represents compiled.indexed mapping world
      (FunctionValues.sourceType function) (.closure function) native
      (CallableContract.functionType parameter result) := by
  obtain ⟨association⟩ := member
  exact association.represents

theorem StaticMember.extend
    (member : StaticMember headers keys registry faults mapping world function native bindings parameter result)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    StaticMember headers keys registry faults futureMapping futureWorld function native bindings parameter result := by
  obtain ⟨association⟩ := member
  exact ⟨association.extend maps worlds⟩

theorem StaticMember.legacy
    (member : CallableIndexedOwnedPhysicalClosureAssociation.StaticMember
      headers keys registry faults mapping world function native bindings parameter result) :
    StaticMember headers keys registry faults mapping world function native bindings parameter result := by
  obtain ⟨association⟩ := member
  exact ⟨.legacy association⟩


theorem Association.stage_origin
    (member : Association headers keys registry faults mapping world function native bindings parameter result) :
    CallableLedger.OriginRep compiled.indexed.base.plan compiled.indexed.ancestry.graph.inputs.callable.table
      (.closure function) native := by
  cases member with
  | legacy original => exact original.original.stage_origin
  | preparedOrdinary _owner captured code _history support _origin _prefix _globals _reference _typed _prepared _slots _callerReceipt =>
    have prepared := RecursiveNamedPreparedStageContracts.of_compiled compiled
      compiled.indexed.ancestry.graph.inputs.callableSelected
    exact CompatibleAmbientStageOrigins.actual_lambda_origin prepared.accepted code.descriptor
      support.source_receipt code.viewOfSource support.unique code.found
      (code.form.trans code.sourceForm) _

  | preparedBranching _owner captured code _history support _origin _prefix _globals _reference _typed _prepared _slots _callerReceipt =>
    have prepared := RecursiveNamedPreparedStageContracts.of_compiled compiled
      compiled.indexed.ancestry.graph.inputs.callableSelected
    exact CompatibleAmbientStageOrigins.actual_lambda_origin prepared.accepted code.descriptor
      support.source_receipt code.viewOfSource support.unique code.found
      (code.form.trans code.sourceForm) _

theorem StaticMember.stage_origin
    (member : StaticMember headers keys registry faults mapping world function native bindings parameter result) :
    CallableLedger.OriginRep compiled.indexed.base.plan compiled.indexed.ancestry.graph.inputs.callable.table
      (.closure function) native := by
  obtain ⟨association⟩ := member
  exact association.stage_origin

theorem Association.source_binders
    (member : Association headers keys registry faults mapping world function native bindings parameter result) :
    bindings.map (fun binding => binding.1.scheme.body) =
      function.parameters.map (fun binder => binder.scheme.body) := by
  cases member with
  | legacy original => exact original.original.source_binders
  | preparedOrdinary _owner _captured code _history _support _origin _prefix _globals _reference _typed _prepared _slots _callerReceipt =>
    simpa only [List.map_map, Function.comp_def] using
      (congrArg (List.map (fun binder : TypedBinder => binder.scheme.body))
        (CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) code)).symm

  | preparedBranching _owner _captured code _history _support _origin _prefix _globals _reference _typed _prepared _slots _callerReceipt =>
    simpa only [List.map_map, Function.comp_def] using
      (congrArg (List.map (fun binder : TypedBinder => binder.scheme.body))
        (CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) code)).symm

theorem Association.projected_bindings
    (member : Association headers keys registry faults mapping world function native bindings parameter result) :
    ∀ binding ∈ bindings,
      compiled.compatible.checked.catalog.project binding.1.scheme.body = .ok binding.2 := by
  cases member with
  | legacy original => exact original.original.projected_bindings
  | preparedOrdinary _owner _captured _code _history _support _origin _prefix _globals _reference _typed prepared _slots _callerReceipt =>
    exact prepared.projected_bindings

  | preparedBranching _owner _captured _code _history _support _origin _prefix _globals _reference _typed prepared _slots _callerReceipt =>
    exact prepared.projected_bindings

theorem Association.parameter_core
    (member : Association headers keys registry faults mapping world function native bindings parameter result)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    parameter = SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) := by
  cases member with
  | legacy original => exact original.original.parameter_core profile
  | preparedOrdinary _owner _captured code _history support _origin _prefix _globals _reference _typed prepared _slots _callerReceipt =>
    exact CallableIndexedOwnedStoredNativePackReceipts.code_binding_pack code profile
      prepared.projected_bindings support.body.projection

  | preparedBranching _owner _captured code _history support _origin _prefix _globals _reference _typed prepared _slots _callerReceipt =>
    exact CallableIndexedOwnedStoredNativePackReceipts.code_binding_pack code profile
      prepared.projected_bindings support.body.projection

theorem StaticMember.source_binders
    (member : StaticMember headers keys registry faults mapping world function native bindings parameter result) :
    bindings.map (fun binding => binding.1.scheme.body) =
      function.parameters.map (fun binder => binder.scheme.body) := by
  obtain ⟨association⟩ := member
  exact association.source_binders

theorem StaticMember.projected_bindings
    (member : StaticMember headers keys registry faults mapping world function native bindings parameter result) :
    ∀ binding ∈ bindings,
      compiled.compatible.checked.catalog.project binding.1.scheme.body = .ok binding.2 := by
  obtain ⟨association⟩ := member
  exact association.projected_bindings

theorem StaticMember.parameter_core
    (member : StaticMember headers keys registry faults mapping world function native bindings parameter result)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    parameter = SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) := by
  obtain ⟨association⟩ := member
  exact association.parameter_core profile

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalClosureAssociation
