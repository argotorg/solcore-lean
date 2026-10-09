import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedContextualOrdinaryLambdaFormation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedContextualPrincipalLambdaFormation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureAssociation

/-! Positive contextual ordinary and principal members retain the actual formed code,
owner, captured history and same-body syntax through storage-independent
map/world extension. The original accepted call's escaped-control diagnostic
belongs to this same code. Projection supplies the existing strict joint
invocation association; no representation inverse or body meaning is used. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualStoredClosureAssociationReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedOrdinaryLambdaSupport (Support SourceOrigin)
open CallableIndexedOwnedContextualLambdaProvenance (OrdinaryAt PrincipalAt)
open CallableIndexedOwnedStoredClosureInvocation (Association)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- This is the actual positive contextual constructor with its generated
escaped-control row. Arbitrary prior representations supply no such member. -/
inductive Member
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping) :
    Dynamic.Closure → Value → List CallableIndexedParameterCertificates.Binding → Ty → Ty → Prop where
  | ordinary {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
      (owner : OwnedKey keys)
      (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code)
      (support : Support code registry faults) (origin : SourceOrigin support history)
      (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
        (values := .initial compiled.compatible.checked) support.caller)
      (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
      (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)
        compiled.indexed.layouts.definitions)
      (provenance : OrdinaryAt code support)
      (escaped : faults .controlEscapedFunction code.compilation.internalReason) :
      Member headers keys registry faults mapping world function
        (value code captured.embedding history.native actual) code.receipt.loweredParameters
        code.receipt.parameterCore code.receipt.resultCore
  | principal {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
      (owner : OwnedKey keys)
      (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code)
      (support : CallableIndexedOwnedMethodLambdaSupport.Support code registry faults)
      (origin : CallableIndexedOwnedMethodLambdaSupport.SourceOrigin support history)
      (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
      (leading : captured.administrative[0]? = some support.principal.named.signature.parameterType)
      (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)
        compiled.indexed.layouts.definitions)
      (provenance : PrincipalAt code support)
      (escaped : faults .controlEscapedFunction code.compilation.internalReason) :
      Member headers keys registry faults mapping world function
        (value code captured.embedding history.native actual) code.receipt.loweredParameters
        code.receipt.parameterCore code.receipt.resultCore

variable {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
  {function : Dynamic.Closure} {native : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}

/-- Forward selection keeps the genuine contextual branch and all its fields. -/
theorem Member.selection
    (member : Member headers keys registry faults mapping world function native bindings parameterCore resultCore) :
    CallableIndexedOwnedGeneralFunctionSelection.Selection headers keys registry faults mapping world
      (FunctionValues.sourceType function) (.closure function) native
      (CallableContract.functionType parameterCore resultCore) := by
  cases member with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance _escaped =>
    exact .contextual_ordinary_lambda owner captured code history support origin prefixContext globals referenceIndex typed provenance
  | principal owner captured code history support origin globals leading referenceIndex typed provenance _escaped =>
    exact .contextual_principal_lambda owner captured code history support origin globals leading referenceIndex typed provenance

/-- Only forward projection to the exact general relation is needed. -/
theorem Member.represents
    (member : Member headers keys registry faults mapping world function native bindings parameterCore resultCore) :
    CallableIndexedOwnedGeneralLambdaValues.Represents headers keys registry faults mapping world
      (FunctionValues.sourceType function) (.closure function) native
      (CallableContract.functionType parameterCore resultCore) :=
  CallableIndexedOwnedGeneralFunctionSelection.represents member.selection

/-- The retained provenance supplies syntax for this exact body context.
The authentic escaped-control row remains an independent compiler receipt. -/
theorem Member.association
    (member : Member headers keys registry faults mapping world function native bindings parameterCore resultCore) :
    Association headers keys registry faults mapping world function native bindings parameterCore resultCore := by
  cases member with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance escaped =>
    exact .ordinary owner captured code history support origin prefixContext globals referenceIndex typed escaped provenance.syntax
  | principal owner captured code history support origin globals leading referenceIndex typed provenance escaped =>
    exact .principal owner captured code history support origin globals leading referenceIndex typed escaped provenance.syntax

/-- Actual map/world growth changes only capture and runtime typing indices.
The original code, owner, history, syntax and diagnostic row stay the same. -/
theorem Member.extend
    (member : Member headers keys registry faults mapping world function native bindings parameterCore resultCore)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    Member headers keys registry faults futureMapping futureWorld function native bindings parameterCore resultCore := by
  cases member with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance escaped =>
    exact .ordinary owner (captured.extend maps worlds) code history support origin prefixContext globals
      referenceIndex (typed.weaken worlds) provenance escaped
  | principal owner captured code history support origin globals leading referenceIndex typed provenance escaped =>
    exact .principal owner (captured.extend maps worlds) code history support origin globals leading
      referenceIndex (typed.weaken worlds) provenance escaped

section Formation
variable {scope : SourceCoreLocalCell.Scope} {actual canonical : Environment}
  {heap : Dynamic.Heap} {store : Store}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (support : Support code registry faults) (owner : OwnedKey keys)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner support.caller _ initial)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) support.caller)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  (provenance : OrdinaryAt code support)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (inclusion : (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile).Includes functions)
  (escaped : faults .controlEscapedFunction code.compilation.internalReason)

open CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation (history_at source_origin reference_index)

include profile prefixContext observed provenance inclusion escaped in
/-- One original contextual formation retains its complete traces and
represented value, plus the same positive member for later initialized reads.
The escaped row is supplied by the actual accepted compiler selection. -/
theorem formation_member
    (stored : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
      function.source function.captured heap code.id (.closure function) heap ∧
    Evaluates actual store (code.lowered.expression.rename captured.embedding)
      (.inRight .word (value code captured.embedding (history_at captured code support owner initial packet).native actual)) store ∧
    functions.Represents registry mapping world (FunctionValues.sourceType function) (.closure function)
      (value code captured.embedding (history_at captured code support owner initial packet).native actual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
    (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
      result = .inRight .word (value code captured.embedding (history_at captured code support owner initial packet).native actual) ∧
      finalStore = store) ∧
    Member headers keys registry faults mapping world function
      (value code captured.embedding (history_at captured code support owner initial packet).native actual)
      code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore := by
  obtain ⟨sourceTrace, nativeTrace, related, determined⟩ :=
    CallableIndexedOwnedAdmittedContextualOrdinaryLambdaFormation.formation captured code support owner initial packet
      profile prefixContext observed provenance functions inclusion stored ordinary coercions
  have typed : RuntimeValueHasType world
      (value code captured.embedding (history_at captured code support owner initial packet).native actual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)
      compiled.indexed.layouts.definitions := functions.runtime_hasType (registry := registry) related
  exact ⟨sourceTrace, nativeTrace, related, determined,
    .ordinary owner captured code (history_at captured code support owner initial packet) support
      (source_origin captured code support owner initial packet) prefixContext observed
      (reference_index captured code support) typed provenance escaped⟩

end Formation

section PrincipalFormation
variable {scope : SourceCoreLocalCell.Scope} {actual : Environment}
  {heap : Dynamic.Heap} {store : Store}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (support : CallableIndexedOwnedMethodLambdaSupport.Support code registry faults)
  (owner : OwnedKey keys)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, captured.canonical⟩)
  (packet : CallableIndexedOwnedOriginCanonicalState.Packet owner support.principal.named _ initial)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (provenance : PrincipalAt code support)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (inclusion : (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile).Includes functions)
  (escaped : faults .controlEscapedFunction code.compilation.internalReason)

include packet profile provenance inclusion escaped in
/-- One original contextual principal formation retains its genuine leading
bundle, owner and history with the exact positive member. The accepted code's
escaped-control diagnostic stays an independent compiler input. -/
theorem principal_formation_member
    (stored : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
      function.source function.captured heap code.id (.closure function) heap ∧
    Evaluates actual store (code.lowered.expression.rename captured.embedding)
      (.inRight .word (value code captured.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native actual)) store ∧
    functions.Represents registry mapping world (FunctionValues.sourceType function) (.closure function)
      (value code captured.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native actual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
    (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
      result = .inRight .word (value code captured.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native actual) ∧
      finalStore = store) ∧
    Member headers keys registry faults mapping world function
      (value code captured.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native actual)
      code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore := by
  obtain ⟨sourceTrace, nativeTrace, related, determined⟩ :=
    CallableIndexedOwnedAdmittedContextualPrincipalLambdaFormation.formation captured code support owner initial packet
      profile functions inclusion provenance stored ordinary coercions
  have typed : RuntimeValueHasType world
      (value code captured.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native actual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)
      compiled.indexed.layouts.definitions := functions.runtime_hasType (registry := registry) related
  exact ⟨sourceTrace, nativeTrace, related, determined,
    .principal owner captured code
      (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet) support
      (CallableIndexedOwnedMethodLambdaFormationReceipts.source_origin captured code support owner initial packet)
      packet.observed (CallableIndexedOwnedMethodLambdaFormationReceipts.leading captured code support owner initial packet)
      (CallableIndexedOwnedMethodLambdaFormationReceipts.reference_index captured code support) typed provenance escaped⟩

end PrincipalFormation
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualStoredClosureAssociationReceipts
