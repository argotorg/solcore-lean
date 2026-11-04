import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ReadyContinuations
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.CanonicalCallerState
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.MethodPrincipal
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaStaticBodySupport
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.NamedHeaderReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaIssuedRecipes
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.NestedEntries
import Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyMutualMeaning
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.InvocationBounds
import Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyStaticOrigins

/-!
# Owned callables: lambda ready families

Measured ready families of lambdas: continuations, entries, receipts and joint families.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaReadyContinuations
/-! Real anonymous parameter entries retain complete captures, code, Source
frames and their own reached ordered pool. Genuine raw Source arguments and
actual hook/parameter effects supply admission before the strict shared child.
No arbitrary closure representation or completed body family is a premise. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaReadyContinuations
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedLambdaValues
open CallableIndexedOwnedParameterReadyContinuations (bridge)
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedOwnedBodySourceOrigin (source_origin)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (body : CallableIndexedOwnedLambdaInvocationBounds.BodyOrigin (program := program) code inputs registry faults)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments inputs.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)

include beforeTyped argumentsTyped stable in
/-- Source admission and stable histories belong to the actual Source prefix
post, whose full captured canonical spine and nextHistory remain original. -/
def source_admitted_entry
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩) :
    CallableIndexedOwnedAdmittedBodyEntries.Entry (bridge (headers := headers) (keys := keys))
      (condition := CallableIndexedOwnedAllocationProducer.StableOwner keys) (origin := body.origin) (functions := functions) := by
  let original := CallableIndexedOwnedLambdaInvocationBounds.source_entry
    captured code history inputs functions owner caller body entry reached
  have source : CallableIndexedOwnedAdmittedBodyEntries.SourceReceipt program body.origin.function
      body.origin.context original.environment original.heap := by
    change CallableIndexedOwnedAdmittedBodyEntries.SourceReceipt program body.origin.function
      body.origin.context entry.entry.environment entry.entry.heap
    simpa only [body.function_eq, body.context_eq] using
      CallableIndexedOwnedAdmittedBodyEntries.SourceReceipt.of_lambda captured code history inputs functions entry
        body.frame beforeTyped argumentsTyped
  exact CallableIndexedOwnedAdmittedBodyEntries.Entry.of_parameters
    (bridge (headers := headers) (keys := keys)) original source caller stable owner.position entry.nextHistory entry.entry.frame

include beforeTyped argumentsTyped stable in
/-- The measured native prefix exposes the same actual Source allocation and
raw local agreement independently of the native body size. -/
def native_admitted_entry
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    CallableIndexedOwnedAdmittedBodyEntries.Entry (bridge (headers := headers) (keys := keys))
      (condition := CallableIndexedOwnedAllocationProducer.StableOwner keys) (origin := body.origin) (functions := functions) := by
  let original := CallableIndexedOwnedLambdaInvocationBounds.native_entry
    captured code history inputs functions owner caller body entry reached
  have rawArguments : Dynamic.ValuesHaveTypes function.context before arguments
      (function.parameters.map (fun binder => binder.scheme.body)) := by
    simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq inputs.extended] using argumentsTyped
  have allocated := entry.allocation.preservesHeapTyping (beforeTyped.copy entry.copy)
    (rawArguments.mono entry.copy.metadata_extends)
  have fields := Dynamic.MonoBindersExtend.runtimeContextFields inputs.extended
  have heapTyped : Dynamic.HeapWellTyped inputs.context entry.heap :=
    allocated.transportClosed fields.signatures body.frame.code.closed (fields.targetClosed body.frame.code.closed)
      body.frame.code.variables_closed (fields.targetResidualVariablesOpen body.frame.code.residual_variables_open)
  have runtime := CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters body.frame inputs.extended
  have bodyTyped := CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters body.frame inputs.extended
  have source : CallableIndexedOwnedAdmittedBodyEntries.SourceReceipt program body.origin.function
      body.origin.context original.environment original.heap := by
    change CallableIndexedOwnedAdmittedBodyEntries.SourceReceipt program body.origin.function
      body.origin.context entry.environment entry.heap
    simpa only [body.function_eq, body.context_eq] using
      (show CallableIndexedOwnedAdmittedBodyEntries.SourceReceipt program function inputs.context entry.environment entry.heap from
        ⟨runtime.1, runtime.2, heapTyped, entry.locals, bodyTyped⟩)
  exact CallableIndexedOwnedAdmittedBodyEntries.Entry.of_parameters
    (bridge (headers := headers) (keys := keys)) original source caller stable owner.position entry.nextHistory entry.frame

/-- Source packaging preserves the entire original entry definitionally. -/
theorem source_original
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩) :
    (source_admitted_entry captured code history inputs functions owner caller body beforeTyped argumentsTyped stable entry reached).original =
      CallableIndexedOwnedLambdaInvocationBounds.source_entry captured code history inputs functions owner caller body entry reached := rfl

/-- Native packaging retains the actual Prefix entry and initial pool. -/
theorem native_original
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    (native_admitted_entry captured code history inputs functions owner caller body beforeTyped argumentsTyped stable entry reached).original =
      CallableIndexedOwnedLambdaInvocationBounds.native_entry captured code history inputs functions owner caller body entry reached := rfl

variable (wellFormed : ProgramWellFormed program)
  (syntaxTree : GenericImperativeMatch.Syntax body.origin.function.source body.origin.expressionSyntax
    body.origin.context (.statements true body.origin.function.body) body.origin.function.resultType)
  {ι : Type} (origins : ι → CallableRuntimeBodyOrigins.StaticOrigin (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) registry faults)

include wellFormed syntaxTree in
/-- Each actual Source-produced parameter packet selects its authentic family
origin. The callback consumes only the same strict child supplied by Mutual. -/
theorem source_continuation (budget : Nat)
    (selection : ∀ (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
        captured code history inputs functions registry arguments nativeArguments before store owner.key.frameLocation
        (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
      (added : Environment) (_length : added.length = code.receipt.loweredParameters.length)
      (copied : Environment) (_spine : entry.entry.canonical = added ++ copied)
      (_kept : ∀ slot, scope.length ≤ slot → copied[slot]? = captured.canonical[slot]?)
      (reached : State headers keys
        ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
          entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩),
      { i : ι // origins i = source_origin body.origin
        (source_admitted_entry captured code history inputs functions owner caller body beforeTyped argumentsTyped stable entry reached).source.runtime })
    (below : RecursiveNamedCatalogInvocationBounds.Below budget (fun child => ∀ i,
      CallableRuntimeBodyReadyOrigins.PreservesAt (protocol headers keys)
        (readiness (bridge (headers := headers) (keys := keys))) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
        (ProtectedStateImperativeTypedSourceSites.Facts (origins i).function.source (origins i).expressionSyntax)
        functions program (origins i) child)) :
    CallableIndexedOwnedLambdaInvocationBounds.SourceContinuation (arguments := arguments) (nativeArguments := nativeArguments)
      captured code history inputs functions owner caller body budget := by
  intro entry added length copied spine kept reached
  let selected := selection entry added length copied spine kept reached
  exact CallableIndexedOwnedParameterReadyContinuations.source_at
    (source_admitted_entry captured code history inputs functions owner caller body beforeTyped argumentsTyped stable entry reached)
    wellFormed syntaxTree origins selected.val selected.property budget below

include wellFormed syntaxTree in
/-- The authentic measured Prefix and its full captured spine select the
same compiler family origin; reflected Source grades remain independent. -/
theorem native_continuation (budget : Nat)
    (selection : ∀ (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
        captured code history inputs functions registry arguments before store owner.key.frameLocation
        (caller.rows owner.position).authority.current)
      (reached : State headers keys
        ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
          entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩),
      { i : ι // origins i = source_origin body.origin
        (native_admitted_entry captured code history inputs functions owner caller body beforeTyped argumentsTyped stable entry reached).source.runtime })
    (below : RecursiveNamedCatalogInvocationBounds.Below budget (fun child => ∀ i,
      CallableRuntimeBodyReadyOrigins.ReflectsAt (protocol headers keys)
        (readiness (bridge (headers := headers) (keys := keys))) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
        (ProtectedStateImperativeTypedSourceSites.Facts (origins i).function.source (origins i).expressionSyntax)
        functions program (origins i) child)) :
    CallableIndexedOwnedLambdaInvocationBounds.NativeContinuation (arguments := arguments)
      captured code history inputs functions owner caller body budget := by
  intro entry reached
  let selected := selection entry reached
  exact CallableIndexedOwnedParameterReadyContinuations.native_at
    (native_admitted_entry captured code history inputs functions owner caller body beforeTyped argumentsTyped stable entry reached)
    wellFormed syntaxTree origins selected.val selected.property budget below

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaReadyContinuations
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaEntries
/-! Actual method-lambda parameter prefixes retain the genuine trait
principal's bundle and full Source seed. The original same-Code lambda
entry, actual reached pool and original Source admission remain unchanged. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaEntries
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedMethodLambdaSupport

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}

/-- The principal packet and all original ordered pool fields remain together. -/
def bridge (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (principal : SourceCoreGeneralFunctions.Function) :
    CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True)
      (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner principal) :=
  CallableIndexedOwnedIndirectCallerProtocol.forget_slots
    (CallableIndexedOwnedOriginCanonicalState.carrier owner principal)

variable {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (support : Support code registry faults) (sourceOrigin : SourceOrigin support history)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  (leading : captured.administrative[0]? = some support.principal.named.signature.parameterType)
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)

include observed leading sourceOrigin in
/-- Original Source prefix observations authenticate the reached row's own
full seed and the actual captured bundle, without an ordinary Header. -/
theorem source_packet
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history support.body.toContext functions registry arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (added : Environment) (length : added.length = code.receipt.loweredParameters.length)
    (copied : Environment) (spine : entry.entry.canonical = added ++ copied)
    (kept : ∀ slot, scope.length ≤ slot → copied[slot]? = captured.canonical[slot]?)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩) :
    CallableIndexedOwnedOriginCanonicalState.Packet owner support.principal.named _ reached := by
  apply CallableIndexedOwnedOriginCanonicalState.packet_of_stable_read owner support.principal.named reached
  · exact ⟨CallableIndexedOwnedLambdaCanonicalEntries.globals_after_prefix captured code owner 1 observed added length copied spine kept,
      entry.entry.reference⟩
  · exact entry.entry.environments
  · exact leading
  · exact sourceOrigin.metadata ▸ entry.nextHistory
  · exact entry.entry.read

include observed leading sourceOrigin in
/-- The independent measured prefix keeps its exact canonical spine and
read; the authentic method seed selects the reached row's own ghost. -/
theorem native_packet
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history support.body.toContext functions registry arguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    CallableIndexedOwnedOriginCanonicalState.Packet owner support.principal.named _ reached := by
  obtain ⟨added, copied, length, spine, kept⟩ := entry.spine
  apply CallableIndexedOwnedOriginCanonicalState.packet_of_stable_read owner support.principal.named reached
  · exact ⟨CallableIndexedOwnedLambdaCanonicalEntries.globals_after_prefix captured code owner 1 observed added length copied spine kept,
      entry.reference⟩
  · exact entry.environments
  · exact leading
  · exact sourceOrigin.metadata ▸ entry.nextHistory
  · exact entry.read

variable (escaped : faults .controlEscapedFunction code.compilation.internalReason)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments support.body.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)

include observed leading sourceOrigin beforeTyped argumentsTyped stable in
/-- The complete real Source entry is wrapped only with the authenticated
principal packet. Its Source receipt and stable rows are the original ones. -/
def source_admitted_entry
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history support.body.toContext functions registry arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (added : Environment) (length : added.length = code.receipt.loweredParameters.length)
    (copied : Environment) (spine : entry.entry.canonical = added ++ copied)
    (kept : ∀ slot, scope.length ≤ slot → copied[slot]? = captured.canonical[slot]?)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩) :
    CallableIndexedOwnedAdmittedBodyEntries.Entry (bridge (headers := headers) owner support.principal.named)
      (condition := CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (origin := (support.body_origin escaped).origin) (functions := functions) := by
  let base := CallableIndexedOwnedLambdaReadyContinuations.source_admitted_entry
    captured code history support.body.toContext functions owner caller (support.body_origin escaped)
    beforeTyped argumentsTyped stable entry reached
  exact ⟨{ base.original with initial := ⟨reached,
    source_packet captured code history support sourceOrigin functions owner observed leading caller entry added length copied spine kept reached⟩ },
    base.source, base.rows⟩

include observed leading sourceOrigin beforeTyped argumentsTyped stable in
/-- Native admission uses the same actual Prefix allocation and reached pool;
Source body typing is established independently of the native body grade. -/
def native_admitted_entry
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history support.body.toContext functions registry arguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    CallableIndexedOwnedAdmittedBodyEntries.Entry (bridge (headers := headers) owner support.principal.named)
      (condition := CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (origin := (support.body_origin escaped).origin) (functions := functions) := by
  let base := CallableIndexedOwnedLambdaReadyContinuations.native_admitted_entry
    captured code history support.body.toContext functions owner caller (support.body_origin escaped)
    beforeTyped argumentsTyped stable entry reached
  exact ⟨{ base.original with initial := ⟨reached,
    native_packet captured code history support sourceOrigin functions owner observed leading caller entry reached⟩ },
    base.source, base.rows⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaEntries
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaReadyFamilyReceipts
/-! A method-produced lambda retains genuine trait Source authority and its
same-Code generic static body. Actual parameter prefixes construct the exact
principal-protocol index consumed by the shared family's strict body child. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaReadyFamilyReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedMethodLambdaSupport
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedOwnedBodySourceOrigin (source_origin)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- All original Code, Source authority, dictionary and body receipts remain
static. The genuine actual parameter admission supplies Source runtime. -/
structure Index where
  owner : CallableIndexedOwnedFunctionValues.OwnedKey keys
  function : Dynamic.Closure
  scope : SourceCoreLocalCell.Scope
  administrative : Core.Context
  code : Code compiled.indexed function scope administrative
  history : History code
  support : Support code registry faults
  sourceOrigin : SourceOrigin support history
  leading : administrative[0]? = some support.principal.named.signature.parameterType
  escaped : faults .controlEscapedFunction code.compilation.internalReason
  syntaxTree : GenericImperativeMatch.Syntax function.source (support.expressionSyntax function.source)
    support.body.context (.statements true function.body) function.resultType
  sourceRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
    support.body.context function.source

/-- The whole same-Code compiler origin keeps its independent Source domain. -/
def origin (index : Index (keys := keys) (registry := registry) (faults := faults)) :=
  source_origin (index.support.origin index.escaped) index.sourceRuntime

/-- The exact genuine method principal determines its captured packet protocol. -/
def body_protocol (index : Index (keys := keys) (registry := registry) (faults := faults)) :=
  CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) index.owner index.support.principal.named

/-- The bridge retains the same complete actual pool and principal packet. -/
def bridge (index : Index (keys := keys) (registry := registry) (faults := faults)) :=
  CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) index.owner index.support.principal.named

variable {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (support : Support code registry faults) (sourceOrigin : SourceOrigin support history)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  (leading : captured.administrative[0]? = some support.principal.named.signature.parameterType)
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (escaped : faults .controlEscapedFunction code.compilation.internalReason)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments support.body.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)
  (syntaxTree : GenericImperativeMatch.Syntax function.source (support.expressionSyntax function.source)
    support.body.context (.statements true function.body) function.resultType)

/-- Original Source prefix allocation and admission construct this index
internally at the same complete reached parameter pool. -/
def of_source_entry
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history support.body.toContext functions registry arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (added : Environment) (length : added.length = code.receipt.loweredParameters.length)
    (copied : Environment) (spine : entry.entry.canonical = added ++ copied)
    (kept : ∀ slot, scope.length ≤ slot → copied[slot]? = captured.canonical[slot]?)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩) :
    Index (keys := keys) (registry := registry) (faults := faults) :=
  ⟨owner, function, scope, captured.administrative, code, history, support, sourceOrigin,
    leading, escaped, syntaxTree,
    (CallableIndexedOwnedMethodLambdaEntries.source_admitted_entry captured code history support sourceOrigin functions
      owner observed leading caller escaped beforeTyped argumentsTyped stable entry added length copied spine kept reached).source.runtime⟩

/-- Native prefix admission supplies its own genuine runtime receipt without
identifying the independent reflected Source grade with native execution. -/
def of_native_entry
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history support.body.toContext functions registry arguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    Index (keys := keys) (registry := registry) (faults := faults) :=
  ⟨owner, function, scope, captured.administrative, code, history, support, sourceOrigin,
    leading, escaped, syntaxTree,
    (CallableIndexedOwnedMethodLambdaEntries.native_admitted_entry captured code history support sourceOrigin functions
      owner observed leading caller escaped beforeTyped argumentsTyped stable entry reached).source.runtime⟩

variable (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))

include observed leading sourceOrigin beforeTyped argumentsTyped stable syntaxTree wellFormed in
/-- Only the strictly smaller shared-family body is consumed at this exact
authentic parameter index. The complete original entry output is retained. -/
theorem source_continuation (budget : Nat)
    (below : ∀ index : Index (keys := keys) (registry := registry) (faults := faults),
      RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyReadyOrigins.PreservesAt (body_protocol (headers := headers) index)
          (readiness (bridge (headers := headers) index)) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
          (ProtectedStateImperativeTypedSourceSites.Facts (origin index).function.source (origin index).expressionSyntax)
          functions (Program.ofChecked compiled.sourceProgram) (origin index))) :
    CallableIndexedOwnedLambdaInvocationBounds.SourceContinuation (arguments := arguments) (nativeArguments := nativeArguments)
      captured code history support.body.toContext functions owner caller (support.body_origin escaped) budget := by
  intro entry added length copied spine kept reached child strict outcome after trace
  let index := of_source_entry captured code history support sourceOrigin functions owner observed leading caller
    escaped beforeTyped argumentsTyped stable syntaxTree entry added length copied spine kept reached
  let actualEntry := CallableIndexedOwnedMethodLambdaEntries.source_admitted_entry captured code history support sourceOrigin functions
    owner observed leading caller escaped beforeTyped argumentsTyped stable entry added length copied spine kept reached
  have ready := below index child strict
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
      frame, metadata, exit, returned, related, _post⟩ :=
    CallableIndexedOwnedSourceBodyReadyBounds.preserves_at
      (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
      actualEntry.source.runtime wellFormed syntaxTree ready actualEntry trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
    frame, metadata, exit, returned.val, related⟩

include observed leading sourceOrigin beforeTyped argumentsTyped stable syntaxTree wellFormed in
/-- The original measured native prefix supplies this exact index and receives
the same restored body pool with its independently reconstructed Source grade. -/
theorem native_continuation (budget : Nat)
    (below : ∀ index : Index (keys := keys) (registry := registry) (faults := faults),
      RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyReadyOrigins.ReflectsAt (body_protocol (headers := headers) index)
          (readiness (bridge (headers := headers) index)) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
          (ProtectedStateImperativeTypedSourceSites.Facts (origin index).function.source (origin index).expressionSyntax)
          functions (Program.ofChecked compiled.sourceProgram) (origin index))) :
    CallableIndexedOwnedLambdaInvocationBounds.NativeContinuation (arguments := arguments)
      captured code history support.body.toContext functions owner caller (support.body_origin escaped) budget := by
  intro entry reached child strict value finalStore completed
  let index := of_native_entry captured code history support sourceOrigin functions owner observed leading caller
    escaped beforeTyped argumentsTyped stable syntaxTree entry reached
  let actualEntry := CallableIndexedOwnedMethodLambdaEntries.native_admitted_entry captured code history support sourceOrigin functions
    owner observed leading caller escaped beforeTyped argumentsTyped stable entry reached
  have ready := below index child strict
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
      frame, metadata, exit, returned, related, _post⟩ :=
    CallableIndexedOwnedSourceBodyReadyBounds.reflects_at
      (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
      actualEntry.source.runtime wellFormed syntaxTree ready actualEntry completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
    frame, metadata, exit, returned.val, related⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaReadyFamilyReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaFormationReceipts
/-! Actual method-principal packets supply the complete formation history and
captured bundle. Source authority stays in the genuine same-Code support;
native environment tags establish only the corresponding bundle observation.
The formation copies the captured cells and extends the actual store. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaFormationReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedMethodLambdaSupport

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store} {actual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (support : Support code registry faults)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, captured.canonical⟩)
  (packet : CallableIndexedOwnedOriginCanonicalState.Packet owner support.principal.named _ initial)

/-- The packet's own physical row retains the full authentic compiler seed. -/
def history_at : History code where
  native := (initial.rows owner.position).authority.current
  ghost := (initial.rows owner.position).authority.ghost
  metadata := CallableIndexedNamedGeneration.state support.principal.named
  carried := packet.carried
  source := support.source.symm
  owner := by rw [support.compilation]; rfl
  active := support.active.symm

/-- The original method Source seed is retained by construction. -/
theorem source_origin : SourceOrigin support (history_at captured code support owner initial packet) := ⟨rfl⟩

include packet in
/-- The genuine captured environment identifies its existing leading bundle. -/
theorem leading : captured.administrative[0]? = some support.principal.named.signature.parameterType := by
  have bundle := packet.bundle
  rw [captured.represented.runtime_hasTypes.type_tags] at bundle
  simpa [SourceCoreLocalCell.coreContext, List.getElem?_append] using bundle

include support in
/-- Same-Code method compilation fixes the original physical frame slot. -/
theorem reference_index : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length := by
  rw [CallableIndexedLambdaValues.Code.referenceIndex, support.compilation]
  rfl

include packet in
/-- Real Source and native formation, native typing and deterministic output
follow the original producers at this exact packet and pool. The closure is
formed over the copies of its captured cells. -/
theorem formation
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) projects
      compiled.indexed.layouts.definitions}
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (copied : code.policy.snapshotLambda code.id = true)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed model captured code (history_at captured code support owner initial packet) heap store
        owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding)
        (.inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual)) formed.finalStore ∧
      CallableIndexedOwnedMethodLambdaValues.Represents headers keys registry faults formed.finalMap formed.finalWorld
        (FunctionValues.sourceType function) (.closure formed.closure)
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual) ∧ finalStore = formed.finalStore) := by
  exact CallableIndexedOwnedMethodLambdaValues.method_lambda_of_formation initial owner captured code
    (history_at captured code support owner initial packet) support
    (source_origin captured code support owner initial packet) packet.observed
    (reference_index captured code support) rfl profile heaps copied ordinary coercions

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaFormationReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedTypedLambdaStaticBody
/-! This same-Code receipt keeps only the static fields used by typed finish.
Its producer projects the genuine retained body and independent Syntax; no
body tree or Syntax is recovered from Code. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedTypedLambdaStaticBody
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues

structure Body {compiled : SourceCoreUnifiedCompilation.Compiled}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : Code compiled.indexed function scope administrative) (program : Program)
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    (certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    extends CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code where
  frame : Dynamic.ClosureFrame program function
  readFuel : Nat
  flow : Expr
  projection : compiled.compatible.checked.catalog.project function.resultType = .ok code.receipt.resultCore
  emitted : code.receipt.body = CompatibleStatements.finish code.receipt.resultCore flow
    code.compilation.internalReason code.compilation.internalReason
  tree : GenericImperativeMatch.Tree compiled.indexed.layouts code.compilation.owner code.active
    compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length code.allocationError
    (.initial compiled.compatible.checked) function.source
    (expressionSyntax function.source) (certificates readFuel function.source)
    compiled.indexed.layouts.definitions administrative context
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    (.statements true function.body) function.resultType code.receipt.resultCore flow
  valid : CompatibleRuntimeContextValidity.Valid code.compilation.solvedRequirements context function.evidence
  unique : NodeOccurrencesUnique function.source
  syntaxTree : GenericImperativeMatch.Syntax function.source (expressionSyntax function.source)
    context (.statements true function.body) function.resultType

/-- This projection preserves the original Context, flow, tree and Code. -/
def Body.of_body_with {compiled : SourceCoreUnifiedCompilation.Compiled}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {code : Code compiled.indexed function scope administrative} {program : Program}
    {expressionSyntax : TypedSource → ExpressionId → Prop}
    {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (body : CallableIndexedLambdaStaticBodySupport.BodyWith (values := .initial compiled.compatible.checked)
      expressionSyntax certificates code program registry faults)
    (syntaxTree : GenericImperativeMatch.Syntax function.source (expressionSyntax function.source)
      body.context (.statements true function.body) function.resultType) :
    Body code program expressionSyntax certificates where
  toContext := body.toContext
  frame := body.frame
  readFuel := body.readFuel
  flow := body.flow
  projection := body.projection
  emitted := body.emitted
  tree := body.tree
  valid := body.valid
  unique := body.unique
  syntaxTree := syntaxTree

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedTypedLambdaStaticBody
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedTypedLambdaBodyContinuations
/-! Genuine lambda parameter entries supply independent Source admission.
Strict members of the same flow family feed typed finish at those exact
entries; direct control transfers require no escaped token. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedTypedLambdaBodyContinuations
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedBodyEntries (SourceReceipt)
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedOwnedParameterReadyContinuations (bridge)
open RecursiveNamedCatalogInvocationBounds (Below)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  {expressionSyntax : TypedSource → ExpressionId → Prop}
  {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (body : CallableIndexedOwnedTypedLambdaStaticBody.Body code program expressionSyntax certificates)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments body.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)
  (wellFormed : ProgramWellFormed program)

/-- Runtime validity includes the original full ledger and independent Source validity. -/
def Validity (context : SourceSemantics.Context) : Prop :=
  CompatibleRuntimeContextValidity.Valid code.compilation.solvedRequirements context function.evidence ∧
    Dynamic.SourceRuntimeValid program context function.source

/-- This is the strict flow member consumed by the original typed finish core. -/
def FlowPreserves (size : Nat) : Prop :=
  RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (protocol headers keys) (readiness (bridge (headers := headers) (keys := keys)))
    (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (ProtectedStateImperativeTypedSourceSites.Facts function.source (expressionSyntax function.source))
    functions program function.evidence (Validity (program := program) captured code)
    (source := function.source) (context := body.context) (registry := registry) (faults := faults)
    (frameLayout := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length)
    (administrative := captured.administrative) size
    (scope := code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    true function.body function.resultType code.receipt.resultCore body.flow

def FlowReflects (size : Nat) : Prop :=
  RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (protocol headers keys) (readiness (bridge (headers := headers) (keys := keys)))
    (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (ProtectedStateImperativeTypedSourceSites.Facts function.source (expressionSyntax function.source))
    functions program function.evidence (Validity (program := program) captured code)
    (source := function.source) (context := body.context) (registry := registry) (faults := faults)
    (frameLayout := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length)
    (administrative := captured.administrative) size
    (scope := code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    true function.body function.resultType code.receipt.resultCore body.flow

include beforeTyped argumentsTyped in
/-- Source allocation supplies typing at its actual parameter heap. -/
theorem source_receipt
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history body.toContext functions registry arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost) :
    SourceReceipt program function body.context entry.entry.environment entry.entry.heap :=
  SourceReceipt.of_lambda captured code history body.toContext functions entry body.frame beforeTyped argumentsTyped

include beforeTyped argumentsTyped in
/-- The native prefix retains its real raw allocation. Source typing is derived
from that allocation and the complete original ClosureFrame. -/
theorem native_receipt
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history body.toContext functions registry arguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current) :
    SourceReceipt program function body.context entry.environment entry.heap := by
  have rawArguments : Dynamic.ValuesHaveTypes function.context before arguments
      (function.parameters.map (fun binder => binder.scheme.body)) := by
    simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq body.extended] using argumentsTyped
  have allocated := entry.allocation.preservesHeapTyping (beforeTyped.copy entry.copy)
    (rawArguments.mono entry.copy.metadata_extends)
  have fields := Dynamic.MonoBindersExtend.runtimeContextFields body.extended
  have heapTyped : Dynamic.HeapWellTyped body.context entry.heap :=
    allocated.transportClosed fields.signatures body.frame.code.closed (fields.targetClosed body.frame.code.closed)
      body.frame.code.variables_closed (fields.targetResidualVariablesOpen body.frame.code.residual_variables_open)
  have runtime := CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters body.frame body.extended
  have typed := CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters body.frame body.extended
  exact ⟨runtime.1, runtime.2, heapTyped, entry.locals, typed⟩

include stable in
private theorem parameter_rows {next : NativeFrame} {nextGhost : GhostFrame} {metadata : Option MetadataState}
    {final : ProtectedStateTransition.Index}
    (reached : State headers keys final)
    (carried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table next nextGhost metadata)
    (parameters : AdministrativePreserved mapping
      (store.set owner.key.frameLocation (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame next))
      final.mapping final.store) :
    CallableIndexedOwnedIndirectExpressionHeads.StableRows reached := by
  exact CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative
    (install caller owner.position (.stable carried)) reached
    (CallableIndexedOwnedAdmittedBodyEntries.stable_rows_install caller stable owner.position carried) parameters

private theorem body_facts {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    (receipt : SourceReceipt program function body.context environment heap) :
    ProtectedStateImperativeTypedSourceSites.Facts function.source (expressionSyntax function.source)
      body.context true function.body function.resultType := by
  obtain ⟨final, facts, typed, _⟩ := receipt.bodyTyped
  exact ⟨body.syntaxTree, { returnType := function.resultType }, final, facts, typed⟩

include beforeTyped argumentsTyped stable wellFormed in
/-- The strict same-family flow child supplies body meaning at the actual
Source parameter entry. Typed finish closes direct transfers internally. -/
theorem source_continuation (budget : Nat)
    (below : Below budget (FlowPreserves captured code body functions (registry := registry) (faults := faults) (headers := headers) (keys := keys))) :
    CallableIndexedOwnedLambdaEntryBodyContracts.SourceContinuation
      (registry := registry) (faults := faults) (arguments := arguments) (nativeArguments := nativeArguments)
      captured code history body.toContext functions owner caller budget := by
  intro entry _added _length _copied _spine _kept reached child strict outcome after trace
  have source := source_receipt captured code history body functions owner caller beforeTyped argumentsTyped entry
  have admitted : Admission (bridge (headers := headers) (keys := keys)) body.context reached :=
    ⟨source.heapTyped, parameter_rows owner caller stable reached entry.nextHistory entry.entry.frame⟩
  have gate : CallableIndexedOwnedAllocationProducer.StableOwner keys owner.key.frameLocation entry.next :=
    ⟨owner.position, _, _, rfl, entry.nextHistory⟩
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
      frame, metadata, exit, post⟩ :=
    CallableIndexedOwnedTypedFunctionFinishBounds.WithReady.preserves_at_emitted_with_source_receipt
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (functions := functions) (program := program) (tree := body.tree)
      (projection := body.projection) (unique := body.unique)
      (protocol headers keys) (readiness (bridge (headers := headers) (keys := keys)))
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (ProtectedStateImperativeTypedSourceSites.Facts function.source (expressionSyntax function.source))
      body.emitted (Validity (program := program) captured code) child (below child strict) ⟨body.valid, source.runtime⟩
      (body_facts captured code body source)
      entry.entry.environments entry.entry.heaps entry.entry.locals entry.entry.lookups entry.entry.actualTyped
      entry.entry.reference entry.entry.read entry.entry.unmapped reached gate admitted source wellFormed trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
    frame, metadata, exit, post.forget⟩

include beforeTyped argumentsTyped stable wellFormed in
/-- Native finish consumes only strict flow members, preserving its original
measured input and independently reconstructed Source grade. -/
theorem native_continuation (budget : Nat)
    (below : Below budget (FlowReflects captured code body functions (registry := registry) (faults := faults) (headers := headers) (keys := keys))) :
    CallableIndexedOwnedLambdaEntryBodyContracts.NativeContinuation
      (registry := registry) (faults := faults) (arguments := arguments)
      captured code history body.toContext functions owner caller budget := by
  intro entry reached child strict value finalStore completed
  have source := native_receipt captured code history body functions owner caller beforeTyped argumentsTyped entry
  have admitted : Admission (bridge (headers := headers) (keys := keys)) body.context reached :=
    ⟨source.heapTyped, parameter_rows owner caller stable reached entry.nextHistory entry.frame⟩
  have gate : CallableIndexedOwnedAllocationProducer.StableOwner keys owner.key.frameLocation entry.next :=
    ⟨owner.position, _, _, rfl, entry.nextHistory⟩
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
      frame, metadata, exit, post⟩ :=
    CallableIndexedOwnedTypedFunctionFinishBounds.WithReady.reflects_at_emitted_with_source_receipt
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (functions := functions) (program := program) (tree := body.tree)
      (projection := body.projection) (unique := body.unique)
      (protocol headers keys) (readiness (bridge (headers := headers) (keys := keys)))
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (ProtectedStateImperativeTypedSourceSites.Facts function.source (expressionSyntax function.source))
      body.emitted (Validity (program := program) captured code) budget child (Nat.le_of_lt strict) below ⟨body.valid, source.runtime⟩
      (body_facts captured code body source)
      entry.environments entry.heaps entry.locals entry.lookups entry.actualTyped
      entry.reference entry.read entry.unmapped reached gate admitted source wellFormed completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
    frame, metadata, exit, post.forget⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedTypedLambdaBodyContinuations
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaProvenance
/-! Contextual provenance retains the original chosen Site, its real binder
policy, production recipe and independent body Syntax. Constructor indices describe exactly the
existing recapture operation; no Site or Syntax is recovered from Code. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaProvenance
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues
open RecursiveNamedLambdaFormationHeads

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- The equation returned by the original contextual producer. -/
def BinderPolicy {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} (named : CallableIndexedNamedGeneration.Named)
    (code : Code compiled.indexed function scope administrative) : Prop :=
  code.policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder
    ((CallableIndexedNamedGeneration.representation compiled.indexed).atContext named.signature.key [])
    compiled.indexed.base.locals named.signature.key []

/-- Metadata for every expression reached from the original body is retained
verbatim. Edits elsewhere in the source remain allowed. -/
def BodyView {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} (code : Code compiled.indexed function scope administrative) : Prop :=
  ∀ id, CallableLambdaBodyReachability.Reaches function.source
    (function.body.map NodeId.statement) (.expression id) →
    function.source.lookupExpression? id = code.view.lookupExpression? id

theorem BodyView.of_eq {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}
    (same : code.view = function.source) : BodyView code := by
  intro id _reached
  rw [same]

theorem BodyView.of_empty {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}
    (empty : function.body = []) : BodyView code := by
  intro id reached
  have none {node : NodeId} (path : CallableLambdaBodyReachability.Reaches function.source
      (function.body.map NodeId.statement) node) : False := by
    induction path with
    | root member => simp only [empty, List.map_nil, List.not_mem_nil] at member
    | expression _ _ _ ih => exact ih
    | statement _ _ _ ih => exact ih
  exact False.elim (none reached)

/-- Reached reads keep the original token from the compiler's actual issuer. -/
def BodyReasons {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} (code : Code compiled.indexed function scope administrative)
    (named : CallableIndexedNamedGeneration.Named) : Prop :=
  ∀ id, CallableLambdaBodyReachability.Reaches function.source
    (function.body.map NodeId.statement) (.expression id) →
    ∃ diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked),
      compiled.indexed.base.diagnostics = some diagnostics ∧
      code.reasonAt id = diagnostics.program.reasonAt named.signature.key id

theorem BodyReasons.of_issued {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}
    {named : CallableIndexedNamedGeneration.Named}
    {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (issued : compiled.indexed.base.diagnostics = some diagnostics)
    (same : code.reasonAt = diagnostics.program.reasonAt named.signature.key) : BodyReasons code named := by
  intro id _reached
  exact ⟨diagnostics, issued, congrFun same id⟩

theorem BodyReasons.of_empty {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}
    {named : CallableIndexedNamedGeneration.Named} (empty : function.body = []) : BodyReasons code named := by
  intro id reached
  have none {node : NodeId} (path : CallableLambdaBodyReachability.Reaches function.source
      (function.body.map NodeId.statement) node) : False := by
    induction path with
    | root member => simp only [empty, List.map_nil, List.not_mem_nil] at member
    | expression _ _ _ ih => exact ih
    | statement _ _ _ ih => exact ih
  exact False.elim (none reached)

/-- This is the same complete principal support record used at formation. -/
def principal_support {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (site : CallableIndexedLambdaGeneration.Site compiled.indexed principal.named parameters result statements
      context principal.dictionary [] scope administrative)
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    (certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (body : CallableIndexedLambdaStaticBodySupport.BodyWith (values := .initial compiled.compatible.checked)
      expressionSyntax certificates site.code (Program.ofChecked compiled.sourceProgram) registry faults)
    (environment : Dynamic.Environment) :
    CallableIndexedOwnedMethodLambdaSupport.Support (recaptureCode (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) site.code environment) registry faults where
  method := method
  principal := principal
  expressionSyntax := expressionSyntax
  certificates := certificates
  source := rfl
  compilation := site.compilation
  active := site.active
  body := recaptureBodyWith (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) site.code body environment

/-- The actual ordinary seed and static body identify the exact recaptured
Code and Support. All Source fields remain those of the original seed. -/
inductive OrdinaryAt : {function : Dynamic.Closure} → {scope : SourceCoreLocalCell.Scope} →
    {administrative : Core.Context} → (code : Code compiled.indexed function scope administrative) →
    CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults → Prop where
  | recaptured
      (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
      {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
      {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
      {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
      (site : CallableIndexedLambdaGeneration.Site compiled.indexed caller.named parameters result statements
        context evidence [] scope administrative)
      (expressionSyntax : TypedSource → ExpressionId → Prop)
      (certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
      (body : CallableIndexedLambdaStaticBodySupport.BodyWith (values := .initial compiled.compatible.checked)
        expressionSyntax certificates site.code (Program.ofChecked compiled.sourceProgram) registry faults)
      (binderPolicy : BinderPolicy caller.named site.code)
      (recipe : CallableIndexedOwnedContextualLambdaBodyRecipes.Retained caller.named site.code)
      (compilerPolicy : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained caller.named site.code)
      (issuedRecipe : CallableIndexedOwnedContextualLambdaIssuedRecipes.Retained caller.named site.code)
      (bodyView : BodyView site.code)
      (bodyReasons : BodyReasons site.code caller.named)
      (declarations : CompatibleExpressionReads.ScopeDeclarations
        (CallableIndexedNamedGeneration.source caller.named) scope context)
      (syntaxTree : GenericImperativeMatch.Syntax (CallableIndexedNamedGeneration.source caller.named)
        (expressionSyntax (CallableIndexedNamedGeneration.source caller.named)) body.context
        (.statements true statements) result)
      (environment : Dynamic.Environment)
      (globals : caller.globals = compiled.indexed.base.globals.length)
      (callerReceipt : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt caller context evidence) :
      OrdinaryAt (recaptureCode (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) site.code environment)
        ((CallableIndexedOwnedOrdinaryLambdaSupport.Support.of_site caller site expressionSyntax certificates body).recapture environment)

/-- The method seed keeps its own dictionary and principal, never an ordinary
Header. Its full body context and Syntax are indexed by the same chosen Site. -/
inductive PrincipalAt : {function : Dynamic.Closure} → {scope : SourceCoreLocalCell.Scope} →
    {administrative : Core.Context} → (code : Code compiled.indexed function scope administrative) →
    CallableIndexedOwnedMethodLambdaSupport.Support code registry faults → Prop where
  | recaptured {method : ExecutableImplMethods.CheckedMethod}
      (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
      {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
      {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
      (site : CallableIndexedLambdaGeneration.Site compiled.indexed principal.named parameters result statements
        context principal.dictionary [] scope administrative)
      (expressionSyntax : TypedSource → ExpressionId → Prop)
      (certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
      (body : CallableIndexedLambdaStaticBodySupport.BodyWith (values := .initial compiled.compatible.checked)
        expressionSyntax certificates site.code (Program.ofChecked compiled.sourceProgram) registry faults)
      (binderPolicy : BinderPolicy principal.named site.code)
      (recipe : CallableIndexedOwnedContextualLambdaBodyRecipes.Retained principal.named site.code)
      (compilerPolicy : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained principal.named site.code)
      (issuedRecipe : CallableIndexedOwnedContextualLambdaIssuedRecipes.Retained principal.named site.code)
      (bodyView : BodyView site.code)
      (syntaxTree : GenericImperativeMatch.Syntax (CallableIndexedNamedGeneration.source principal.named)
        (expressionSyntax (CallableIndexedNamedGeneration.source principal.named)) body.context
        (.statements true statements) result)
      (environment : Dynamic.Environment) :
      PrincipalAt (recaptureCode (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) site.code environment)
        (principal_support principal site expressionSyntax certificates body environment)

variable {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {code : Code compiled.indexed function scope administrative}

/-- The original formation retained its actual compiled global extent. -/
theorem OrdinaryAt.globals
    {support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults}
    (receipt : OrdinaryAt code support) :
    support.caller.globals = compiled.indexed.base.globals.length := by
  cases receipt with
  | recaptured _ _ _ _ _ _ _ _ _ _ _ _ _ _ globals _callerReceipt => exact globals

/-- The original complete named dictionary and captured context survive recapture. -/
theorem OrdinaryAt.caller_receipt
    {support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults}
    (receipt : OrdinaryAt code support) :
    Nonempty (CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt
      support.caller function.context function.evidence) := by
  cases receipt with
  | recaptured _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ callerReceipt => exact ⟨callerReceipt⟩

/-- Actual parameter extension preserves the caller's runtime context fields. -/
theorem OrdinaryAt.body_caller_receipt
    {support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults}
    (receipt : OrdinaryAt code support) :
    Nonempty (CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt
      support.caller support.body.context function.evidence) := by
  obtain ⟨callerReceipt⟩ := receipt.caller_receipt
  exact ⟨callerReceipt.extend (Dynamic.MonoBindersExtend.runtimeContextFields support.body.extended)⟩

/-- Only proof goals consume the retained seed; no data Site is chosen from
the Prop receipt. Recapture preserves the exact policy definition. -/
theorem OrdinaryAt.binder_policy
    {support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults}
    (receipt : OrdinaryAt code support) : BinderPolicy support.caller.named code := by
  cases receipt with
  | recaptured caller site expressionSyntax certificates body binderPolicy recipe compilerPolicy issuedRecipe bodyView bodyReasons declarations syntaxTree environment _globals _callerReceipt => exact binderPolicy

theorem OrdinaryAt.syntax
    {support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults}
    (receipt : OrdinaryAt code support) :
    GenericImperativeMatch.Syntax function.source (support.expressionSyntax function.source)
      support.body.context (.statements true function.body) function.resultType := by
  cases receipt with
  | recaptured caller site expressionSyntax certificates body binderPolicy recipe compilerPolicy issuedRecipe bodyView bodyReasons declarations syntaxTree environment _globals _callerReceipt => exact syntaxTree

theorem PrincipalAt.binder_policy
    {support : CallableIndexedOwnedMethodLambdaSupport.Support code registry faults}
    (receipt : PrincipalAt code support) : BinderPolicy support.principal.named code := by
  cases receipt with
  | recaptured principal site expressionSyntax certificates body binderPolicy recipe compilerPolicy issuedRecipe bodyView syntaxTree environment => exact binderPolicy

theorem PrincipalAt.syntax
    {support : CallableIndexedOwnedMethodLambdaSupport.Support code registry faults}
    (receipt : PrincipalAt code support) :
    GenericImperativeMatch.Syntax function.source (support.expressionSyntax function.source)
      support.body.context (.statements true function.body) function.resultType := by
  cases receipt with
  | recaptured principal site expressionSyntax certificates body binderPolicy recipe compilerPolicy issuedRecipe bodyView syntaxTree environment => exact syntaxTree

/-- The same original production recipe survives recapture at the ordinary seed. -/
theorem OrdinaryAt.body_recipe
    {support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults}
    (receipt : OrdinaryAt code support) :
    CallableIndexedOwnedContextualLambdaBodyRecipes.Retained support.caller.named code := by
  cases receipt with
  | recaptured caller site expressionSyntax certificates body binderPolicy recipe compilerPolicy issuedRecipe bodyView bodyReasons declarations syntaxTree environment _globals _callerReceipt =>
      exact recipe

/-- Method provenance retains its own principal and the same production recipe. -/
theorem PrincipalAt.body_recipe
    {support : CallableIndexedOwnedMethodLambdaSupport.Support code registry faults}
    (receipt : PrincipalAt code support) :
    CallableIndexedOwnedContextualLambdaBodyRecipes.Retained support.principal.named code := by
  cases receipt with
  | recaptured principal site expressionSyntax certificates body binderPolicy recipe compilerPolicy issuedRecipe bodyView syntaxTree environment =>
      exact recipe

/-- The original actual expression policy remains attached to this same Code
when captures are installed. It is not recovered from body compilation. -/
theorem OrdinaryAt.policy_recipe
    {support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults}
    (receipt : OrdinaryAt code support) :
    CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained support.caller.named code := by
  cases receipt with
  | recaptured caller site expressionSyntax certificates body binderPolicy recipe compilerPolicy issuedRecipe bodyView bodyReasons declarations syntaxTree environment _globals _callerReceipt =>
      exact compilerPolicy

theorem PrincipalAt.policy_recipe
    {support : CallableIndexedOwnedMethodLambdaSupport.Support code registry faults}
    (receipt : PrincipalAt code support) :
    CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained support.principal.named code := by
  cases receipt with
  | recaptured principal site expressionSyntax certificates body binderPolicy recipe compilerPolicy issuedRecipe bodyView syntaxTree environment =>
      exact compilerPolicy

/-- Recapture preserves the exact original body lookups. -/
theorem OrdinaryAt.body_view
    {support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults}
    (receipt : OrdinaryAt code support) : BodyView code := by
  cases receipt with
  | recaptured caller site expressionSyntax certificates body binderPolicy recipe compilerPolicy issuedRecipe bodyView bodyReasons declarations syntaxTree environment _globals _callerReceipt =>
      exact bodyView

/-- Recapture retains the original named diagnostic tokens on all used reads. -/
theorem OrdinaryAt.body_reasons
    {support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults}
    (receipt : OrdinaryAt code support) : BodyReasons code support.caller.named := by
  cases receipt with
  | recaptured caller site expressionSyntax certificates body binderPolicy recipe compilerPolicy issuedRecipe bodyView bodyReasons declarations syntaxTree environment _globals _callerReceipt =>
      exact bodyReasons

/-- The captured scope retains its original Source binder declarations. -/
theorem OrdinaryAt.scope_declarations
    {support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults}
    (receipt : OrdinaryAt code support) :
    CompatibleExpressionReads.ScopeDeclarations function.source scope function.context := by
  cases receipt with
  | recaptured caller site expressionSyntax certificates body binderPolicy recipe compilerPolicy issuedRecipe bodyView bodyReasons declarations syntaxTree environment _globals _callerReceipt =>
      exact declarations

theorem PrincipalAt.body_view
    {support : CallableIndexedOwnedMethodLambdaSupport.Support code registry faults}
    (receipt : PrincipalAt code support) : BodyView code := by
  cases receipt with
  | recaptured principal site expressionSyntax certificates body binderPolicy recipe compilerPolicy issuedRecipe bodyView syntaxTree environment =>
      exact bodyView

/-- The same compiler receipt and actual issued assignment table survive recapture. -/
theorem OrdinaryAt.issued_recipe
    {support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults}
    (receipt : OrdinaryAt code support) :
    CallableIndexedOwnedContextualLambdaIssuedRecipes.Retained support.caller.named code := by
  cases receipt with
  | recaptured caller site expressionSyntax certificates body binderPolicy recipe compilerPolicy issuedRecipe bodyView bodyReasons declarations syntaxTree environment _globals _callerReceipt => exact issuedRecipe

/-- The same compiler receipt and actual issued assignment table survive recapture. -/
theorem PrincipalAt.issued_recipe
    {support : CallableIndexedOwnedMethodLambdaSupport.Support code registry faults}
    (receipt : PrincipalAt code support) :
    CallableIndexedOwnedContextualLambdaIssuedRecipes.Retained support.principal.named code := by
  cases receipt with
  | recaptured principal site expressionSyntax certificates body binderPolicy recipe compilerPolicy issuedRecipe bodyView syntaxTree environment => exact issuedRecipe

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaProvenance
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralLambdaValues
/-! One shared owned function relation includes the complete method model and
ordinary closures with unrestricted genuine same-Code body support. New closures
retain their actual Header seed, captures, physical owner and full static body.
Every model conversion is forward; rich heaps stay under this relation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralLambdaValues
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleEquality
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedOrdinaryLambdaSupport (Support SourceOrigin)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}

/-- Prior method values remain intact. Principal closures retain their
actual leading bundle, and ordinary closures retain the genuine Header prefix. -/
inductive Represents (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping) : TypeSystem.Ty → Dynamic.Value → Value → Ty → Prop where
  | prior {sourceType source native type}
      (related : CallableIndexedOwnedMethodLambdaValues.Represents headers keys registry faults mapping world sourceType source native type) :
      Represents headers keys registry faults mapping world sourceType source native type
  | principal_lambda {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
      (owner : OwnedKey keys) (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code)
      (body : CallableIndexedOwnedMethodLambdaSupport.Support code registry faults)
      (origin : CallableIndexedOwnedMethodLambdaSupport.SourceOrigin body history)
      (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
      (leading : captured.administrative[0]? = some body.principal.named.signature.parameterType)
      (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) compiled.indexed.layouts.definitions) :
      Represents headers keys registry faults mapping world (FunctionValues.sourceType function) (.closure function)
        (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)
  | ordinary_lambda {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
      (owner : OwnedKey keys) (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code)
      (body : Support code registry faults) (origin : SourceOrigin body history)
      (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
        (values := .initial compiled.compatible.checked) body.caller)
      (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
      (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) compiled.indexed.layouts.definitions) :
      Represents headers keys registry faults mapping world (FunctionValues.sourceType function) (.closure function)
        (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)
  | contextual_principal_lambda {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
      (owner : OwnedKey keys) (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code)
      (body : CallableIndexedOwnedMethodLambdaSupport.Support code registry faults)
      (origin : CallableIndexedOwnedMethodLambdaSupport.SourceOrigin body history)
      (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
      (leading : captured.administrative[0]? = some body.principal.named.signature.parameterType)
      (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) compiled.indexed.layouts.definitions)
      (provenance : CallableIndexedOwnedContextualLambdaProvenance.PrincipalAt code body) :
      Represents headers keys registry faults mapping world (FunctionValues.sourceType function) (.closure function)
        (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)
  | contextual_ordinary_lambda {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
      (owner : OwnedKey keys) (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code)
      (body : Support code registry faults) (origin : SourceOrigin body history)
      (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
        (values := .initial compiled.compatible.checked) body.caller)
      (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
      (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) compiled.indexed.layouts.definitions)
      (provenance : CallableIndexedOwnedContextualLambdaProvenance.OrdinaryAt code body) :
      Represents headers keys registry faults mapping world (FunctionValues.sourceType function) (.closure function)
        (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)

theorem Represents.forget {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {native : Value} {type : Ty}
    (related : Represents headers keys registry faults mapping world sourceType source native type) :
    CallableIndexedLambdaValues.Represents compiled.indexed mapping world sourceType source native type := by
  cases related with
  | prior original => exact original.forget
  | principal_lambda owner captured code history body origin globals leading referenceIndex typed =>
    exact .lambda captured code history typed
  | contextual_principal_lambda owner captured code history body origin globals leading referenceIndex typed provenance =>
    exact .lambda captured code history typed
  | ordinary_lambda owner captured code history body origin prefixContext globals referenceIndex typed =>
    exact .lambda captured code history typed

  | contextual_ordinary_lambda owner captured code history body origin prefixContext globals referenceIndex typed provenance =>
    exact .lambda captured code history typed

def model (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed) where
  Represents := fun _ mapping world => Represents headers keys bodyRegistry faults mapping world
  projection := fun related => (CallableIndexedLambdaValues.model compiled.indexed profile).projection
    (registry := bodyRegistry) related.forget
  runtime_hasType := fun related => (CallableIndexedLambdaValues.model compiled.indexed profile).runtime_hasType
    (registry := bodyRegistry) related.forget
  source_function := fun related => (CallableIndexedLambdaValues.model compiled.indexed profile).source_function
    (registry := bodyRegistry) related.forget
  extend := by
    intro registry futureRegistry mapping futureMap world futureWorld sourceType source native type related registries maps worlds
    cases related with
    | prior original => exact .prior ((CallableIndexedOwnedMethodLambdaValues.model headers keys bodyRegistry faults profile).extend
        original registries maps worlds)
    | principal_lambda owner captured code history body origin globals leading referenceIndex typed =>
      exact .principal_lambda owner (captured.extend maps worlds) code history body origin globals leading referenceIndex (typed.weaken worlds)
    | contextual_principal_lambda owner captured code history body origin globals leading referenceIndex typed provenance =>
      exact .contextual_principal_lambda owner (captured.extend maps worlds) code history body origin globals leading referenceIndex (typed.weaken worlds) provenance
    | ordinary_lambda owner captured code history body origin prefixContext globals referenceIndex typed =>
      exact .ordinary_lambda owner (captured.extend maps worlds) code history body origin prefixContext globals referenceIndex (typed.weaken worlds)

    | contextual_ordinary_lambda owner captured code history body origin prefixContext globals referenceIndex typed provenance =>
      exact .contextual_ordinary_lambda owner (captured.extend maps worlds) code history body origin prefixContext globals referenceIndex (typed.weaken worlds) provenance

theorem observations (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    FunctionObservations compiled.compatible.checked.catalog (model headers keys bodyRegistry faults profile)
      (CallableIndexedLambdaValues.Identity compiled.indexed) := by
  intro registry mapping world sourceType source native type related
  exact CallableIndexedLambdaValues.observations compiled.indexed profile (registry := registry) related.forget

theorem runtime_views (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    FunctionRuntimeViews (model headers keys bodyRegistry faults profile) := by
  intro registry mapping world parameter result source native type related
  exact CallableIndexedLambdaValues.runtime_views compiled.indexed profile (registry := registry) related.forget

/-- The entire method relation embeds with its original full payload. -/
theorem includes_method (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    (CallableIndexedOwnedMethodLambdaValues.model headers keys bodyRegistry faults profile).Includes
      (model headers keys bodyRegistry faults profile) := fun related => .prior related

/-- The original owned relation follows the same forward constructor path. -/
theorem includes_original (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    (CallableIndexedOwnedFunctionValues.model headers keys bodyRegistry faults profile).Includes
      (model headers keys bodyRegistry faults profile) := fun related => .prior (.prior related)

/-- Domain embeddings preserve the complete immutable ordinary and method keys. -/
theorem Represents.map_keys {keys futureKeys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {native : Value} {type : Ty}
    (embedding : CallableIndexedOwnedFunctionValues.KeyEmbedding keys futureKeys)
    (related : Represents headers keys registry faults mapping world sourceType source native type) :
    Represents headers futureKeys registry faults mapping world sourceType source native type := by
  cases related with
  | prior original => exact .prior (original.map_keys embedding)
  | @principal_lambda function scope actual owner captured code history body origin globals leading referenceIndex typed =>
    have actualGlobals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers (embedding.map owner).key.locations 1 scope captured.canonical (embedding.map owner).key.frameLocation := by
      rw [embedding.same owner]
      exact globals
    exact .principal_lambda (embedding.map owner) captured code history body origin actualGlobals leading referenceIndex typed
  | @contextual_principal_lambda function scope actual owner captured code history body origin globals leading referenceIndex typed provenance =>
    have actualGlobals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers (embedding.map owner).key.locations 1 scope captured.canonical (embedding.map owner).key.frameLocation := by
      rw [embedding.same owner]
      exact globals
    exact .contextual_principal_lambda (embedding.map owner) captured code history body origin actualGlobals leading referenceIndex typed provenance
  | @ordinary_lambda function scope actual owner captured code history body origin prefixContext globals referenceIndex typed =>
    have actualGlobals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers (embedding.map owner).key.locations 1 scope captured.canonical (embedding.map owner).key.frameLocation := by
      rw [embedding.same owner]
      exact globals
    exact .ordinary_lambda (embedding.map owner) captured code history body origin prefixContext actualGlobals referenceIndex typed

  | @contextual_ordinary_lambda function scope actual owner captured code history body origin prefixContext globals referenceIndex typed provenance =>
    have actualGlobals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers (embedding.map owner).key.locations 1 scope captured.canonical (embedding.map owner).key.frameLocation := by
      rw [embedding.same owner]
      exact globals
    exact .contextual_ordinary_lambda (embedding.map owner) captured code history body origin prefixContext actualGlobals referenceIndex typed provenance

theorem includes {keys futureKeys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
    (embedding : CallableIndexedOwnedFunctionValues.KeyEmbedding keys futureKeys)
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    (model headers keys bodyRegistry faults profile).Includes (model headers futureKeys bodyRegistry faults profile) :=
  fun related => related.map_keys embedding

/-- A genuine closure keeps either its complete method-model payload or
all unrestricted ordinary support, Source and capture receipts. -/
theorem Represents.closure_cases {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {function : Dynamic.Closure} {native : Value} {type : Ty}
    (related : Represents headers keys registry faults mapping world sourceType (.closure function) native type) :
    CallableIndexedOwnedMethodLambdaValues.Represents headers keys registry faults mapping world sourceType (.closure function) native type ∨
    ∃ owner : OwnedKey keys, ∃ scope actual,
      ∃ (captured : Captures compiled.indexed mapping world scope function.captured actual)
        (code : Code compiled.indexed function scope captured.administrative) (history : History code)
        (body : Support code registry faults),
        SourceOrigin body history ∧
        captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
          (values := .initial compiled.compatible.checked) body.caller ∧
        CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
          (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
          headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation ∧
        code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length ∧
        sourceType = FunctionValues.sourceType function ∧ native = value code captured.embedding history.native actual ∧
        type = CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore ∧
        RuntimeValueHasType world (value code captured.embedding history.native actual)
          (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) compiled.indexed.layouts.definitions := by
  cases related with
  | prior original => exact Or.inl original
  | principal_lambda owner captured code history body origin globals leading referenceIndex typed =>
    exact Or.inl (.method_lambda owner captured code history body origin globals referenceIndex typed)
  | contextual_principal_lambda owner captured code history body origin globals leading referenceIndex typed provenance =>
    exact Or.inl (.method_lambda owner captured code history body origin globals referenceIndex typed)
  | ordinary_lambda owner captured code history body origin prefixContext globals referenceIndex typed =>
    exact Or.inr ⟨owner, _, _, captured, code, history, body, origin, prefixContext, globals, referenceIndex, rfl, rfl, rfl, typed⟩

  | contextual_ordinary_lambda owner captured code history body origin prefixContext globals referenceIndex typed provenance =>
    exact Or.inr ⟨owner, _, _, captured, code, history, body, origin, prefixContext, globals, referenceIndex, rfl, rfl, rfl, typed⟩

/-- Actual ordinary formation reads its existing physical frame and retains
the full owned history and body. Original primitive producers supply Source
formation, native completion, typing and output determinism. The value copies
its captured cells, and the copies keep the catalog slots and the frame cell. -/
theorem ordinary_lambda_of_formation
    {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
    {bodyRegistry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
    (pool : CallableIndexedAuthorityPool.Pool (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers keys mapping world heap store)
    (owner : OwnedKey keys) (captured : Captures compiled.indexed mapping world scope function.captured actual)
    (code : Code compiled.indexed function scope captured.administrative) (history : History code)
    (body : Support code bodyRegistry faults) (origin : SourceOrigin body history)
    (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
      (values := .initial compiled.compatible.checked) body.caller)
    (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
      headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
    (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
    (current : (pool.rows owner.position).authority.current = history.native)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) projects
      compiled.indexed.layouts.definitions}
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (copied : code.policy.snapshotLambda code.id = true)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed model captured code history heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding)
        (.inRight .word (value code formed.embedding history.native formed.closureActual)) formed.finalStore ∧
      Represents headers keys bodyRegistry faults formed.finalMap formed.finalWorld (FunctionValues.sourceType function)
        (.closure formed.closure) (value code formed.embedding history.native formed.closureActual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (value code formed.embedding history.native formed.closureActual) ∧
          finalStore = formed.finalStore) := by
  have reference : captured.canonical[code.referenceIndex]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
    rw [referenceIndex]
    exact globals.reference
  have read : store.read? owner.key.frameLocation =
      some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame history.native) := by
    have actualRead := (pool.rows owner.position).authority.frame.read
    rw [(pool.rows owner.position).frame_eq, current] at actualRead
    exact actualRead
  obtain ⟨formed⟩ := CallableIndexedLambdaValues.formation captured code history copied referenceIndex heaps reference read
  have typed := (CallableIndexedLambdaValues.model compiled.indexed profile).runtime_hasType
    (registry := bodyRegistry) (formed.represents heaps.runtime_hasTypes)
  exact ⟨formed, formed.source _ ordinary coercions, formed.evaluated,
    .ordinary_lambda (function := formed.closure) owner formed.captures formed.closureCode formed.closureHistory
      (body.recapture formed.captured) ⟨origin.metadata⟩ prefixContext (globals.of_slots formed.slots)
      referenceIndex typed,
    fun _ _ completed => Core.evaluation_deterministic completed formed.evaluated⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralLambdaValues
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaNestedEntries
/-! The real lambda parameter spine retains its lexical principal's original
named Source seed, captured bundle and canonical globals. Both Source and
native entry factories use their own actual reached parameter pools. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaNestedEntries
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open SourceCoreCallableIndexedFrames RecursiveNamedLambdaFormationHeads
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative)
  (history : History code) (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (principal : CallableIndexedOwnedFunctionValues.Header compiled program)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := program)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  (prefixContext : captured.administrative = nativePrefix (indexed := compiled.indexed) (values := .initial compiled.compatible.checked) (program := program) principal)
  (sourceSeed : history.metadata = CallableIndexedNamedGeneration.state principal.named)
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (body : CallableIndexedOwnedLambdaInvocationBounds.BodyOrigin (program := program) code inputs registry faults)

include observed prefixContext sourceSeed in
theorem source_packet
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (added : Environment) (length : added.length = code.receipt.loweredParameters.length)
    (copied : Environment) (spine : entry.entry.canonical = added ++ copied)
    (kept : ∀ slot, scope.length ≤ slot → copied[slot]? = captured.canonical[slot]?)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩) :
    CallableIndexedOwnedNestedCanonicalState.Packet owner principal _ reached := by
  apply CallableIndexedOwnedNestedCanonicalState.packet_of_stable_read owner principal reached
  · exact ⟨CallableIndexedOwnedLambdaCanonicalEntries.globals_after_prefix captured code owner 1 observed added length copied spine kept,
      entry.entry.reference⟩
  · exact entry.entry.environments
  · rw [prefixContext]
    rfl
  · exact sourceSeed ▸ entry.nextHistory
  · exact entry.entry.read

include observed prefixContext sourceSeed in
theorem native_packet
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    CallableIndexedOwnedNestedCanonicalState.Packet owner principal _ reached := by
  obtain ⟨added, copied, length, spine, kept⟩ := entry.spine
  apply CallableIndexedOwnedNestedCanonicalState.packet_of_stable_read owner principal reached
  · exact ⟨CallableIndexedOwnedLambdaCanonicalEntries.globals_after_prefix captured code owner 1 observed added length copied spine kept,
      entry.reference⟩
  · exact entry.environments
  · rw [prefixContext]
    rfl
  · exact sourceSeed ▸ entry.nextHistory
  · exact entry.read

include observed prefixContext sourceSeed in
def source_entry
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (added : Environment) (length : added.length = code.receipt.loweredParameters.length)
    (copied : Environment) (spine : entry.entry.canonical = added ++ copied)
    (kept : ∀ slot, scope.length ≤ slot → copied[slot]? = captured.canonical[slot]?)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩) :
    CallableRuntimeBodyOrigins.Stateful.Entry
      (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner principal)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) body.origin functions :=
  CallableIndexedOwnedBodyNestedEntries.wrap functions owner principal
    (CallableIndexedOwnedLambdaInvocationBounds.source_entry captured code history inputs functions owner caller body entry reached)
    (by
      change CallableIndexedOwnedNestedCanonicalState.Packet owner principal
        ⟨body.origin.scope, entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩ reached
      rw [body.scope_eq]
      exact source_packet captured code history inputs functions owner principal observed prefixContext sourceSeed caller entry added length copied spine kept reached)

include observed prefixContext sourceSeed in
def native_entry
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    CallableRuntimeBodyOrigins.Stateful.Entry
      (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner principal)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) body.origin functions :=
  CallableIndexedOwnedBodyNestedEntries.wrap functions owner principal
    (CallableIndexedOwnedLambdaInvocationBounds.native_entry captured code history inputs functions owner caller body entry reached)
    (by
      change CallableIndexedOwnedNestedCanonicalState.Packet owner principal
        ⟨body.origin.scope, entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩ reached
      rw [body.scope_eq]
      exact native_packet captured code history inputs functions owner principal observed prefixContext sourceSeed caller entry reached)

include observed prefixContext sourceSeed in
/-- The strict family callback is applied only to the genuine Source-produced
parameter entry, with its actual spine and full reached pool. -/
theorem source_continuation_of_nested (budget : Nat)
    (meaning : ∀ (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
        captured code history inputs functions registry arguments nativeArguments before store owner.key.frameLocation
        (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
      (added : Environment) (length : added.length = code.receipt.loweredParameters.length)
      (copied : Environment) (spine : entry.entry.canonical = added ++ copied)
      (kept : ∀ slot, scope.length ≤ slot → copied[slot]? = captured.canonical[slot]?)
      (reached : State headers keys
        ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
          entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩),
      RecursiveNamedBoundedContracts.Below budget (CallableRuntimeBodyEntryContracts.PreservesAt
        (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (protocol := CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner principal)
        (conditionGate := CallableIndexedOwnedAllocationProducer.StableOwner keys) (origin := body.origin)
        functions program (source_entry captured code history inputs functions owner principal observed prefixContext sourceSeed
          caller body entry added length copied spine kept reached))) :
    CallableIndexedOwnedLambdaInvocationBounds.SourceContinuation (arguments := arguments) (nativeArguments := nativeArguments)
      captured code history inputs functions owner caller body budget := by
  intro entry added length copied spine kept reached child strict
  exact CallableIndexedOwnedBodyNestedEntries.preserves_of_nested functions owner principal
    (CallableIndexedOwnedLambdaInvocationBounds.source_entry captured code history inputs functions owner caller body entry reached)
    _ (meaning entry added length copied spine kept reached child strict)

include observed prefixContext sourceSeed in
/-- Native reflection uses its own real measured prefix. The independent
Source body grade and the actual returned pool survive projection. -/
theorem native_continuation_of_nested (budget : Nat)
    (meaning : ∀ (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
        captured code history inputs functions registry arguments before store owner.key.frameLocation
        (caller.rows owner.position).authority.current)
      (reached : State headers keys
        ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
          entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩),
      RecursiveNamedBoundedContracts.Below budget (CallableRuntimeBodyEntryContracts.ReflectsAt
        (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (protocol := CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner principal)
        (conditionGate := CallableIndexedOwnedAllocationProducer.StableOwner keys) (origin := body.origin)
        functions program (native_entry captured code history inputs functions owner principal observed prefixContext sourceSeed
          caller body entry reached))) :
    CallableIndexedOwnedLambdaInvocationBounds.NativeContinuation (arguments := arguments)
      captured code history inputs functions owner caller body budget := by
  intro entry reached child strict
  exact CallableIndexedOwnedBodyNestedEntries.reflects_of_nested functions owner principal
    (CallableIndexedOwnedLambdaInvocationBounds.native_entry captured code history inputs functions owner caller body entry reached)
    _ (meaning entry reached child strict)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaNestedEntries
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaNestedReadyContinuations
/-! Real anonymous parameter entries retain complete captures, code, Source
frames and their own reached ordered pool. Genuine raw Source arguments and
actual hook/parameter effects supply admission before the strict shared child.
Authentic captured slots, prefix and full Source seed add a nested packet to
the same real pool; no slots are inferred from base ownership. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaNestedReadyContinuations
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedLambdaValues
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedOwnedBodySourceOrigin (source_origin)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (body : CallableIndexedOwnedLambdaInvocationBounds.BodyOrigin (program := program) code inputs registry faults)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments inputs.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)
  (principal : CallableIndexedOwnedFunctionValues.Header compiled program)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := program)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (indexed := compiled.indexed) (values := .initial compiled.compatible.checked) (program := program) principal)
  (sourceSeed : history.metadata = CallableIndexedNamedGeneration.state principal.named)

/-- The genuine nested packet carries full globals, bundle and Source seed;
its bridge projects and restores exactly the same actual pool. -/
def bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True)
    (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner principal) :=
  CallableIndexedOwnedIndirectCallerProtocol.forget_slots (CallableIndexedOwnedNestedCallerProtocol.carrier owner principal)

include beforeTyped argumentsTyped stable observed prefixContext sourceSeed in
/-- Source admission and stable histories belong to the actual Source prefix
post, whose full captured canonical spine and nextHistory remain original. -/
def source_admitted_entry
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (added : Environment) (length : added.length = code.receipt.loweredParameters.length)
    (copied : Environment) (spine : entry.entry.canonical = added ++ copied)
    (kept : ∀ slot, scope.length ≤ slot → copied[slot]? = captured.canonical[slot]?)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩) :
    CallableIndexedOwnedAdmittedBodyEntries.Entry (bridge (headers := headers) owner principal)
      (condition := CallableIndexedOwnedAllocationProducer.StableOwner keys) (origin := body.origin) (functions := functions) := by
  let base := CallableIndexedOwnedLambdaReadyContinuations.source_admitted_entry
    captured code history inputs functions owner caller body beforeTyped argumentsTyped stable entry reached
  exact ⟨CallableIndexedOwnedLambdaNestedEntries.source_entry captured code history inputs functions owner principal
    observed prefixContext sourceSeed caller body entry added length copied spine kept reached, base.source, base.rows⟩

include beforeTyped argumentsTyped stable observed prefixContext sourceSeed in
/-- The measured native prefix exposes the same actual Source allocation and
raw local agreement independently of the native body size. -/
def native_admitted_entry
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    CallableIndexedOwnedAdmittedBodyEntries.Entry (bridge (headers := headers) owner principal)
      (condition := CallableIndexedOwnedAllocationProducer.StableOwner keys) (origin := body.origin) (functions := functions) := by
  let base := CallableIndexedOwnedLambdaReadyContinuations.native_admitted_entry
    captured code history inputs functions owner caller body beforeTyped argumentsTyped stable entry reached
  exact ⟨CallableIndexedOwnedLambdaNestedEntries.native_entry captured code history inputs functions owner principal
    observed prefixContext sourceSeed caller body entry reached, base.source, base.rows⟩

/-- Source packaging preserves the entire original entry definitionally. -/
theorem source_original
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (added : Environment) (length : added.length = code.receipt.loweredParameters.length)
    (copied : Environment) (spine : entry.entry.canonical = added ++ copied)
    (kept : ∀ slot, scope.length ≤ slot → copied[slot]? = captured.canonical[slot]?)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩) :
    (source_admitted_entry captured code history inputs functions owner caller body beforeTyped argumentsTyped stable principal observed prefixContext sourceSeed entry added length copied spine kept reached).original =
      CallableIndexedOwnedLambdaNestedEntries.source_entry captured code history inputs functions owner principal
        observed prefixContext sourceSeed caller body entry added length copied spine kept reached := rfl

/-- Native packaging retains the actual Prefix entry and initial pool. -/
theorem native_original
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    (native_admitted_entry captured code history inputs functions owner caller body beforeTyped argumentsTyped stable principal observed prefixContext sourceSeed entry reached).original =
      CallableIndexedOwnedLambdaNestedEntries.native_entry captured code history inputs functions owner principal
        observed prefixContext sourceSeed caller body entry reached := rfl

variable (wellFormed : ProgramWellFormed program)
  (syntaxTree : GenericImperativeMatch.Syntax body.origin.function.source body.origin.expressionSyntax
    body.origin.context (.statements true body.origin.function.body) body.origin.function.resultType)
  {ι : Type} (origins : ι → CallableRuntimeBodyOrigins.StaticOrigin (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) registry faults)

include wellFormed syntaxTree in
/-- Each actual Source-produced parameter packet selects its authentic family
origin. The callback consumes only the same strict child supplied by Mutual. -/
theorem source_continuation (budget : Nat)
    (selection : ∀ (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
        captured code history inputs functions registry arguments nativeArguments before store owner.key.frameLocation
        (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
      (added : Environment) (length : added.length = code.receipt.loweredParameters.length)
      (copied : Environment) (spine : entry.entry.canonical = added ++ copied)
      (kept : ∀ slot, scope.length ≤ slot → copied[slot]? = captured.canonical[slot]?)
      (reached : State headers keys
        ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
          entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩),
      { i : ι // origins i = source_origin body.origin
        (source_admitted_entry captured code history inputs functions owner caller body beforeTyped argumentsTyped stable principal observed prefixContext sourceSeed entry added length copied spine kept reached).source.runtime })
    (below : RecursiveNamedCatalogInvocationBounds.Below budget (fun child => ∀ i,
      CallableRuntimeBodyReadyOrigins.PreservesAt (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner principal)
        (readiness (bridge (headers := headers) owner principal)) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
        (ProtectedStateImperativeTypedSourceSites.Facts (origins i).function.source (origins i).expressionSyntax)
        functions program (origins i) child)) :
    CallableIndexedOwnedLambdaInvocationBounds.SourceContinuation (arguments := arguments) (nativeArguments := nativeArguments)
      captured code history inputs functions owner caller body budget := by
  intro entry added length copied spine kept reached
  let selected := selection entry added length copied spine kept reached
  intro child strict outcome after trace
  have ready := below child strict selected.val
  rw [selected.property] at ready
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
      frame, metadata, exit, returned, related, _post⟩ :=
    CallableIndexedOwnedSourceBodyReadyBounds.preserves_at (bridge (headers := headers) owner principal)
      (source_admitted_entry captured code history inputs functions owner caller body beforeTyped argumentsTyped stable principal observed prefixContext sourceSeed entry added length copied spine kept reached).source.runtime
      wellFormed syntaxTree ready
      (source_admitted_entry captured code history inputs functions owner caller body beforeTyped argumentsTyped stable principal observed prefixContext sourceSeed entry added length copied spine kept reached) trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
    frame, metadata, exit, returned.val, related⟩

include wellFormed syntaxTree in
/-- The authentic measured Prefix and its full captured spine select the
same compiler family origin; reflected Source grades remain independent. -/
theorem native_continuation (budget : Nat)
    (selection : ∀ (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
        captured code history inputs functions registry arguments before store owner.key.frameLocation
        (caller.rows owner.position).authority.current)
      (reached : State headers keys
        ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
          entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩),
      { i : ι // origins i = source_origin body.origin
        (native_admitted_entry captured code history inputs functions owner caller body beforeTyped argumentsTyped stable principal observed prefixContext sourceSeed entry reached).source.runtime })
    (below : RecursiveNamedCatalogInvocationBounds.Below budget (fun child => ∀ i,
      CallableRuntimeBodyReadyOrigins.ReflectsAt (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner principal)
        (readiness (bridge (headers := headers) owner principal)) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
        (ProtectedStateImperativeTypedSourceSites.Facts (origins i).function.source (origins i).expressionSyntax)
        functions program (origins i) child)) :
    CallableIndexedOwnedLambdaInvocationBounds.NativeContinuation (arguments := arguments)
      captured code history inputs functions owner caller body budget := by
  intro entry reached
  let selected := selection entry reached
  intro child strict value finalStore completed
  have ready := below child strict selected.val
  rw [selected.property] at ready
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
      frame, metadata, exit, returned, related, _post⟩ :=
    CallableIndexedOwnedSourceBodyReadyBounds.reflects_at (bridge (headers := headers) owner principal)
      (native_admitted_entry captured code history inputs functions owner caller body beforeTyped argumentsTyped stable principal observed prefixContext sourceSeed entry reached).source.runtime
      wellFormed syntaxTree ready
      (native_admitted_entry captured code history inputs functions owner caller body beforeTyped argumentsTyped stable principal observed prefixContext sourceSeed entry reached) completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
    frame, metadata, exit, returned.val, related⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaNestedReadyContinuations
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaEntries
/-! Unrestricted ordinary static support enters the existing actual lambda
parameter producers through its genuine cached Header and complete Source seed.
Full real Entry/Prefix, raw Source receipt and reached ordered pool stay original.
The function model remains a parameter throughout these finite adapters. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaEntries
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedOrdinaryLambdaSupport

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}

/-- The genuine nested Header packet projects and restores the same pool. -/
def bridge (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)) :=
  CallableIndexedOwnedLambdaNestedReadyContinuations.bridge (headers := headers) owner caller

variable {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (support : Support code registry faults) (sourceOrigin : SourceOrigin support history)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) support.caller)
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)

include observed prefixContext sourceOrigin in
/-- The actual Source Entry and spine select the original Header packet. -/
theorem source_packet
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history support.body.toContext functions registry arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (added : Environment) (length : added.length = code.receipt.loweredParameters.length)
    (copied : Environment) (spine : entry.entry.canonical = added ++ copied)
    (kept : ∀ slot, scope.length ≤ slot → copied[slot]? = captured.canonical[slot]?)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩) :
    CallableIndexedOwnedNestedCanonicalState.Packet owner support.caller _ reached :=
  CallableIndexedOwnedLambdaNestedEntries.source_packet captured code history support.body.toContext
    functions owner support.caller observed prefixContext sourceOrigin.metadata caller entry added length copied spine kept reached

include observed prefixContext sourceOrigin in
/-- The independent native Prefix keeps its real spine, read and full seed. -/
theorem native_packet
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history support.body.toContext functions registry arguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    CallableIndexedOwnedNestedCanonicalState.Packet owner support.caller _ reached :=
  CallableIndexedOwnedLambdaNestedEntries.native_packet captured code history support.body.toContext
    functions owner support.caller observed prefixContext sourceOrigin.metadata caller entry reached

variable (escaped : faults .controlEscapedFunction code.compilation.internalReason)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments support.body.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)

include observed prefixContext sourceOrigin beforeTyped argumentsTyped stable in
/-- The complete real Source entry is wrapped only with the authenticated
Header packet. Its Source receipt and stable rows are the original ones. -/
def source_admitted_entry
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history support.body.toContext functions registry arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (added : Environment) (length : added.length = code.receipt.loweredParameters.length)
    (copied : Environment) (spine : entry.entry.canonical = added ++ copied)
    (kept : ∀ slot, scope.length ≤ slot → copied[slot]? = captured.canonical[slot]?)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩) :
    CallableIndexedOwnedAdmittedBodyEntries.Entry (bridge (headers := headers) owner support.caller)
      (condition := CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (origin := (support.body_origin escaped).origin) (functions := functions) :=
  CallableIndexedOwnedLambdaNestedReadyContinuations.source_admitted_entry
    captured code history support.body.toContext functions owner caller (support.body_origin escaped)
    beforeTyped argumentsTyped stable support.caller observed prefixContext sourceOrigin.metadata
    entry added length copied spine kept reached

include observed prefixContext sourceOrigin beforeTyped argumentsTyped stable in
/-- Native admission uses the same actual Prefix allocation and reached pool;
Source body typing is established independently of the native body grade. -/
def native_admitted_entry
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history support.body.toContext functions registry arguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    CallableIndexedOwnedAdmittedBodyEntries.Entry (bridge (headers := headers) owner support.caller)
      (condition := CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (origin := (support.body_origin escaped).origin) (functions := functions) :=
  CallableIndexedOwnedLambdaNestedReadyContinuations.native_admitted_entry
    captured code history support.body.toContext functions owner caller (support.body_origin escaped)
    beforeTyped argumentsTyped stable support.caller observed prefixContext sourceOrigin.metadata entry reached

include observed prefixContext sourceOrigin beforeTyped argumentsTyped stable in
/-- The Source adapter retains exactly the producer's full reached pool. -/
theorem source_pool
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history support.body.toContext functions registry arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (added : Environment) (length : added.length = code.receipt.loweredParameters.length)
    (copied : Environment) (spine : entry.entry.canonical = added ++ copied)
    (kept : ∀ slot, scope.length ≤ slot → copied[slot]? = captured.canonical[slot]?)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩) :
    (source_admitted_entry captured code history support sourceOrigin functions owner observed prefixContext caller
      escaped beforeTyped argumentsTyped stable entry added length copied spine kept reached).original.initial.val = reached := rfl

include observed prefixContext sourceOrigin beforeTyped argumentsTyped stable in
/-- Native packaging retains the independent Prefix producer's same pool. -/
theorem native_pool
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history support.body.toContext functions registry arguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    (native_admitted_entry captured code history support sourceOrigin functions owner observed prefixContext caller
      escaped beforeTyped argumentsTyped stable entry reached).original.initial.val = reached := rfl

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaEntries
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaReadyFamilyReceipts
/-! Genuine lambda code, complete captured compiler seed and original body
Syntax construct a dependent family index at the actual parameter entry.
Its strict child is consumed through the original pointwise continuation. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaReadyFamilyReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedLambdaValues
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedOwnedBodySourceOrigin (source_origin)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- Code and body alignments remain original receipts. Runtime validity is
independent raw Source authority, supplied by the actual parameter admission. -/
structure Index where
  owner : CallableIndexedOwnedFunctionValues.OwnedKey keys
  principal : CallableIndexedOwnedFunctionValues.Header compiled program
  function : Dynamic.Closure
  scope : SourceCoreLocalCell.Scope
  administrative : Core.Context
  code : Code compiled.indexed function scope administrative
  history : History code
  inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code
  body : CallableIndexedOwnedLambdaInvocationBounds.BodyOrigin (program := program) code inputs registry faults
  prefixContext : administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (indexed := compiled.indexed) (values := .initial compiled.compatible.checked) (program := program) principal
  sourceSeed : history.metadata = CallableIndexedNamedGeneration.state principal.named
  syntaxTree : GenericImperativeMatch.Syntax body.origin.function.source body.origin.expressionSyntax
    body.origin.context (.statements true body.origin.function.body) body.origin.function.resultType
  sourceRuntime : Dynamic.SourceRuntimeValid program body.origin.context body.origin.function.source

/-- The whole compiler origin is retained, with its genuine Source domain. -/
def origin (index : Index (keys := keys) (registry := registry) (faults := faults)) :=
  source_origin index.body.origin index.sourceRuntime

/-- This exact captured principal and owner determine the stronger protocol. -/
def body_protocol (index : Index (keys := keys) (registry := registry) (faults := faults)) :=
  CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) index.owner index.principal

/-- The bridge keeps the complete actual pool beside the principal packet. -/
def bridge (index : Index (keys := keys) (registry := registry) (faults := faults)) :=
  CallableIndexedOwnedLambdaNestedReadyContinuations.bridge (headers := headers) index.owner index.principal

variable {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (body : CallableIndexedOwnedLambdaInvocationBounds.BodyOrigin (program := program) code inputs registry faults)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments inputs.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)
  (principal : CallableIndexedOwnedFunctionValues.Header compiled program)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := program)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (indexed := compiled.indexed) (values := .initial compiled.compatible.checked) (program := program) principal)
  (sourceSeed : history.metadata = CallableIndexedNamedGeneration.state principal.named)
  (syntaxTree : GenericImperativeMatch.Syntax body.origin.function.source body.origin.expressionSyntax
    body.origin.context (.statements true body.origin.function.body) body.origin.function.resultType)

/-- The real Source prefix supplies its runtime receipt. No arbitrary closure
representation or external origin-selection function is used. -/
def of_source_entry
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (added : Environment) (length : added.length = code.receipt.loweredParameters.length)
    (copied : Environment) (spine : entry.entry.canonical = added ++ copied)
    (kept : ∀ slot, scope.length ≤ slot → copied[slot]? = captured.canonical[slot]?)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩) :
    Index (keys := keys) (registry := registry) (faults := faults) :=
  ⟨owner, principal, function, scope, captured.administrative, code, history, inputs, body,
    prefixContext, sourceSeed, syntaxTree,
    (CallableIndexedOwnedLambdaNestedReadyContinuations.source_admitted_entry captured code history inputs functions owner caller body
      beforeTyped argumentsTyped stable principal observed prefixContext sourceSeed entry added length copied spine kept reached).source.runtime⟩

/-- The measured native prefix retains the same compiler/body receipts and
supplies independent raw Source admission at its own reached pool. -/
def of_native_entry
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    Index (keys := keys) (registry := registry) (faults := faults) :=
  ⟨owner, principal, function, scope, captured.administrative, code, history, inputs, body,
    prefixContext, sourceSeed, syntaxTree,
    (CallableIndexedOwnedLambdaNestedReadyContinuations.native_admitted_entry captured code history inputs functions owner caller body
      beforeTyped argumentsTyped stable principal observed prefixContext sourceSeed entry reached).source.runtime⟩

variable (wellFormed : ProgramWellFormed program)

include wellFormed beforeTyped argumentsTyped stable observed prefixContext sourceSeed syntaxTree in
/-- Each authentic actual Source parameter entry constructs its index and
uses only the strict shared-family child in that index's exact protocol. -/
theorem source_continuation (budget : Nat)
    (below : ∀ index : Index (keys := keys) (registry := registry) (faults := faults),
      RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyReadyOrigins.PreservesAt (body_protocol (headers := headers) index)
          (readiness (bridge (headers := headers) index)) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
          (ProtectedStateImperativeTypedSourceSites.Facts (origin index).function.source (origin index).expressionSyntax)
          functions program (origin index))) :
    CallableIndexedOwnedLambdaInvocationBounds.SourceContinuation (arguments := arguments) (nativeArguments := nativeArguments)
      captured code history inputs functions owner caller body budget := by
  intro entry added length copied spine kept reached child strict outcome after trace
  let index := of_source_entry captured code history inputs functions owner caller body beforeTyped argumentsTyped stable
    principal observed prefixContext sourceSeed syntaxTree entry added length copied spine kept reached
  let actualEntry := CallableIndexedOwnedLambdaNestedReadyContinuations.source_admitted_entry
    captured code history inputs functions owner caller body beforeTyped argumentsTyped stable
    principal observed prefixContext sourceSeed entry added length copied spine kept reached
  have ready := below index child strict
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
      frame, metadata, exit, returned, related, _post⟩ :=
    CallableIndexedOwnedSourceBodyReadyBounds.preserves_at
      (CallableIndexedOwnedLambdaNestedReadyContinuations.bridge (headers := headers) owner principal)
      actualEntry.source.runtime wellFormed syntaxTree ready actualEntry trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
    frame, metadata, exit, returned.val, related⟩

include wellFormed beforeTyped argumentsTyped stable observed prefixContext sourceSeed syntaxTree in
/-- The original measured prefix constructs the same static index directly;
reflection preserves the independently reconstructed Source body grade. -/
theorem native_continuation (budget : Nat)
    (below : ∀ index : Index (keys := keys) (registry := registry) (faults := faults),
      RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyReadyOrigins.ReflectsAt (body_protocol (headers := headers) index)
          (readiness (bridge (headers := headers) index)) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
          (ProtectedStateImperativeTypedSourceSites.Facts (origin index).function.source (origin index).expressionSyntax)
          functions program (origin index))) :
    CallableIndexedOwnedLambdaInvocationBounds.NativeContinuation (arguments := arguments)
      captured code history inputs functions owner caller body budget := by
  intro entry reached child strict value finalStore completed
  let index := of_native_entry captured code history inputs functions owner caller body beforeTyped argumentsTyped stable
    principal observed prefixContext sourceSeed syntaxTree entry reached
  let actualEntry := CallableIndexedOwnedLambdaNestedReadyContinuations.native_admitted_entry
    captured code history inputs functions owner caller body beforeTyped argumentsTyped stable
    principal observed prefixContext sourceSeed entry reached
  have ready := below index child strict
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
      frame, metadata, exit, returned, related, _post⟩ :=
    CallableIndexedOwnedSourceBodyReadyBounds.reflects_at
      (CallableIndexedOwnedLambdaNestedReadyContinuations.bridge (headers := headers) owner principal)
      actualEntry.source.runtime wellFormed syntaxTree ready actualEntry completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
    frame, metadata, exit, returned.val, related⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaReadyFamilyReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedJointReadyFamilyInputs
/-! Authentic named, lambda and trait-method indices retain their own exact
protocols and original Source/compiler receipts. This static kit supplies the
existing Ready Family inputs and finite catalog producers. Actual joint
expression dispatch remains a separate obligation. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedJointReadyFamilyInputs
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedOwnedBodySourceOrigin (source_origin)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

/-- Every branch retains a genuine complete static receipt. Lambda layouts
must come from its actual compiler body factory; frame equality is in BodyOrigin. -/
inductive Index where
  | named (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
      (receipt : CallableIndexedOwnedNamedReadyFamilyReceipts.Index (headers := headers)
        (registry := registry) (faults := faults) (certificates := certificates)
        (expressionSyntax := expressionSyntax) (diagnosticPolicy := .reachable) true)
  | lambda (receipt : CallableIndexedOwnedLambdaReadyFamilyReceipts.Index
        (compiled := compiled) (program := Program.ofChecked compiled.sourceProgram)
        (keys := keys) (registry := registry) (faults := faults))
      (layouts : receipt.body.origin.layouts = compiled.indexed.layouts)
  | method (receipt : CallableIndexedOwnedMethodReadyFamilyReceipts.Index
        (compiled := compiled) (keys := keys) (registry := registry) (faults := faults))

/-- The complete original compiler origin is preserved branch by branch. -/
def base_origin (index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax)) :
    CallableRuntimeBodyOrigins.StaticOrigin (.initial compiled.compatible.checked)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed) registry faults :=
  match index with
  | .named _ receipt => CallableRuntimeBodyStaticOrigins.named true receipt.profile receipt.escaped
  | .lambda receipt _ => receipt.body.origin
  | .method receipt => CallableIndexedOwnedMethodInvocationBounds.origin receipt.principal.cached.compilation
      receipt.profile receipt.escaped receipt.extend receipt.runtimeOf

/-- Runtime validity is the independent genuine Source receipt of that branch. -/
theorem sourceRuntime (index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax)) :
    Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      (base_origin index).context (base_origin index).function.source := by
  cases index with
  | named _ receipt => exact receipt.sourceRuntime
  | lambda receipt _ => exact receipt.sourceRuntime
  | method receipt => exact receipt.sourceRuntime

/-- The exact Source domain is strengthened without changing the compiled body. -/
def origin (index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax)) :=
  source_origin (base_origin index) (sourceRuntime index)

/-- Named slots, captured lambda packets and trait-principal packets remain
separate genuine protocols over the same full ordered pool representation. -/
def protocol (index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax)) :
    ProtectedStateTransition.Protocol (Records keys) :=
  match index with
  | .named owner _ => CallableIndexedOwnedNamedReadyFamilyReceipts.body_protocol (headers := headers) owner
  | .lambda receipt _ => CallableIndexedOwnedLambdaReadyFamilyReceipts.body_protocol (headers := headers) receipt
  | .method receipt => CallableIndexedOwnedMethodReadyFamilyReceipts.body_protocol (headers := headers) receipt

/-- Each branch returns the identical underlying actual pool and records. -/
def bridge (index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax)) :
    CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) (protocol index) := by
  cases index with
  | named owner _ => exact CallableIndexedOwnedNamedReadyFamilyReceipts.bridge (headers := headers) owner
  | lambda receipt _ => exact CallableIndexedOwnedLambdaReadyFamilyReceipts.bridge (headers := headers) receipt
  | method receipt => exact CallableIndexedOwnedMethodReadyFamilyReceipts.bridge (headers := headers) receipt

/-- Binding extension and restoration use each original actual protocol. -/
def bindings (index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax)) :
    ProtectedStateTransition.Bindings (protocol index) := by
  cases index with
  | named owner _ => exact CallableIndexedOwnedCanonicalState.bindings (headers := headers) owner (owner.key.capturePrefix + 1)
  | lambda receipt _ => exact CallableIndexedOwnedNestedCanonicalState.bindings (headers := headers) receipt.owner receipt.principal
  | method receipt => exact CallableIndexedOwnedOriginCanonicalState.bindings (headers := headers) receipt.owner receipt.principal.named

/-- Actual administrative effects preserve packet facets at that same post. -/
def transport (index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax)) :
    ProtectedStateTransition.AdministrativeTransport (protocol index) := by
  cases index with
  | named owner _ => exact CallableIndexedOwnedCanonicalState.administrativeTransport (headers := headers) owner (owner.key.capturePrefix + 1)
  | lambda receipt _ => exact CallableIndexedOwnedNestedCanonicalState.administrativeTransport (headers := headers) receipt.owner receipt.principal
  | method receipt => exact CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) receipt.owner receipt.principal.named

variable (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)

/-- Real marked allocation returns the exact reached protocol state; layout
casts use only authentic static equalities. -/
def producer (index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax)) :
    ProtectedStateTransition.MarkedAllocation.Producer (protocol index) (origin index).layouts (origin index).frameLayout
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) := by
  cases index with
  | named owner receipt =>
    change ProtectedStateTransition.MarkedAllocation.Producer
      (CallableIndexedOwnedNamedReadyFamilyReceipts.body_protocol (headers := headers) owner)
      receipt.header.layouts compiled.indexed.ancestry.layout.frame
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    exact (sameLayouts receipt.header receipt.member).symm ▸
      CallableIndexedOwnedCanonicalState.markedProducer (headers := headers) owner (owner.key.capturePrefix + 1)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
  | lambda receipt layouts =>
    exact layouts.symm ▸ receipt.body.frame_eq.symm ▸
      CallableIndexedOwnedNestedCanonicalState.markedProducer (headers := headers) receipt.owner receipt.principal
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
  | method receipt =>
    exact CallableIndexedOwnedOriginCanonicalState.markedProducer (headers := headers) receipt.owner receipt.principal.named
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)

private theorem ready_cast {stateProtocol : ProtectedStateTransition.Protocol (Records keys)}
    {first second : SourceCoreAllocationLayouts.Prepared} {firstFrame secondFrame : SourceCoreCallableIndexedFrames.Layout}
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    (layouts : first = second) (frame : firstFrame = secondFrame)
    (marked : ProtectedStateTransition.MarkedAllocation.Producer stateProtocol second secondFrame model)
    {location : Location} {native : NativeFrame}
    (ready : ProtectedStateTransition.OrdinaryAllocation.ReadyAt marked.toOrdinary location native) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt
      ((layouts.symm ▸ frame.symm ▸ marked).toOrdinary) location native := by
  cases layouts
  cases frame
  exact ready

include functions sameLayouts in
/-- A genuine selected stable row supplies allocation readiness in the same
branch; no Source typing or canonical slots are inferred by this gate. -/
theorem acquire (index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax))
    (location : Location) (native : NativeFrame)
    (stable : CallableIndexedOwnedAllocationProducer.StableOwner keys location native) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt (producer functions sameLayouts index).toOrdinary location native := by
  cases index with
  | named owner receipt =>
    exact ready_cast (sameLayouts receipt.header receipt.member) rfl _
      (CallableIndexedOwnedCanonicalState.readyAt_of_stableOwner (headers := headers) owner (owner.key.capturePrefix + 1)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) stable)
  | lambda receipt layouts =>
    exact ready_cast layouts receipt.body.frame_eq _
      (CallableIndexedOwnedNestedCanonicalState.readyAt_of_stableOwner (headers := headers) receipt.owner receipt.principal
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) stable)
  | method receipt =>
    exact CallableIndexedOwnedOriginCanonicalState.readyAt_of_stableOwner (headers := headers) receipt.owner receipt.principal.named
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) stable

variable (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))

/-- Genuine Source facts, static sites, actual allocation and snapshot
transfers build the existing finite catalog input fields internally. -/
def inputs (index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax)) :=
  CallableIndexedOwnedBodyReadyCatalog.inputs (bridge index) (base_origin index) (sourceRuntime index)
    (bindings index) wellFormed

variable (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)

include extension faithful observations sameLayouts in
/-- The sole family supplies these actual smaller expression results. The
finite head/loop recipes are proved internally at the exact indexed protocol. -/
theorem preserving_kits (index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax)) (budget : Nat)
    (expressions : ∀ context, (origin index).validity context →
      RecursiveNamedHeaderContracts.AtMost budget (fun size =>
        RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionPreservesAt (protocol index) (readiness (bridge index))
          (Program.ofChecked compiled.sourceProgram) (origin index).function.evidence
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          (inputs wellFormed index).exprFacts ((origin index).certificates context)
          (source := (origin index).function.source) (context := context) (faults := faults) size)) :
    CallableRuntimeBodyReadyInputs.PreservingKits (protocol index) (readiness (bridge index)) (bindings index)
      (Program.ofChecked compiled.sourceProgram) (origin index) functions
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) (inputs wellFormed index) budget :=
  CallableIndexedOwnedBodyReadyCatalog.preserving_ready_kits (bridge index) (base_origin index) (sourceRuntime index)
    (bindings index) wellFormed functions extension faithful observations (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (producer functions sameLayouts index) (acquire functions sameLayouts index) (transport index) budget expressions

include extension faithful observations sameLayouts in
/-- Native finite kits use the same original strict expression children and
return the same indexed witness; no joint body closure is asserted here. -/
theorem reflecting_kits (functionTypes : FunctionRuntimeViews functions)
    (index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax)) (budget : Nat)
    (expressions : ∀ context, (origin index).validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size =>
        RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionReflectsAt (protocol index) (readiness (bridge index))
          (Program.ofChecked compiled.sourceProgram) (origin index).function.evidence
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          (inputs wellFormed index).exprFacts ((origin index).certificates context)
          (source := (origin index).function.source) (context := context) (faults := faults) size)) :
    CallableRuntimeBodyReadyInputs.ReflectingKits (protocol index) (readiness (bridge index)) (bindings index)
      (Program.ofChecked compiled.sourceProgram) (origin index) functions
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) (inputs wellFormed index) budget :=
  CallableIndexedOwnedBodyReadyCatalog.reflecting_ready_kits (bridge index) (base_origin index) (sourceRuntime index)
    (bindings index) wellFormed functions extension faithful observations (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (producer functions sameLayouts index) (acquire functions sameLayouts index) (transport index) budget functionTypes expressions

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedJointReadyFamilyInputs
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedTypedLambdaInvocationBounds
/-! Typed lambda invocation uses the real parameter receipts and strict flow
family. The original saved-frame restoration and finite apply edges preserve
that actual caller pool, without an escaped-token assumption. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedTypedLambdaInvocationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedParameterMeaning
open RecursiveNamedCatalogInvocationBounds (Below)
open CallableIndexedOwnedTypedLambdaBodyContinuations (FlowPreserves FlowReflects)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  {expressionSyntax : TypedSource → ExpressionId → Prop}
  {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (body : CallableIndexedOwnedTypedLambdaStaticBody.Body code program expressionSyntax certificates)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap} {store : Store}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation))
  {currentMetadata : Option MetadataState}
  (currentCarried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost currentMetadata)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed compiled.indexed.ancestry.graph.inputs
    history.metadata code.descriptor.id = true)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments body.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)
  (wellFormed : ProgramWellFormed program)

/-- The original invocation result retains its real restored caller state. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (value : Value) (finalStore : Store) : Prop :=
  ∃ finalMap finalWorld,
    FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      finalMap finalWorld function.resultType code.receipt.resultCore faults outcome value ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
    ProtectedStateTransition.Transition (protocol headers keys) caller
      ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩

include represented heaps locals reference currentCarried allowed beforeTyped argumentsTyped stable wellFormed in
theorem invocation_preserves_bounded (budget : Nat)
    (below : Below budget (FlowPreserves captured code body functions (registry := registry) (faults := faults) (headers := headers) (keys := keys)))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome program size callContext callerEvidence function.evidence before
      (.closure function) arguments outcome after) (within : size ≤ budget) :
    ∃ value finalStore,
      Evaluates (DataPatternValues.packValues nativeArguments :: SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame history.native :: capturedActual)
        store (code.body.rename captured.embedding.lift.lift) value finalStore ∧
      ResultAt (registry := registry) (faults := faults) captured code functions caller outcome after value finalStore := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, finalHeaps, maps, worlds, frame, metadata, transition⟩ :=
    CallableIndexedOwnedLambdaInvocationBounds.invocation_preserves_bounded_at_with_continuation
      captured code history body.toContext functions represented owner caller heaps locals reference currentCarried allowed
      budget (CallableIndexedOwnedTypedLambdaBodyContinuations.source_continuation
        captured code history body functions owner caller beforeTyped argumentsTyped stable wellFormed budget below)
      trace within
  exact ⟨value, finalStore, evaluated, finalMap, finalWorld, result, finalHeaps, maps, worlds, frame, metadata, transition⟩

include represented heaps locals reference currentCarried allowed beforeTyped argumentsTyped stable wellFormed in
theorem invocation_reflects_bounded (budget : Nat)
    (below : Below budget (FlowReflects captured code body functions (registry := registry) (faults := faults) (headers := headers) (keys := keys)))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size
      (DataPatternValues.packValues nativeArguments :: SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame history.native :: capturedActual)
      store (code.body.rename captured.embedding.lift.lift) value finalStore) (within : size ≤ budget) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.CallOutcome program sourceSize callContext callerEvidence function.evidence before
        (.closure function) arguments outcome after ∧
      ResultAt (registry := registry) (faults := faults) captured code functions caller outcome after value finalStore := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, finalHeaps, maps, worlds, frame, metadata, transition⟩ :=
    CallableIndexedOwnedLambdaInvocationBounds.invocation_reflects_bounded_at_with_continuation
      captured code history body.toContext functions represented owner caller heaps locals reference currentCarried allowed
      body.frame budget (CallableIndexedOwnedTypedLambdaBodyContinuations.native_continuation
        captured code history body functions owner caller beforeTyped argumentsTyped stable wellFormed budget below)
      completed within
  exact ⟨sourceSize, outcome, after, trace, finalMap, finalWorld, result, finalHeaps, maps, worlds, frame, metadata, transition⟩

include represented heaps locals reference currentCarried allowed beforeTyped argumentsTyped stable wellFormed in
theorem application_preserves_bounded (budget : Nat)
    (below : Below budget (FlowPreserves captured code body functions (registry := registry) (faults := faults) (headers := headers) (keys := keys)))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome program size callContext callerEvidence function.evidence before
      (.closure function) arguments outcome after) (within : size ≤ budget) :
    ∃ value finalStore,
      Evaluates [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      ResultAt (registry := registry) (faults := faults) captured code functions caller outcome after value finalStore := by
  obtain ⟨value, finalStore, evaluated, result⟩ := invocation_preserves_bounded
    captured code history body functions represented owner caller heaps locals reference currentCarried allowed
    beforeTyped argumentsTyped stable wellFormed budget below trace within
  exact ⟨value, finalStore, .apply (.second (.first (.var rfl))) (.var rfl) evaluated, result⟩

include represented heaps locals reference currentCarried allowed beforeTyped argumentsTyped stable wellFormed in
theorem application_reflects_bounded (budget : Nat)
    (below : Below budget (FlowReflects captured code body functions (registry := registry) (faults := faults) (headers := headers) (keys := keys)))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.CallOutcome program sourceSize callContext callerEvidence function.evidence before
        (.closure function) arguments outcome after ∧
      ResultAt (registry := registry) (faults := faults) captured code functions caller outcome after value finalStore := by
  obtain ⟨bodySize, smaller, applied⟩ := completed.apply_body (.second (.first (.var rfl))) (.var rfl)
  exact invocation_reflects_bounded
    captured code history body functions represented owner caller heaps locals reference currentCarried allowed
    beforeTyped argumentsTyped stable wellFormed budget below applied (Nat.le_trans (Nat.le_of_lt smaller) within)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedTypedLambdaInvocationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodPrincipalCaptures
/-! A genuine method-principal packet fixes its captured native bundle,
globals and frame prefix at the real input environment. Source locations remain
related independently by EnvRepresents. Prefix capture retains the original
full native environment and the identical underlying owned pool. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodPrincipalCaptures
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedLambdaValues
open RecursiveNamedLambdaFormationHeads (environments_prefix agrees_prefix)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {method : ExecutableImplMethods.CheckedMethod}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {heap : Dynamic.Heap} {store : Store} {canonical actual : Environment}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {ξ : Renaming}
  (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedOriginCanonicalState.Packet owner principal.named _ initial)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)

/-- These are precisely the compiler's method bundle, globals and frame slots. -/
def nativePrefix : Core.Context :=
  principal.named.signature.parameterType :: compiled.indexed.base.globals.map (·.referenceType) ++
    [.cell compiled.indexed.ancestry.layout.frame.type]

include packet complete related in
/-- Actual environment tags identify only the genuine used native prefix.
Source authority remains the independent principal and packet history. -/
theorem entry_prefix_at : NativeExpressionContextSupport.Agrees
    (nativePrefix principal).length (nativePrefix principal) administrative := by
  have typed := related.runtime_hasTypes.type_tags
  have tag {index : Nat} {value : Value} (found : canonical[index]? = some value) :
      (SourceCoreLocalCell.coreContext scope ++ administrative)[index]? = some value.type := by
    rw [← typed]
    simp [found]
  intro index smaller
  cases index with
  | zero =>
    have bundle := packet.bundle
    rw [typed] at bundle
    simpa [SourceCoreLocalCell.coreContext, nativePrefix, List.getElem?_append] using bundle
  | succ slot =>
    have bound : slot < compiled.indexed.base.globals.length + 1 := by
      simp only [nativePrefix, List.length_cons, List.length_append, List.length_map,
        List.length_nil] at smaller
      omega
    by_cases globalSlot : slot < compiled.indexed.base.globals.length
    · let signature := compiled.indexed.base.globals[slot]
      have selected : compiled.indexed.base.globals[slot]? = some signature := List.getElem?_eq_some_iff.mpr ⟨globalSlot, rfl⟩
      obtain ⟨target, member, sameSlot, sameSignature⟩ := complete slot signature selected
      have found := packet.globals target member
      have atType := tag found
      rw [sameSlot] at atType
      have outside : ¬ scope.length + 1 + slot < scope.length := by omega
      have offset : scope.length + 1 + slot - scope.length = slot + 1 := by omega
      simpa [SourceCoreLocalCell.coreContext, nativePrefix, List.getElem?_append, outside, offset,
        globalSlot, selected, signature, sameSignature, SourceCoreCalls.Signature.referenceType,
        OptionalCell.referenceType, Value.type] using atType
    · have last : slot = compiled.indexed.base.globals.length := by omega
      have atType := tag packet.reference
      have outside : ¬ scope.length + 1 + compiled.indexed.base.globals.length < scope.length := by omega
      have offset : scope.length + 1 + compiled.indexed.base.globals.length - scope.length = compiled.indexed.base.globals.length + 1 := by omega
      simpa [SourceCoreLocalCell.coreContext, nativePrefix, List.getElem?_append, outside, offset,
        last, Value.type] using atType

include packet complete related agrees typed in
/-- Capture construction retains all actual native captures, their typing and
embedding. Only canonical unused administrative suffixes are projected away. -/
def captures : Captures compiled.indexed mapping world scope environment actual := by
  let represented := environments_prefix related (nativePrefix principal)
    (entry_prefix_at principal owner initial packet complete related)
  let same : EnvironmentsAgree ξ (canonical.take (scope.length + (nativePrefix principal).length)) actual :=
    agrees_prefix agrees (scope.length + (nativePrefix principal).length)
  exact {
    administrative := nativePrefix principal
    canonical := canonical.take (scope.length + (nativePrefix principal).length)
    actualContext := actualContext
    embedding := ξ
    represented := represented
    agrees := same
    respects := TypedLexicalWhile.environment_respects represented.runtime_hasTypes typed same
    typed := typed }

include packet complete related agrees typed in
/-- The real global/frame observations remain inside the canonical prefix. -/
theorem captured_globals
    (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length) :
    CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
      headers owner.key.locations 1 scope
      (captures principal owner initial packet complete related agrees typed).canonical owner.key.frameLocation := by
  apply packet.observed.take
  · intro header member
    have bound := slots header member
    simp only [nativePrefix, List.length_cons, List.length_append, List.length_map, List.length_nil]
    omega
  · simp only [nativePrefix, List.length_cons, List.length_append, List.length_map, List.length_nil]
    omega

include packet complete related agrees typed in
/-- The exact original pool acquires only the projected canonical observations;
its carried metadata and every original ordered row remain identical. -/
theorem captured_packet
    (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length) :
    CallableIndexedOwnedOriginCanonicalState.Packet owner principal.named
      ⟨scope, mapping, world, heap, store,
        (captures principal owner initial packet complete related agrees typed).canonical⟩ initial := by
  have observed := captured_globals principal owner initial packet complete related agrees typed slots
  refine ⟨observed.globals, observed.reference, ?_, packet.carried⟩
  have tags := (captures principal owner initial packet complete related agrees typed).represented.runtime_hasTypes.type_tags
  rw [tags]
  change (SourceCoreLocalCell.coreContext scope ++ nativePrefix principal)[scope.length]? = some principal.named.signature.parameterType
  simpa [SourceCoreLocalCell.coreContext, List.getElem?_append] using
    (show (nativePrefix principal)[0]? = some principal.named.signature.parameterType from rfl)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodPrincipalCaptures
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaBodyViewEdits
/-! A finite list computed from the actual two source tables records exactly
which original expression lookups differ. BodyView excludes all reached edits;
no choice of metadata or compiler input is made in this projection. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaBodyViewEdits
open Core Frontend SourceInference
open CallableIndexedLambdaValues CallableLambdaViewEdits CallableLambdaBodyReachability
open CallableIndexedOwnedContextualLambdaProvenance (BodyView)

def changed (source view : TypedSource) : List ExpressionId :=
  (source.nodes.filterMap (fun node => match node with
    | .expression expression => some expression.id
    | .statement _ => none)).filter (fun id => decide (source.lookupExpression? id ≠ view.lookupExpression? id))

theorem local_view {source view : TypedSource} (metadata : LambdaMetadataViews.MetadataView source view) :
    LocalView source view (changed source view) := by
  refine ⟨metadata, ?_⟩
  intro id fresh
  cases original : source.lookupExpression? id with
  | none =>
    cases viewed : view.lookupExpression? id with
    | none => rfl
    | some node =>
      obtain ⟨prior, found, _⟩ := metadata.expression viewed
      rw [original] at found
      cases found
  | some node =>
    by_cases same : some node = view.lookupExpression? id
    · exact same
    apply False.elim
    have different := same
    have member : id ∈ source.nodes.filterMap (fun entry => match entry with
        | .expression expression => some expression.id
        | .statement _ => none) := by
      obtain ⟨present, same⟩ := lookupExpression?_sound original
      exact List.mem_filterMap.mpr ⟨.expression node, present, congrArg some same⟩
    apply fresh
    exact List.mem_filter.mpr ⟨member, by simpa only [decide_eq_true_eq, original] using different⟩

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {code : Code compiled.indexed function scope administrative}

theorem avoids (preserved : BodyView code) :
    Avoids function.source (function.body.map NodeId.statement) (changed function.source code.view) := by
  intro id member reached
  have different := of_decide_eq_true (List.mem_filter.mp member).2
  exact different (preserved id reached)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaBodyViewEdits
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedJointLambdaReadyContinuations
/-! The actual selected lambda entry carries its genuine compiler layout.
Only that exact dependent index enters the joint family; no arbitrary static
lambda origin is assigned compiled layouts. Strict child results return the
same original reached pool and independently measured Source trace. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedJointLambdaReadyContinuations
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedLambdaValues
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

variable {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (body : CallableIndexedOwnedLambdaInvocationBounds.BodyOrigin (program := Program.ofChecked compiled.sourceProgram) code inputs registry faults)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments inputs.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)
  (principal : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (indexed := compiled.indexed) (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram) principal)
  (sourceSeed : history.metadata = CallableIndexedNamedGeneration.state principal.named)
  (syntaxTree : GenericImperativeMatch.Syntax body.origin.function.source body.origin.expressionSyntax
    body.origin.context (.statements true body.origin.function.body) body.origin.function.resultType)

variable (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (layouts : body.origin.layouts = compiled.indexed.layouts)

include layouts wellFormed beforeTyped argumentsTyped stable observed prefixContext sourceSeed syntaxTree in
/-- Each authentic actual Source parameter entry constructs its index and
uses only the strict shared-family child in that index's exact protocol. -/
theorem source_continuation (budget : Nat)
    (below : ∀ index : CallableIndexedOwnedJointReadyFamilyInputs.Index
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax),
      RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyReadyOrigins.PreservesAt (CallableIndexedOwnedJointReadyFamilyInputs.protocol index)
          (readiness (CallableIndexedOwnedJointReadyFamilyInputs.bridge index))
          (CallableIndexedOwnedAllocationProducer.StableOwner keys)
          (CallableIndexedOwnedJointReadyFamilyInputs.inputs wellFormed index).facts
          functions (Program.ofChecked compiled.sourceProgram) (CallableIndexedOwnedJointReadyFamilyInputs.origin index))) :
    CallableIndexedOwnedLambdaInvocationBounds.SourceContinuation (arguments := arguments) (nativeArguments := nativeArguments)
      captured code history inputs functions owner caller body budget := by
  intro entry added length copied spine kept reached child strict outcome after trace
  let index := CallableIndexedOwnedLambdaReadyFamilyReceipts.of_source_entry captured code history inputs functions owner caller body beforeTyped argumentsTyped stable
    principal observed prefixContext sourceSeed syntaxTree entry added length copied spine kept reached
  let actualEntry := CallableIndexedOwnedLambdaNestedReadyContinuations.source_admitted_entry
    captured code history inputs functions owner caller body beforeTyped argumentsTyped stable
    principal observed prefixContext sourceSeed entry added length copied spine kept reached
  have ready := below (.lambda index layouts) child strict
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
      frame, metadata, exit, returned, related, _post⟩ :=
    CallableIndexedOwnedSourceBodyReadyBounds.preserves_at
      (CallableIndexedOwnedLambdaNestedReadyContinuations.bridge (headers := headers) owner principal)
      actualEntry.source.runtime wellFormed syntaxTree ready actualEntry trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
    frame, metadata, exit, returned.val, related⟩

include layouts wellFormed beforeTyped argumentsTyped stable observed prefixContext sourceSeed syntaxTree in
/-- The original measured prefix constructs the same static index directly;
reflection preserves the independently reconstructed Source body grade. -/
theorem native_continuation (budget : Nat)
    (below : ∀ index : CallableIndexedOwnedJointReadyFamilyInputs.Index
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax),
      RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyReadyOrigins.ReflectsAt (CallableIndexedOwnedJointReadyFamilyInputs.protocol index)
          (readiness (CallableIndexedOwnedJointReadyFamilyInputs.bridge index))
          (CallableIndexedOwnedAllocationProducer.StableOwner keys)
          (CallableIndexedOwnedJointReadyFamilyInputs.inputs wellFormed index).facts
          functions (Program.ofChecked compiled.sourceProgram) (CallableIndexedOwnedJointReadyFamilyInputs.origin index))) :
    CallableIndexedOwnedLambdaInvocationBounds.NativeContinuation (arguments := arguments)
      captured code history inputs functions owner caller body budget := by
  intro entry reached child strict value finalStore completed
  let index := CallableIndexedOwnedLambdaReadyFamilyReceipts.of_native_entry captured code history inputs functions owner caller body beforeTyped argumentsTyped stable
    principal observed prefixContext sourceSeed syntaxTree entry reached
  let actualEntry := CallableIndexedOwnedLambdaNestedReadyContinuations.native_admitted_entry
    captured code history inputs functions owner caller body beforeTyped argumentsTyped stable
    principal observed prefixContext sourceSeed entry reached
  have ready := below (.lambda index layouts) child strict
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
      frame, metadata, exit, returned, related, _post⟩ :=
    CallableIndexedOwnedSourceBodyReadyBounds.reflects_at
      (CallableIndexedOwnedLambdaNestedReadyContinuations.bridge (headers := headers) owner principal)
      actualEntry.source.runtime wellFormed syntaxTree ready actualEntry completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
    frame, metadata, exit, returned.val, related⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedJointLambdaReadyContinuations
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedJointReadyFamilyBounds
/-! This finite connection uses the existing measured Ready Family for the
three authentic joint indices. Its expression selectors receive only the
strictly smaller dependent body meanings and must be supplied by the actual
expression dispatcher. The module does not close that mixed dispatcher. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedJointReadyFamilyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedOwnedJointReadyFamilyInputs

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

variable (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))

/-- The actual source expression dispatcher receives strictly smaller joint
body meanings at each callee's own protocol, full origin and genuine facts. -/
abbrev PreservingExpressions : Prop :=
  ∀ index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax),
    ∀ context, (origin index).validity context → ∀ budget child, child ≤ budget →
      (∀ callee : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
          (certificates := certificates) (expressionSyntax := expressionSyntax), RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyReadyOrigins.PreservesAt (protocol callee) (readiness (bridge callee))
          (CallableIndexedOwnedAllocationProducer.StableOwner keys) (inputs wellFormed callee).facts
          functions (Program.ofChecked compiled.sourceProgram) (origin callee))) →
      RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionPreservesAt (protocol index) (readiness (bridge index))
        (Program.ofChecked compiled.sourceProgram) (origin index).function.evidence
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        (inputs wellFormed index).exprFacts ((origin index).certificates context)
        (context := context) (source := (origin index).function.source) (faults := faults) child

/-- Native expression children retain the original strict dependent callee
bounds and independently reconstructed Source grades at the actual post. -/
abbrev ReflectingExpressions : Prop :=
  ∀ index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax),
    ∀ context, (origin index).validity context → ∀ budget child, child ≤ budget →
      (∀ callee : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
          (certificates := certificates) (expressionSyntax := expressionSyntax), RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyReadyOrigins.ReflectsAt (protocol callee) (readiness (bridge callee))
          (CallableIndexedOwnedAllocationProducer.StableOwner keys) (inputs wellFormed callee).facts
          functions (Program.ofChecked compiled.sourceProgram) (origin callee))) →
      RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionReflectsAt (protocol index) (readiness (bridge index))
        (Program.ofChecked compiled.sourceProgram) (origin index).function.evidence
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        (inputs wellFormed index).exprFacts ((origin index).certificates context)
        (context := context) (source := (origin index).function.source) (faults := faults) child

variable (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)

include extension faithful observations sameLayouts in
/-- The sole existing measured Family composes genuine finite catalog kits
with this source dispatcher; all actual reached entry fields remain intact. -/
theorem preserves_at
    (expressions : PreservingExpressions (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed)
    (size : Nat) : ∀ index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax),
    CallableRuntimeBodyReadyOrigins.PreservesAt (protocol index) (readiness (bridge index))
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) (inputs wellFormed index).facts
      functions (Program.ofChecked compiled.sourceProgram) (origin index) size := by
  exact CallableRuntimeBodyMutualMeaning.Stateful.WithReady.Family.preserves_at (registry := registry) (faults := faults)
    origin functions (Program.ofChecked compiled.sourceProgram)
    protocol (fun _ => CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (producer functions sameLayouts) (acquire functions sameLayouts) transport bindings
    (fun index => readiness (bridge index)) (inputs wellFormed) expressions
    (fun index budget children => preserving_kits functions sameLayouts wellFormed extension faithful observations
      index budget children) size

include extension faithful observations sameLayouts in
/-- The same Family consumes original native completions and preserves the
independent Source grade and each branch's actual returned protocol witness. -/
theorem reflects_at (functionTypes : FunctionRuntimeViews functions)
    (expressions : ReflectingExpressions (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed)
    (size : Nat) : ∀ index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax),
    CallableRuntimeBodyReadyOrigins.ReflectsAt (protocol index) (readiness (bridge index))
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) (inputs wellFormed index).facts
      functions (Program.ofChecked compiled.sourceProgram) (origin index) size := by
  exact CallableRuntimeBodyMutualMeaning.Stateful.WithReady.Family.reflects_at (registry := registry) (faults := faults)
    origin functions (Program.ofChecked compiled.sourceProgram)
    protocol (fun _ => CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (producer functions sameLayouts) (acquire functions sameLayouts) transport bindings
    (fun index => readiness (bridge index)) (inputs wellFormed) expressions
    (fun index budget children => reflecting_kits functions sameLayouts wellFormed extension faithful observations
      functionTypes index budget children) size

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedJointReadyFamilyBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodBuiltinBounds
/-! An authentic builtin method profile closes its actual body and invocation
without semantic callbacks. Its original builtin/data/control/read expression
grammar is proved internally, while lexical and parameter allocations use the
real marked producer and retain their reached ordered pool records. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodBuiltinBounds
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedParameterMeaning SourceCoreCallableIndexedFrames
open CallableIndexedOwnedFunctionState CallablePreparedMethodRuntimeMeaning

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
  {code : Expr} (generation : CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics code)
  {sourceBody : Dynamic.BodyInstance} {dictionary : Dynamic.EvidenceEnvironment}
  {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (profile : Profile generation (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) sourceBody dictionary administrative registry faults)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (escaped : faults .controlEscapedFunction generation.own.table.escapedReason)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (diagnostics.reasonAt named.signature.key id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((diagnostics.reasonAt named.signature.key id).add tag))

/-- Every original static method field and its full independent dictionary
remain in the existing builtin origin factory. -/
abbrev origin := CallableRuntimeBodyStaticOrigins.method_builtin generation profile escaped

include extension faithful observations functionTypes uninitialized missing in
/-- The original shared measured family closes this authentic builtin profile.
Only its proved expression fragment is lifted through administrative effects;
body allocation still consumes the actual marked producer and selected gate. -/
theorem body_preserves_at (size : Nat) :
    CallableRuntimeBodyOrigins.Stateful.PreservesAt (protocol headers keys)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions program
      (origin generation profile escaped) size := by
  exact CallableRuntimeBodyMutualMeaning.Stateful.preserves_at
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (registry := registry) (faults := faults)
    (fun _ : Unit => origin generation profile escaped) functions extension program faithful observations
    (protocol headers keys) (fun _ => CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (fun _ => CallableIndexedOwnedMarkedAllocation.producer headers keys
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
    (by
      intro _ location native gate
      exact CallableIndexedOwnedAllocationProducer.readyAt_of_stableOwner
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) gate)
    (administrativeTransport headers keys) (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
    (by
      intro _ context valid budget child _within _callees
      apply ProtectedStateTransition.PreservesAt.of_administrative _ _ _ _ _ _ _ _ (administrativeTransport headers keys)
      exact RecursiveNamedBoundedContracts.preserves_at_of_unbounded
        (ProtectedExpressionMeaning.preserves_of_typed (ProtectedStateTransition.entry (protocol headers keys))
          (CompatibleExpressionBuiltinRuntime.preserves functions extension faithful observations functionTypes
            program dictionary valid.ledger valid.runtime profile.body.unique uninitialized missing)) child)
    size ()

include extension faithful observations functionTypes uninitialized missing in
/-- Reflection uses the same exact runtime ledger and original source method
profile. Its source grade is reconstructed from each original native child,
with all actual body pool transitions retained by the shared family. -/
theorem body_reflects_at (size : Nat) :
    CallableRuntimeBodyOrigins.Stateful.ReflectsAt (protocol headers keys)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions program
      (origin generation profile escaped) size := by
  exact CallableRuntimeBodyMutualMeaning.Stateful.reflects_at
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (registry := registry) (faults := faults)
    (fun _ : Unit => origin generation profile escaped) functions extension program faithful observations functionTypes
    (protocol headers keys) (fun _ => CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (fun _ => CallableIndexedOwnedMarkedAllocation.producer headers keys
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
    (by
      intro _ location native gate
      exact CallableIndexedOwnedAllocationProducer.readyAt_of_stableOwner
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) gate)
    (administrativeTransport headers keys) (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
    (by
      intro _ context valid budget child _within _callees
      apply ProtectedStateTransition.ReflectsAt.of_administrative _ _ _ _ _ _ _ _ (administrativeTransport headers keys)
      exact RecursiveNamedBoundedContracts.reflects_at_of_unbounded
        (ProtectedExpressionMeaning.reflects_of_typed (ProtectedStateTransition.entry (protocol headers keys))
          (CompatibleExpressionBuiltinRuntime.reflects functions extension faithful observations functionTypes
            program dictionary valid.ledger valid.runtime uninitialized missing)) child)
    size ()

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
  (installed : Installed generation (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (sourceBody := sourceBody) (administrative := administrative)
    functions mapping world before store callerEnvironment)
  (represented : Arguments (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world named.inputs arguments payloads)
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (sameFrame : installed.frameLocation = owner.key.frameLocation)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)

include profile escaped represented owner sameFrame heaps extension faithful observations functionTypes uninitialized missing in
/-- An original source method outcome runs the actual hook, parameters and
closed builtin body. The exact reached body pool supplies caller restoration;
no expression or body meaning is a premise. -/
theorem invocation_preserves {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyOutcome program size sourceBody dictionary before arguments outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues payloads :: installed.captured) store
        (generation.output.rename installed.embedding.lift) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩ := by
  exact CallableIndexedOwnedMethodInvocationBounds.invocation_preserves_bounded_with generation
    (CallablePreparedMethodCatalogHookMeaning.of_builtin generation profile) functions escaped
    (fun valid extended => valid.extend extended) (fun valid => valid)
    installed represented owner caller sameFrame heaps size
    (fun child _strict => body_preserves_at generation profile functions extension faithful observations functionTypes
      escaped uninitialized missing child) trace (Nat.le_refl size)

include profile escaped represented owner sameFrame heaps extension faithful observations functionTypes uninitialized missing in
/-- Completed native method execution reflects its independent source outcome
through the same actual parameter/body/restoration chain and full dictionary.
The returned caller state preserves the reached pool's ordered records. -/
theorem invocation_reflects {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: installed.captured) store
      (generation.output.rename installed.embedding.lift) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyOutcome program sourceSize sourceBody dictionary before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩ := by
  exact CallableIndexedOwnedMethodInvocationBounds.invocation_reflects_bounded_with generation
    (CallablePreparedMethodCatalogHookMeaning.of_builtin generation profile) functions escaped
    (fun valid extended => valid.extend extended) (fun valid => valid)
    installed represented owner caller sameFrame heaps size
    (fun child _strict => body_reflects_at generation profile functions extension faithful observations functionTypes
      escaped uninitialized missing child) completed (Nat.le_refl size)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodBuiltinBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodPrincipalBuiltinBounds
/-! An authentic selected method principal closes its builtin body and invocation
without semantic callbacks. Its original builtin/data/control/read expression
grammar is proved internally, while lexical and parameter allocations use the
real marked producer and retain their reached ordered pool records. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodPrincipalBuiltinBounds
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedParameterMeaning SourceCoreCallableIndexedFrames
open CallableIndexedOwnedFunctionState CallablePreparedMethodRuntimeMeaning

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (profile : Profile principal.cached.compilation (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) principal.sourceBody principal.dictionary administrative registry faults)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (escaped : faults .controlEscapedFunction principal.cached.compilation.own.table.escapedReason)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (principal.cached.diagnostics.reasonAt principal.named.signature.key id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((principal.cached.diagnostics.reasonAt principal.named.signature.key id).add tag))

/-- Every original static method field and its full independent dictionary
remain in the existing builtin origin factory. -/
abbrev origin := CallableRuntimeBodyStaticOrigins.method_builtin principal.cached.compilation profile escaped

include extension faithful observations functionTypes uninitialized missing in
/-- The original shared measured family closes this authentic builtin profile.
Only its proved expression fragment is lifted through administrative effects;
body allocation still consumes the actual marked producer and selected gate. -/
theorem body_preserves_at (size : Nat) :
    CallableRuntimeBodyOrigins.Stateful.PreservesAt (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner principal.named)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions (Program.ofChecked compiled.sourceProgram)
      (origin principal profile escaped) size := by
  exact CallableRuntimeBodyMutualMeaning.Stateful.preserves_at
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (registry := registry) (faults := faults)
    (fun _ : Unit => origin principal profile escaped) functions extension (Program.ofChecked compiled.sourceProgram) faithful observations
    (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner principal.named) (fun _ => CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (fun _ => CallableIndexedOwnedOriginCanonicalState.markedProducer (headers := headers) owner principal.named
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
    (by
      intro _ location native gate
      exact CallableIndexedOwnedOriginCanonicalState.readyAt_of_stableOwner (headers := headers) owner principal.named
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) gate)
    (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner principal.named) (CallableIndexedOwnedOriginCanonicalState.bindings (headers := headers) owner principal.named)
    (by
      intro _ context valid budget child _within _callees
      apply ProtectedStateTransition.PreservesAt.of_administrative _ _ _ _ _ _ _ _ (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner principal.named)
      exact RecursiveNamedBoundedContracts.preserves_at_of_unbounded
        (ProtectedExpressionMeaning.preserves_of_typed (ProtectedStateTransition.entry (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner principal.named))
          (CompatibleExpressionBuiltinRuntime.preserves functions extension faithful observations functionTypes
            (Program.ofChecked compiled.sourceProgram) principal.dictionary valid.ledger valid.runtime profile.body.unique uninitialized missing)) child)
    size ()

include extension faithful observations functionTypes uninitialized missing in
/-- Reflection uses the same exact runtime ledger and original source method
profile. Its source grade is reconstructed from each original native child,
with all actual body pool transitions retained by the shared family. -/
theorem body_reflects_at (size : Nat) :
    CallableRuntimeBodyOrigins.Stateful.ReflectsAt (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner principal.named)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions (Program.ofChecked compiled.sourceProgram)
      (origin principal profile escaped) size := by
  exact CallableRuntimeBodyMutualMeaning.Stateful.reflects_at
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (registry := registry) (faults := faults)
    (fun _ : Unit => origin principal profile escaped) functions extension (Program.ofChecked compiled.sourceProgram) faithful observations functionTypes
    (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner principal.named) (fun _ => CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (fun _ => CallableIndexedOwnedOriginCanonicalState.markedProducer (headers := headers) owner principal.named
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
    (by
      intro _ location native gate
      exact CallableIndexedOwnedOriginCanonicalState.readyAt_of_stableOwner (headers := headers) owner principal.named
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) gate)
    (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner principal.named) (CallableIndexedOwnedOriginCanonicalState.bindings (headers := headers) owner principal.named)
    (by
      intro _ context valid budget child _within _callees
      apply ProtectedStateTransition.ReflectsAt.of_administrative _ _ _ _ _ _ _ _ (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner principal.named)
      exact RecursiveNamedBoundedContracts.reflects_at_of_unbounded
        (ProtectedExpressionMeaning.reflects_of_typed (ProtectedStateTransition.entry (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner principal.named))
          (CompatibleExpressionBuiltinRuntime.reflects functions extension faithful observations functionTypes
            (Program.ofChecked compiled.sourceProgram) principal.dictionary valid.ledger valid.runtime uninitialized missing)) child)
    size ()

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
  (installed : Installed principal.cached.compilation (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (sourceBody := principal.sourceBody) (administrative := administrative)
    functions mapping world before store callerEnvironment)
  (represented : Arguments (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world principal.named.inputs arguments payloads)
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (observed : CallableIndexedOwnedExpressionHeads.Globals (headers := headers) owner 0 [] installed.canonical)
  (sameFrame : installed.frameLocation = owner.key.frameLocation)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)

include profile escaped represented observed sameFrame heaps extension faithful observations functionTypes uninitialized missing in
/-- An original source method outcome runs the actual hook, parameters and
closed builtin body. The exact reached body pool supplies caller restoration;
no expression or body meaning is a premise. -/
theorem invocation_preserves {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked compiled.sourceProgram) size principal.sourceBody principal.dictionary before arguments outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues payloads :: installed.captured) store
        (principal.cached.compilation.output.rename installed.embedding.lift) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld principal.sourceBody.resultType principal.named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩ := by
  exact CallableIndexedOwnedMethodInvocationBounds.invocation_preserves_bounded_at_with_history principal.cached.compilation
    (CallablePreparedMethodCatalogHookMeaning.of_builtin principal.cached.compilation profile) functions escaped
    (fun valid extended => valid.extend extended) (fun valid => valid)
    installed represented owner caller sameFrame heaps size
    (CallableIndexedOwnedMethodPrincipalContinuations.source_continuation principal
      (CallablePreparedMethodCatalogHookMeaning.of_builtin principal.cached.compilation profile) functions escaped
      (fun valid extended => valid.extend extended) (fun valid => valid) installed owner caller observed size
      (fun child _strict => body_preserves_at principal owner profile functions extension faithful observations functionTypes
        escaped uninitialized missing child)) trace (Nat.le_refl size)

include profile escaped represented observed sameFrame heaps extension faithful observations functionTypes uninitialized missing in
/-- Completed native method execution reflects its independent source outcome
through the same actual parameter/body/restoration chain and full dictionary.
The returned caller state preserves the reached pool's ordered records. -/
theorem invocation_reflects {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: installed.captured) store
      (principal.cached.compilation.output.rename installed.embedding.lift) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked compiled.sourceProgram) sourceSize principal.sourceBody principal.dictionary before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld principal.sourceBody.resultType principal.named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩ := by
  exact CallableIndexedOwnedMethodInvocationBounds.invocation_reflects_bounded_at_with_history principal.cached.compilation
    (CallablePreparedMethodCatalogHookMeaning.of_builtin principal.cached.compilation profile) functions escaped
    (fun valid extended => valid.extend extended) (fun valid => valid)
    installed represented owner caller sameFrame heaps size
    (CallableIndexedOwnedMethodPrincipalContinuations.native_continuation principal
      (CallablePreparedMethodCatalogHookMeaning.of_builtin principal.cached.compilation profile) functions escaped
      (fun valid extended => valid.extend extended) (fun valid => valid) installed owner caller observed size
      (fun child _strict => body_reflects_at principal owner profile functions extension faithful observations functionTypes
        escaped uninitialized missing child)) completed (Nat.le_refl size)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodPrincipalBuiltinBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedNamedFamilyClosure
/-! Each authentic named header has its own formation packet beside the same
actual pool. The existing measured mutual body fold closes smaller calls, and
the original nested expression Tree closes its compositional children. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedNamedFamilyClosure
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open CallableIndexedOwnedFunctionState
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (prefixZero : owner.key.capturePrefix = 0)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (globals : ∀ header, header ∈ headers → header.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
variable
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) identities)
  (functionTypes : FunctionRuntimeViews (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (ranks : CallableIndexedOwnedFunctionValues.Header compiled program → Nat)
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}

/-- Original static nested certificates retain the full Source and dictionary
of each named header and its genuine compiler context. -/
abbrev certificates (header : CallableIndexedOwnedFunctionValues.Header compiled program)
    (context : SourceSemantics.Context) : GenericExpressionMeaning.Certificate :=
  CallableIndexedLambdaNestedRuntimeCertificates.Certificates
    (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) (program := program)
    (CallableIndexedLambdaNestedRuntimeBodyMeaning.LowerSupport
      (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
      headers header registry faults (ranks header))
    (ranks header) header headers (CallableIndexedNamedGeneration.context compiled.indexed header.named)
    header.readFuel header.function.source context header.function.evidence header.solved header.reasonAt


variable (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame},
      (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers owner.key.locations owner.key.capturePrefix (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost) →
      (CallableIndexedOwnedNamedCanonicalEntries.condition (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner header) entry →
      MatchProfileWith (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (fun context => RecursiveNamedCatalogMutualMeaning.ContextFor true header.solved context header.function.evidence)
        (certificates (headers := headers) (registry := registry) (faults := faults) ranks header)
        diagnosticPolicy header (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)

private def producer {header : CallableIndexedOwnedFunctionValues.Header compiled program} (member : header ∈ headers) :
    ProtectedStateTransition.MarkedAllocation.Producer (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header) header.layouts compiled.indexed.ancestry.layout.frame
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile)) :=
  (sameLayouts header member).symm ▸ CallableIndexedOwnedNestedCanonicalState.markedProducer owner header
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))

private theorem ready_layout {header : CallableIndexedOwnedFunctionValues.Header compiled program}
    {first second : SourceCoreAllocationLayouts.Prepared}
    (same : first = second)
    (marked : ProtectedStateTransition.MarkedAllocation.Producer (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header) second compiled.indexed.ancestry.layout.frame
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile)))
    {location : Location} {native : NativeFrame}
    (ready : ProtectedStateTransition.OrdinaryAllocation.ReadyAt marked.toOrdinary location native) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt ((same.symm ▸ marked).toOrdinary) location native := by
  cases same
  exact ready

private theorem acquire {header : CallableIndexedOwnedFunctionValues.Header compiled program} (member : header ∈ headers)
    (location : Location) (native : NativeFrame)
    (stable : CallableIndexedOwnedAllocationProducer.StableOwner keys location native) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt
      (producer (headers := headers) (registry := registry) (faults := faults) owner profile sameLayouts member).toOrdinary location native := by
  exact ready_layout owner profile (sameLayouts header member)
    (CallableIndexedOwnedNestedCanonicalState.markedProducer owner header
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile)))
    (CallableIndexedOwnedNestedCanonicalState.readyAt_of_stableOwner owner header
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile)) stable)

include prefixZero profile complete globals slots sameLayouts extension faithful observations functionTypes
  owners uninitialized missing escaped profiles in
/-- Source traces keep their original grades and the actual reached per-header
formation packet. Strict callees come only from the shared measured fold. -/
theorem preserves_nested_at (size : Nat) : ∀ header, header ∈ headers →
    RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) registry header faults
      (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header)
      (CallableIndexedOwnedNamedCanonicalEntries.condition (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner header) size := by
  let Index := Σ header : {header // header ∈ headers}, Σ administrative : Core.Context,
    MatchProfileWith (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (fun context => RecursiveNamedCatalogMutualMeaning.ContextFor true header.val.solved context header.val.function.evidence)
      (certificates (headers := headers) (registry := registry) (faults := faults) ranks header.val)
      diagnosticPolicy header.val (expressionSyntax header.val)
      (SourceCoreCompatibleCatalog.packTypes (header.val.bindings.map Prod.snd) :: administrative) registry faults
  let origins : Index → CallableRuntimeBodyOrigins.StaticOrigin (.initial compiled.compatible.checked)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed) registry faults := fun index =>
    CallableRuntimeBodyStaticOrigins.named true index.2.2 (escaped index.1.val index.1.property)
  let protocols := fun index : Index => (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner index.1.val)
  have bodies := CallableRuntimeBodyMutualMeaning.Stateful.Family.preserves_at origins
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) extension program faithful observations
    protocols (fun _ => CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (fun index => producer owner profile sameLayouts index.1.property)
    (fun index => acquire owner profile sameLayouts index.1.property)
    (fun index => CallableIndexedOwnedNestedCanonicalState.administrativeTransport owner index.1.val)
    (fun index => CallableIndexedOwnedNestedCanonicalState.bindings owner index.1.val)
    (by
      intro index context valid budget child within below
      rcases index with ⟨⟨header, member⟩, administrative, bodyProfile⟩
      apply CallableIndexedOwnedNestedExpressionTreeBounds.preserves_at_runtime
        owner header prefixZero profile complete (globals header member) slots
        header.agreement.source extension faithful observations functionTypes header.function.evidence
        header.unique owners (uninitialized header member) (missing header member)
        sameLayouts (fun target => CallableIndexedOwnedNamedCanonicalEntries.condition
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner target)
        (fun target _ => CallableIndexedOwnedNamedCanonicalEntries.authorized
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner target)
        valid.ledger valid.runtime budget child within
      intro callee calleeMember smaller strict
      apply CallableIndexedOwnedNamedCanonicalEntries.preserves_of_nested (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner callee
        prefixZero (globals callee calleeMember) smaller
      intro arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost
        entry initial outcome after aligned trace
      let actualProfile := profiles callee calleeMember entry aligned
      let target : Index := ⟨⟨callee, calleeMember⟩, administrative, actualProfile⟩
      have meaning := below target smaller strict
      let actualEntry := CallableRuntimeBodyStaticOrigins.named_entry
        (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner callee)
        (CallableIndexedOwnedAllocationProducer.StableOwner keys) true actualProfile
        (escaped callee calleeMember) entry initial
        (CallableIndexedOwnedNamedCanonicalEntries.stable_owner (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner callee entry aligned)
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds, frame, metadata, _, transition⟩ :=
        meaning actualEntry trace
      exact ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds, frame, metadata, transition⟩) size
  intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost
    entry initial outcome after aligned trace
  let actualProfile := profiles header member entry aligned
  let index : Index := ⟨⟨header, member⟩, administrative, actualProfile⟩
  let actualEntry := CallableRuntimeBodyStaticOrigins.named_entry
        (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header)
    (CallableIndexedOwnedAllocationProducer.StableOwner keys) true actualProfile
    (escaped header member) entry initial
    (CallableIndexedOwnedNamedCanonicalEntries.stable_owner (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner header entry aligned)
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds, frame, metadata, _, transition⟩ :=
    bodies index actualEntry trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds, frame, metadata, transition⟩

include prefixZero profile complete globals slots sameLayouts extension faithful observations functionTypes
  uninitialized missing escaped profiles in
/-- Native completions return their original grades and the actual reached per-header
formation packet. Strict callees come only from the shared measured fold. -/
theorem reflects_nested_at (size : Nat) : ∀ header, header ∈ headers →
    RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) registry header faults
      (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header)
      (CallableIndexedOwnedNamedCanonicalEntries.condition (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner header) size := by
  let Index := Σ header : {header // header ∈ headers}, Σ administrative : Core.Context,
    MatchProfileWith (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (fun context => RecursiveNamedCatalogMutualMeaning.ContextFor true header.val.solved context header.val.function.evidence)
      (certificates (headers := headers) (registry := registry) (faults := faults) ranks header.val)
      diagnosticPolicy header.val (expressionSyntax header.val)
      (SourceCoreCompatibleCatalog.packTypes (header.val.bindings.map Prod.snd) :: administrative) registry faults
  let origins : Index → CallableRuntimeBodyOrigins.StaticOrigin (.initial compiled.compatible.checked)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed) registry faults := fun index =>
    CallableRuntimeBodyStaticOrigins.named true index.2.2 (escaped index.1.val index.1.property)
  let protocols := fun index : Index => (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner index.1.val)
  have bodies := CallableRuntimeBodyMutualMeaning.Stateful.Family.reflects_at origins
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) extension program faithful observations functionTypes
    protocols (fun _ => CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (fun index => producer owner profile sameLayouts index.1.property)
    (fun index => acquire owner profile sameLayouts index.1.property)
    (fun index => CallableIndexedOwnedNestedCanonicalState.administrativeTransport owner index.1.val)
    (fun index => CallableIndexedOwnedNestedCanonicalState.bindings owner index.1.val)
    (by
      intro index context valid budget child within below
      rcases index with ⟨⟨header, member⟩, administrative, bodyProfile⟩
      apply CallableIndexedOwnedNestedExpressionTreeBounds.reflects_at_runtime
        owner header prefixZero profile complete (globals header member) slots
        header.agreement.source extension faithful observations functionTypes header.function.evidence
        (uninitialized header member) (missing header member)
        sameLayouts (fun target => CallableIndexedOwnedNamedCanonicalEntries.condition
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner target)
        (fun target _ => CallableIndexedOwnedNamedCanonicalEntries.authorized
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner target)
        valid.ledger valid.runtime budget child within
      intro callee calleeMember smaller strict
      apply CallableIndexedOwnedNamedCanonicalEntries.reflects_of_nested (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner callee
        prefixZero (globals callee calleeMember) smaller
      intro arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost
        entry initial value finalStore aligned completed
      let actualProfile := profiles callee calleeMember entry aligned
      let target : Index := ⟨⟨callee, calleeMember⟩, administrative, actualProfile⟩
      have meaning := below target smaller strict
      let actualEntry := CallableRuntimeBodyStaticOrigins.named_entry
        (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner callee)
        (CallableIndexedOwnedAllocationProducer.StableOwner keys) true actualProfile
        (escaped callee calleeMember) entry initial
        (CallableIndexedOwnedNamedCanonicalEntries.stable_owner (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner callee entry aligned)
      obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds, frame, metadata, _, transition⟩ :=
        meaning actualEntry completed
      exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds, frame, metadata, transition⟩) size
  intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost
    entry initial value finalStore aligned completed
  let actualProfile := profiles header member entry aligned
  let index : Index := ⟨⟨header, member⟩, administrative, actualProfile⟩
  let actualEntry := CallableRuntimeBodyStaticOrigins.named_entry
        (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header)
    (CallableIndexedOwnedAllocationProducer.StableOwner keys) true actualProfile
    (escaped header member) entry initial
    (CallableIndexedOwnedNamedCanonicalEntries.stable_owner (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner header entry aligned)
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds, frame, metadata, _, transition⟩ :=
    bodies index actualEntry completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds, frame, metadata, transition⟩

include prefixZero profile complete globals slots sameLayouts extension faithful observations functionTypes
  owners uninitialized missing escaped profiles in
/-- Genuine parameter observations wrap the input; forgetting the final packet
returns the exact reached base pool from the internally closed family. -/
theorem preserves_at (size : Nat) : ∀ header, header ∈ headers →
    RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) registry header faults (protocol headers keys)
      (CallableIndexedOwnedNamedCanonicalEntries.condition (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner header) size := by
  intro header member
  exact CallableIndexedOwnedNamedCanonicalEntries.preserves_of_nested (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner header
    prefixZero (globals header member) size
    (preserves_nested_at owner prefixZero profile complete globals slots sameLayouts extension faithful observations functionTypes
      owners uninitialized missing escaped ranks profiles size header member)

include prefixZero profile complete globals slots sameLayouts extension faithful observations functionTypes
  uninitialized missing escaped profiles in
/-- Genuine parameter observations wrap the input; forgetting the final packet
returns the exact reached base pool from the internally closed family. -/
theorem reflects_at (size : Nat) : ∀ header, header ∈ headers →
    RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) registry header faults (protocol headers keys)
      (CallableIndexedOwnedNamedCanonicalEntries.condition (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner header) size := by
  intro header member
  exact CallableIndexedOwnedNamedCanonicalEntries.reflects_of_nested (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner header
    prefixZero (globals header member) size
    (reflects_nested_at owner prefixZero profile complete globals slots sameLayouts extension faithful observations functionTypes
      uninitialized missing escaped ranks profiles size header member)

include prefixZero profile complete globals slots sameLayouts extension faithful observations functionTypes
  owners uninitialized missing escaped profiles in
/-- The original nested Tree closes all expression children and uses only the
strictly smaller bodies already closed by the same mutual family. -/
theorem expression_preserves_at
    (header : CallableIndexedOwnedFunctionValues.Header compiled program) (member : header ∈ headers)
    (context : SourceSemantics.Context)
    (valid : RecursiveNamedCatalogMutualMeaning.ContextFor true header.solved context header.function.evidence)
    (size : Nat) :
    ProtectedStateTransition.PreservesAt
      (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context header.function.evidence header.function.source
      (certificates (headers := headers) (registry := registry) (faults := faults) ranks header context) faults size := by
  apply CallableIndexedOwnedNestedExpressionTreeBounds.preserves_at_runtime
    owner header prefixZero profile complete (globals header member) slots
    header.agreement.source extension faithful observations functionTypes header.function.evidence
    header.unique owners (uninitialized header member) (missing header member)
    sameLayouts (fun target => CallableIndexedOwnedNamedCanonicalEntries.condition
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner target)
    (fun target _ => CallableIndexedOwnedNamedCanonicalEntries.authorized
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner target)
    valid.ledger valid.runtime size size (Nat.le_refl _)
  intro callee calleeMember child _strict
  exact preserves_at owner prefixZero profile complete globals slots sameLayouts extension faithful observations functionTypes
    owners uninitialized missing escaped ranks profiles child callee calleeMember

include prefixZero profile complete globals slots sameLayouts extension faithful observations functionTypes
  uninitialized missing escaped profiles in
/-- The original nested Tree closes all expression children and uses only the
strictly smaller bodies already closed by the same mutual family. -/
theorem expression_reflects_at
    (header : CallableIndexedOwnedFunctionValues.Header compiled program) (member : header ∈ headers)
    (context : SourceSemantics.Context)
    (valid : RecursiveNamedCatalogMutualMeaning.ContextFor true header.solved context header.function.evidence)
    (size : Nat) :
    ProtectedStateTransition.ReflectsAt
      (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context header.function.evidence header.function.source
      (certificates (headers := headers) (registry := registry) (faults := faults) ranks header context) faults size := by
  apply CallableIndexedOwnedNestedExpressionTreeBounds.reflects_at_runtime
    owner header prefixZero profile complete (globals header member) slots
    header.agreement.source extension faithful observations functionTypes header.function.evidence
    (uninitialized header member) (missing header member)
    sameLayouts (fun target => CallableIndexedOwnedNamedCanonicalEntries.condition
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner target)
    (fun target _ => CallableIndexedOwnedNamedCanonicalEntries.authorized
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner target)
    valid.ledger valid.runtime size size (Nat.le_refl _)
  intro callee calleeMember child _strict
  exact reflects_at owner prefixZero profile complete globals slots sameLayouts extension faithful observations functionTypes
    uninitialized missing escaped ranks profiles child callee calleeMember

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedNamedFamilyClosure
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedLambdaBodyBounds
/-! Authentic nested lambda bodies use the same imperative kernel and static
expression Tree. Named callees are closed by the proved named family; actual
parameter entries retain their own formation packets and reached pools. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedLambdaBodyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open CallableIndexedLambdaValues RecursiveNamedLambdaFormationHeads
open CallableIndexedOwnedFunctionState
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (prefixZero : owner.key.capturePrefix = 0)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (globals : ∀ header, header ∈ headers → header.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
variable
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) identities)
  (functionTypes : FunctionRuntimeViews (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (ranks : CallableIndexedOwnedFunctionValues.Header compiled program → Nat)
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}

variable (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame},
      (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers owner.key.locations owner.key.capturePrefix (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost) →
      (CallableIndexedOwnedNamedCanonicalEntries.condition (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner header) entry →
      MatchProfileWith (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (fun context => RecursiveNamedCatalogMutualMeaning.ContextFor true header.solved context header.function.evidence)
        (CallableIndexedOwnedNestedNamedFamilyClosure.certificates (headers := headers) (registry := registry) (faults := faults) ranks header)
        diagnosticPolicy header (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)

section Body
variable (principal : CallableIndexedOwnedFunctionValues.Header compiled program)
  (principalGlobals : principal.globals = compiled.indexed.base.globals.length)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {rank : Nat}
  (code : Code compiled.indexed function scope administrative)
  (body : CallableIndexedLambdaNestedRuntimeBodyMeaning.Body (values := .initial compiled.compatible.checked)
    headers principal registry faults rank code)
  (bodyUninitialized : ∀ id location, faults (.uninitializedLocation location) (code.reasonAt id))
  (bodyMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((code.reasonAt id).add tag))
  (bodyEscaped : faults .controlEscapedFunction code.compilation.internalReason)

include prefixZero complete globals slots sameLayouts extension faithful observations functionTypes
  owners uninitialized missing escaped profiles principalGlobals body bodyUninitialized bodyMissing in
/-- The original nested body Tree closes expressions internally. Its actual
input and returned formation packet contain exactly the real reached pools. -/
theorem preserves_at (size : Nat) :
    CallableRuntimeBodyOrigins.Stateful.PreservesAt
      (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner principal)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) program
      (CallableRuntimeBodyStaticOrigins.lambda_nested (values := .initial compiled.compatible.checked)
        (indexed := compiled.indexed) (program := program) code body bodyEscaped) size := by
  intro entry outcome after trace
  let readFuel := body.body.readFuel
  have expressions : ∀ context, CompatibleRuntimeContextValidity.Valid code.compilation.solvedRequirements context function.evidence →
      RecursiveNamedHeaderContracts.AtMost size (fun child => ProtectedStateTransition.PreservesAt
        (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner principal)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        program context function.evidence function.source
        (CallableIndexedLambdaNestedRuntimeCertificates.Certificates
          (CallableIndexedLambdaNestedRuntimeBodyMeaning.LowerSupport (values := .initial compiled.compatible.checked)
            (indexed := compiled.indexed) headers principal registry faults rank)
          rank principal headers code.compilation readFuel function.source context function.evidence
          code.compilation.solvedRequirements code.reasonAt) faults child) := by
    intro context valid child within
    rw [body.compilation] at valid ⊢
    apply CallableIndexedOwnedNestedExpressionTreeBounds.preserves_at_runtime
      owner principal prefixZero profile complete principalGlobals slots body.source
      extension faithful observations functionTypes function.evidence body.body.unique owners bodyUninitialized bodyMissing
      sameLayouts (fun target => CallableIndexedOwnedNamedCanonicalEntries.condition
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner target)
      (fun target _ => CallableIndexedOwnedNamedCanonicalEntries.authorized
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner target)
      valid.ledger valid.runtime size child within
    intro callee member smaller _strict
    exact CallableIndexedOwnedNestedNamedFamilyClosure.preserves_at owner prefixZero profile complete globals slots sameLayouts
      extension faithful observations functionTypes owners uninitialized missing escaped ranks profiles smaller callee member
  exact CallableRuntimeBodyKernel.Stateful.BodyFor.preserves_sized
    (body := body.toKernel) (functions := CallableIndexedOwnedFunctionValues.model headers keys registry faults profile)
    (definitions := rfl) (registered := CallableIndexedAmbient.frame_registered compiled.indexed)
    (extension := extension) (program := program) (faithful := faithful) (observations := observations)
    (escapedFault := bodyEscaped) (extend := fun valid extended => valid.extend extended)
    (runtimeOf := fun valid => valid)
    (protocol := CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner principal)
    (producer := CallableIndexedOwnedNestedCanonicalState.markedProducer owner principal
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile)))
    (conditionGate := CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (acquire := fun _ _ stable => CallableIndexedOwnedNestedCanonicalState.readyAt_of_stableOwner owner principal
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile)) stable)
    (stateTransport := CallableIndexedOwnedNestedCanonicalState.administrativeTransport owner principal)
    (stateBindings := CallableIndexedOwnedNestedCanonicalState.bindings owner principal)
    size size (Nat.le_refl _) expressions
    entry.environments entry.heaps entry.locals entry.lookups entry.actualTyped entry.reference entry.read
    entry.unmapped entry.initial entry.gate trace

include prefixZero complete globals slots sameLayouts extension faithful observations functionTypes
  uninitialized missing escaped profiles principalGlobals body bodyUninitialized bodyMissing in
/-- The same native body proof returns its independent Source grade and the
actual post state, including every ordered record produced by callees. -/
theorem reflects_at (size : Nat) :
    CallableRuntimeBodyOrigins.Stateful.ReflectsAt
      (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner principal)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) program
      (CallableRuntimeBodyStaticOrigins.lambda_nested (values := .initial compiled.compatible.checked)
        (indexed := compiled.indexed) (program := program) code body bodyEscaped) size := by
  intro entry value finalStore completed
  let readFuel := body.body.readFuel
  have expressions : ∀ context, CompatibleRuntimeContextValidity.Valid code.compilation.solvedRequirements context function.evidence →
      RecursiveNamedBoundedContracts.Below size (fun child => ProtectedStateTransition.ReflectsAt
        (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner principal)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        program context function.evidence function.source
        (CallableIndexedLambdaNestedRuntimeCertificates.Certificates
          (CallableIndexedLambdaNestedRuntimeBodyMeaning.LowerSupport (values := .initial compiled.compatible.checked)
            (indexed := compiled.indexed) headers principal registry faults rank)
          rank principal headers code.compilation readFuel function.source context function.evidence
          code.compilation.solvedRequirements code.reasonAt) faults child) := by
    intro context valid child strict
    rw [body.compilation] at valid ⊢
    apply CallableIndexedOwnedNestedExpressionTreeBounds.reflects_at_runtime
      owner principal prefixZero profile complete principalGlobals slots body.source
      extension faithful observations functionTypes function.evidence bodyUninitialized bodyMissing
      sameLayouts (fun target => CallableIndexedOwnedNamedCanonicalEntries.condition
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner target)
      (fun target _ => CallableIndexedOwnedNamedCanonicalEntries.authorized
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner target)
      valid.ledger valid.runtime size child (Nat.le_of_lt strict)
    intro callee member smaller _strict
    exact CallableIndexedOwnedNestedNamedFamilyClosure.reflects_at owner prefixZero profile complete globals slots sameLayouts
      extension faithful observations functionTypes uninitialized missing escaped ranks profiles smaller callee member
  exact CallableRuntimeBodyKernel.Stateful.BodyFor.reflects_sized
    (body := body.toKernel) (functions := CallableIndexedOwnedFunctionValues.model headers keys registry faults profile)
    (definitions := rfl) (registered := CallableIndexedAmbient.frame_registered compiled.indexed)
    (extension := extension) (program := program) (faithful := faithful) (observations := observations)
    (functionTypes := functionTypes) (escapedFault := bodyEscaped)
    (extend := fun valid extended => valid.extend extended) (runtimeOf := fun valid => valid)
    (protocol := CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner principal)
    (producer := CallableIndexedOwnedNestedCanonicalState.markedProducer owner principal
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile)))
    (conditionGate := CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (acquire := fun _ _ stable => CallableIndexedOwnedNestedCanonicalState.readyAt_of_stableOwner owner principal
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile)) stable)
    (stateTransport := CallableIndexedOwnedNestedCanonicalState.administrativeTransport owner principal)
    (stateBindings := CallableIndexedOwnedNestedCanonicalState.bindings owner principal)
    size size (Nat.le_refl _) expressions
    entry.environments entry.heaps entry.locals entry.lookups entry.actualTyped entry.reference entry.read
    entry.unmapped entry.initial entry.gate completed
end Body

section Continuation
variable (principal : CallableIndexedOwnedFunctionValues.Header compiled program)
  (principalGlobals : principal.globals = compiled.indexed.base.globals.length)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {rank : Nat}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative)
  (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  (body : CallableIndexedLambdaNestedRuntimeBodyMeaning.Body (values := .initial compiled.compatible.checked)
    headers principal registry faults rank code)
  (bodyUninitialized : ∀ id location, faults (.uninitializedLocation location) (code.reasonAt id))
  (bodyMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((code.reasonAt id).add tag))
  (bodyEscaped : faults .controlEscapedFunction code.compilation.internalReason)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := program)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  (sourceSeed : history.metadata = CallableIndexedNamedGeneration.state principal.named)
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)

include prefixZero complete globals slots sameLayouts extension faithful observations functionTypes
  owners uninitialized missing escaped profiles principalGlobals body bodyUninitialized bodyMissing observed sourceSeed in
/-- A strict Source invocation child uses its authentic parameter Entry and
actual reached pool. All expression and named body meanings are closed here. -/
theorem source_continuation (budget : Nat) :
    CallableIndexedOwnedLambdaInvocationBounds.SourceContinuation (arguments := arguments) (nativeArguments := nativeArguments)
      captured code history inputs (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile)
      owner caller (CallableIndexedOwnedLambdaInvocationBounds.BodyOrigin.nested code inputs body bodyEscaped) budget := by
  apply CallableIndexedOwnedLambdaNestedEntries.source_continuation_of_nested
    captured code history inputs (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile)
    owner principal observed body.administrative sourceSeed caller
    (CallableIndexedOwnedLambdaInvocationBounds.BodyOrigin.nested code inputs body bodyEscaped) budget
  intro entry added length copied spine kept reached child _strict
  exact preserves_at owner prefixZero profile complete globals slots sameLayouts extension faithful observations functionTypes
    owners uninitialized missing escaped ranks profiles principal principalGlobals code body bodyUninitialized bodyMissing bodyEscaped child
    (CallableIndexedOwnedLambdaNestedEntries.source_entry captured code history inputs
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner principal observed body.administrative sourceSeed
      caller (CallableIndexedOwnedLambdaInvocationBounds.BodyOrigin.nested code inputs body bodyEscaped) entry added length copied spine kept reached)

include prefixZero complete globals slots sameLayouts extension faithful observations functionTypes
  uninitialized missing escaped profiles principalGlobals body bodyUninitialized bodyMissing observed sourceSeed in
/-- Native invocation reflection consumes its own complete measured Prefix and
retains the independent Source grade and the same body-produced final pool. -/
theorem native_continuation (budget : Nat) :
    CallableIndexedOwnedLambdaInvocationBounds.NativeContinuation (arguments := arguments)
      captured code history inputs (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile)
      owner caller (CallableIndexedOwnedLambdaInvocationBounds.BodyOrigin.nested code inputs body bodyEscaped) budget := by
  apply CallableIndexedOwnedLambdaNestedEntries.native_continuation_of_nested
    captured code history inputs (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile)
    owner principal observed body.administrative sourceSeed caller
    (CallableIndexedOwnedLambdaInvocationBounds.BodyOrigin.nested code inputs body bodyEscaped) budget
  intro entry reached child _strict
  exact reflects_at owner prefixZero profile complete globals slots sameLayouts extension faithful observations functionTypes
    uninitialized missing escaped ranks profiles principal principalGlobals code body bodyUninitialized bodyMissing bodyEscaped child
    (CallableIndexedOwnedLambdaNestedEntries.native_entry captured code history inputs
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner principal observed body.administrative sourceSeed
      caller (CallableIndexedOwnedLambdaInvocationBounds.BodyOrigin.nested code inputs body bodyEscaped) entry reached)
end Continuation

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedLambdaBodyBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedTypedLambdaProtocolContinuations
/-! Typed finish consumes flow under the actual caller protocol carried by its
parameter packet. A packet adds only authentic static canonical authority to
that same Entry/Prefix and base pool. Source and native finish each use one
strict flow child and the original SourceReceipt; their real returned pool is
projected forward. No arbitrary base environment acquires a canonical packet.
-/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedTypedLambdaProtocolContinuations
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedOwnedTypedLambdaBodyContinuations (Validity)
open RecursiveNamedCatalogInvocationBounds (Below)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  {expressionSyntax : TypedSource → ExpressionId → Prop}
  {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (body : CallableIndexedOwnedTypedLambdaStaticBody.Body code program expressionSyntax certificates)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {bodyProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) bodyProtocol)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)

/-- The only new packet fields are genuine states over the original parameter
indices, with a literal forward base-pool equation. No execution or grade field
is present. Concrete ordinary/Principal constructors supply these states. -/
structure Packets where
  source : ∀ (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history body.toContext functions registry arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (added : Environment), added.length = code.receipt.loweredParameters.length →
    ∀ copied : Environment, entry.entry.canonical = added ++ copied →
      (∀ slot, scope.length ≤ slot → copied[slot]? = captured.canonical[slot]?) →
    ∀ reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩,
      { actual : bodyProtocol.State
          ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
            entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩ //
        bridge.pool actual = reached }
  native : ∀ (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history body.toContext functions registry arguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current),
    ∀ reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩,
      { actual : bodyProtocol.State
          ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
            entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩ //
        bridge.pool actual = reached }

/-- Flow is indexed by the protocol which contains actual canonical authority,
rather than by every arbitrary bare base-pool environment. The retained tree,
Source/context/scope, body flow and validity remain exactly the original ones. -/
def FlowPreserves (size : Nat) : Prop :=
  RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    bodyProtocol (readiness bridge)
    (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (ProtectedStateImperativeTypedSourceSites.Facts function.source (expressionSyntax function.source))
    functions program function.evidence (Validity (program := program) captured code)
    (source := function.source) (context := body.context) (registry := registry) (faults := faults)
    (frameLayout := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length)
    (administrative := captured.administrative) size
    (scope := code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    true function.body function.resultType code.receipt.resultCore body.flow

def FlowReflects (size : Nat) : Prop :=
  RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    bodyProtocol (readiness bridge)
    (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (ProtectedStateImperativeTypedSourceSites.Facts function.source (expressionSyntax function.source))
    functions program function.evidence (Validity (program := program) captured code)
    (source := function.source) (context := body.context) (registry := registry) (faults := faults)
    (frameLayout := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length)
    (administrative := captured.administrative) size
    (scope := code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    true function.body function.resultType code.receipt.resultCore body.flow

private theorem project_transition {initial final : ProtectedStateTransition.Index}
    {base : State headers keys initial} {actual : bodyProtocol.State initial}
    (same : bridge.pool actual = base)
    (transition : ProtectedStateTransition.Transition bodyProtocol actual final) :
    ProtectedStateTransition.Transition (protocol headers keys) base final := by
  obtain ⟨returned, related⟩ := transition
  refine ⟨bridge.pool returned, ?_⟩
  change CallableIndexedOwnedFunctionState.Relates base (bridge.pool returned)
  simpa only [same] using bridge.related related

variable (packets : Packets (registry := registry) (arguments := arguments)
    (nativeArguments := nativeArguments) captured code history body functions bridge owner caller)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments body.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)
  (wellFormed : ProgramWellFormed program)

include stable in
private theorem parameter_rows {next : NativeFrame} {nextGhost : GhostFrame} {metadata : Option MetadataState}
    {final : ProtectedStateTransition.Index}
    (reached : State headers keys final)
    (carried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table next nextGhost metadata)
    (parameters : AdministrativePreserved mapping
      (store.set owner.key.frameLocation (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame next))
      final.mapping final.store) :
    CallableIndexedOwnedIndirectExpressionHeads.StableRows reached :=
  CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative
    (install caller owner.position (.stable carried)) reached
    (CallableIndexedOwnedAdmittedBodyEntries.stable_rows_install caller stable owner.position carried) parameters

private theorem body_facts {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    (receipt : CallableIndexedOwnedAdmittedBodyEntries.SourceReceipt program function body.context environment heap) :
    ProtectedStateImperativeTypedSourceSites.Facts function.source (expressionSyntax function.source)
      body.context true function.body function.resultType := by
  obtain ⟨final, facts, typed, _⟩ := receipt.bodyTyped
  exact ⟨body.syntaxTree, { returnType := function.resultType }, final, facts, typed⟩

include beforeTyped argumentsTyped stable wellFormed packets in
/-- The authentic Source parameter Entry acquires its real canonical packet,
then one protocol-indexed strict flow child supplies original typed finish.
Only that same returned state projects to the low-level base continuation. -/
theorem source_continuation (budget : Nat)
    (below : Below budget (FlowPreserves captured code body functions bridge
      (registry := registry) (faults := faults))) :
    CallableIndexedOwnedLambdaEntryBodyContracts.SourceContinuation
      (registry := registry) (faults := faults) (arguments := arguments) (nativeArguments := nativeArguments)
      captured code history body.toContext functions owner caller budget := by
  intro entry added length copied spine kept reached child strict outcome after trace
  let selected := packets.source entry added length copied spine kept reached
  have source := CallableIndexedOwnedTypedLambdaBodyContinuations.source_receipt
    captured code history body functions owner caller beforeTyped argumentsTyped entry
  have admitted : Admission bridge body.context selected.val := by
    refine ⟨source.heapTyped, ?_⟩
    rw [selected.property]
    exact parameter_rows owner caller stable reached entry.nextHistory entry.entry.frame
  have gate : CallableIndexedOwnedAllocationProducer.StableOwner keys owner.key.frameLocation entry.next :=
    ⟨owner.position, _, _, rfl, entry.nextHistory⟩
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
      frame, metadata, exit, post⟩ :=
    CallableIndexedOwnedTypedFunctionFinishBounds.WithReady.preserves_at_emitted_with_source_receipt
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (functions := functions) (program := program) (tree := body.tree)
      (projection := body.projection) (unique := body.unique)
      bodyProtocol (readiness bridge) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (ProtectedStateImperativeTypedSourceSites.Facts function.source (expressionSyntax function.source))
      body.emitted (Validity (program := program) captured code) child (below child strict) ⟨body.valid, source.runtime⟩
      (body_facts captured code body source)
      entry.entry.environments entry.entry.heaps entry.entry.locals entry.entry.lookups entry.entry.actualTyped
      entry.entry.reference entry.entry.read entry.entry.unmapped selected.val gate admitted source wellFormed trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
    frame, metadata, exit, project_transition bridge selected.property post.forget⟩

include beforeTyped argumentsTyped stable wellFormed packets in
/-- The independent native Prefix has its own authentic canonical packet and
SourceReceipt. One strict native flow family feeds finish; the original reached
base pool and independent Source grade survive the forward projection. -/
theorem native_continuation (budget : Nat)
    (below : Below budget (FlowReflects captured code body functions bridge
      (registry := registry) (faults := faults))) :
    CallableIndexedOwnedLambdaEntryBodyContracts.NativeContinuation
      (registry := registry) (faults := faults) (arguments := arguments)
      captured code history body.toContext functions owner caller budget := by
  intro entry reached child strict value finalStore completed
  let selected := Packets.native (registry := registry) (arguments := arguments)
    (nativeArguments := nativeArguments) packets entry reached
  have source := CallableIndexedOwnedTypedLambdaBodyContinuations.native_receipt
    captured code history body functions owner caller beforeTyped argumentsTyped entry
  have admitted : Admission bridge body.context selected.val := by
    refine ⟨source.heapTyped, ?_⟩
    rw [selected.property]
    exact parameter_rows owner caller stable reached entry.nextHistory entry.frame
  have gate : CallableIndexedOwnedAllocationProducer.StableOwner keys owner.key.frameLocation entry.next :=
    ⟨owner.position, _, _, rfl, entry.nextHistory⟩
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
      frame, metadata, exit, post⟩ :=
    CallableIndexedOwnedTypedFunctionFinishBounds.WithReady.reflects_at_emitted_with_source_receipt
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (functions := functions) (program := program) (tree := body.tree)
      (projection := body.projection) (unique := body.unique)
      bodyProtocol (readiness bridge) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (ProtectedStateImperativeTypedSourceSites.Facts function.source (expressionSyntax function.source))
      body.emitted (Validity (program := program) captured code) budget child (Nat.le_of_lt strict) below ⟨body.valid, source.runtime⟩
      (body_facts captured code body source)
      entry.environments entry.heaps entry.locals entry.lookups entry.actualTyped
      entry.reference entry.read entry.unmapped selected.val gate admitted source wellFormed completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
    frame, metadata, exit, project_transition bridge selected.property post.forget⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedTypedLambdaProtocolContinuations
end
