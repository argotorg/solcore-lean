import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.InvocationBounds
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.RuntimeBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.FunctionValuesAndState
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.IndirectExpressionHeads
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateForHeaders
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LexicalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Diagnostics.ReachedNamedFaultPaths
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogEntries
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.StatementContracts
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateForPost
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LoopAndMatchBounds

/-!
# Owned callables: nested entries

Nested caller protocol and body entries, nested expression heads and tree bounds, and named argument admission.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSourceBodyReadyBounds
/-! Source runtime validity strengthens the compiler origin's visited domain.
The completed shared body proof still describes the original actual entry,
code and returned pool. These finite adapters expose that original contract. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSourceBodyReadyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedOwnedBodySourceOrigin (source_origin)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {condition : Location → NativeFrame → Prop}
  {origin : CallableRuntimeBodyOrigins.StaticOrigin (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) registry faults}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  (runtime : Dynamic.SourceRuntimeValid program origin.context origin.function.source)
  (wellFormed : ProgramWellFormed program)
  (syntaxTree : GenericImperativeMatch.Syntax origin.function.source origin.expressionSyntax
    origin.context (.statements true origin.function.body) origin.function.resultType)

include wellFormed syntaxTree in
/-- Reindexing the genuine Source domain retains the exact preservation
witness at the original parameter entry and returned state. -/
theorem preserves_at {size : Nat}
    (meaning : CallableRuntimeBodyReadyOrigins.PreservesAt callerProtocol (readiness bridge) condition
      (ProtectedStateImperativeTypedSourceSites.Facts origin.function.source origin.expressionSyntax)
      functions program (source_origin origin runtime) size) :
    CallableIndexedOwnedAdmittedBodyEntries.PreservesAt bridge
      (condition := condition) (origin := origin) (functions := functions) size := by
  intro entry outcome after trace
  exact CallableIndexedOwnedAdmittedBodyReadyBounds.preserves_at
    (origin := source_origin origin runtime) (size := size) bridge wellFormed syntaxTree meaning
    (CallableIndexedOwnedBodySourceOrigin.admitted_entry bridge entry) trace

include wellFormed syntaxTree in
/-- The same original native completion is reflected with an independent
Source grade and admission at its actual returned state. -/
theorem reflects_at {size : Nat}
    (meaning : CallableRuntimeBodyReadyOrigins.ReflectsAt callerProtocol (readiness bridge) condition
      (ProtectedStateImperativeTypedSourceSites.Facts origin.function.source origin.expressionSyntax)
      functions program (source_origin origin runtime) size) :
    CallableIndexedOwnedAdmittedBodyEntries.ReflectsAt bridge
      (condition := condition) (origin := origin) (functions := functions) size := by
  intro entry value finalStore completed
  exact CallableIndexedOwnedAdmittedBodyReadyBounds.reflects_at
    (origin := source_origin origin runtime) (size := size) bridge wellFormed syntaxTree meaning
    (CallableIndexedOwnedBodySourceOrigin.admitted_entry bridge entry) completed

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSourceBodyReadyBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedArgumentAdmission
/-! Genuine direct-call typing and the actual successful argument trace supply
raw Source admission for the named callee. The original argument type row stays
independent of projected native types; packed typing is unpacked only after the
actual argument arity is known. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedArgumentAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open RecursiveNamedCatalog CallableAncestryPairedLookup

/-- The actual direct-call parent exposes the original raw argument row and
its complete declaration application. -/
theorem direct_arguments {source : TypedSource} {context : SourceSemantics.Context}
    {id callee : ExpressionId} {ids : List ExpressionId} {node : ExpressionNode}
    {type : TypeSystem.Ty} {instantiation : DeclarationInstantiation}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.declaration instantiation))
    (typed : ExpressionHasType source context id type) :
    ∃ originalTypes rawResult predicates,
      ExpressionsHaveTypes source context ids originalTypes ∧
      SourceSemantics.DeclarationApplicationValid context instantiation originalTypes rawResult predicates := by
  cases typed with
  | @intro _ _ actualNode rawType plan contains raw _ _ _ _ =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    subst actualNode
    rw [form] at raw
    cases raw with
    | directCall _ application arguments => exact ⟨_, _, _, arguments, application⟩

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context} {definitions : DataEnvironment} {program : Program}

/-- Original argument execution supplies the actual heap; the genuine Header
certificate supplies the callee context and raw binder types. -/
theorem at_successful_arguments (header : Header prepared values definitions program)
    {context : SourceSemantics.Context} {source : TypedSource} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {ids : List ExpressionId} {arguments : List Dynamic.Value} {originalTypes : List TypeSystem.Ty}
    {rawResult : TypeSystem.Ty} {predicates : List ProgramPredicate}
    (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context) (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (argumentTypes : ExpressionsHaveTypes source context ids originalTypes)
    (application : SourceSemantics.DeclarationApplicationValid context header.instantiation originalTypes rawResult predicates)
    (evaluated : Dynamic.ExpressionsEvaluate program context evidence source environment before ids arguments after)
    (arity : header.function.parameters.length = arguments.length) :
    Dynamic.HeapWellTyped header.function.context after ∧
      Dynamic.ValuesHaveTypes header.function.context after arguments header.types := by
  have preserves : Dynamic.ExpressionExecutionPreserves program context evidence source environment := by
    intro before after id value type covers locals heapTyped typed evaluated
    exact wellFormed.wholeLanguagePreservation.expression context evidence source environment before after id value type runtime covers locals heapTyped typed evaluated
  have actual := Dynamic.ExpressionsEvaluate.preserves preserves covers locals heapTyped argumentTypes evaluated
  obtain ⟨facts, certified⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
  cases application with
  | intro _signature _valid _declaration _parameters _result functionType _predicates =>
    have packedType := (TypeSystem.Ty.function.inj (functionType.symm.trans certified.callable_type)).1
    obtain ⟨packed, packing⟩ := Dynamic.ValuesPack.exists_pack arguments
    have packedTyped := packing.hasType actual.1
    rw [packedType] at packedTyped
    have signatures := certified.signatures_eq.trans runtime.signatures.symm
    have bodyHeap := actual.2.1.transportClosed signatures runtime.closed certified.type_parameters_empty
      runtime.variables_closed certified.residual_type_variables_open
    have bodyPacked := packedTyped.transportClosed signatures runtime.closed certified.type_parameters_empty
      runtime.variables_closed certified.residual_type_variables_open
    have length : arguments.length = header.types.length :=
      arity.symm.trans ((congrArg List.length header.frame.parameters).trans certified.typing.inputs_extend.length_eq)
    have bodyArguments := packing.unpackTypes bodyPacked length
    exact ⟨header.frame.context.symm ▸ bodyHeap, header.frame.context.symm ▸ bodyArguments⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedArgumentAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedCanonicalEntries
/-! A real named hook and its exact specialization record authorize the full
Source metadata at the selected physical frame. The actual parameter entry
then supplies the frame reference, argument bundle and original global slots
beside the same reached pool used by the body. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedCanonicalEntries
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open CallableIndexedOwnedFunctionState
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (header : CallableIndexedOwnedFunctionValues.Header compiled program)

/-- This condition retains the physical selected owner and the complete
original named Source seed. It makes no assertion about body execution. -/
def condition : BodyCondition (prepared := compiled.indexed.ancestry)
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
    functions registry header :=
  fun {_ _ _ _ _ _ _ _ _ frameLocation current ghost} _ =>
    frameLocation = owner.key.frameLocation ∧
    Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table current ghost
      (some (CallableIndexedNamedGeneration.state header.named))

/-- The genuine compiler record fixes the Source seed retained by the actual
hook's named history, including its original source and substitution. -/
theorem authorized :
    CallableIndexedOwnedInvocationBounds.BodyAuthorizationAt
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      functions registry header owner.key.frameLocation (condition functions owner header) := by
  intro origin index metadata arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation
    physical selected carried _emitted _entry
  have record := CallableIndexedActualNamedSourceReceipts.header_record compiled header
  have generated := CallableIndexedNamedGeneration.seed compiled.indexed selected record
  have authenticated := carried.authenticates
  cases authenticated with
  | named actual =>
    have same : metadata = CallableIndexedNamedGeneration.state header.named :=
      Option.some.inj (actual.symm.trans generated)
    exact ⟨physical, same ▸ carried⟩

/-- The same physical and Source receipts supply the original allocation gate. -/
theorem stable_owner
    {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
    {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
    {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
    (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost)
    (allowed : condition functions owner header entry) :
    CallableIndexedOwnedAllocationProducer.StableOwner keys frameLocation current :=
  ⟨owner.position, ghost, some (CallableIndexedNamedGeneration.state header.named), allowed.1.symm, allowed.2⟩

variable {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
  (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers owner.key.locations owner.key.capturePrefix functions registry header arguments before initialStore initialMap initialWorld
    administrative actualContext actual ξ frameLocation current ghost)
  (initial : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
    entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)

/-- A complete real parameter entry supplies every nested formation observation.
The Source metadata comes from the genuine hook condition, not pool ownership. -/
theorem packet (captureZero : owner.key.capturePrefix = 0)
    (globals : header.globals = compiled.indexed.base.globals.length)
    (allowed : condition functions owner header entry) :
    CallableIndexedOwnedNestedCanonicalState.Packet owner header _ initial := by
  apply CallableIndexedOwnedNestedCanonicalState.packet_of_stable_read owner header initial
  · refine ⟨?_, ?_⟩
    · intro target member
      simpa only [captureZero, Nat.zero_add] using entry.catalog.globals target member
    · simpa only [List.length_map, List.length_reverse, globals, allowed.1] using entry.reference
  · exact entry.environments
  · rw [header.parameterType]
    rfl
  · exact allowed.2
  · simpa only [allowed.1] using entry.state.read

/-- The proof wrapper contains the original reached pool verbatim. -/
def wrap (captureZero : owner.key.capturePrefix = 0)
    (globals : header.globals = compiled.indexed.base.globals.length)
    (allowed : condition functions owner header entry) :
    (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header).State
      ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩ :=
  ⟨initial, packet functions owner header entry initial captureZero globals allowed⟩

theorem wrap_pool (captureZero : owner.key.capturePrefix = 0)
    (globals : header.globals = compiled.indexed.base.globals.length)
    (allowed : condition functions owner header entry) :
    (wrap functions owner header entry initial captureZero globals allowed).val = initial := rfl

section Meaning
variable {faults : FunctionCalls.FaultRep}

/-- Specialize the nested body proof at its complete actual parameter input,
then return the same reached base pool after forgetting only the packet. -/
theorem preserves_of_nested (captureZero : owner.key.capturePrefix = 0)
    (globals : header.globals = compiled.indexed.base.globals.length) (size : Nat)
    (meaning : RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      functions registry header faults (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header)
      (condition functions owner header) size) :
    RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      functions registry header faults (protocol headers keys) (condition functions owner header) size := by
  intro arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost
    entry initial outcome after allowed trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds, frame, metadata, returned, related⟩ :=
    meaning entry (wrap functions owner header entry initial captureZero globals allowed) allowed trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds, frame, metadata, returned.val, related⟩

/-- The independent Source grade and complete actual native post survive the
same proof-wrapper projection. -/
theorem reflects_of_nested (captureZero : owner.key.capturePrefix = 0)
    (globals : header.globals = compiled.indexed.base.globals.length) (size : Nat)
    (meaning : RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      functions registry header faults (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header)
      (condition functions owner header) size) :
    RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      functions registry header faults (protocol headers keys) (condition functions owner header) size := by
  intro arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost
    entry initial value finalStore allowed completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds, frame, metadata, returned, related⟩ :=
    meaning entry (wrap functions owner header entry initial captureZero globals allowed) allowed completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds, frame, metadata, returned.val, related⟩

end Meaning

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedCanonicalEntries
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyNestedEntries
/-! A genuine nested formation packet accompanies one complete actual body
entry. The wrapper preserves the same underlying input and reached pools. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyNestedEntries
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (principal : CallableIndexedOwnedFunctionValues.Header compiled program)
  {conditionGate : Location → CallableIndexedHistory.NativeFrame → Prop}
  {origin : CallableRuntimeBodyOrigins.StaticOrigin (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) registry faults}
  (entry : CallableRuntimeBodyOrigins.Stateful.Entry (protocol headers keys) conditionGate origin functions)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner principal _ entry.initial)

def wrap : CallableRuntimeBodyOrigins.Stateful.Entry
    (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner principal) conditionGate origin functions :=
  { entry with initial := ⟨entry.initial, packet⟩ }

theorem preserves_of_nested {size : Nat}
    (meaning : CallableRuntimeBodyEntryContracts.PreservesAt
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (protocol := CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner principal)
      (conditionGate := conditionGate) (origin := origin) functions program
      (wrap functions owner principal entry packet) size) :
    CallableRuntimeBodyEntryContracts.PreservesAt
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (protocol := protocol headers keys) (conditionGate := conditionGate) (origin := origin)
      functions program entry size := by
  intro outcome after trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds,
    frame, metadata, exit, returned, related⟩ := meaning trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds,
    frame, metadata, exit, returned.val, related⟩

theorem reflects_of_nested {size : Nat}
    (meaning : CallableRuntimeBodyEntryContracts.ReflectsAt
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (protocol := CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner principal)
      (conditionGate := conditionGate) (origin := origin) functions program
      (wrap functions owner principal entry packet) size) :
    CallableRuntimeBodyEntryContracts.ReflectsAt
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (protocol := protocol headers keys) (conditionGate := conditionGate) (origin := origin)
      functions program entry size := by
  intro value finalStore completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds,
    frame, metadata, exit, returned, related⟩ := meaning completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds,
    frame, metadata, exit, returned.val, related⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyNestedEntries
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedCallerProtocol
/-! Genuine nested formation observations return with the same actual named
call post pool. The retained administrative frame read authenticates reached
metadata against its own ghost; ordered records are projected verbatim. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedCallerProtocol
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedNestedCanonicalState
open CallableIndexedOwnedExpressionHeads (Globals)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : CallableIndexedOwnedFunctionValues.Header compiled program)

/-- Stronger caller facts accompany the actual argument/body returned pool.
The return operation never substitutes an administratively extended pool. -/
def carrier : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => Globals (headers := headers) owner 1 index.scope index.canonical)
    (protocol (headers := headers) owner caller) where
  pool := fun state => state.val
  records_eq := fun _ => rfl
  related := fun relation => relation
  slots := fun state => state.property.globals
  restore := by
    intro index initial mapping world heap store reached maps worlds frame metadata relation
    exact ⟨⟨reached, Packet.after owner caller initial.property reached frame⟩, rfl, relation⟩

/-- The carrier reads the same complete pool witness from the wrapper. -/
theorem pool_eq {index : ProtectedStateTransition.Index}
    (state : (protocol (headers := headers) owner caller).State index) :
    (carrier owner caller).pool state = state.val := rfl

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedCallerProtocol
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyRestorationAdmission
/-! The actual body post survives restoration of the saved caller cell.
Successful Source typing moves only along a genuine context-support receipt;
faults retain every row's stable history without a deep heap typing claim. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyRestorationAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {caller body : ProtectedStateTransition.Index}

/-- This carrier observes the actual owned pool before and after restoration. -/
def bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) (protocol headers keys) :=
  CallableIndexedOwnedIndirectCallerProtocol.of_legacy CallableIndexedOwnedCallerProtocol.base

/-- Saved stable reads and the actual restored frame authenticate every
returned row against that row's own current ghost. -/
theorem restore_rows (saved : State headers keys caller) (reached : State headers keys body)
    (selected : Fin keys.length) (savedRows : StableRows saved)
    (restoredFrame : AdministrativePreserved caller.mapping caller.store body.mapping
      (CallableIndexedOwnedBodyRestoration.finalIndex (body := body) saved selected).store) :
    StableRows (CallableIndexedOwnedBodyRestoration.returned saved reached selected) :=
  StableRows.after_administrative saved
    (CallableIndexedOwnedBodyRestoration.returned saved reached selected) savedRows restoredFrame

/-- A genuine fault post retains rows without requiring value or heap typing,
or a relation between the body and caller's static type contexts. -/
theorem restore_fault_post (saved : State headers keys caller) (reached : State headers keys body)
    (selected : Fin keys.length) {context : SourceSemantics.Context} {type : TypeSystem.Ty}
    {reason : Dynamic.SemanticFault} (savedRows : StableRows saved)
    (restoredFrame : AdministrativePreserved caller.mapping caller.store body.mapping
      (CallableIndexedOwnedBodyRestoration.finalIndex (body := body) saved selected).store) :
    PostAdmission bridge context type (.fault reason)
      (CallableIndexedOwnedBodyRestoration.returned saved reached selected) := by
  refine ⟨restore_rows saved reached selected savedRows restoredFrame, ?_⟩
  intro value same
  cases same

/-- Restoration keeps the body's raw heap and the returned pool's own ghosts.
The saved caller's stable reads authenticate all of those restored rows. -/
theorem restore_post (saved : State headers keys caller) (reached : State headers keys body)
    (selected : Fin keys.length) {bodyContext callerContext : SourceSemantics.Context}
    {type : TypeSystem.Ty} {outcome : Dynamic.ExpressionOutcome}
    (savedRows : StableRows saved)
    (post : PostAdmission bridge bodyContext type outcome reached)
    (supports : Dynamic.TypeContextSupports bodyContext callerContext)
    (restoredFrame : AdministrativePreserved caller.mapping caller.store body.mapping
      (CallableIndexedOwnedBodyRestoration.finalIndex (body := body) saved selected).store) :
    PostAdmission bridge callerContext type outcome
      (CallableIndexedOwnedBodyRestoration.returned saved reached selected) := by
  refine ⟨restore_rows saved reached selected savedRows restoredFrame, ?_⟩
  intro value same
  obtain ⟨valueTyped, heapTyped⟩ := post.successful value same
  exact ⟨valueTyped.transportContext supports, heapTyped.transportContext supports⟩

/-- The original restore producer runs once and retains its complete tuple.
The added post describes that same returned state and unchanged Source heap. -/
theorem restore_return_with_post (saved : State headers keys caller)
    (reached : State headers keys body) (selected : Fin keys.length) {next : NativeFrame}
    {functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
    {registry : SourceCoreRawMetadata.Registry}
    {bodyContext callerContext : SourceSemantics.Context} {type : TypeSystem.Ty}
    {outcome : Dynamic.ExpressionOutcome}
    (registered : compiled.indexed.ancestry.layout.frame.Registered compiled.indexed.layouts.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
      body.mapping body.world body.heap body.store)
    (worlds : WorldExtends caller.world body.world)
    (frame : AdministrativePreserved caller.mapping
      (caller.store.set keys[selected.val].frameLocation (encode compiled.indexed.ancestry.layout.frame next))
      body.mapping body.store)
    (related : Relates saved reached) (savedRows : StableRows saved)
    (post : PostAdmission bridge bodyContext type outcome reached)
    (supports : Dynamic.TypeContextSupports bodyContext callerContext) :
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
      body.mapping body.world body.heap
      (CallableIndexedOwnedBodyRestoration.finalIndex (body := body) saved selected).store ∧
    AdministrativePreserved caller.mapping caller.store body.mapping
      (CallableIndexedOwnedBodyRestoration.finalIndex (body := body) saved selected).store ∧
    CellState compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      compiled.indexed.ancestry.layout.frame keys[selected.val].frameLocation
      (saved.rows selected).authority.current (saved.rows selected).authority.ghost
      (CallableIndexedOwnedBodyRestoration.finalIndex (body := body) saved selected).store ∧
    Relates reached (CallableIndexedOwnedBodyRestoration.returned saved reached selected) ∧
    Relates saved (CallableIndexedOwnedBodyRestoration.returned saved reached selected) ∧
    records (CallableIndexedOwnedBodyRestoration.returned saved reached selected) = records reached ∧
    ProtectedStateTransition.Transition (protocol headers keys) saved
      (CallableIndexedOwnedBodyRestoration.finalIndex (body := body) saved selected) ∧
    PostAdmission bridge callerContext type outcome
      (CallableIndexedOwnedBodyRestoration.returned saved reached selected) := by
  obtain ⟨finalHeaps, finalFrame, finalCell, fromBody, fromSaved, sameRecords, transition⟩ :=
    CallableIndexedOwnedBodyRestoration.restore_return saved reached selected registered heaps worlds frame related
  exact ⟨finalHeaps, finalFrame, finalCell, fromBody, fromSaved, sameRecords, transition,
    restore_post saved reached selected savedRows post supports finalFrame⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyRestorationAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedDirectTypedNamedBodyContinuations
/-! Named calls retain their original Header, compiler profile and canonical
global slots. Actual parameter allocations establish independent Source typing.
Strict flow children with actual reached diagnostics feed the original typed finish and low invocation;
the returned state is the same reached pool. The joint named/global flow
family remains an explicit obligation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedDirectTypedNamedBodyContinuations
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open CallableIndexedOwnedAdmittedBodyEntries (SourceReceipt)
open CallableIndexedOwnedSourceAdmission (Admission)
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds (BodyState Below)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled program →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled program → ExpressionId → Prop}

/-- Actual static compilation evidence for this Header. Registry-specific
reached diagnostics are supplied to the flow producer separately. -/
structure Profile (runtime : Bool) (header : CallableIndexedOwnedFunctionValues.Header compiled program)
    (administrative : Core.Context) where private mk ::
  initialValid : RecursiveNamedCatalogMutualMeaning.ContextFor runtime header.solved header.context header.function.evidence
  accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
    header.output header.reasonAt header.fellThrough header.escaped = .ok header.body
  projection : compiled.compatible.checked.catalog.project header.function.resultType = .ok header.output
  flow : Expr
  generated : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
    header.output header.reasonAt true header.escaped = .ok flow
  emitted : header.body = CompatibleStatements.finish header.output flow header.fellThrough header.escaped
  tree : GenericImperativeMatch.Tree header.layouts header.owner header.active compiled.indexed.ancestry.layout.frame header.globals
    header.onError (.initial compiled.compatible.checked) header.function.source (expressionSyntax header)
    (certificates header)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) header.context
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    (.statements true header.function.body) header.function.resultType header.output flow

/-- Accepted body and flow equations derive the actual finish equation. The
retained Tree is static compiler evidence and supplies no execution law. -/
def Profile.of_extracted {runtime : Bool}
    {header : CallableIndexedOwnedFunctionValues.Header compiled program} {administrative : Core.Context} {flow : Expr}
    (initialValid : RecursiveNamedCatalogMutualMeaning.ContextFor runtime header.solved header.context header.function.evidence)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
      header.output header.reasonAt header.fellThrough header.escaped = .ok header.body)
    (projection : compiled.compatible.checked.catalog.project header.function.resultType = .ok header.output)
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
      header.output header.reasonAt true header.escaped = .ok flow)
    (tree : GenericImperativeMatch.Tree header.layouts header.owner header.active compiled.indexed.ancestry.layout.frame header.globals
      header.onError (.initial compiled.compatible.checked) header.function.source (expressionSyntax header)
      (certificates header)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) header.context
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      (.statements true header.function.body) header.function.resultType header.output flow) :
    Profile (certificates := certificates) (expressionSyntax := expressionSyntax) runtime header administrative := by
  have emitted : header.body = CompatibleStatements.finish header.output flow header.fellThrough header.escaped := by
    unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
    rw [generated] at accepted
    exact Except.ok.inj accepted.symm
  exact ⟨initialValid, accepted, projection, flow, generated, emitted, tree⟩

def body_protocol (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) :=
  CallableIndexedOwnedExpressionHeads.argumentProtocol (headers := headers) owner (owner.key.capturePrefix + 1)

def bridge (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) :=
  CallableIndexedOwnedIndirectCallerProtocol.of_legacy
    (CallableIndexedOwnedCallerProtocol.canonical (headers := headers) owner (owner.key.capturePrefix + 1))

/-- Visited contexts retain the real ledger and independent Source validity. -/
def Validity (runtime : Bool) (header : CallableIndexedOwnedFunctionValues.Header compiled program)
    (context : SourceSemantics.Context) : Prop :=
  RecursiveNamedCatalogMutualMeaning.ContextFor runtime header.solved context header.function.evidence ∧
    Dynamic.SourceRuntimeValid program context header.function.source

section Flows
variable (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) (runtime : Bool)
  {header : CallableIndexedOwnedFunctionValues.Header compiled program} {administrative : Core.Context}
  (profile : Profile (certificates := certificates)
    (expressionSyntax := expressionSyntax) runtime header administrative)

/-- This is a flow obligation at the exact retained profile, before finish. -/
def FlowPreserves (size : Nat) : Prop :=
  RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (body_protocol (headers := headers) owner) (readiness (bridge (headers := headers) owner))
    (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (ProtectedStateImperativeTypedSourceSites.Facts header.function.source (expressionSyntax header))
    functions program header.function.evidence (Validity runtime header)
    (source := header.function.source) (context := header.context) (registry := registry) (faults := faults)
    (frameLayout := compiled.indexed.ancestry.layout.frame) (globals := header.globals)
    (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
    size (scope := header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    true header.function.body header.function.resultType header.output profile.flow

def FlowReflects (size : Nat) : Prop :=
  RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (body_protocol (headers := headers) owner) (readiness (bridge (headers := headers) owner))
    (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (ProtectedStateImperativeTypedSourceSites.Facts header.function.source (expressionSyntax header))
    functions program header.function.evidence (Validity runtime header)
    (source := header.function.source) (context := header.context) (registry := registry) (faults := faults)
    (frameLayout := compiled.indexed.ancestry.layout.frame) (globals := header.globals)
    (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
    size (scope := header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    true header.function.body header.function.resultType header.output profile.flow

end Flows

section Entries
variable (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) (runtime : Bool)
  {header : CallableIndexedOwnedFunctionValues.Header compiled program}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  {arguments : List Dynamic.Value}
  (beforeTyped : Dynamic.HeapWellTyped header.function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)
  (wellFormed : ProgramWellFormed program)

/-- Profiles are requested at an authentic complete parameter entry. -/
def ProfilesFor :=
  ∀ {arguments before initialStore mapping world administrative actualContext actual ξ frameLocation current ghost},
    BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix functions registry header arguments before initialStore
      mapping world administrative actualContext actual ξ frameLocation current ghost →
    Profile (certificates := certificates)
      (expressionSyntax := expressionSyntax) runtime header administrative

private theorem body_facts {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    (syntaxTree : GenericImperativeMatch.Syntax header.function.source (expressionSyntax header)
      header.context (.statements true header.function.body) header.function.resultType)
    (source : SourceReceipt program header.function header.context environment heap) :
    ProtectedStateImperativeTypedSourceSites.Facts header.function.source (expressionSyntax header)
      header.context true header.function.body header.function.resultType := by
  obtain ⟨final, facts, typed, _⟩ := source.bodyTyped
  exact ⟨syntaxTree, { returnType := header.function.resultType }, final, facts, typed⟩

include stable in
private theorem parameter_rows {origin : Word} {index : Int} {metadata : MetadataState}
    {frameLocation : Location} {final : ProtectedStateTransition.Index}
    (physical : frameLocation = owner.key.frameLocation)
    (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (.state index) (.named origin) (some metadata))
    (reached : State headers keys final)
    (parameters : AdministrativePreserved mapping
      (store.set frameLocation (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame (.state index)))
      final.mapping final.store) :
    CallableIndexedOwnedIndirectExpressionHeads.StableRows reached := by
  have actualFrame := Eq.mp (congrArg (fun location => AdministrativePreserved mapping
    (store.set location (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame (.state index)))
    final.mapping final.store) physical) parameters
  exact CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative
    (install caller owner.position (.stable history)) reached
    (CallableIndexedOwnedAdmittedBodyEntries.stable_rows_install caller stable owner.position history) actualFrame

variable (profiles : ProfilesFor (registry := registry) (certificates := certificates)
    (expressionSyntax := expressionSyntax) functions owner runtime (header := header))
  (syntaxTree : GenericImperativeMatch.Syntax header.function.source (expressionSyntax header)
    header.context (.statements true header.function.body) header.function.resultType)

include beforeTyped argumentsTyped stable wellFormed profiles syntaxTree in
/-- The real parameter allocation supplies Source admission. Its original
canonical globals wrap the same reached pool before the strict flow child. -/
theorem source_continuation (budget : Nat)
    (below : Below budget (fun child => ∀ administrative
      (profile : Profile (certificates := certificates)
        (expressionSyntax := expressionSyntax) runtime header administrative),
      FlowPreserves (registry := registry) (faults := faults) (headers := headers) functions owner runtime profile child)) :
    CallableIndexedOwnedInvocationBounds.SourceContinuation
      (functions := functions) (registry := registry) (faults := faults)
      (header := header) (arguments := arguments) owner caller
      (CallableIndexedOwnedInvocationBounds.stableOwnerCondition (headers := headers) (keys := keys)
        (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header) budget := by
  intro origin index metadata administrative actualContext actual ξ frameLocation
    physical _selected history _emitted entry _agreement reached _related _allowed child strict outcome after trace
  let profile := profiles entry
  have source := SourceReceipt.of_named wellFormed header.frame header.extended entry.allocation beforeTyped argumentsTyped
  let initial : (body_protocol (headers := headers) owner).State
      ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩ :=
    ⟨reached, entry.catalog.globals⟩
  have admitted : Admission (bridge (headers := headers) owner) header.context initial :=
    ⟨source.heapTyped, parameter_rows owner caller stable physical history reached entry.frame⟩
  have gate : CallableIndexedOwnedAllocationProducer.StableOwner keys frameLocation (.state index) :=
    ⟨owner.position, .named origin, some metadata, physical.symm, history⟩
  have reference : entry.canonical[
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))).length + 1 + header.globals]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type frameLocation) := by
    simpa only [List.length_map, List.length_reverse] using entry.reference
  have unmapped := Eq.mp (congrArg (fun location => location ∉ entry.mapping) entry.catalog_frame)
    entry.catalog.authority.unmapped
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
      frame, metadata, _exit, post⟩ :=
    CallableIndexedOwnedTypedFunctionFinishBounds.WithReady.preserves_at_emitted_with_source_receipt
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (functions := functions) (program := program) (tree := profile.tree)
      (projection := profile.projection) (unique := header.unique)
      (body_protocol (headers := headers) owner) (readiness (bridge (headers := headers) owner))
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (ProtectedStateImperativeTypedSourceSites.Facts header.function.source (expressionSyntax header))
      profile.emitted (Validity runtime header) child (below child strict administrative profile)
      ⟨profile.initialValid, source.runtime⟩ (body_facts syntaxTree source)
      entry.environments entry.heaps entry.locals entry.lookups entry.actualTyped
      reference entry.state.read unmapped initial gate admitted source wellFormed trace
  obtain ⟨returned, related⟩ := post.forget
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
    frame, metadata, returned.val, related⟩

include beforeTyped argumentsTyped stable wellFormed profiles syntaxTree in
/-- The independent measured native body consumes strict flow grades only.
The returned Source grade and exact actual parameter pool remain unchanged. -/
theorem native_continuation (budget : Nat)
    (below : Below budget (fun child => ∀ administrative
      (profile : Profile (certificates := certificates)
        (expressionSyntax := expressionSyntax) runtime header administrative),
      FlowReflects (registry := registry) (faults := faults) (headers := headers) functions owner runtime profile child)) :
    CallableIndexedOwnedInvocationBounds.NativeContinuation
      (functions := functions) (registry := registry) (faults := faults)
      (header := header) (arguments := arguments) owner caller
      (CallableIndexedOwnedInvocationBounds.stableOwnerCondition (headers := headers) (keys := keys)
        (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header) budget := by
  intro origin index metadata administrative actualContext actual ξ frameLocation prefixSize bodyStore value finalStore
    physical _selected history _emitted _prefix _prefixWithin _restored entry reached _related _allowed
    child strict bodyValue bodyStore completed
  let profile := profiles entry
  have source := SourceReceipt.of_named wellFormed header.frame header.extended entry.allocation beforeTyped argumentsTyped
  let initial : (body_protocol (headers := headers) owner).State
      ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩ :=
    ⟨reached, entry.catalog.globals⟩
  have admitted : Admission (bridge (headers := headers) owner) header.context initial :=
    ⟨source.heapTyped, parameter_rows owner caller stable physical history reached entry.frame⟩
  have gate : CallableIndexedOwnedAllocationProducer.StableOwner keys frameLocation (.state index) :=
    ⟨owner.position, .named origin, some metadata, physical.symm, history⟩
  have reference : entry.canonical[
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))).length + 1 + header.globals]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type frameLocation) := by
    simpa only [List.length_map, List.length_reverse] using entry.reference
  have unmapped := Eq.mp (congrArg (fun location => location ∉ entry.mapping) entry.catalog_frame)
    entry.catalog.authority.unmapped
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
      frame, metadata, _exit, post⟩ :=
    CallableIndexedOwnedTypedFunctionFinishBounds.WithReady.reflects_at_emitted_with_source_receipt
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (functions := functions) (program := program) (tree := profile.tree)
      (projection := profile.projection) (unique := header.unique)
      (body_protocol (headers := headers) owner) (readiness (bridge (headers := headers) owner))
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (ProtectedStateImperativeTypedSourceSites.Facts header.function.source (expressionSyntax header))
      profile.emitted (Validity runtime header) budget child (Nat.le_of_lt strict)
      (fun grade smaller => below grade smaller administrative profile)
      ⟨profile.initialValid, source.runtime⟩ (body_facts syntaxTree source)
      entry.environments entry.heaps entry.locals entry.lookups entry.actualTyped
      reference entry.state.read unmapped initial gate admitted source wellFormed completed
  obtain ⟨returned, related⟩ := post.forget
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
    frame, metadata, returned.val, related⟩

end Entries
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedDirectTypedNamedBodyContinuations
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPrimitiveNamedBodyFaultBounds
/-! Actual singleton tail and return bodies obtain their primitive path from
the existing admitted builtin producer. Finite returnValue and finish steps
retain the actual child token and body store; both execution grades stay real. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPrimitiveNamedBodyFaultBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission CallableIndexedOwnedIndirectExpressionHeads
open CallableIndexedOwnedAdmittedBodyEntries (SourceReceipt)
open CallableIndexedOwnedInvocationBounds NamedInvocationFaultPostContracts
open ReachedNamedPrimitiveBodyFaultPaths

private def poolBridge {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)} :
    CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) (protocol headers keys) :=
  CallableIndexedOwnedIndirectCallerProtocol.of_legacy CallableIndexedOwnedCallerProtocol.base

private theorem emitted_rename {values : SourceCoreCompatibleValues.Context} {function : Dynamic.Closure}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {statement : StatementId}
    {node : StatementNode} {expression : ExpressionId} {expressionNode : ExpressionNode} {fuel : Nat}
    {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    {body : Expr} {fellThrough escaped : Word}
    (singleton : SingletonAt values function context scope statement node expression expressionNode fuel solved reasonAt
      lowered body fellThrough escaped) (ξ : Renaming) :
    body.rename ξ = CompatibleStatements.finish lowered.type
      (LocalLoop.returnValue lowered.type (lowered.expression.rename ξ)) fellThrough escaped := by
  rw [singleton.emitted, ImperativeFunctionFinish.rename, LoopRenaming.returnValue]

private def returnedControl : Dynamic.ExpressionOutcome → Dynamic.ControlOutcome
  | .value value => .returned value
  | .fault reason => .fault reason

private theorem fault_finished {actual : Environment} {initialStore bodyStore : Store} {type : Ty}
    {expression : Expr} {token fellThrough escaped : Word}
    (child : Evaluates actual initialStore expression (.inLeft type (.word token)) bodyStore) :
    Evaluates actual initialStore (CompatibleStatements.finish type (LocalLoop.returnValue type expression) fellThrough escaped)
      (.inLeft type (.word token)) bodyStore :=
  LocalControl.finish_failure _ (LocalLoop.toControl_failure _ escaped (LocalLoop.returnValue_failure _ child))

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {header : CallableIndexedOwnedFunctionValues.Header compiled program}
  {locations : CallableIndexedOwnedFunctionValues.Header compiled program → Location} {capturePrefix : Nat}
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
  (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
    administrative actualContext actual ξ frameLocation current ghost)
  (reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
    entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
  {statement : StatementId} {node : StatementNode} {expression : ExpressionId} {expressionNode : ExpressionNode}
  {fuel : Nat} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {lowered : SourceCoreBasic.LoweredExpr} {fellThrough escaped : Word}
  (singleton : SingletonAt (.initial compiled.compatible.checked) header.function header.context
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) statement node expression expressionNode
    fuel solved reasonAt lowered header.body fellThrough escaped)
  (nativeType : lowered.type = header.output)
  (source : SourceReceipt program header.function header.context entry.environment entry.heap)
  (rows : StableRows reached)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (valid : CompatibleExpressionLiterals.ContextValid solved header.context header.function.evidence)
  (reads : ReachedLoweredReadOutcomePorts.ReadPolicies fuel (.initial compiled.compatible.checked)
    header.function.source header.context reasonAt faults)
  (missing : IndexFaultPostContracts.MissingPolicies (.initial compiled.compatible.checked)
    header.function.source functions registry program header.context header.function.evidence reasonAt faults)
  (unique : NodeOccurrencesUnique header.function.source) (wellFormed : ProgramWellFormed program)

include singleton nativeType source rows extension faithful observations functionTypes valid reads missing unique wellFormed in
/-- The actual sized Source singleton selects its strict child, whose builtin
producer returns the same full tuple and causal path at the body store. -/
theorem source_body_with_post [FunctionCalls.FaultTokens faults] (size : Nat) :
    SourceBodyAtWithPost (model_bodyPost compiled.compatible.checked functions registry)
      (faults := faults) entry reached size := by
  intro outcome after bodyTrace
  obtain ⟨finalContext, control, flowTrace, exit⟩ := RecursiveNamedFunctionFinishBounds.trace_flow bodyTrace
  rw [singleton.statements] at flowTrace
  have child : finalContext = header.context ∧ ∃ childSize expressionOutcome,
      RecursiveNamedCallBounds.ExpressionOutcome program childSize header.context header.function.evidence
        header.function.source entry.environment entry.heap expression expressionOutcome after ∧
      control = (returnedControl expressionOutcome) ∧
      childSize < size := by
    rcases singleton.form with tail | returning
    · exact RecursiveNamedStatementSourceBounds.tail_inv unique (lookupStatement?_sound singleton.found) tail flowTrace
    · exact RecursiveNamedLexicalTreeSourceBounds.returning unique singleton.found returning flowTrace
  obtain ⟨rfl, childSize, expressionOutcome, childTrace, rfl, _smaller⟩ := child
  have admitted : Admission (poolBridge (headers := headers) (keys := keys)) header.context reached :=
    ⟨source.heapTyped, rows⟩
  obtain ⟨value, bodyStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, finalState, related, _postAdmission, retained⟩ :=
    CallableIndexedOwnedAdmittedBuiltinFaultBounds.preserves (poolBridge (headers := headers) (keys := keys))
      functions header.function.evidence (administrativeTransport headers keys) extension faithful observations functionTypes
      valid reads missing unique wellFormed source.runtime source.covers singleton.tree singleton.expressionFound singleton.expressionTyped
      entry.environments entry.heaps source.locals entry.lookups entry.actualTyped reached admitted childTrace
  have rawUnit : ∀ next,
      (returnedControl expressionOutcome) =
        Dynamic.ControlOutcome.fallthrough next → header.function.resultType = .unit := by
    cases expressionOutcome <;> intro next same <;> cases same
  have transfers : ImperativeFunctionFinish.TransferFaults faults escaped
      (returnedControl expressionOutcome) := by
    cases expressionOutcome <;> constructor <;> intro next same <;> cases same
  obtain ⟨flowValue, flowEvaluation, flowRelated⟩ : ∃ flowValue,
      Evaluates entry.actualBody entry.store (LocalLoop.returnValue lowered.type (lowered.expression.rename entry.embedding)) flowValue bodyStore ∧
      TypedLexicalWhile.FlowRep (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (registry := registry)
        functions finalMap finalWorld faults header.function.resultType lowered.type
        (returnedControl expressionOutcome) flowValue := by
    cases represented with
    | value payload => exact ⟨_, LocalLoop.returnValue_success _ evaluated, .returned (singleton.resultType ▸ payload)⟩
    | fault matched => exact ⟨_, LocalLoop.returnValue_failure _ evaluated, .fault matched⟩
  obtain ⟨result, completed, finished⟩ := ImperativeFunctionFinish.from_flow_with_transfers
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (mapping := finalMap) (world := finalWorld) (faults := faults) (outcome := returnedControl expressionOutcome)
    functions rawUnit singleton.projection fellThrough escaped transfers flowRelated flowEvaluation
  have bodyEvaluation : Evaluates entry.actualBody entry.store (header.body.rename entry.embedding) result bodyStore := by
    rw [emitted_rename singleton]
    exact completed
  refine ⟨result, bodyStore, finalMap, finalWorld, bodyEvaluation, ?_, finalHeaps, maps, worlds, frame,
    metadata, ⟨finalState, related⟩, ?_⟩
  · simpa only [nativeType, SourceCoreCompatibleValues.Context.initial] using ImperativeFunctionFinish.result finished exit
  · cases expressionOutcome with
    | value sourceValue => cases exit; trivial
    | fault reason =>
      cases exit
      cases childTrace with | fault failed =>
        obtain ⟨token, sameValue, origin⟩ := CallableIndexedOwnedAdmittedBuiltinFaultBounds.NativeFaultAt.at_fault retained evaluated
        have faultChild : Evaluates entry.actualBody entry.store (lowered.expression.rename entry.embedding)
            (.inLeft lowered.type (.word token)) bodyStore := sameValue ▸ evaluated
        have faultBody : Evaluates entry.actualBody entry.store (header.body.rename entry.embedding)
            (.inLeft lowered.type (.word token)) bodyStore := by
          rw [emitted_rename singleton]
          exact fault_finished faultChild
        refine ⟨token, ?_, model_bodyPost.of_child singleton failed.sound origin faultChild faultBody⟩
        simpa only [nativeType] using (evaluation_deterministic bodyEvaluation faultBody).1

include singleton nativeType source rows extension faithful observations functionTypes valid reads missing unique wellFormed in
/-- The actual finish and returnValue children supply strict native bounds.
The singleton Source grade is constructed independently from its real child. -/
theorem native_body_with_post [FunctionCalls.FaultTokens faults] (size : Nat) :
    NativeBodyAtWithPost (model_bodyPost compiled.compatible.checked functions registry)
      (faults := faults) entry reached size := by
  intro value finalStore bodyCompletion
  have nativeFinish : EvaluationSize size entry.actualBody entry.store
      (CompatibleStatements.finish lowered.type
        (LocalLoop.returnValue lowered.type (lowered.expression.rename entry.embedding)) fellThrough escaped) value finalStore := by
    rw [← emitted_rename singleton]
    exact bodyCompletion
  obtain ⟨flowSize, flowValue, flowStore, _flowSmaller, flowCompletion⟩ := RecursiveNamedCallBounds.finish_flow nativeFinish
  obtain ⟨expressionSize, expressionStore, expressionValue, _expressionSmaller, expressionCompletion⟩ :=
    flowCompletion.bind_computation
  have admitted : Admission (poolBridge (headers := headers) (keys := keys)) header.context reached :=
    ⟨source.heapTyped, rows⟩
  obtain ⟨sourceSize, expressionOutcome, after, finalMap, finalWorld, childTrace, represented, finalHeaps,
      maps, worlds, frame, metadata, finalState, related, _postAdmission, retained⟩ :=
    CallableIndexedOwnedAdmittedBuiltinFaultBounds.reflects (poolBridge (headers := headers) (keys := keys))
      functions header.function.evidence (administrativeTransport headers keys) extension faithful observations functionTypes
      valid reads missing unique wellFormed source.runtime source.covers singleton.tree singleton.expressionFound singleton.expressionTyped
      entry.environments entry.heaps source.locals entry.lookups entry.actualTyped reached admitted expressionCompletion
  have rawUnit : ∀ next,
      (returnedControl expressionOutcome) =
        Dynamic.ControlOutcome.fallthrough next → header.function.resultType = .unit := by
    cases expressionOutcome <;> intro next same <;> cases same
  have transfers : ImperativeFunctionFinish.TransferFaults faults escaped
      (returnedControl expressionOutcome) := by
    cases expressionOutcome <;> constructor <;> intro next same <;> cases same
  obtain ⟨returnValue, returnEvaluation, returnRelated⟩ : ∃ returnValue,
      Evaluates entry.actualBody entry.store (LocalLoop.returnValue lowered.type (lowered.expression.rename entry.embedding)) returnValue expressionStore ∧
      TypedLexicalWhile.FlowRep (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (registry := registry)
        functions finalMap finalWorld faults header.function.resultType lowered.type
        (returnedControl expressionOutcome) returnValue := by
    cases represented with
    | value payload => exact ⟨_, LocalLoop.returnValue_success _ expressionCompletion.sound, .returned (singleton.resultType ▸ payload)⟩
    | fault matched => exact ⟨_, LocalLoop.returnValue_failure _ expressionCompletion.sound, .fault matched⟩
  obtain ⟨result, completed, finished⟩ := ImperativeFunctionFinish.from_flow_with_transfers
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (mapping := finalMap) (world := finalWorld) (faults := faults) (outcome := returnedControl expressionOutcome)
    functions rawUnit singleton.projection fellThrough escaped transfers returnRelated returnEvaluation
  have bodyEvaluation : Evaluates entry.actualBody entry.store (header.body.rename entry.embedding) result expressionStore := by
    rw [emitted_rename singleton]
    exact completed
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic bodyCompletion.sound bodyEvaluation
  cases expressionOutcome with
  | value sourceValue =>
    cases childTrace with | value childEvaluated =>
      obtain ⟨bodySize, bodyTrace⟩ : ∃ bodySize,
          RecursiveNamedCallBounds.BodyTrace program bodySize header.function header.context
            entry.environment entry.heap (.value sourceValue) after := by
        rcases singleton.form with tail | returning
        · refine ⟨SourceExecutionSize.stepSize [sourceSize], .returned (finalContext := header.context) ?_⟩
          rw [singleton.statements]
          exact .tailExpression (lookupStatement?_sound singleton.found) tail childEvaluated
        · refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [sourceSize]], .returned (finalContext := header.context) ?_⟩
          rw [singleton.statements]
          exact .singleton (lookupStatement?_sound singleton.found) (by intro expression; simp [returning])
            (.returnValue (lookupStatement?_sound singleton.found) returning childEvaluated)
      refine ⟨bodySize, .value sourceValue, after, finalMap, finalWorld, bodyTrace, ?_, finalHeaps,
        maps, worlds, frame, metadata, ⟨finalState, related⟩, trivial⟩
      simpa only [nativeType, SourceCoreCompatibleValues.Context.initial] using ImperativeFunctionFinish.result finished (CompatibleNamedBody.Exit.returned sourceValue)
  | fault reason =>
    cases childTrace with | fault childFailed =>
      obtain ⟨bodySize, bodyTrace⟩ : ∃ bodySize,
          RecursiveNamedCallBounds.BodyTrace program bodySize header.function header.context
            entry.environment entry.heap (.fault reason) after := by
        rcases singleton.form with tail | returning
        · refine ⟨SourceExecutionSize.stepSize [sourceSize], .fault (finalContext := header.context) ?_⟩
          rw [singleton.statements]
          exact .tailExpression (lookupStatement?_sound singleton.found) tail childFailed
        · refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [sourceSize]], .fault (finalContext := header.context) ?_⟩
          rw [singleton.statements]
          exact .singleton (.returnValue (lookupStatement?_sound singleton.found) returning childFailed)
      refine ⟨bodySize, .fault reason, after, finalMap, finalWorld, bodyTrace, ?_, finalHeaps,
        maps, worlds, frame, metadata, ⟨finalState, related⟩, ?_⟩
      · simpa only [nativeType, SourceCoreCompatibleValues.Context.initial] using ImperativeFunctionFinish.result finished (CompatibleNamedBody.Exit.fault reason)
      · obtain ⟨token, sameValue, origin⟩ := CallableIndexedOwnedAdmittedBuiltinFaultBounds.NativeFaultAt.at_fault
          retained expressionCompletion.sound
        have faultChild : Evaluates entry.actualBody entry.store (lowered.expression.rename entry.embedding)
            (.inLeft lowered.type (.word token)) finalStore := sameValue ▸ expressionCompletion.sound
        have faultBody : Evaluates entry.actualBody entry.store (header.body.rename entry.embedding)
            (.inLeft lowered.type (.word token)) finalStore := by
          rw [emitted_rename singleton]
          exact fault_finished faultChild
        refine ⟨token, ?_, model_bodyPost.of_child singleton childFailed.sound origin faultChild faultBody⟩
        simpa only [nativeType] using (evaluation_deterministic bodyEvaluation faultBody).1

include singleton nativeType source rows extension faithful observations functionTypes valid reads missing unique wellFormed in
/-- Every strict Source member is produced by the same concrete singleton theorem. -/
theorem source_below [FunctionCalls.FaultTokens faults] (budget : Nat) :
    RecursiveNamedBoundedContracts.Below budget
      (SourceBodyAtWithPost (model_bodyPost compiled.compatible.checked functions registry)
        (faults := faults) entry reached) := by
  intro child _strict
  exact source_body_with_post functions entry reached singleton nativeType source rows extension faithful
    observations functionTypes valid reads missing unique wellFormed child

include singleton nativeType source rows extension faithful observations functionTypes valid reads missing unique wellFormed in
/-- Native strict membership uses its actual measured body completion. -/
theorem native_below [FunctionCalls.FaultTokens faults] (budget : Nat) :
    RecursiveNamedBoundedContracts.Below budget
      (NativeBodyAtWithPost (model_bodyPost compiled.compatible.checked functions registry)
        (faults := faults) entry reached) := by
  intro child _strict
  exact native_body_with_post functions entry reached singleton nativeType source rows extension faithful
    observations functionTypes valid reads missing unique wellFormed child

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPrimitiveNamedBodyFaultBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedExpressionHeads
/-! Original view and nested literal receipts consume the actual stronger
formation protocol. Ordered argument children carry the same packet into the
real named call; genuine literal formation retains the reached own history. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedExpressionHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues SourceCoreCallableIndexedFrames
open CallableIndexedOwnedFunctionState CallableIndexedOwnedExpressionHeads
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open CallableIndexedOwnedNestedCanonicalState
open CallableIndexedOwnedNestedCallerProtocol (carrier)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate} {compilation : SourceCoreFunctions.Context}

theorem view_preserves_at_with
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (caller : CallableIndexedOwnedFunctionValues.Header compiled program)
    (prefixMatches : compilation.administrativePrefix = 1)
    (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
    (conditions : ∀ header, BodyCondition (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header)
    (authorized : ∀ header, header ∈ headers → CallableIndexedOwnedInvocationBounds.BodyAuthorizationAt (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header owner.key.frameLocation (conditions header))
    (budget size : Nat) (within : size ≤ budget)
    (idsUnique : RequirementIdsUnique context) (unique : NodeOccurrencesUnique source)
    (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
    (argumentMeaning : Below budget (ProtectedStateTransition.PreservesAt (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source certificate faults))
    (bodyMeaning : ∀ header, header ∈ headers → Below budget (RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      functions registry header faults (protocol headers keys) (conditions header))) :
    ProtectedStateTransition.PreservesAt (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) program context evidence source
      (CallableLambdaViewNamedRuntimeCertificates.Head (prepared := compiled.indexed.ancestry)
        (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers compilation source context evidence certificate) faults size := by
  have bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
      (fun index => Globals (headers := headers) owner compilation.administrativePrefix index.scope index.canonical)
      (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller) := by
    simpa only [prefixMatches] using carrier (headers := headers) owner caller
  intro scope id lowered head
  cases head with
  | authenticated receipt =>
    exact CallableIndexedOwnedExpressionHeads.preserves_at_with_caller functions owner sameLayouts conditions authorized bridge
      budget size within idsUnique unique owners argumentMeaning bodyMeaning receipt
  | ordinary receipt =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees typed initial trace
    have same := Option.some.inj (receipt.metadata.found.symm.trans found)
    subst root
    have independent := RecursiveNamedArgumentTraceBounds.source_inv receipt.metadata receipt.form receipt.calleeFound
      receipt.predicates receipt.evidenceEmpty unique trace
    obtain ⟨emitted, packed, _, _⟩ := receipt.emission.equation
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, preserved, heapMetadata, transition⟩ :=
      call_preserves_bounded_with_caller functions receipt.sequence receipt.nativeTypes packed owner
        (sameLayouts receipt.header receipt.member) (conditions receipt.header) (authorized receipt.header receipt.member)
        budget bridge argumentMeaning (bodyMeaning receipt.header receipt.member) owners receipt.member
        initial environments heaps locals agrees typed independent within
    refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps,
      maps, worlds, preserved, heapMetadata, transition⟩
    · change Evaluates actual store (lowered.expression.rename ξ) value finalStore
      rw [emitted, NamedCalls.Arguments.call_rename, receipt.selectedSlot]
      exact evaluated
    · simpa only [receipt.sourceType, receipt.nativeType] using represented

theorem view_reflects_at_with
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (caller : CallableIndexedOwnedFunctionValues.Header compiled program)
    (prefixMatches : compilation.administrativePrefix = 1)
    (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
    (conditions : ∀ header, BodyCondition (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header)
    (authorized : ∀ header, header ∈ headers → CallableIndexedOwnedInvocationBounds.BodyAuthorizationAt (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header owner.key.frameLocation (conditions header))
    (budget size : Nat) (within : size ≤ budget)
    (argumentMeaning : Below budget (ProtectedStateTransition.ReflectsAt (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source certificate faults))
    (bodyMeaning : ∀ header, header ∈ headers → Below budget (RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      functions registry header faults (protocol headers keys) (conditions header))) :
    ProtectedStateTransition.ReflectsAt (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) program context evidence source
      (CallableLambdaViewNamedRuntimeCertificates.Head (prepared := compiled.indexed.ancestry)
        (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers compilation source context evidence certificate) faults size := by
  have bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
      (fun index => Globals (headers := headers) owner compilation.administrativePrefix index.scope index.canonical)
      (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller) := by
    simpa only [prefixMatches] using carrier (headers := headers) owner caller
  intro scope id lowered head
  cases head with
  | authenticated receipt =>
    exact CallableIndexedOwnedExpressionHeads.reflects_at_with_caller functions owner sameLayouts conditions authorized bridge
      budget size within argumentMeaning bodyMeaning receipt
  | ordinary receipt =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees typed initial evaluated
    have same := Option.some.inj (receipt.metadata.found.symm.trans found)
    subst root
    obtain ⟨emitted, packed, _, _⟩ := receipt.emission.equation
    change EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore at evaluated
    rw [emitted, NamedCalls.Arguments.call_rename, receipt.selectedSlot] at evaluated
    obtain ⟨traceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, preserved, heapMetadata, transition⟩ :=
      call_reflects_bounded_with_caller functions receipt.sequence receipt.nativeTypes packed owner
        (sameLayouts receipt.header receipt.member) (conditions receipt.header) (authorized receipt.header receipt.member)
        budget bridge argumentMeaning (bodyMeaning receipt.header receipt.member) receipt.member
        initial environments heaps locals agrees typed evaluated within
    obtain ⟨sourceSize, independent⟩ := RecursiveNamedArgumentTraceBounds.source_intro receipt.metadata receipt.form receipt.calleeFound
      receipt.calleeForm receipt.calleeRequirements receipt.calleeCoercions receipt.valid receipt.predicates receipt.evidenceEmpty trace
    exact ⟨sourceSize, outcome, after, finalMap, finalWorld, independent,
      by simpa only [receipt.sourceType, receipt.nativeType] using represented,
      finalHeaps, maps, worlds, preserved, heapMetadata, transition⟩

section Nested
open CallableIndexedLambdaNestedRuntimeBodyMeaning
variable (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : CallableIndexedOwnedFunctionValues.Header compiled program)
  (prefixZero : owner.key.capturePrefix = 0)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (globals : caller.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (sameSource : source = CallableIndexedNamedGeneration.source caller.named)
  {rank : Nat}
local notation "F" => CallableIndexedOwnedFunctionValues.model headers keys registry faults profile
local notation "P" => CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller
local notation "Calls" => CallableIndexedLambdaNestedRuntimeCertificates.Head
  (LowerSupport (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) headers caller registry faults rank)
  rank caller headers (CallableIndexedNamedGeneration.context compiled.indexed caller.named) source context evidence

include prefixZero complete globals slots sameSource in
/-- The original two nested head constructors supply either the actual named
view call or genuine strong lambda formation. Their children keep this input
protocol, so original formation observations remain available after calls. -/
theorem nested_preserves_at_with
    (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
    (conditions : ∀ header, BodyCondition (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) F registry header)
    (authorized : ∀ header, header ∈ headers → CallableIndexedOwnedInvocationBounds.BodyAuthorizationAt (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) F registry header owner.key.frameLocation (conditions header))
    (budget size : Nat) (within : size ≤ budget)
    (idsUnique : RequirementIdsUnique context) (unique : NodeOccurrencesUnique source)
    (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
    (argumentMeaning : Below budget (ProtectedStateTransition.PreservesAt P
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry F)
      program context evidence source certificate faults))
    (bodyMeaning : ∀ header, header ∈ headers → Below budget (RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      F registry header faults (CallableIndexedOwnedFunctionState.protocol headers keys) (conditions header))) :
    ProtectedStateTransition.PreservesAt P
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry F)
      program context evidence source (Calls certificate) faults size := by
  intro scope id lowered head
  cases head with
  | existing receipt =>
    exact view_preserves_at_with F owner caller rfl sameLayouts conditions authorized
      budget size within idsUnique unique owners argumentMeaning bodyMeaning receipt
  | lambda leaf =>
    exact formation_preserves_at owner caller prefixZero profile complete globals slots sameSource size unique ⟨leaf⟩

include prefixZero complete globals slots sameSource in
/-- Native completion selects the same authentic head receipt and actual
reached protocol witness; its reconstructed Source grade stays independent. -/
theorem nested_reflects_at_with
    (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
    (conditions : ∀ header, BodyCondition (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) F registry header)
    (authorized : ∀ header, header ∈ headers → CallableIndexedOwnedInvocationBounds.BodyAuthorizationAt (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) F registry header owner.key.frameLocation (conditions header))
    (budget size : Nat) (within : size ≤ budget)
    (argumentMeaning : Below budget (ProtectedStateTransition.ReflectsAt P
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry F)
      program context evidence source certificate faults))
    (bodyMeaning : ∀ header, header ∈ headers → Below budget (RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      F registry header faults (CallableIndexedOwnedFunctionState.protocol headers keys) (conditions header))) :
    ProtectedStateTransition.ReflectsAt P
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry F)
      program context evidence source (Calls certificate) faults size := by
  intro scope id lowered head
  cases head with
  | existing receipt =>
    exact view_reflects_at_with F owner caller rfl sameLayouts conditions authorized
      budget size within argumentMeaning bodyMeaning receipt
  | lambda leaf =>
    exact formation_reflects_at owner caller prefixZero profile complete globals slots sameSource size ⟨leaf⟩

end Nested

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedExpressionHeads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedExpressionTreeBounds
/-! The same static expression Tree fold carries the actual nested formation
packet through every compositional child. Genuine original View calls consume
ordered actual argument states; literal lambdas use full reached owner receipts. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedExpressionTreeBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds RecursiveNamedBoundedContracts
open CallableIndexedLambdaNestedRuntimeBodyMeaning
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {source : TypedSource} {context : SourceSemantics.Context}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : CallableIndexedOwnedFunctionValues.Header compiled program)
  (prefixZero : owner.key.capturePrefix = 0)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (globals : caller.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (sameSource : source = CallableIndexedNamedGeneration.source caller.named)
  {rank : Nat}
variable
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) identities)
  (functionTypes : FunctionRuntimeViews (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
  (evidence : Dynamic.EvidenceEnvironment)
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  {literals : GenericExpressionMeaning.Certificate}
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

variable
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
  (conditions : ∀ header, BodyCondition (prepared := compiled.indexed.ancestry)
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) registry header)
  (authorized : ∀ header, header ∈ headers → CallableIndexedOwnedInvocationBounds.BodyAuthorizationAt
    (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) registry header owner.key.frameLocation (conditions header))

include prefixZero complete globals slots sameSource extension faithful functionLeaves functionTypes unique owners uninitialized missing sameLayouts authorized in
/-- The unchanged static Tree fold closes every expression child. Actual call
bodies remain only at genuine strict Source child grades. -/
theorem preserves_at_with_literals [FunctionCalls.FaultTokens faults]
    (idsUnique : RequirementIdsUnique context)
    (literalMeaning : GenericExpressionMeaning.Preserves
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source literals faults)
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) registry header faults (CallableIndexedOwnedFunctionState.protocol headers keys) (conditions header))) :
    ProtectedStateTransition.PreservesAt (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals
        (calls := (CallableIndexedLambdaNestedRuntimeCertificates.Head (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) (program := program)
          (LowerSupport (indexed := compiled.indexed) (values := .initial compiled.compatible.checked) headers caller registry faults rank)
          rank caller headers (CallableIndexedNamedGeneration.context compiled.indexed caller.named) source context evidence))
        (fuel := fuel) (values := .initial compiled.compatible.checked) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults size := by
  refine RecursiveNamedExpressionTreeBounds.preserves_at_with_state
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (program := program) (registry := registry) (source := source) (context := context)
    (reasonAt := reasonAt) (solved := solved) (fuel := fuel) (literals := literals) (faults := faults) (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) evidence
    (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller)
    ((CallableIndexedLambdaNestedRuntimeCertificates.Head (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) (program := program)
          (LowerSupport (indexed := compiled.indexed) (values := .initial compiled.compatible.checked) headers caller registry faults rank)
          rank caller headers (CallableIndexedNamedGeneration.context compiled.indexed caller.named) source context evidence)) budget size within ?_ ?_
  · intro child childWithin
    exact ProtectedStateTransition.PreservesAt.of_administrative _ _ _ _ _ _ _ _
      (CallableIndexedOwnedNestedCanonicalState.administrativeTransport owner caller)
      (RecursiveNamedBoundedContracts.preserves_at_of_unbounded
        (ProtectedExpressionMeaning.preserves_of_typed _
          (CompatibleExpressionBuiltins.preserves_with_literals (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) extension faithful functionLeaves functionTypes
            program evidence unique uninitialized missing literalMeaning)) child)
  · intro childCertificate child childWithin children
    exact ProtectedStateExpressionCallsHeads.head_preserves_at_with_calls (certificate := childCertificate)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) extension faithful functionLeaves functionTypes evidence unique missing
      (CallableIndexedLambdaNestedRuntimeCertificates.Head (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) (program := program)
          (LowerSupport (indexed := compiled.indexed) (values := .initial compiled.compatible.checked) headers caller registry faults rank)
          rank caller headers (CallableIndexedNamedGeneration.context compiled.indexed caller.named) source context evidence) (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller) (CallableIndexedOwnedNestedCanonicalState.administrativeTransport owner caller)
      budget child childWithin children
      (CallableIndexedOwnedNestedExpressionHeads.nested_preserves_at_with (certificate := childCertificate)
        owner caller prefixZero profile complete globals slots sameSource
        sameLayouts conditions authorized budget child childWithin idsUnique unique owners
        (fun smaller smallerWithin => children smaller (Nat.le_of_lt smallerWithin)) bodies)

include prefixZero complete globals slots sameSource extension faithful functionLeaves functionTypes uninitialized missing sameLayouts authorized in
/-- Core children and named hook bodies supply their independent strict grades;
the existing fold returns the separately measured Source trace and real pool. -/
theorem reflects_at_with_literals [FunctionCalls.FaultTokens faults]
    (literalMeaning : GenericExpressionMeaning.Reflects
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source literals faults)
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) registry header faults (CallableIndexedOwnedFunctionState.protocol headers keys) (conditions header))) :
    ProtectedStateTransition.ReflectsAt (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals
        (calls := (CallableIndexedLambdaNestedRuntimeCertificates.Head (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) (program := program)
          (LowerSupport (indexed := compiled.indexed) (values := .initial compiled.compatible.checked) headers caller registry faults rank)
          rank caller headers (CallableIndexedNamedGeneration.context compiled.indexed caller.named) source context evidence))
        (fuel := fuel) (values := .initial compiled.compatible.checked) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults size := by
  refine RecursiveNamedExpressionTreeBounds.reflects_at_with_state
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (program := program) (registry := registry) (source := source) (context := context)
    (reasonAt := reasonAt) (solved := solved) (fuel := fuel) (literals := literals) (faults := faults) (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) evidence
    (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller)
    ((CallableIndexedLambdaNestedRuntimeCertificates.Head (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) (program := program)
          (LowerSupport (indexed := compiled.indexed) (values := .initial compiled.compatible.checked) headers caller registry faults rank)
          rank caller headers (CallableIndexedNamedGeneration.context compiled.indexed caller.named) source context evidence)) budget size within ?_ ?_
  · intro child childWithin
    exact ProtectedStateTransition.ReflectsAt.of_administrative _ _ _ _ _ _ _ _
      (CallableIndexedOwnedNestedCanonicalState.administrativeTransport owner caller)
      (RecursiveNamedBoundedContracts.reflects_at_of_unbounded
        (ProtectedExpressionMeaning.reflects_of_typed _
          (CompatibleExpressionBuiltins.reflects_with_literals (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) extension faithful functionLeaves functionTypes
            program evidence uninitialized missing literalMeaning)) child)
  · intro childCertificate child childWithin children
    exact ProtectedStateExpressionCallsHeads.head_reflects_at_with_calls (certificate := childCertificate)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) extension faithful functionLeaves functionTypes evidence missing
      (CallableIndexedLambdaNestedRuntimeCertificates.Head (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) (program := program)
          (LowerSupport (indexed := compiled.indexed) (values := .initial compiled.compatible.checked) headers caller registry faults rank)
          rank caller headers (CallableIndexedNamedGeneration.context compiled.indexed caller.named) source context evidence) (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller) (CallableIndexedOwnedNestedCanonicalState.administrativeTransport owner caller)
      budget child childWithin children
      (CallableIndexedOwnedNestedExpressionHeads.nested_reflects_at_with (certificate := childCertificate)
        owner caller prefixZero profile complete globals slots sameSource
        sameLayouts conditions authorized budget child childWithin
        (fun smaller smallerWithin => children smaller (Nat.le_of_lt smallerWithin)) bodies)

include prefixZero complete globals slots sameSource extension faithful functionLeaves functionTypes valid unique owners uninitialized missing sameLayouts authorized in
/-- The original compiler Tree supplies its complete literal receipts. -/
theorem preserves_at [FunctionCalls.FaultTokens faults]
    (idsUnique : RequirementIdsUnique context)
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) registry header faults (CallableIndexedOwnedFunctionState.protocol headers keys) (conditions header))) :
    ProtectedStateTransition.PreservesAt (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source
      (CompatibleExpressionCalls.Tree
        ((CallableIndexedLambdaNestedRuntimeCertificates.Head (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) (program := program)
          (LowerSupport (indexed := compiled.indexed) (values := .initial compiled.compatible.checked) headers caller registry faults rank)
          rank caller headers (CallableIndexedNamedGeneration.context compiled.indexed caller.named) source context evidence))
        fuel (.initial compiled.compatible.checked) source context solved reasonAt) faults size := by
  intro scope id lowered tree
  exact preserves_at_with_literals owner caller prefixZero profile complete globals slots sameSource extension faithful functionLeaves functionTypes evidence unique owners uninitialized missing
    sameLayouts conditions authorized idsUnique
    (CompatibleExpressionLiterals.preserves (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) program context evidence valid unique faults) budget size within bodies
    ⟨tree, tree.literalSites⟩

include prefixZero complete globals slots sameSource extension faithful functionLeaves functionTypes valid uninitialized missing sameLayouts authorized in
/-- The original compiler Tree supplies its complete literal receipts. -/
theorem reflects_at [FunctionCalls.FaultTokens faults]
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) registry header faults (CallableIndexedOwnedFunctionState.protocol headers keys) (conditions header))) :
    ProtectedStateTransition.ReflectsAt (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source
      (CompatibleExpressionCalls.Tree
        ((CallableIndexedLambdaNestedRuntimeCertificates.Head (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) (program := program)
          (LowerSupport (indexed := compiled.indexed) (values := .initial compiled.compatible.checked) headers caller registry faults rank)
          rank caller headers (CallableIndexedNamedGeneration.context compiled.indexed caller.named) source context evidence))
        fuel (.initial compiled.compatible.checked) source context solved reasonAt) faults size := by
  intro scope id lowered tree
  exact reflects_at_with_literals owner caller prefixZero profile complete globals slots sameSource extension faithful functionLeaves functionTypes evidence uninitialized missing
    sameLayouts conditions authorized
    (CompatibleExpressionLiterals.reflects (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) program context evidence valid source faults) budget size within bodies
    ⟨tree, tree.literalSites⟩

include prefixZero complete globals slots sameSource extension faithful functionLeaves functionTypes unique owners uninitialized missing sameLayouts authorized in
/-- Genuine runtime ledger receipts supply every literal leaf of the same Tree. -/
theorem preserves_at_runtime [FunctionCalls.FaultTokens faults]
    (sameLedger : context.solvedRequirements = solved)
    (runtime : RuntimeRequirementLedgerValid context)
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) registry header faults (CallableIndexedOwnedFunctionState.protocol headers keys) (conditions header))) :
    ProtectedStateTransition.PreservesAt (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals
        (calls := (CallableIndexedLambdaNestedRuntimeCertificates.Head (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) (program := program)
          (LowerSupport (indexed := compiled.indexed) (values := .initial compiled.compatible.checked) headers caller registry faults rank)
          rank caller headers (CallableIndexedNamedGeneration.context compiled.indexed caller.named) source context evidence))
        (fuel := fuel) (values := .initial compiled.compatible.checked) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt)
        (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved source id code)) faults size :=
  preserves_at_with_literals owner caller prefixZero profile complete globals slots sameSource extension faithful functionLeaves functionTypes evidence unique owners uninitialized missing
    sameLayouts conditions authorized runtime.idsUnique
    (CompatibleExpressionLiteralRuntime.preserves (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) program context evidence sameLedger runtime unique faults) budget size within bodies

include prefixZero complete globals slots sameSource extension faithful functionLeaves functionTypes uninitialized missing sameLayouts authorized in
/-- Genuine runtime ledger receipts supply every literal leaf of the same Tree. -/
theorem reflects_at_runtime [FunctionCalls.FaultTokens faults]
    (sameLedger : context.solvedRequirements = solved)
    (runtime : RuntimeRequirementLedgerValid context)
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) registry header faults (CallableIndexedOwnedFunctionState.protocol headers keys) (conditions header))) :
    ProtectedStateTransition.ReflectsAt (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals
        (calls := (CallableIndexedLambdaNestedRuntimeCertificates.Head (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) (program := program)
          (LowerSupport (indexed := compiled.indexed) (values := .initial compiled.compatible.checked) headers caller registry faults rank)
          rank caller headers (CallableIndexedNamedGeneration.context compiled.indexed caller.named) source context evidence))
        (fuel := fuel) (values := .initial compiled.compatible.checked) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt)
        (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved source id code)) faults size :=
  reflects_at_with_literals owner caller prefixZero profile complete globals slots sameSource extension faithful functionLeaves functionTypes evidence uninitialized missing
    sameLayouts conditions authorized
    (CompatibleExpressionLiteralRuntime.reflects (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) program context evidence sameLedger runtime source faults) budget size within bodies

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedExpressionTreeBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReachedAdmittedExpressionCallsHeads
/-! Genuine parent Source typing and actual input admission select the existing
head producers. Each branch returns its own actual reached witness and post
admission. Calls retain an explicit producer for their authentic certificate;
this dispatcher adds no body-family closure or execution induction. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReachedAdmittedExpressionCallsHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  {source : TypedSource} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
  {certificate : GenericExpressionMeaning.Certificate} {faults : FunctionCalls.FaultRep}
  {reasonAt : ExpressionId → Word}
  (unique : NodeOccurrencesUnique source)
  (missing : IndexFaultPostContracts.MissingPolicies (.initial compiled.compatible.checked) source functions registry program context evidence reasonAt faults)
  (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
  (covers : evidence.Covers context)

include transport extension faithful functionLeaves functionTypes unique missing wellFormed runtime covers

theorem preserves_at_with_calls [FunctionCalls.FaultTokens faults]
    (calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate)
    (budget size : Nat) (within : size ≤ budget)
    (children : ∀ child, child ≤ budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source certificate faults child)
    (callMeaning : CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source (calls certificate) faults size) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source
      (CompatibleExpressionCalls.Head calls (.initial compiled.compatible.checked) source context reasonAt certificate)
      faults size := by
  intro scope id lowered head node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial admitted trace
  change ProtectedStateExpressionCallsHeads.WithFacts.PreservesResult
    (registry := registry) (faults := faults) functions callerProtocol
    (fun node outcome {_} reached => PostAdmission bridge context node.type outcome reached) initial node lowered actual ξ outcome after
  refine ProtectedStateExpressionCallsHeads.WithFacts.head_preserves_at_with_providers
    (functions := functions) (evidence := evidence) (stateProtocol := callerProtocol)
    (post := fun node outcome {_} reached => PostAdmission bridge context node.type outcome reached)
    (facts := fun _ id _ node => ExpressionHasType source context id node.type)
    (ready := Admission bridge context) (calls := calls)
    found initial ?_ ?_ ?_ ?_ ?_ head sourceTyped admitted trace
  · intro branch parentFound parentTyped actualAdmission childTrace
    exact CallableIndexedOwnedAdmittedCompositionsBounds.preserves_at bridge functions budget size within
      unique wellFormed runtime covers children branch parentFound parentTyped environments heaps locals agrees typed initial actualAdmission childTrace
  · intro branch parentFound parentTyped actualAdmission childTrace
    exact CallableIndexedOwnedReachedAdmittedDataHeadBounds.preserves_at (calls := calls)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      bridge transport functions extension faithful functionLeaves functionTypes missing budget size within
      unique wellFormed runtime covers children branch parentFound parentTyped environments heaps locals agrees typed initial actualAdmission childTrace
  · intro branch parentFound parentTyped actualAdmission childTrace
    exact CallableIndexedOwnedAdmittedSequenceHeads.Builtin.preserves_at
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      bridge functions evidence wellFormed runtime covers unique functionLeaves budget size within children branch parentFound parentTyped environments heaps locals agrees typed initial actualAdmission childTrace
  · intro branch parentFound parentTyped actualAdmission childTrace
    exact CallableIndexedOwnedAdmittedSequenceHeads.Tuple.preserves_at
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      bridge functions evidence wellFormed runtime covers unique budget size within children branch parentFound parentTyped environments heaps locals agrees typed initial actualAdmission childTrace
  · intro branch parentFound parentTyped actualAdmission childTrace
    exact callMeaning branch parentFound parentTyped environments heaps locals agrees typed initial actualAdmission childTrace

theorem reflects_at_with_calls [FunctionCalls.FaultTokens faults]
    (calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate)
    (budget size : Nat) (within : size ≤ budget)
    (children : ∀ child, child ≤ budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source certificate faults child)
    (callMeaning : CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source (calls certificate) faults size) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source
      (CompatibleExpressionCalls.Head calls (.initial compiled.compatible.checked) source context reasonAt certificate)
      faults size := by
  intro scope id lowered head node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed initial admitted trace
  change ProtectedStateExpressionCallsHeads.WithFacts.ReflectsResult (program := program) (source := source) (context := context)
    (registry := registry) (faults := faults) functions evidence callerProtocol
    (fun node outcome {_} reached => PostAdmission bridge context node.type outcome reached) initial node id lowered environment value finalStore
  refine ProtectedStateExpressionCallsHeads.WithFacts.head_reflects_at_with_providers
    (functions := functions) (evidence := evidence) (stateProtocol := callerProtocol)
    (post := fun node outcome {_} reached => PostAdmission bridge context node.type outcome reached)
    (facts := fun _ id _ node => ExpressionHasType source context id node.type)
    (ready := Admission bridge context) (calls := calls)
    found initial ?_ ?_ ?_ ?_ ?_ head sourceTyped admitted trace
  · intro branch parentFound parentTyped actualAdmission childTrace
    exact CallableIndexedOwnedAdmittedCompositionsBounds.reflects_at bridge functions budget size within
      unique wellFormed runtime covers children branch parentFound parentTyped environments heaps locals agrees typed initial actualAdmission childTrace
  · intro branch parentFound parentTyped actualAdmission childTrace
    exact CallableIndexedOwnedReachedAdmittedDataHeadBounds.reflects_at (calls := calls)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      bridge transport functions extension faithful functionLeaves functionTypes missing budget size within
      unique wellFormed runtime covers children branch parentFound parentTyped environments heaps locals agrees typed initial actualAdmission childTrace
  · intro branch parentFound parentTyped actualAdmission childTrace
    exact CallableIndexedOwnedAdmittedSequenceHeads.Builtin.reflects_at
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      bridge functions evidence wellFormed runtime covers unique functionLeaves budget size within children branch parentFound parentTyped environments heaps locals agrees typed initial actualAdmission childTrace
  · intro branch parentFound parentTyped actualAdmission childTrace
    exact CallableIndexedOwnedAdmittedSequenceHeads.Tuple.reflects_at
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      bridge functions evidence wellFormed runtime covers unique budget size within children branch parentFound parentTyped environments heaps locals agrees typed initial actualAdmission childTrace
  · intro branch parentFound parentTyped actualAdmission childTrace
    exact callMeaning branch parentFound parentTyped environments heaps locals agrees typed initial actualAdmission childTrace

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReachedAdmittedExpressionCallsHeads
end
