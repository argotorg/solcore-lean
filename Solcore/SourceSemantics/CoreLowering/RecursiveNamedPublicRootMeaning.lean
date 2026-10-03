import Solcore.SourceSemantics.CoreLowering.RecursiveNamedProgramCallMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootArguments
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicBootstrapGlobals
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogNativeContexts

/-! Actual public-root selection fixes the full named row and its physical slot.
Pure argument reads and the prefix environment agreement are internal. Source
arguments, real catalog authority, staging and static Match profiles remain
independent inputs; native tags never identify a source declaration. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open RecursiveNamedCatalog RecursiveNamedCatalogNativeContexts RecursiveGlobalInitializationMeaning

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {program : SourceSemantics.Program}
  {headers : Inventory compiled.indexed.ancestry values ambient.definitions program}
  {root : SourceCoreIndexedSession.Root compiled}
  {header : Header compiled.indexed.ancestry values ambient.definitions program}

/-- Static provenance of the original first matching row, including its slot.
The chosen Header retains the separate source attribution and cached receipts. -/
def RootSelection (headers : Inventory compiled.indexed.ancestry values ambient.definitions program)
    (root : SourceCoreIndexedSession.Root compiled)
    (header : Header compiled.indexed.ancestry values ambient.definitions program) : Prop :=
  header ∈ headers ∧ ∃ entry, entry ∈ compiled.indexed.entries ∧ root.FactoryShape compiled entry ∧
    compiled.indexed.base.functions.zipIdx.find?
      (fun item => decide (item.1.signature.key = entry.key)) = some (header.named, header.slot)

/-- Full row equality follows from the original selected slot, even when keys
repeat. Complete inventory coverage does not replace first-match provenance. -/
theorem selection_of_issued (issued : root.Issued compiled) (complete : Complete headers) :
    ∃ header, RootSelection headers root header := by
  obtain ⟨entry, entryMember, shape⟩ := issued
  obtain ⟨named, index, found, rest⟩ := shape
  have row : compiled.indexed.base.functions[index]? = some named :=
    List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some found)
  obtain ⟨header, member, slot, _⟩ := complete index named.signature
    (CallableIndexedPreparedInventories.cached_global_at compiled row)
  have selected : compiled.indexed.base.functions[index]? = some header.named := slot ▸ header.selected
  have same : header.named = named := Option.some.inj (selected.symm.trans row)
  refine ⟨header, member, entry, entryMember, ⟨named, index, found, rest⟩, ?_⟩
  simpa only [slot, same] using found

/-- Accepted preparation supplies the actual indexed entry and first-match
receipt, retaining the caller's independent complete source inventory. -/
theorem selection_of_recipe {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {root : SourceCoreIndexedSession.Root recipe.compiled} (member : root ∈ recipe.roots)
    {headers : Inventory recipe.compiled.indexed.ancestry values ambient.definitions program}
    (complete : Complete headers) : ∃ header, RootSelection headers root header :=
  selection_of_issued (SourceCoreIndexedSession.Recipe.prepare_roots accepted member) complete

namespace RootSelection

theorem member (selected : RootSelection headers root header) : header ∈ headers := selected.1

/-- The original factory equation is transported by equality of both complete
selected fields. Source input types are deliberately not inferred here. -/
theorem shape (selected : RootSelection headers root header) :
    root.types = header.named.inputs.map Prod.snd ∧
    root.body = SourceCoreCalls.call header.named.signature (header.slot + root.types.length)
      (SourceCoreCalls.packArguments (root.types.zipIdx.map fun (type, index) =>
        ⟨type, LanguageResult.success (.var (root.types.length - 1 - index))⟩)).expression Word.zero := by
  obtain ⟨_, entry, _, shape, found⟩ := selected
  obtain ⟨named, index, first, _, _, _, types, _, _, _, body, _⟩ := shape
  have same := Prod.mk.inj (Option.some.inj (found.symm.trans first))
  obtain ⟨rfl, rfl⟩ := same
  exact ⟨types, body⟩

/-- Only arity is needed by native argument reads. Raw binder identity fixes
that arity before the independent payload representation supplies its length. -/
theorem argument_length (selected : RootSelection headers root header)
    {mapping : LocationMap} {world : StoreTyping} {arguments : List Dynamic.Value} {payloads : List Value}
    {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
    (represented : CallableIndexedParameterMeaning.Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world header.bindings arguments payloads) : root.types.length = payloads.length := by
  have binders := congrArg List.length (header.parameters.symm.trans header.agreement.parameters)
  simp only [List.length_map] at binders
  rw [selected.shape.1, List.length_map, ← binders]
  exact represented.length.2

/-- Actual argument code copies arbitrary payloads and preserves the full
store. Neither source meaning nor source parameter types follow from copying. -/
theorem arguments_evaluate (selected : RootSelection headers root header)
    {mapping : LocationMap} {world : StoreTyping} {arguments : List Dynamic.Value} {payloads : List Value}
    {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
    (represented : CallableIndexedParameterMeaning.Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world header.bindings arguments payloads) (store : Store) :
    Evaluates (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed) store
      (SourceCoreCalls.packArguments (root.types.zipIdx.map fun (type, index) =>
        ⟨type, LanguageResult.success (.var (root.types.length - 1 - index))⟩)).expression
      (.inRight .word (DataPatternValues.packValues payloads)) store :=
  RecursiveNamedPublicRootArguments.arguments_evaluate _ _ _ _ (selected.argument_length represented)

end RootSelection

/-- Prefix insertion preserves each original global value, including closure
captures. It does not construct or rewrite catalog authority. -/
theorem globals_agree (payloads globals : Environment) :
    EnvironmentsAgree (shift payloads.length) globals (payloads.reverse ++ globals) := by
  intro index value found
  change (payloads.reverse ++ globals)[index + payloads.length]? = some value
  rw [List.getElem?_append_right (by simp only [List.length_reverse]; omega)]
  simpa only [List.length_reverse, Nat.add_sub_cancel] using found

section Meaning
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedCatalogInvocationBounds
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory compiled.indexed.ancestry values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {compilation : Header compiled.indexed.ancestry values ambient.definitions program → SourceCoreFunctions.Context}
  {expressionSyntax : Header compiled.indexed.ancestry values ambient.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      MatchProfileFor diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  (caller : Entry headers locations capturePrefix 0 [] mapping world before store
    (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed))
  {header : Header compiled.indexed.ancestry values ambient.definitions program}
  {root : SourceCoreIndexedSession.Root compiled} (selected : RootSelection headers root header)
  {arguments : List Dynamic.Value} {payloads : List Value}
  (represented : CallableIndexedParameterMeaning.Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world header.bindings arguments payloads)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)


include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller selected represented heaps in
/-- The real global reference and capture supply the emitted call's read.
Source execution supplies the body; original native completeness supplies a
budget for the complete call, including argument packing and dispatch. -/
theorem has_sufficient_fuel
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → runStateful fuel
        (.initial root.body
          (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed) store) = .done value finalStore) ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix 0 [] finalMap finalWorld after finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)) := by
  have result := RecursiveNamedProgramCallMeaning.emitted_call_has_sufficient_fuel_match (reason := Word.zero) functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles caller selected.member represented heaps
    (globals_agree payloads _) (selected.arguments_evaluate represented store) executed
  simpa only [selected.shape.2, selected.argument_length represented, shift, List.length_nil, Nat.zero_add] using result

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller selected represented heaps in
/-- An original completed call exposes the same smaller body derivation.
Reflection uses the independent source entry conditions and never a source
execution or body-preservation law as an input. -/
theorem completed_reflects_program
    (admitted : Staging.ProgramHasStages program)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    {fuel : Nat} {value : Core.Value} {finalStore : Core.Store}
    (completed : runStateful fuel
      (.initial root.body
          (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed) store) = .done value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix 0 [] finalMap finalWorld after finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)) := by
  apply RecursiveNamedProgramCallMeaning.completed_call_reflects_program_match (reason := Word.zero) functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles caller selected.member represented heaps
    admitted heapTyped argumentsTyped (globals_agree payloads _) (selected.arguments_evaluate represented store)
  simpa only [selected.shape.2, selected.argument_length represented, shift, List.length_nil, Nat.zero_add] using completed

end Meaning

/-- Fresh completed initialization supplies an Entry in exactly the public
native globals. All original source inventory and initialization conditions
remain explicit; arbitrary existing sessions are outside this helper. -/
theorem fresh_entry (compiled : SourceCoreUnifiedCompilation.Compiled)
    {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
    (headers : Inventory compiled.indexed.ancestry values ambient.definitions program)
    (ledger : Ledger headers compiled.indexed.secondPass.closures)
    (sizes : ∀ header, header ∈ headers → header.globals = compiled.indexed.base.globals.length)
    (locals : ∀ header, header ∈ headers → header.function.context.locals = [])
    {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (definitions : compiled.indexed.layouts.definitions = ambient.definitions)
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    {fuel : Nat} {value : Value} {finalStore : Store}
    (completed : runStateful fuel (.initial recipe.bootstrap [] []) = .done value finalStore) :
    value = .inRight .word .unit ∧ ∃ world,
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions [] world ⟨[]⟩ finalStore ∧
      Nonempty (Entry headers
        (fun header => RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot)
        0 0 [] [] world ⟨[]⟩ finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)) := by
  simpa only [RecursiveNamedPublicBootstrapGlobals.environment_eq] using
    RecursiveNamedCatalogPreparedInitialization.completed_entry compiled headers ledger sizes locals
      accepted definitions functions registry completed

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootMeaning
