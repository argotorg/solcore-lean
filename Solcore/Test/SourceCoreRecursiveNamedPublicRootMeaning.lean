import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootMeaning

/-! Actual root consumers close argument evaluation and environment transport.
Independent source representation, real Entry, staging and Match profiles remain
visible. Duplicate keys retain the first complete row and its original slot.
This file adds formal consumers only; existing public runtime tests are reused. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedPublicRootMeaning
open Solcore SourceSemantics SourceSemantics.CoreLowering
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open RecursiveNamedCatalog RecursiveNamedCatalogNativeContexts RecursiveGlobalInitializationMeaning
open RecursiveNamedPublicRootMeaning
section Actual
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
theorem actual_has_sufficient_fuel
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
  exact RecursiveNamedPublicRootMeaning.has_sufficient_fuel functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles caller selected represented heaps executed

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller selected represented heaps in
/-- An original completed call exposes the same smaller body derivation.
Reflection uses the independent source entry conditions and never a source
execution or body-preservation law as an input. -/
theorem actual_completed_reflects_program
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
  exact RecursiveNamedPublicRootMeaning.completed_reflects_program functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles caller selected represented heaps admitted heapTyped argumentsTyped completed

end Actual

abbrev actual_recipe_selection := @RecursiveNamedPublicRootMeaning.selection_of_recipe
abbrev actual_fresh_entry := @RecursiveNamedPublicRootMeaning.fresh_entry

section Boundaries

/-- Identical keys and complete rows still retain the first physical slot. -/
theorem duplicate_keeps_first (named : SourceCoreGeneralFunctions.Function) :
    [named, named].zipIdx.find? (fun item => decide (item.1.signature.key = named.signature.key)) =
      some (named, 0) := by simp

/-- A later same-key row cannot replace the actual first-find receipt. -/
theorem duplicate_later_slot (named : SourceCoreGeneralFunctions.Function) :
    [named, named].zipIdx.find? (fun item => decide (item.1.signature.key = named.signature.key)) ≠
      some (named, 1) := by simp

/-- Reversed native storage still packs the original argument order. Arbitrary
payloads, including closures, are copied without changing their captures. -/
theorem ordered_arguments (leftType rightType : Core.Ty) (left right : Core.Value)
    (globals : Environment) (store : Store) :
    Evaluates (right :: left :: globals) store
      (SourceCoreCalls.packArguments ([leftType, rightType].zipIdx.map fun (type, index) =>
        ⟨type, LanguageResult.success (.var (2 - 1 - index))⟩)).expression
      (.inRight .word (.pair left right)) store := by
  simpa only [List.length_cons, List.length_nil, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.append_assoc, List.cons_append, DataPatternValues.packValues] using
    RecursiveNamedPublicRootArguments.arguments_evaluate [leftType, rightType] [left, right] globals store rfl

/-- Zero inputs remain empty; a Unit payload is one distinct input slot. -/
theorem empty_and_unit_arity : ([] : List Core.Value).length ≠ [Core.Value.unit].length := by decide

end Boundaries
end Tests.SourceCoreRecursiveNamedPublicRootMeaning
