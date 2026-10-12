import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedArgumentReceipts
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedInputs
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootSourceSignature

/-! Nested public inputs are assembled in their original argument positions.
The per-position producer follows actual encoding through products,
constructor payloads and ordered mapping entries. Exact list lengths retain
all Source and native arguments, including repeated handles. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedArgumentsReceiving
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning
open RecursiveNamedPublicNestedInputs (Inputs)
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionState (State)
open CallableIndexedParameterCertificates (Binding)

private theorem projected_at {checked : SourceCoreCompatibleCatalog.Checked}
    {bindings : List Binding} {index : Nat} {binding : Binding}
    (projected : (bindings.map (fun binding => binding.1.scheme.body)).mapM checked.catalog.project =
      .ok (bindings.map Prod.snd))
    (found : bindings[index]? = some binding) :
    checked.catalog.project binding.1.scheme.body = .ok binding.2 := by
  induction bindings generalizing index with
  | nil => simp at found
  | cons head tail ih =>
      simp only [List.map_cons] at projected
      obtain ⟨type, types, headProjected, tailProjected, shape⟩ := CompatibleEncoding.project_cons projected
      have parts := List.cons.inj shape
      have headActual : checked.catalog.project head.1.scheme.body = .ok head.2 := by
        simpa only [← parts.1] using headProjected
      have tailActual : (tail.map (fun binding => binding.1.scheme.body)).mapM checked.catalog.project =
          .ok (tail.map Prod.snd) := by
        simpa only [← parts.2] using tailProjected
      cases index with
      | zero =>
          have same := Option.some.inj found
          cases same
          exact headActual
      | succ index => exact ih tailActual found

/-- Reconstruct both complete lists from their original positions. Exact
lengths exclude silently discarded native or Source suffixes. -/
private theorem arguments_of_positions
    {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
    {mapping : LocationMap} {world : StoreTyping} {context : SourceSemantics.Context} {heap : Dynamic.Heap}
    {bindings : List Binding} {sources : List Dynamic.Value} {native : Environment}
    (sourceLength : sources.length = bindings.length) (nativeLength : native.length = bindings.length)
    (positions : ∀ {index : Nat} {binding : Binding}, bindings[index]? = some binding →
      ∃ source value, sources[index]? = some source ∧ native[index]? = some value ∧
        ValueRep checked registry functions mapping world binding.1.scheme.body source value binding.2 ∧
        Dynamic.ValueHasType context heap source binding.1.scheme.body) :
    CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel checked registry functions) mapping world bindings sources native ∧
      Dynamic.ValuesHaveTypes context heap sources (bindings.map (fun binding => binding.1.scheme.body)) := by
  induction bindings generalizing sources native with
  | nil =>
      have sourceNil := List.eq_nil_of_length_eq_zero sourceLength
      have nativeNil := List.eq_nil_of_length_eq_zero nativeLength
      subst sources
      subst native
      exact ⟨.nil, .nil⟩
  | cons binding bindings ih =>
      cases sources with
      | nil => simp at sourceLength
      | cons source sources =>
          cases native with
          | nil => simp at nativeLength
          | cons value native =>
              obtain ⟨actualSource, actualValue, sourceAt, valueAt, represented, typed⟩ :=
                positions (index := 0) rfl
              have sameSource : source = actualSource := Option.some.inj sourceAt
              have sameValue : value = actualValue := Option.some.inj valueAt
              subst actualSource
              subst actualValue
              simp only [List.length_cons] at sourceLength nativeLength
              have remaining := ih (Nat.succ.inj sourceLength) (Nat.succ.inj nativeLength) (by
                intro index next found
                exact positions (index := index + 1) found)
              exact ⟨.cons represented remaining.1, .cons typed remaining.2⟩

/-- Actual nested startup constructs all argument representations and Source
value typing at the body's receiving registry. Structural input receipts
preserve raw types, container order and the actual issuance histories. -/
theorem StartAt.nested_arguments_receiving
    {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    (prepared : Recipe.prepare compiled = .ok recipe)
    (inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled))
    (rows : Inventory inputs)
    (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (caller : State (headers rows) (keys compiled)
      ⟨[], [], (RecursiveNamedCatalogPreparedInitialization.store compiled).map Core.Value.type,
        ⟨[]⟩, RecursiveNamedCatalogPreparedInitialization.store compiled,
        SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩)
    {artifact : Artifact} {session : Session artifact}
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {checkpoint : Checkpoint artifact} {root : Root compiled}
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    {native : Environment} {arguments : List Dynamic.Value}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session key publicArguments fuel checkpoint recipe
      ((Recipe.prepare_compiled prepared).symm ▸ root)
      ((RecursiveNamedCatalogPreparedInitialization.store compiled).map Core.Value.type)
      (RecursiveNamedCatalogPreparedInitialization.store compiled) native encodedValues)
    (selected : RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) (headers rows) root header)
    (receipts : Inputs rows session header.function.context
      (header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (metadata : SourceCoreRawMetadata.Extends encodedValues.registry registry)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions (headers rows) (keys compiled)
          bodyRegistry faults profile))
      [] ((RecursiveNamedCatalogPreparedInitialization.store compiled).map Core.Value.type)
      header.bindings arguments native ∧
    Dynamic.ValuesHaveTypes header.function.context ⟨[]⟩ arguments header.types := by
  have sameCompiled := Recipe.prepare_compiled prepared
  cases sameCompiled
  have arity := congrArg List.length (header.parameters.symm.trans header.agreement.parameters)
  simp only [List.length_map] at arity
  have nativeLength := congrArg List.length started.typed.type_tags
  rw [selected.shape.1] at nativeLength
  simp only [List.length_map] at nativeLength
  have nativeCount : native.length = header.bindings.length := nativeLength.trans arity.symm
  have sourceCount : arguments.length = header.bindings.length := by
    simpa only [List.length_map] using receipts.source_length
  have record := CallableIndexedActualNamedSourceReceipts.header_record recipe.compiled header
  have projected := RecursiveNamedHeaderParameterProjections.projections_of_record
    header rfl wellFormed record
  have rawInputs := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).1
  have assembled := arguments_of_positions (functions :=
      CallableIndexedOwnedContextualCellOrigins.functions (headers rows) (keys recipe.compiled)
        bodyRegistry faults profile) (registry := registry) (mapping := [])
      (world := (RecursiveNamedCatalogPreparedInitialization.store recipe.compiled).map Core.Value.type)
      (context := header.function.context) (heap := ⟨[]⟩)
      sourceCount nativeCount (by
        intro index binding bindingAt
        have rawAt : (header.bindings.map (fun binding => binding.1.scheme.body))[index]? =
            some binding.1.scheme.body := by
          simp only [List.getElem?_map, bindingAt, Option.map_some]
        obtain ⟨publicValue, source, publicAt, sourceAt, receipt⟩ := receipts.lookup rawAt
        have bindingProjected := projected_at projected bindingAt
        have rawRoot : root.inputs[index]? = some binding.1.scheme.body := by
          rw [rawInputs]
          exact rawAt
        obtain ⟨value, type, valueAt, projection, represented, typed⟩ :=
          RecursiveNamedPublicNestedArgumentReceipts.StartAt.nested_argument_represents
            prepared inputs rows bodyRegistry registry faults profile caller header
            started rawRoot publicAt receipt metadata wellFormed
        have typeEq := Except.ok.inj (projection.symm.trans bindingProjected)
        exact ⟨source, value, sourceAt, valueAt, typeEq ▸ represented, typed⟩)
  have typesEq : header.bindings.map (fun binding => binding.1.scheme.body) = header.types := by
    simpa only [header.parameters, List.map_map, Function.comp_def] using header.extended.bodyTypes_eq
  exact ⟨assembled.1, typesEq ▸ assembled.2⟩


end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedArgumentsReceiving
