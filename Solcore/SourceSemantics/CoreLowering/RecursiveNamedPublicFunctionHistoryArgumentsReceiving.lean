import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionHistoryEncoding
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedRawInputs
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootSourceSignature
import Solcore.SourceSemantics.CoreLowering.CallableIndexedActualNamedSourceReceipts
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderParameterProjections

/-! Arbitrary ordered arguments can contain distinct retained functions and
repeated aliases inside data containers. Current function-history evidence
supplies meaning and typing; actual startup fixes every native payload and
intermediate registry. Both lists retain the actual map, world and heap. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionHistoryArgumentsReceiving
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning
open RecursiveNamedPublicFunctionHistoryInputs (Inputs)
open RecursiveNamedPublicFunctionHistory (Entry)
open CallableIndexedOwnedFunctionValues (Header)
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

/-- Actual retained history and original input encoding produce complete
current arguments. Each selected native position is preserved, with no extra
Source or native suffix and no supplied body execution law. -/
theorem StartAt.history_arguments_receiving
    {artifact : Artifact} {session : Session artifact} {key : Key}
    {publicArguments : List SourceCorePublicValues.Value} {inputFuel : Nat}
    {checkpoint : Checkpoint artifact} {recipe : Recipe} {root : Root recipe.compiled}
    {world : StoreTyping} {store : Store} {native : Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session key publicArguments inputFuel checkpoint recipe root world store native encodedValues)
    (functions : FunctionModel recipe.compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed))
    {headers : List (Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
    {header : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
    (selected : RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed)
      (program := Program.ofChecked recipe.compiled.sourceProgram) headers root header)
    (history : List Entry)
    (imported : ∀ entry, entry ∈ history →
      session.EncodesAt entry.fuel entry.sourceType (.function entry.handle) entry.native)
    {receiving : SourceCoreRawMetadata.Registry} {mapping : LocationMap} {heap : Dynamic.Heap}
    (retained : ∀ entry, entry ∈ history →
      ValueRep recipe.compiled.compatible.checked receiving functions mapping world
        entry.sourceType entry.source entry.native entry.nativeType)
    (retainedTyped : ∀ entry, entry ∈ history →
      Dynamic.ValueHasType header.function.context heap entry.source entry.sourceType)
    {sources : List Dynamic.Value}
    (receipts : Inputs history header.function.context
      (header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments sources)
    (metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiving)
    (wellFormed : ProgramWellFormed (Program.ofChecked recipe.compiled.sourceProgram)) :
    CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel recipe.compiled.compatible.checked receiving functions)
      mapping world header.bindings sources native ∧
    Dynamic.ValuesHaveTypes header.function.context heap sources header.types := by
  have arity := congrArg List.length (header.parameters.symm.trans header.agreement.parameters)
  simp only [List.length_map] at arity
  have nativeLength := congrArg List.length started.typed.type_tags
  rw [selected.shape.1] at nativeLength
  simp only [List.length_map] at nativeLength
  have nativeCount : native.length = header.bindings.length := nativeLength.trans arity.symm
  have sourceCount : sources.length = header.bindings.length := by
    simpa only [List.length_map] using receipts.source_length
  have record := CallableIndexedActualNamedSourceReceipts.header_record recipe.compiled header
  have projected := RecursiveNamedHeaderParameterProjections.projections_of_record
    header rfl wellFormed record
  have rawInputs := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).1
  have assembled := arguments_of_positions (functions := functions) (registry := receiving)
      (mapping := mapping) (world := world) (context := header.function.context) (heap := heap)
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
        obtain ⟨before, encoded, type, valueAt, typeAt, projection, owner, accepted, extended⟩ :=
          RecursiveNamedPublicNestedRawInputs.StartAt.raw_input started rawRoot publicAt
        obtain ⟨actual, actualAt, typed⟩ := started.typed.lookup typeAt
        have sameValue : actual = encoded.value := Option.some.inj (actualAt.symm.trans valueAt)
        subst actual
        obtain ⟨meaning, sourceTyped⟩ := RecursiveNamedPublicFunctionHistoryEncoding.Input.meaning
          receipt started.recipe_eq imported retained retainedTyped
        have represented := meaning owner rfl accepted projection typed (extended.trans metadata)
        have typeEq := Except.ok.inj (projection.symm.trans bindingProjected)
        exact ⟨source, encoded.value, sourceAt, valueAt, typeEq ▸ represented, sourceTyped⟩)
  have typesEq : header.bindings.map (fun binding => binding.1.scheme.body) = header.types := by
    simpa only [header.parameters, List.map_map, Function.comp_def] using header.extended.bodyTypes_eq
  exact ⟨assembled.1, typesEq ▸ assembled.2⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionHistoryArgumentsReceiving
