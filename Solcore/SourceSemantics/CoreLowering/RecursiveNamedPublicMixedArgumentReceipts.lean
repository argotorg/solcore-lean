import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNamedArgumentReceipts
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicBuiltinArgumentReceipts
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicMixedDataArgumentReceipts
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootSourceSignature

/-! Ordered mixed public inputs retain their actual issuance histories and raw
Source types. A data leaf carries only independent structural typing and its
public interpretation; a named or builtin leaf carries genuine issuance and a
finite continuation of that session's issuances. The whole argument relation
is constructed at the real startup, preserving positions and repeated values.
Nested function carriers and previously executed sessions are separate work. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicMixedArgumentReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Issued Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open CallableIndexedOwnedFunctionState (State)
open CallableIndexedParameterCertificates (Binding)

/-- Each leaf names its independent Source value without assuming its runtime
representation, Source typing judgment or execution behavior. -/
inductive Input {compiled : SourceCoreUnifiedCompilation.Compiled}
    {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
    (rows : Inventory inputs) {artifact : Artifact} (session : Session artifact)
    (context : SourceSemantics.Context) :
    TypeSystem.Ty → SourceCorePublicValues.Value → Dynamic.Value → Prop where
  | data {type : TypeSystem.Ty} {value : SourceCorePublicValues.Value} {source : Dynamic.Value}
      (typed : RecursiveNamedPublicDataArgumentReceipts.PublicDataTyped context value type)
      (meaning : RecursiveNamedPublicDataInputs.Means value source) :
      Input rows session context type value source
  | named {input : CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled}
      (packet : Issued input) (member : Inventory.HasRow packet rows)
      {before : Session artifact} {issued : Completion artifact} {issuanceFuel : Nat}
      (issuance : before.NamedIssuedAt packet.header.named.signature.key issuanceFuel issued)
      (continued : issued.session.IssuanceChain session)
      {handle : Handle} (handleValue : issued.value = .function handle) :
      Input rows session context packet.header.named.specialized.function.type issued.value
        (.global (CallableNamedReversal.global (CallableNamedMetadata.global
          packet.header.named.specialized input.prepared.available)))
  | builtin {function : BuiltinFunctionId}
      {before : Session artifact} {issued : Completion artifact} {issuanceFuel : Nat}
      (issuance : before.BuiltinIssuedAt function issuanceFuel issued)
      (continued : issued.session.IssuanceChain session)
      {handle : Handle} (handleValue : issued.value = .function handle) :
      Input rows session context function.type issued.value (.builtin ⟨function⟩)

/-- Argument positions and duplicates remain explicit list structure. -/
inductive Inputs {compiled : SourceCoreUnifiedCompilation.Compiled}
    {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
    (rows : Inventory inputs) {artifact : Artifact} (session : Session artifact)
    (context : SourceSemantics.Context) :
    List TypeSystem.Ty → List SourceCorePublicValues.Value → List Dynamic.Value → Prop where
  | nil : Inputs rows session context [] [] []
  | cons {type : TypeSystem.Ty} {types : List TypeSystem.Ty}
      {value : SourceCorePublicValues.Value} {values : List SourceCorePublicValues.Value}
      {source : Dynamic.Value} {sources : List Dynamic.Value}
      (head : Input rows session context type value source)
      (tail : Inputs rows session context types values sources) :
      Inputs rows session context (type :: types) (value :: values) (source :: sources)

private theorem Inputs.source_length {compiled : SourceCoreUnifiedCompilation.Compiled}
    {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
    {rows : Inventory inputs} {artifact : Artifact} {session : Session artifact}
    {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    {values : List SourceCorePublicValues.Value} {sources : List Dynamic.Value}
    (receipts : Inputs rows session context types values sources) : sources.length = types.length := by
  induction receipts with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

private theorem Inputs.lookup {compiled : SourceCoreUnifiedCompilation.Compiled}
    {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
    {rows : Inventory inputs} {artifact : Artifact} {session : Session artifact}
    {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    {values : List SourceCorePublicValues.Value} {sources : List Dynamic.Value}
    (receipts : Inputs rows session context types values sources)
    {index : Nat} {type : TypeSystem.Ty} (found : types[index]? = some type) :
    ∃ value source, values[index]? = some value ∧ sources[index]? = some source ∧
      Input rows session context type value source := by
  induction receipts generalizing index with
  | nil => simp at found
  | cons head tail ih =>
      cases index with
      | zero =>
          have same := Option.some.inj found
          cases same
          exact ⟨_, _, rfl, rfl, head⟩
      | succ index =>
          obtain ⟨value, source, valueAt, sourceAt, receipt⟩ := ih found
          exact ⟨value, source, valueAt, sourceAt, receipt⟩

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

/-- Actual mixed startup constructs all argument representation and Source
value typing at the body's receiving registry. Only raw public input receipts,
genuine issuance chains and the actual metadata extension are supplied. -/
theorem StartAt.mixed_arguments_receiving
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
        generalize rawEq : binding.1.scheme.body = raw at receipt rawRoot bindingProjected ⊢
        cases receipt with
        | data inputTyped meaning =>
            obtain ⟨value, type, valueAt, _typeAt, _projection, represented, typed⟩ :=
              RecursiveNamedPublicMixedDataArgumentReceipts.StartAt.data_argument_represents started
                (CallableIndexedOwnedContextualCellOrigins.functions (headers rows) (keys recipe.compiled)
                  bodyRegistry faults profile) registry [] header.function.context ⟨[]⟩ metadata
                rawRoot publicAt inputTyped meaning
            have typeEq := Except.ok.inj (represented.projection.symm.trans bindingProjected)
            exact ⟨source, value, sourceAt, valueAt, typeEq ▸ represented, typed⟩
        | named packet member issuance continued handleValue =>
            have handleAt := publicAt
            rw [handleValue] at handleAt
            obtain ⟨value, valueAt, represented, typed⟩ :=
              RecursiveNamedPublicNamedArgumentReceipts.StartAt.named_argument_represents_after
                prepared inputs rows packet member bodyRegistry registry faults profile caller header
                issuance continued started handleValue handleAt wellFormed
            have typeEq := Except.ok.inj (represented.projection.symm.trans bindingProjected)
            exact ⟨_, value, sourceAt, valueAt, typeEq ▸ represented, typed⟩
        | builtin issuance continued handleValue =>
            have handleAt := publicAt
            rw [handleValue] at handleAt
            obtain ⟨value, _same, _sourceType, valueAt, represented, typed⟩ :=
              RecursiveNamedPublicBuiltinArgumentReceipts.StartAt.builtin_argument_represents_after
                prepared (headers rows) (keys recipe.compiled) bodyRegistry registry faults profile
                [] header.function.context ⟨[]⟩ issuance continued started handleValue handleAt
            have typeEq := Except.ok.inj (represented.projection.symm.trans bindingProjected)
            exact ⟨_, value, sourceAt, valueAt, typeEq ▸ represented, typed⟩)
  have typesEq : header.bindings.map (fun binding => binding.1.scheme.body) = header.types := by
    simpa only [header.parameters, List.map_map, Function.comp_def] using header.extended.bodyTypes_eq
  exact ⟨assembled.1, typesEq ▸ assembled.2⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicMixedArgumentReceipts
