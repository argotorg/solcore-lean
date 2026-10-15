import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalCellOrigins
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicFactoryValues
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalFactoryValues
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicCurrentFactoryValues
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicBuiltinArgumentReceipts
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionHistoryEntries

/-! Newly issued functions join an existing history through actual issuance
and encoding observations. Their Source meaning is derived from the current
owned caller and physical store, rather than supplied as a certificate. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionHistory
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionState (State)

inductive IssuedEntry {compiled : SourceCoreUnifiedCompilation.Compiled} {artifact : Artifact} :
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))) →
    (keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))) →
    FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed) →
    SourceCoreRawMetadata.Registry → Header compiled (Program.ofChecked compiled.sourceProgram) →
    Session artifact → Session artifact → Entry → Prop where
  | named {recipe : Recipe} (prepared : Recipe.prepare compiled = .ok recipe)
      (inputs : List (Input compiled)) (rows : Inventory inputs)
      {input : Input compiled} (packet : Issued input) (member : Inventory.HasRow packet rows)
      (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
      (profile : compiled.compatible.checked.catalog.callableContracts = true)
      (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
      {before : Session artifact} {issued : Completion artifact} {fuel : Nat}
      (issuance : before.NamedIssuedAt packet.header.named.signature.key fuel issued)
      (atRecipe : ArtifactRecipe artifact recipe)
      {handle : Handle} (handleValue : issued.value = .function handle) {native : Core.Value}
      (encoded : issued.session.EncodesAt fuel packet.header.named.specialized.function.type (.function handle) native)
      (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
      IssuedEntry (headers rows) (keys compiled)
        (CallableIndexedOwnedContextualCellOrigins.functions (headers rows) (keys compiled) bodyRegistry faults profile)
        registry anchor before issued.session
        ⟨packet.header.named.specialized.function.type,
          .global (CallableNamedReversal.global (CallableNamedMetadata.global packet.header.named.specialized input.prepared.available)),
          handle, native, CallableContract.functionType packet.header.named.signature.parameterType packet.header.named.signature.resultType, fuel⟩
  | builtin {recipe : Recipe} (prepared : Recipe.prepare compiled = .ok recipe)
      (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
      (keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram)))
      (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
      (profile : compiled.compatible.checked.catalog.callableContracts = true)
      (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
      {before : Session artifact} {issued : Completion artifact} {function : BuiltinFunctionId} {fuel : Nat}
      (issuance : before.BuiltinIssuedAt function fuel issued)
      (atRecipe : ArtifactRecipe artifact recipe)
      {handle : Handle} (handleValue : issued.value = .function handle) {native : Core.Value}
      (encoded : issued.session.EncodesAt fuel function.type (.function handle) native) :
      IssuedEntry headers keys (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)
        registry anchor before issued.session
        ⟨function.type, .builtin ⟨function⟩, handle, native,
          CallableContract.functionType (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function), fuel⟩
  | physicalNamed {recipe : Recipe} (prepared : Recipe.prepare compiled = .ok recipe)
      (inputs : List (Input compiled)) (rows : Inventory inputs)
      {input : Input compiled} (packet : Issued input) (member : Inventory.HasRow packet rows)
      (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
      (profile : compiled.compatible.checked.catalog.callableContracts = true)
      (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
      {before : Session artifact} {issued : Completion artifact} {fuel : Nat}
      (issuance : before.NamedIssuedAt packet.header.named.signature.key fuel issued)
      (atRecipe : ArtifactRecipe artifact recipe)
      {handle : Handle} (handleValue : issued.value = .function handle) {native : Core.Value}
      (encoded : issued.session.EncodesAt fuel packet.header.named.specialized.function.type (.function handle) native)
      (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
      IssuedEntry (headers rows) (keys compiled)
        (CallableIndexedOwnedPhysicalCellOrigins.functions (headers rows) (keys compiled) bodyRegistry faults profile)
        registry anchor before issued.session
        ⟨packet.header.named.specialized.function.type,
          .global (CallableNamedReversal.global (CallableNamedMetadata.global packet.header.named.specialized input.prepared.available)),
          handle, native, CallableContract.functionType packet.header.named.signature.parameterType packet.header.named.signature.resultType, fuel⟩
  | physicalNamedSelected {recipe : Recipe} (prepared : Recipe.prepare compiled = .ok recipe)
      (inputs : List (Input compiled)) (rows : Inventory inputs)
      {input : Input compiled} (packet : Issued input) (member : Inventory.HasRow packet rows)
      (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
      (profile : compiled.compatible.checked.catalog.callableContracts = true)
      (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
      {before : Session artifact} {issued : Completion artifact} {fuel : Nat}
      (issuance : before.NamedIssuedAt packet.header.named.signature.key fuel issued)
      (atRecipe : ArtifactRecipe artifact recipe)
      {handle : Handle} (handleValue : issued.value = .function handle) {native : Core.Value}
      (encoded : issued.session.EncodesAt fuel packet.header.named.specialized.function.type (.function handle) native)
      (certified : SelectedCompilationNamedArgumentRows.CertifiedAt (header := packet.header) (function := CallableNamedReversal.global (CallableNamedMetadata.global packet.header.named.specialized input.prepared.available))) :
      IssuedEntry (headers rows) (keys compiled)
        (CallableIndexedOwnedPhysicalCellOrigins.functions (headers rows) (keys compiled) bodyRegistry faults profile)
        registry anchor before issued.session
        ⟨packet.header.named.specialized.function.type,
          .global (CallableNamedReversal.global (CallableNamedMetadata.global packet.header.named.specialized input.prepared.available)),
          handle, native, CallableContract.functionType packet.header.named.signature.parameterType packet.header.named.signature.resultType, fuel⟩
  | physicalBuiltin {recipe : Recipe} (prepared : Recipe.prepare compiled = .ok recipe)
      (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
      (keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram)))
      (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
      (profile : compiled.compatible.checked.catalog.callableContracts = true)
      (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
      {before : Session artifact} {issued : Completion artifact} {function : BuiltinFunctionId} {fuel : Nat}
      (issuance : before.BuiltinIssuedAt function fuel issued)
      (atRecipe : ArtifactRecipe artifact recipe)
      {handle : Handle} (handleValue : issued.value = .function handle) {native : Core.Value}
      (encoded : issued.session.EncodesAt fuel function.type (.function handle) native) :
      IssuedEntry headers keys (CallableIndexedOwnedPhysicalCellOrigins.functions headers keys bodyRegistry faults profile)
        registry anchor before issued.session
        ⟨function.type, .builtin ⟨function⟩, handle, native,
          CallableContract.functionType (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function), fuel⟩

  | preparedPhysicalNamedSelected {recipe : Recipe} (prepared : Recipe.prepare compiled = .ok recipe)
      (inputs : List (Input compiled)) (rows : Inventory inputs)
      {input : Input compiled} (packet : Issued input) (member : Inventory.HasRow packet rows)
      (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
      (profile : compiled.compatible.checked.catalog.callableContracts = true)
      (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
      {before : Session artifact} {issued : Completion artifact} {fuel : Nat}
      (issuance : before.NamedIssuedAt packet.header.named.signature.key fuel issued)
      (atRecipe : ArtifactRecipe artifact recipe)
      {handle : Handle} (handleValue : issued.value = .function handle) {native : Core.Value}
      (encoded : issued.session.EncodesAt fuel packet.header.named.specialized.function.type (.function handle) native)
      (certified : SelectedCompilationNamedArgumentRows.CertifiedAt (header := packet.header) (function := CallableNamedReversal.global (CallableNamedMetadata.global packet.header.named.specialized input.prepared.available))) :
      IssuedEntry (headers rows) (keys compiled)
        (CallableIndexedOwnedPreparedPhysicalCellOrigins.functions (headers rows) (keys compiled) bodyRegistry faults profile)
        registry anchor before issued.session
        ⟨packet.header.named.specialized.function.type,
          .global (CallableNamedReversal.global (CallableNamedMetadata.global packet.header.named.specialized input.prepared.available)),
          handle, native, CallableContract.functionType packet.header.named.signature.parameterType packet.header.named.signature.resultType, fuel⟩
  | preparedPhysicalBuiltin {recipe : Recipe} (prepared : Recipe.prepare compiled = .ok recipe)
      (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
      (keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram)))
      (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
      (profile : compiled.compatible.checked.catalog.callableContracts = true)
      (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
      {before : Session artifact} {issued : Completion artifact} {function : BuiltinFunctionId} {fuel : Nat}
      (issuance : before.BuiltinIssuedAt function fuel issued)
      (atRecipe : ArtifactRecipe artifact recipe)
      {handle : Handle} (handleValue : issued.value = .function handle) {native : Core.Value}
      (encoded : issued.session.EncodesAt fuel function.type (.function handle) native) :
      IssuedEntry headers keys (CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry faults profile)
        registry anchor before issued.session
        ⟨function.type, .builtin ⟨function⟩, handle, native,
          CallableContract.functionType (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function), fuel⟩

/-- Retaining a newly issued entry preserves all earlier registry slots. -/
theorem IssuedEntry.chain
    {compiled : SourceCoreUnifiedCompilation.Compiled} {artifact : Artifact}
    {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
    {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
    {registry : SourceCoreRawMetadata.Registry} {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}
    {before after : Session artifact} {entry : Entry}
    (receipt : IssuedEntry headers keys functions registry anchor before after entry) :
    before.IssuanceChain after := by
  cases receipt with
  | named _ _ _ _ _ _ _ _ _ _ issuance _ handleValue _ _ => exact .named (.refl _) issuance handleValue
  | builtin _ _ _ _ _ _ _ _ issuance _ handleValue _ => exact .builtin (.refl _) issuance handleValue
  | physicalNamed _ _ _ _ _ _ _ _ _ _ issuance _ handleValue _ _ => exact .named (.refl _) issuance handleValue
  | physicalNamedSelected _ _ _ _ _ _ _ _ _ _ issuance _ handleValue _ _ => exact .named (.refl _) issuance handleValue
  | preparedPhysicalNamedSelected _ _ _ _ _ _ _ _ _ _ issuance _ handleValue _ _ => exact .named (.refl _) issuance handleValue
  | physicalBuiltin _ _ _ _ _ _ _ _ issuance _ handleValue _ => exact .builtin (.refl _) issuance handleValue
  | preparedPhysicalBuiltin _ _ _ _ _ _ _ _ issuance _ handleValue _ => exact .builtin (.refl _) issuance handleValue

/-- Current store checks identify every fresh named capture. Builtins retain
their compiler-owned closed code. Both cases use the real issued handle. -/
theorem IssuedEntry.current
    {compiled : SourceCoreUnifiedCompilation.Compiled} {artifact : Artifact}
    {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
    {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
    {registry : SourceCoreRawMetadata.Registry} {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}
    {before after : Session artifact} {entry : Entry}
    (receipt : IssuedEntry headers keys functions registry anchor before after entry)
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    (caller : State headers keys ⟨[], mapping, world, heap, store,
      SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩)
    (atNative : before.NativeAt world store) :
    before.SameRuntime after ∧
      after.EncodesAt entry.fuel entry.sourceType (.function entry.handle) entry.native ∧
      ValueRep compiled.compatible.checked registry functions mapping world
        entry.sourceType entry.source entry.native entry.nativeType ∧
      Dynamic.ValueHasType anchor.function.context heap entry.source entry.sourceType := by
  cases receipt with
  | named prepared inputs rows packet member bodyRegistry registry faults profile anchor issuance atRecipe handleValue encoded wellFormed =>
      obtain ⟨native, imported, represented, typed⟩ :=
        RecursiveNamedPublicCurrentFactoryValues.Session.named_value_represents_current
          prepared inputs rows packet member bodyRegistry registry faults profile caller anchor
          issuance atNative (.refl _) atRecipe handleValue wellFormed
      have same := imported.unique encoded
      cases same
      exact ⟨issuance.same_runtime, encoded, represented, typed⟩
  | builtin prepared headers keys bodyRegistry registry faults profile anchor issuance atRecipe handleValue encoded =>
      obtain ⟨native, sameRuntime, _type, imported, represented, typed⟩ :=
        RecursiveNamedPublicBuiltinArgumentReceipts.Session.builtin_value_represents_after
          prepared headers keys bodyRegistry registry faults profile mapping anchor.function.context heap
          issuance (.refl _) atRecipe handleValue (world := world)
      have same := imported.unique encoded
      cases same
      exact ⟨sameRuntime, encoded, represented, typed⟩
  | physicalNamed prepared inputs rows packet member bodyRegistry registry faults profile anchor issuance atRecipe handleValue encoded wellFormed =>
      obtain ⟨native, imported, represented, typed⟩ :=
        RecursiveNamedPublicPhysicalFactoryValues.Session.named_value_represents_current
          prepared inputs rows packet member bodyRegistry registry faults profile caller anchor
          issuance atNative (.refl _) atRecipe handleValue wellFormed
      have same := imported.unique encoded
      cases same
      exact ⟨issuance.same_runtime, encoded, represented, typed⟩
  | physicalNamedSelected prepared inputs rows packet member bodyRegistry registry faults profile anchor issuance atRecipe handleValue encoded certified =>
      obtain ⟨native, imported, represented, typed⟩ :=
        SelectedCompilationPublicFactoryValues.Session.named_value_represents_current
          prepared inputs rows packet member bodyRegistry registry faults profile caller anchor
          issuance atNative (.refl _) atRecipe handleValue certified
      have same := imported.unique encoded
      cases same
      exact ⟨issuance.same_runtime, encoded, represented, typed⟩
  | physicalBuiltin prepared headers keys bodyRegistry registry faults profile anchor issuance atRecipe handleValue encoded =>
      obtain ⟨native, sameRuntime, _type, imported, represented, typed⟩ :=
        RecursiveNamedPublicPhysicalFactoryValues.Session.builtin_value_represents_after
          prepared headers keys bodyRegistry registry faults profile mapping anchor.function.context heap
          issuance (.refl _) atRecipe handleValue (world := world)
      have same := imported.unique encoded
      cases same
      exact ⟨sameRuntime, encoded, represented, typed⟩

  | preparedPhysicalNamedSelected prepared inputs rows packet member bodyRegistry registry faults profile anchor issuance atRecipe handleValue encoded certified =>
      obtain ⟨native, imported, represented, typed⟩ :=
        SelectedCompilationPublicFactoryValues.Session.named_value_represents_current
          prepared inputs rows packet member bodyRegistry registry faults profile caller anchor
          issuance atNative (.refl _) atRecipe handleValue certified
      have same := imported.unique encoded
      cases same
      exact ⟨issuance.same_runtime, encoded, represented.map_functions
        (CallableIndexedOwnedPreparedPhysicalCellOrigins.includes_physical profile), typed⟩
  | preparedPhysicalBuiltin prepared headers keys bodyRegistry registry faults profile anchor issuance atRecipe handleValue encoded =>
      obtain ⟨native, sameRuntime, _type, imported, represented, typed⟩ :=
        RecursiveNamedPublicPhysicalFactoryValues.Session.builtin_value_represents_after
          prepared headers keys bodyRegistry registry faults profile mapping anchor.function.context heap
          issuance (.refl _) atRecipe handleValue (world := world)
      have same := imported.unique encoded
      cases same
      exact ⟨sameRuntime, encoded, represented.map_functions
        (CallableIndexedOwnedPreparedPhysicalCellOrigins.includes_physical profile), typed⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionHistory
