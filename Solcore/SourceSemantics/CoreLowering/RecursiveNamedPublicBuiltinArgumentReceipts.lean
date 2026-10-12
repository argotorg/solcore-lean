import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicIssuedFunctionInputs
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCellOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedActualNamedSourceReceipts
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderParameterProjections

/-! An actual builtin issuance, successful cached recipe preparation, and the
original startup encoder jointly establish the builtin argument's Source
meaning. The exact closed code, nonwrapping identity and descriptor come from
the compiler-owned factory. The receiving body's function model and metadata
registry are retained; neither authentication nor native type tags determine
Source function meaning. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicBuiltinArgumentReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning
open CallableIndexedOwnedFunctionValues (Header Key)

/-- A builtin argument at its actual startup index has the complete receiving
function representation and deep Source typing, for any Source heap/context.
The caller still selects its actual raw parameter type independently. -/
theorem StartAt.builtin_argument_represents_after
    {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    (prepared : Recipe.prepare compiled = .ok recipe)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (mapping : LocationMap) (context : SourceSemantics.Context) (heap : Dynamic.Heap)
    {artifact : Artifact} {before : Session artifact} {issued : Completion artifact}
    {function : BuiltinFunctionId} {issuanceFuel : Nat}
    (issuance : before.BuiltinIssuedAt function issuanceFuel issued)
    {session : Session artifact}
    (continued : issued.session.IssuanceChain session)
    {key : SourceCoreIndexedSession.Key} {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {checkpoint : Checkpoint artifact} {root : Root recipe.compiled}
    {world : StoreTyping} {store : Store} {native : Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session key arguments fuel checkpoint recipe root world store native encodedValues)
    {handle : Handle} (handleValue : issued.value = .function handle)
    {index : Nat} (found : arguments[index]? = some (.function handle)) :
    ∃ callable, before.SameRuntime issued.session ∧ issued.sourceType = function.type ∧
      native[index]? = some callable ∧
      ValueRep compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)
        mapping world function.type (.builtin ⟨function⟩) callable
        (CallableContract.functionType (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function)) ∧
      Dynamic.ValueHasType context heap (.builtin ⟨function⟩) function.type := by
  obtain ⟨expected, callable, same, sourceType, _budget, factory, selected⟩ :=
    RecursiveNamedPublicIssuedFunctionInputs.StartAt.builtin_argument_after issuance continued started handleValue found
  obtain ⟨actualType, builtinIndex, identity, descriptor, inventory, number, literal⟩ :=
    factory.prepared prepared
  refine ⟨callable, same, sourceType.trans actualType, selected, ?_, .builtin ⟨function⟩⟩
  rw [literal]
  exact .function (.builtin (.prior (.prior (.builtin
    (CallableIndexedBuiltinValues.Represents.builtin inventory number descriptor .nil)))))

/-- The original single-issuance interface is the empty continuation case. -/
theorem StartAt.builtin_argument_represents
    {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    (prepared : Recipe.prepare compiled = .ok recipe)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (mapping : LocationMap) (context : SourceSemantics.Context) (heap : Dynamic.Heap)
    {artifact : Artifact} {before : Session artifact} {issued : Completion artifact}
    {function : BuiltinFunctionId} {issuanceFuel : Nat}
    (issuance : before.BuiltinIssuedAt function issuanceFuel issued)
    {key : SourceCoreIndexedSession.Key} {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {checkpoint : Checkpoint artifact} {root : Root recipe.compiled}
    {world : StoreTyping} {store : Store} {native : Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt issued.session key arguments fuel checkpoint recipe root world store native encodedValues)
    {handle : Handle} (handleValue : issued.value = .function handle)
    {index : Nat} (found : arguments[index]? = some (.function handle)) :
    ∃ callable, before.SameRuntime issued.session ∧ issued.sourceType = function.type ∧
      native[index]? = some callable ∧
      ValueRep compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)
        mapping world function.type (.builtin ⟨function⟩) callable
        (CallableContract.functionType (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function)) ∧
      Dynamic.ValueHasType context heap (.builtin ⟨function⟩) function.type := by
  exact StartAt.builtin_argument_represents_after prepared headers keys bodyRegistry registry faults profile mapping
    context heap issuance (.refl _) started handleValue found

/-- The actual single builtin handle is passed through the root's complete raw
parameter signature. The receiving argument relation and Source typing are
constructed from issuance and preparation, with no argument proof premise. -/
theorem StartAt.builtin_arguments_receiving
    {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    (prepared : Recipe.prepare compiled = .ok recipe)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (mapping : LocationMap) (heap : Dynamic.Heap)
    {artifact : Artifact} {before : Session artifact} {issued : Completion artifact}
    {function : BuiltinFunctionId} {issuanceFuel : Nat}
    (issuance : before.BuiltinIssuedAt function issuanceFuel issued)
    {key : SourceCoreIndexedSession.Key} {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {checkpoint : Checkpoint artifact} {root : Root compiled}
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    {world : StoreTyping} {store : Store} {native : Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt issued.session key arguments fuel checkpoint recipe
      ((Recipe.prepare_compiled prepared).symm ▸ root) world store native encodedValues)
    (selected : RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) headers root header)
    {binding : CallableIndexedParameterCertificates.Binding}
    (sole : header.bindings = [binding]) (rawType : binding.1.scheme.body = function.type)
    (publicValues : arguments = [issued.value])
    {handle : Handle} (handleValue : issued.value = .function handle)
    (programTyped : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile))
      mapping world header.bindings [.builtin ⟨function⟩] native ∧
    Dynamic.ValuesHaveTypes header.function.context heap [.builtin ⟨function⟩] header.types := by
  have sameCompiled := Recipe.prepare_compiled prepared
  cases sameCompiled
  obtain ⟨callable, _same, _sourceType, argument, represented, sourceTyped⟩ :=
    StartAt.builtin_argument_represents prepared headers keys bodyRegistry registry faults profile mapping
      header.function.context heap issuance started handleValue
      (show arguments[0]? = some (.function handle) by rw [publicValues, handleValue]; rfl)
  have arity := congrArg List.length (header.parameters.symm.trans header.agreement.parameters)
  simp only [List.length_map, sole, List.length_cons, List.length_nil] at arity
  have nativeLength := congrArg List.length started.typed.type_tags
  rw [selected.shape.1] at nativeLength
  simp only [List.length_map] at nativeLength
  have nativeOne : native.length = 1 := nativeLength.trans arity.symm
  have nativeEq : native = [callable] := by
    cases native with
    | nil => simp at nativeOne
    | cons first rest =>
        have firstEq : first = callable := Option.some.inj argument
        have restNil : rest = [] := List.eq_nil_of_length_eq_zero (by simpa using nativeOne)
        rw [firstEq, restNil]
  have record := CallableIndexedActualNamedSourceReceipts.header_record recipe.compiled header
  have projected := RecursiveNamedHeaderParameterProjections.projections_of_record
    header rfl programTyped record
  rw [sole] at projected
  obtain ⟨actualType, remaining, projectedHead, _projectedTail, nativeTypes⟩ :=
    CompatibleEncoding.project_cons projected
  have actualTypeEq : actualType = binding.2 := (List.cons.inj nativeTypes).1.symm
  have projectedBuiltin : recipe.compiled.compatible.checked.catalog.project function.type = .ok binding.2 := by
    simpa only [rawType, actualTypeEq, SourceCoreCompatibleValues.Context.initial] using projectedHead
  have payloadType := Except.ok.inj (represented.projection.symm.trans projectedBuiltin)
  have typesEq : header.bindings.map (fun binding => binding.1.scheme.body) = header.types := by
    simpa only [header.parameters, List.map_map, Function.comp_def] using header.extended.bodyTypes_eq
  constructor
  · rw [sole, nativeEq]
    exact .cons (rawType.symm ▸ payloadType ▸ represented) .nil
  · rw [← typesEq, sole, List.map_cons, List.map_nil, rawType]
    exact .cons sourceTyped .nil

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicBuiltinArgumentReceipts
