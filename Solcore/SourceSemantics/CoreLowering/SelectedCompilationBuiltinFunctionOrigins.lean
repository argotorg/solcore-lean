import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPositiveFunctionModels
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalCellOrigins

/-! Indirect builtin dispatch needs only the representation of an actual
builtin leaf. Prepared closure bodies remain in their own receiving model. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationBuiltinFunctionOrigins
open Core Frontend GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

class ErasesBuiltinsToContextual
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) : Prop where
  erase : ∀ {registry mapping world sourceType function native type},
    ValueRep compiled.compatible.checked registry functions mapping world sourceType (.builtin function) native type →
    ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)
      mapping world sourceType (.builtin function) native type

instance of_erasure (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
    [CallableIndexedOwnedPositiveFunctionModels.ErasesToContextual headers keys bodyRegistry faults profile functions] :
    ErasesBuiltinsToContextual headers keys bodyRegistry faults profile functions :=
  ⟨fun represented => represented.map_functions
    (CallableIndexedOwnedPositiveFunctionModels.ErasesToContextual.erase (headers := headers)
      (keys := keys) (bodyRegistry := bodyRegistry) (faults := faults) (profile := profile))⟩

theorem prepared_builtin
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {registry : SourceCoreRawMetadata.Registry} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {native : Value} {type : Core.Ty}
    (represented : ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry faults profile)
      mapping world sourceType source native type) :
    ∀ function, source = .builtin function →
      ValueRep compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)
        mapping world sourceType (.builtin function) native type := by
  induction represented using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) with
  | function related =>
    cases related with
    | builtin related => intro function same; cases same; exact .function (.builtin related)
    | global related => intro function impossible; cases impossible
    | closure related => intro function impossible; cases impossible
  | compatible same _ ih =>
    intro function selected
    exact .compatible same (ih function selected)
  | unit | bool | word | integer | product | proxy | constructed | mappingValue =>
    intro function impossible; cases impossible
  | nil | cons | empty | entry | absent | present => trivial

instance prepared (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    ErasesBuiltinsToContextual headers keys bodyRegistry faults profile
      (CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry faults profile) :=
  ⟨fun represented => prepared_builtin profile represented _ rfl⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationBuiltinFunctionOrigins
