import Solcore.SourceSemantics.CoreLowering.SelectedCompilationBuiltinFunctionOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCalleeStageReceipts

/-! Callable stage gates inspect genuine artifact origins. Prepared closure
bodies keep their own model; only actual builtin leaves require a contextual
representation for builtin execution. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCallableOrigins
open Core Frontend GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

class Origins
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) : Prop
    extends SelectedCompilationBuiltinFunctionOrigins.ErasesBuiltinsToContextual
      headers keys bodyRegistry faults profile functions where
  origin : ∀ {registry mapping world sourceType source native type},
    ValueRep compiled.compatible.checked registry functions mapping world sourceType source native type →
    IsFunction source → CallableLedger.OriginRep compiled.indexed.base.plan
      compiled.indexed.ancestry.graph.inputs.callable.table source native

instance of_erasure (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
    [CallableIndexedOwnedPositiveFunctionModels.ErasesToContextual headers keys bodyRegistry faults profile functions] :
    Origins headers keys bodyRegistry faults profile functions where
  toErasesBuiltinsToContextual := inferInstance
  origin := fun represented shape =>
    CallableIndexedOwnedContextualCalleeStageReceipts.callee_origin
      (CallableIndexedOwnedContextualCalleeOriginReadReceipts.callable_at profile
        (represented.map_functions
          (CallableIndexedOwnedPositiveFunctionModels.ErasesToContextual.erase
            (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry)
            (faults := faults) (profile := profile))) shape)

theorem prepared_origin
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {registry : SourceCoreRawMetadata.Registry} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {native : Value} {type : Core.Ty}
    (represented : ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry faults profile)
      mapping world sourceType source native type) :
    IsFunction source → CallableLedger.OriginRep compiled.indexed.base.plan
      compiled.indexed.ancestry.graph.inputs.callable.table source native := by
  induction represented using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) with
  | function related =>
    intro _shape
    cases related with
    | closure member => exact member.stage_origin
    | global member =>
      exact CallableIndexedOwnedContextualCalleeStageReceipts.function_origin
        (bodyRegistry := bodyRegistry) (faults := faults)
        (CallableIndexedOwnedContextualCellOrigins.FunctionOrigins.global member.represents)
    | builtin member =>
      exact CallableIndexedOwnedContextualCalleeStageReceipts.function_origin
        (CallableIndexedOwnedContextualCellOrigins.FunctionOrigins.builtin member)
  | compatible _ _ ih => exact ih
  | unit | bool | word | integer | product | proxy | constructed | mappingValue =>
    intro impossible; cases impossible
  | nil | cons | empty | entry | absent | present => trivial

instance prepared (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    Origins headers keys bodyRegistry faults profile
      (CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry faults profile) where
  toErasesBuiltinsToContextual := inferInstance
  origin := prepared_origin profile

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCallableOrigins
