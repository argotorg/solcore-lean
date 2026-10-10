import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedContextualQualification
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSourceAdmission

/-! The qualified model has one genuine closure inversion and one reached
expression output. Both retain the original compiler qualification. Allocation,
write and nested payload operations are the existing generic operations. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedQualifiedExpressionOutputs
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedContextualQualification
open CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (qualification : Facet compiled)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {mapping : LocationMap} {world : StoreTyping}
  {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {native : Value} {type : Ty}

/-- The qualified leaf is installed at formation before generic payload
construction; no current or General leaf is upgraded. -/
theorem payload_static_member {function : Dynamic.Closure}
    {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}
    (member : StaticMember qualification headers keys bodyRegistry faults mapping world function native bindings parameter result) :
    PayloadOrigins qualification headers keys bodyRegistry registry faults profile mapping world
      (FunctionValues.sourceType function) (.closure function) native
      (CallableContract.functionType parameter result) :=
  .function (.closure member)

/-- A closure child keeps its actual qualification through compatible wrappers
and every genuine positive payload constructor. This is a Source-shape inverse. -/
theorem closure_member
    (origin : PayloadOrigins qualification headers keys bodyRegistry registry faults profile mapping world
      sourceType source native type) :
    ∀ function, source = .closure function →
      ∃ bindings parameter result,
        StaticMember qualification headers keys bodyRegistry faults mapping world function native bindings parameter result ∧
        type = CallableContract.functionType parameter result := by
  induction origin using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) with
  | function related =>
      cases related with
      | closure member =>
          intro function same
          cases same
          exact ⟨_, _, _, member, rfl⟩
      | global related => intro function impossible; cases impossible
      | builtin related => intro function impossible; cases impossible
  | compatible _ _ ih => exact ih
  | unit | bool | word | integer | product | proxy | constructed | mappingValue =>
      intro function impossible
      cases impossible
  | nil | cons | empty | entry | absent | present => trivial

/-- This is the original reached packet with qualified cells and the actual
qualified result. Its fields contain no body or family execution callback. -/
structure Post
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0}
      (CallableIndexedOwnedFunctionState.Records keys)}
    (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
      (fun _ => True) callerProtocol)
    (context : SourceSemantics.Context)
    (qualification : Facet compiled)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (sourceType : TypeSystem.Ty) (type : Ty)
    (outcome : Dynamic.ExpressionOutcome) (value : Value)
    {index : ProtectedStateTransition.Index} (reached : callerProtocol.State index) : Prop where
  admission : PostAdmission bridge context sourceType outcome reached
  cells : CellOrigins qualification headers keys bodyRegistry registry faults profile
    index.mapping index.world index.heap index.store
  result : FunctionCalls.ResultRepresents
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (functions qualification headers keys bodyRegistry faults profile))
    index.mapping index.world sourceType type faults outcome value

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedQualifiedExpressionOutputs
