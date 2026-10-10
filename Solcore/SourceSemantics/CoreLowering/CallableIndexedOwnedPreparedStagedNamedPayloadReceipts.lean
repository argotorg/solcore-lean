import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCellOrigins

/-! Positive global payloads retain the actual owned named Header, its complete
Source dictionary and original native code/capture. Compatible raw type wrappers
preserve their runtime type equality; they do not manufacture a literal Source
type equality. These projections supply neither a body law nor an application
result. The named staging scope and strict executed child remain separate. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedPayloadReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {mapping : LocationMap} {world : StoreTyping}
  {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {native : Value} {type : Ty}

/-- A positive global leaf has the original owned named relation. The wrapper
case retains its raw runtime type equality and the same native type/value. -/
theorem global_representation
    (origin : CallableIndexedOwnedContextualCellOrigins.PayloadOrigins
      headers keys bodyRegistry registry faults profile mapping world sourceType source native type) :
    ∀ function, source = .global function →
      ∃ originalType,
        CallableIndexedOwnedFunctionValues.Represents headers keys bodyRegistry faults mapping world
          originalType (.global function) native type ∧
        SourceCoreRawMetadata.runtimeType sourceType = SourceCoreRawMetadata.runtimeType originalType := by
  induction origin using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) with
  | function related =>
      cases related with
      | global related =>
          intro function same
          cases same
          cases related with
          | prior prior =>
              cases prior with
              | prior original => exact ⟨_, original, rfl⟩
      | closure member => intro function impossible; cases impossible
      | builtin related => intro function impossible; cases impossible
  | compatible same _ ih =>
      intro function selected
      obtain ⟨originalType, original, rawType⟩ := ih function selected
      exact ⟨originalType, original, same.trans rawType⟩
  | unit | bool | word | integer | product | proxy | constructed | mappingValue =>
      intro function impossible
      cases impossible
  | nil | cons | empty | entry | absent | present => trivial

/-- The actual positive global value exposes the same owned Header, capture,
Source instantiation, descriptor and full native callable code. Body execution
and global application meaning are absent from both premise and conclusion. -/
theorem named_payload
    (origin : CallableIndexedOwnedContextualCellOrigins.PayloadOrigins
      headers keys bodyRegistry registry faults profile mapping world sourceType source native type)
    (function : Dynamic.GlobalFunction) (selected : source = .global function) :
    ∃ owner : OwnedKey keys, ∃ header : Header compiled (Program.ofChecked compiled.sourceProgram),
      ∃ rawD identity, ∃ capture : NamedCapture headers owner.key header mapping world,
      ∃ descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
          (.named header.named.signature.key),
        header ∈ headers ∧ NamedSourceAt header rawD function ∧ NamedInstalledCode capture ∧
        Word.ofNat? (header.slot + 1) = some identity ∧
        compiled.compatible.checked.catalog.project header.named.specialized.function.type = .ok
          (CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType) ∧
        RuntimeValueHasType world (.closure header.named.signature.parameterType
          (LanguageResult.resultType header.named.signature.resultType)
          (header.code.rename capture.embedding.lift) capture.captured)
          header.named.signature.functionType compiled.indexed.layouts.definitions ∧
        SourceCoreRawMetadata.runtimeType sourceType =
          SourceCoreRawMetadata.runtimeType header.named.specialized.function.type ∧
        native = .pair (.pair (.inRight .unit (.word identity)) (.closure header.named.signature.parameterType
          (LanguageResult.resultType header.named.signature.resultType)
          (header.code.rename capture.embedding.lift) capture.captured)) (.word descriptor.id) ∧
        type = CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType := by
  obtain ⟨originalType, original, rawType⟩ := global_representation profile origin function selected
  obtain ⟨owner, header, rawD, identity, capture, descriptor, member, sourceAt, installed,
      number, projection, typed, originalTypeEq, nativeEq, nativeType⟩ := original.named_payload_inv
  exact ⟨owner, header, rawD, identity, capture, descriptor, member, sourceAt, installed,
    number, projection, typed, rawType.trans (congrArg SourceCoreRawMetadata.runtimeType originalTypeEq),
    nativeEq, nativeType⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedPayloadReceipts
