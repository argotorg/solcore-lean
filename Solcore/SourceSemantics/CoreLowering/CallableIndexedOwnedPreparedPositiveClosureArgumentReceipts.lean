import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPositiveFunctionOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogIndirectArgumentReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredArgumentAlignment

/-! An accepted indirect closure call reconstructs its application packet at
the actual argument post. The positive callee supplies the genuine selected
compiler association. Source typing supplies its raw signature, while the
accepted physical count remains an independent input. Neither a body execution
law nor an application receipt is an input to this producer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPositiveClosureArgumentReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedContextualQualification (Facet)
open CallableIndexedOwnedPreparedPositiveFunctionOrigins
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {qualification : Facet compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {certificates : Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {index : ProtectedStateTransition.Index} (initial : callerProtocol.State index)
  {context : SourceSemantics.Context} (admitted : Admission bridge context initial)
  {source : TypedSource}
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  {calleeHeap : Dynamic.Heap} {function : Dynamic.Closure} {native : Value}
  {sourceTypes types : List TypeSystem.Ty} {arguments : List Dynamic.Value} {payloads : List Value}
  {parameter result sourceResultType : TypeSystem.Ty} {packed : Dynamic.Value}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)

local notation "positive" => functions qualification headers keys bodyRegistry faults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry positive

include compiler bridge initial admitted runtime in
/-- Both ordered argument rows are derived independently. The original typed
closure argument producer is then called once at this same reached state. -/
theorem closure_at_arguments
    (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
    {calleeType : TypeSystem.Ty}
    (calleeRelated : PayloadOrigins qualification headers keys bodyRegistry registry faults profile
      index.mapping index.world calleeType (.closure function) native compiler.calleeCode.type)
    (calleeTyped : Dynamic.ValueHasType context calleeHeap (.closure function) (.function parameter result))
    (extension : Dynamic.HeapTypesExtend calleeHeap index.heap)
    (represented : DataExpressionSequence.Values model index.mapping index.world
      sourceTypes (compiler.codes.map (·.type)) arguments payloads)
    (sourceBundle : TypeSystem.Ty.productMany sourceTypes = parameter)
    (physicalArity : arguments.length = function.parameters.length)
    (rawArguments : Dynamic.ValuesHaveTypes context index.heap arguments types)
    (packing : Dynamic.ValuesPack arguments packed)
    (rawBundle : TypeSystem.Ty.productMany types = parameter)
    (resultSame : sourceResultType = result) :
    ∃ actualSourceResult,
      SourceCoreRawMetadata.runtimeType sourceResultType = SourceCoreRawMetadata.runtimeType actualSourceResult ∧
      CallableIndexedOwnedPreparedCatalogIndirectInvocationDispatcher.Receipt
        (qualification := qualification) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
        (certificates := certificates) (expressionSyntax := expressionSyntax)
        (mapping := index.mapping) (world := index.world) (before := index.heap)
        (arguments := arguments) (payloads := payloads)
        positive (.closure function) function.evidence native actualSourceResult compiler.resultType := by
  obtain ⟨bindings, parameterCore, resultCore, ⟨packet⟩, _nativeType⟩ :=
    closure_member calleeRelated function rfl
  let association := packet.association
  have rawSignature := Dynamic.ValueHasType.closure_function_inv calleeTyped
  have compilerSignature : compiler.parameterType = parameterCore ∧ compiler.resultType = resultCore := by
    have accepted := compiler.callableType
    rw [actualFunctionType] at accepted
    exact CallableIndexedOwnedStoredNativePackReceipts.callable_parameters
      (accepted.trans (calleeRelated.runtime_hasType.type_eq.symm.trans association.native_type))
  have bindingCount : bindings.length = function.parameters.length := by
    simpa only [List.length_map] using congrArg List.length association.source_binders
  have sourcePacked : TypeSystem.Ty.productMany sourceTypes =
      TypeSystem.Ty.productMany (bindings.map (fun binding => binding.1.scheme.body)) :=
    sourceBundle.trans (rawSignature.1.trans (congrArg TypeSystem.Ty.productMany association.source_binders).symm)
  have nativePacked : SourceCoreCompatibleCatalog.packTypes (compiler.codes.map (·.type)) =
      SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :=
    (CompatibleExpressionConstructorNativeTyping.packed_type compiler.codes).symm.trans
      (compiler.packedType.symm.trans (compilerSignature.1.trans (association.parameter_core profile)))
  have binderArguments := CallableIndexedOwnedStoredArgumentAlignment.arguments_of_bundles
    bindings represented (physicalArity.trans bindingCount.symm) sourcePacked nativePacked
  refine ⟨function.resultType, congrArg SourceCoreRawMetadata.runtimeType (resultSame.trans rawSignature.2.1), ?_⟩
  rw [compilerSignature.2]
  exact CallableIndexedOwnedPreparedCatalogIndirectArgumentReceipts.closure positive bridge initial
    admitted runtime extension rawArguments packing rawBundle association calleeTyped binderArguments

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPositiveClosureArgumentReceipts
