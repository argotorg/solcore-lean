import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryStoredMembers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredNativePackReceipts

/-! The known chosen constructor and actual callee representation identify
the compiler's native argument bundle. Genuine Source arity and raw binder
types remain independent. The original parameter alignment consumes actual
argument values at their reached map and world without a payload inverse. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryArgumentBundles
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open CallableIndexedOwnedPreparedRuntimeFamilyMembers (OrdinaryIndex)
open CallableIndexedOwnedChosenOrdinaryStoredMembers (ChosenAt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {rootCompilation : Compilation compiled.indexed caller.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) caller.named diagnostics namedCode rootCompilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {i : OrdinaryIndex compiled} {history : History i.code}
  (member : ChosenAt root expressionSyntax headers keys registry faults i history)

include member in
/-- The original positive constructor already contains this native type. -/
theorem native_type :
    (value i.code i.captured.embedding history.native i.capturedActual).type =
      CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore := by
  cases member with
  | ordinary _ _ _ _ _ _ typed => exact typed.type_eq

variable {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource}
  {scope : SourceCoreLocalCell.Scope} {call callee : ExpressionId} {ids : List ExpressionId}
  {metadata : IndirectCallResolution} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt root.selected.policy root.selected.lowerBody fuel
    compilation source scope call callee ids metadata reasonAt lowered)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {raw : TypeSystem.Ty} {carrier : Value}
  (represented : ValueRep compiled.compatible.checked registry functions i.mapping i.world
    raw (.closure i.function) carrier compiler.calleeCode.type)
  (sameNative : carrier = value i.code i.captured.embedding history.native i.capturedActual)

include member represented sameNative in
/-- The actual root's callable convention and the same known callee fix
both native signature components; Source metadata is not inverted. -/
theorem compiler_parameters : compiler.parameterType = i.code.receipt.parameterCore ∧
    compiler.resultType = i.code.receipt.resultCore := by
  have actualType := represented.runtime_hasType.type_eq
  rw [sameNative] at actualType
  have selectedType := native_type root expressionSyntax member
  have accepted := compiler.callableType
  rw [root.callables] at accepted
  change CallableContract.functionType compiler.parameterType compiler.resultType = compiler.calleeCode.type at accepted
  exact CallableIndexedOwnedStoredNativePackReceipts.callable_parameters
    (accepted.trans (actualType.symm.trans selectedType))

include member represented sameNative in
/-- The real ordered compiler vector has the selected Code's packed type. -/
theorem compiler_parameter_pack :
    SourceCoreCompatibleCatalog.packTypes (compiler.codes.map (·.type)) = i.code.receipt.parameterCore :=
  (CompatibleExpressionConstructorNativeTyping.packed_type compiler.codes).symm.trans
    (compiler.packedType.symm.trans
      (compiler_parameters root expressionSyntax member compiler functions represented sameNative).1)

include member represented sameNative in
/-- Original parameter alignment uses actual values at the argument post.
Physical arity and raw Source bundle equality retain their own provenance. -/
theorem arguments_at_compiler
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {futureMap : LocationMap} {futureWorld : StoreTyping}
    (maps : LocationMap.Extends i.mapping futureMap) (worlds : WorldExtends i.world futureWorld)
    {sourceTypes : List TypeSystem.Ty} {arguments : List Dynamic.Value} {payloads : List Value}
    (values : DataExpressionSequence.Values
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      futureMap futureWorld sourceTypes (compiler.codes.map (·.type)) arguments payloads)
    (arity : i.function.parameters.length = arguments.length)
    (rawBundle : TypeSystem.Ty.productMany sourceTypes =
      TypeSystem.Ty.productMany (i.function.parameters.map (fun binder => binder.scheme.body))) :
    CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      futureMap futureWorld i.code.receipt.loweredParameters arguments payloads := by
  exact CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.arguments_of_bundles
    (i.captured.extend maps worlds) i.code i.support i.prepared functions profile values arity rawBundle
    (compiler_parameter_pack root expressionSyntax member compiler functions represented sameNative)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryArgumentBundles
