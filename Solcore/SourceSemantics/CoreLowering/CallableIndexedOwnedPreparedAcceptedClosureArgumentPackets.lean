import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPositiveClosureArgumentReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAcceptedIndirectPhysicalArity
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectSourceTypeRows
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogIndirectApplicationBounds

/-! The actual selected closure and accepted application gate construct the
indirect parent's argument factory. Ordered compiler and represented rows fix
physical arity. Original Source typing fixes the raw argument and result types.
No argument trace, body meaning or application law is retained by this factory. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedAcceptedClosureArgumentPackets
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedContextualQualification (Facet)
open CallableIndexedOwnedPreparedPositiveFunctionOrigins
open CallableIndexedOwnedIndirectSourceAdapters (SourceParent)
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
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate}
  {sourceTypes : List TypeSystem.Ty} {calleeNode : ExpressionNode}
  {mapping : LocationMap} {world : StoreTyping} {calleeHeap : Dynamic.Heap} {store : Store}
  {function : Dynamic.Closure} {native : Value} {canonical : Environment}
  {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}
  {unknown : Word} {sourceType : TypeSystem.Ty}

local notation "positive" => functions qualification headers keys bodyRegistry faults profile

include bridge compiler in
/-- The same selected descriptor and original Source parent close the factory
at every genuine admitted argument post. All body callbacks remain outside it. -/
theorem packets
    (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
    (parent : SourceParent compiler)
    (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
    (unique : NodeOccurrencesUnique source)
    (parentTyped : ExpressionHasType source context id compiler.original.type)
    (calleeFound : source.lookupExpression? callee = some calleeNode)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
    (calleeTyped : Dynamic.ValueHasType context calleeHeap (.closure function) calleeNode.type)
    (represented : PayloadOrigins qualification headers keys bodyRegistry registry faults profile
      mapping world sourceType (.closure function) native compiler.calleeCode.type)
    (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar)
      site site.call ids (.closure function) native)
    (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar site callee ids metadata
      compiler.original dispatch.row)
    (accepted : CallableContract.decision site.gates .beforeApplication unknown dispatch.contract = none) :
    CallableIndexedOwnedPreparedCatalogIndirectApplicationBounds.ArgumentPackets
      (qualification := qualification) (headers := headers) (keys := keys)
      (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (context := context) (invocation := function.evidence) (canonical := canonical)
      (mapping := mapping) (world := world) (calleeHeap := calleeHeap) (store := store)
      (function := .closure function) (calleeNative := native) (sourceTypes := sourceTypes)
      (sourceResultType := compiler.original.type) (resultCore := compiler.resultType)
      bridge positive compiler := by
  obtain ⟨sourceParameter, sourceResult, calleeType, _typedRows, sourceBundle, resultType⟩ :=
    CallableIndexedOwnedIndirectSourceTypeRows.original_rows compiler parent tree unique parentTyped calleeFound
  rw [calleeType] at calleeTyped
  have originalSignature := Dynamic.ValueHasType.closure_function_inv calleeTyped
  have physical := CallableIndexedOwnedAcceptedIndirectPhysicalArity.closure_count dispatch selected accepted
  intro middleMap middleWorld middle middleStore arguments payloads types parameter result packed
    argumentState admitted maps worlds _frame _metadata actualTyped extension rows _heaps rawArguments packing rawBundle
  have actualSignature := Dynamic.ValueHasType.closure_function_inv actualTyped
  have actualBundle : TypeSystem.Ty.productMany sourceTypes = parameter :=
    sourceBundle.trans (originalSignature.1.trans actualSignature.1.symm)
  have resultSame : compiler.original.type = result :=
    resultType.trans (originalSignature.2.1.trans actualSignature.2.1.symm)
  have argumentCount : arguments.length = function.parameters.length := by
    have ordered := compiler.ordered_children.1
    have representedCount : compiler.codes.length = arguments.length := by
      simpa only [List.length_map] using rows.length.1
    exact representedCount.symm.trans (ordered.symm.trans physical.symm)
  exact CallableIndexedOwnedPreparedPositiveClosureArgumentReceipts.closure_at_arguments
    bridge argumentState admitted runtime compiler actualFunctionType
    (represented.extend (SourceCoreRawMetadata.Extends.refl registry) maps worlds) actualTyped extension rows actualBundle argumentCount
    rawArguments packing rawBundle resultSame

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedAcceptedClosureArgumentPackets
