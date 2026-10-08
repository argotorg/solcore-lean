import Solcore.SourceSemantics.CoreLowering.NamedCallBodyFaultPostContracts
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCallEvidenceHeads

/-! A selected ordinary/direct call keeps its original root Source trace and
the low call route at the same returned tuple. Reflection's two Source grades
remain separate. The body post stays at the receipt's actual body store. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.NamedExpressionBodyFaultPostContracts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds CallableIndexedOwnedFunctionState
open NamedInvocationFaultPostContracts NamedCallBodyFaultPostContracts
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {registry : SourceCoreRawMetadata.Registry}
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {environment : Dynamic.Environment} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {canonical actual : Environment} {ξ : Renaming}
  {slots : ProtectedStateTransition.Index → Prop}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}

/-- The selected emission, root trace and low route describe one actual call.
The low call grade is retained independently from the reconstructed root grade. -/
def OuterCallRouteAt (post : BodyFaultPost)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) slots callerProtocol)
    (caller : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (callerPrefix : Nat) (reason : Word) (rootSize : Nat) (nativeSize : Option Nat)
    (id : ExpressionId) (root : ExpressionNode) (lowered : SourceCoreBasic.LoweredExpr)
    (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) (value : Value)
    (finalMap : LocationMap) (finalWorld : StoreTyping) (finalStore : Store) : Prop :=
  ∃ header : CallableIndexedOwnedFunctionValues.Header compiled program,
    ∃ callee ids codes callSize,
      header ∈ headers ∧
      root.form = .call callee ids (.declaration header.instantiation) ∧
      root.type = header.function.resultType ∧ lowered.type = header.output ∧
      lowered.expression.rename ξ = SourceCoreCalls.call header.named.signature
        (ξ (scope.length + callerPrefix + header.slot))
        ((SourceCoreCalls.packArguments codes).expression.rename ξ) reason ∧
      RecursiveNamedCallBounds.ExpressionOutcome program rootSize context evidence source environment before id outcome after ∧
      RecursiveNamedArgumentTraceBounds.TraceAt program context evidence header.function.evidence
        source environment before ids header.instantiation callSize outcome after ∧
      CallRouteAt (functions := functions) (registry := registry) (header := header)
        (source := source) (context := context) (evidence := evidence) (environment := environment)
        (ids := ids) (codes := codes) (actual := actual) (ξ := ξ)
        post owner bridge caller callSize nativeSize outcome after value finalMap finalWorld finalStore

/-- A fault token is obtained from that genuine route and its actual body/list
branch, preserving the emitted output type. -/
theorem fault_word {post : BodyFaultPost}
    {owner : CallableIndexedOwnedFunctionValues.OwnedKey keys}
    {bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) slots callerProtocol}
    {caller : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩}
    {callerPrefix rootSize : Nat} {reason : Word} {nativeSize : Option Nat}
    {id : ExpressionId} {root : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    {fault : Dynamic.SemanticFault} {after : Dynamic.Heap} {value : Value}
    {finalMap : LocationMap} {finalWorld : StoreTyping} {finalStore : Store}
    (route : OuterCallRouteAt (functions := functions) (registry := registry)
      (source := source) (context := context) (evidence := evidence) (environment := environment)
      (actual := actual) (ξ := ξ) post owner bridge caller callerPrefix reason rootSize nativeSize
      id root lowered (.fault fault) after value finalMap finalWorld finalStore) :
    ∃ token, value = .inLeft lowered.type (.word token) := by
  obtain ⟨header, callee, ids, codes, callSize, member, form, sourceType, output,
    emitted, sourceTrace, trace, retained⟩ := route
  cases retained with
  | argumentFailure failed smaller evaluation measured reached related =>
    exact ⟨_, by rw [output]⟩
  | bodyApplied evaluated argumentsSmaller called callSmaller argumentEvaluation argumentMeasured
      argumentState argumentRelated argumentMaps argumentWorlds argumentFrame argumentMetadata
      capture represented heaps bodyTrace bodySmaller bodyEvaluation bodyNative bodyMeasured receipt
      finalState bodyRelated bodyMaps bodyWorlds bodyFrame bodyMetadata returned samePool relatedCaller =>
    obtain ⟨origin, index, metadata, administrative, actualContext, actual, embedding, entry,
      parameterState, bodySize, bodyStore, bodyState, selected, history, bodyEmitted, parameterRelated,
      bodyRelated, trace, strict, completed, post, rest⟩ := receipt
    obtain ⟨token, same, bodyPost⟩ := post
    exact ⟨token, by simpa only [output] using same⟩

end Solcore.SourceSemantics.CoreLowering.NamedExpressionBodyFaultPostContracts
