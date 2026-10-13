import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds

/-! Internal call-head continuations for the shared structural expression proof.
Each continuation is indexed by an actual compiler receipt and its path in the
root certificate. Concrete invocation theorems construct these continuations
from strictly smaller body proofs and the reached protected state. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCallerHeadHandlers
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {caller : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) caller)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {code : SourceCoreBasic.LoweredExpr}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment}
  (model : GenericHeap.PayloadModel catalog projects definitions) (stages : Staging.Recursive.Registry) (faults : RecursiveStageMeaning.FaultRep)
  (budget : Nat)
  (root : Certificate policy body compilation readFuel (.initial compiled.compatible.checked)
    invocation.source context reasonAt scope id code)

def PreservesDirect : Prop :=
  ∀ {fuel scope id callee ids instantiation code types} (compiler : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Receipt policy body fuel compilation
      (.initial compiled.compatible.checked) invocation.source scope id callee ids instantiation reasonAt code),
    DirectCalls compiler root →
    DirectDeclarationCalleeValid context invocation.source callee instantiation →
    DeclarationApplicationValid context instantiation types compiler.node.type instantiation.predicates →
    DataExpressionSequence.Tree invocation.source
      (RecursiveStageTupleMeaning.Entries scope (ids.zip compiler.codes)) scope ids types compiler.codes →
    ∀ size, size ≤ budget →
      PreservesBelow bridge context model stages invocation
        (RecursiveStageTupleMeaning.Entries scope (ids.zip compiler.codes)) faults size →
      PreservesAt bridge context model stages invocation (Point scope id code) faults size

def PreservesMethod : Prop :=
  ∀ {fuel scope id code types} (compiler : CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt policy body fuel compilation
      (.initial compiled.compatible.checked) invocation.source scope id reasonAt code),
    MethodCalls compiler root →
    DataExpressionSequence.Tree invocation.source
      (RecursiveStageTupleMeaning.Entries scope (compiler.arguments.zip compiler.codes)) scope compiler.arguments types compiler.codes →
    ∀ size, size ≤ budget →
      PreservesBelow bridge context model stages invocation
        (RecursiveStageTupleMeaning.Entries scope (compiler.arguments.zip compiler.codes)) faults size →
      PreservesAt bridge context model stages invocation (Point scope id code) faults size

def PreservesIndirect : Prop :=
  ∀ {fuel scope id callee ids metadata code types} (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation
      invocation.source scope id callee ids metadata reasonAt code),
    Calls compiler root →
    DataExpressionSequence.Tree invocation.source
      (RecursiveStageTupleMeaning.Entries scope compiler.entries) scope ids types compiler.codes →
    ∀ size, size ≤ budget →
      PreservesBelow bridge context model stages invocation
        (RecursiveStageTupleMeaning.Entries scope compiler.entries) faults size →
      PreservesAt bridge context model stages invocation (Point scope id code) faults size

def ReflectsDirect : Prop :=
  ∀ {fuel scope id callee ids instantiation code types} (compiler : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Receipt policy body fuel compilation
      (.initial compiled.compatible.checked) invocation.source scope id callee ids instantiation reasonAt code),
    DirectCalls compiler root →
    DirectDeclarationCalleeValid context invocation.source callee instantiation →
    DeclarationApplicationValid context instantiation types compiler.node.type instantiation.predicates →
    DataExpressionSequence.Tree invocation.source
      (RecursiveStageTupleMeaning.Entries scope (ids.zip compiler.codes)) scope ids types compiler.codes →
    ∀ size, size ≤ budget →
      ReflectsBelow bridge context model stages invocation
        (RecursiveStageTupleMeaning.Entries scope (ids.zip compiler.codes)) faults size →
      ReflectsAt bridge context model stages invocation (Point scope id code) faults size

def ReflectsMethod : Prop :=
  ∀ {fuel scope id code types} (compiler : CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt policy body fuel compilation
      (.initial compiled.compatible.checked) invocation.source scope id reasonAt code),
    MethodCalls compiler root →
    DataExpressionSequence.Tree invocation.source
      (RecursiveStageTupleMeaning.Entries scope (compiler.arguments.zip compiler.codes)) scope compiler.arguments types compiler.codes →
    ∀ size, size ≤ budget →
      ReflectsBelow bridge context model stages invocation
        (RecursiveStageTupleMeaning.Entries scope (compiler.arguments.zip compiler.codes)) faults size →
      ReflectsAt bridge context model stages invocation (Point scope id code) faults size

def ReflectsIndirect : Prop :=
  ∀ {fuel scope id callee ids metadata code types} (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation
      invocation.source scope id callee ids metadata reasonAt code),
    Calls compiler root →
    DataExpressionSequence.Tree invocation.source
      (RecursiveStageTupleMeaning.Entries scope compiler.entries) scope ids types compiler.codes →
    ∀ size, size ≤ budget →
      ReflectsBelow bridge context model stages invocation
        (RecursiveStageTupleMeaning.Entries scope compiler.entries) faults size →
      ReflectsAt bridge context model stages invocation (Point scope id code) faults size

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCallerHeadHandlers
