import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds

/-! Internal call-head continuations for the shared structural expression proof.
Each continuation is indexed by an actual compiler receipt and its path in the
root certificate. Concrete invocation theorems construct these continuations
from strictly smaller body proofs and the reached protected state. Each port
retains independent staged preservation and bounded ordinary lifting. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCallerHeadHandlers
open SelectedCompilationStageLiftBounds
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

def Laws (certificate : GenericExpressionMeaning.Certificate) : Prop :=
  (∀ size, PreservesAt bridge context model stages invocation certificate faults size) ∧
  (∀ size, size ≤ budget → LiftsAt bridge context model stages invocation certificate size)

theorem Laws.entries {current : SourceCoreLocalCell.Scope}
    {entries : List (ExpressionId × SourceCoreBasic.LoweredExpr)}
    (children : ∀ child code, (child, code) ∈ entries →
      Laws (context := context) (invocation := invocation) bridge model stages faults budget (Point current child code)) :
    Laws (context := context) (invocation := invocation) bridge model stages faults budget (RecursiveStageTupleMeaning.Entries current entries) := by
  constructor
  · intro size scope id lowered entry
    obtain ⟨rfl, member⟩ := entry
    exact (children id lowered member).1 size ⟨rfl, rfl, rfl⟩
  · intro size within scope id lowered entry
    obtain ⟨rfl, member⟩ := entry
    exact (children id lowered member).2 size within ⟨rfl, rfl, rfl⟩

def Direct : Prop :=
  ∀ {fuel scope id callee ids instantiation code types} (compiler : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Receipt policy body fuel compilation
      (.initial compiled.compatible.checked) invocation.source scope id callee ids instantiation reasonAt code),
    DirectCalls compiler root →
    DirectDeclarationCalleeValid context invocation.source callee instantiation →
    DeclarationApplicationValid context instantiation types compiler.node.type instantiation.predicates →
    DataExpressionSequence.Tree invocation.source
      (RecursiveStageTupleMeaning.Entries scope (ids.zip compiler.codes)) scope ids types compiler.codes →
    (∀ size, PreservesBelow bridge context model stages invocation
        (RecursiveStageTupleMeaning.Entries scope (ids.zip compiler.codes)) faults size →
      PreservesAt bridge context model stages invocation (Point scope id code) faults size) ∧
    (∀ size, size ≤ budget →
      (∀ childSize, childSize < size → LiftsAt bridge context model stages invocation
        (RecursiveStageTupleMeaning.Entries scope (ids.zip compiler.codes)) childSize) →
      (∀ childSize, PreservesAt bridge context model stages invocation
        (RecursiveStageTupleMeaning.Entries scope (ids.zip compiler.codes)) faults childSize) →
      LiftsAt bridge context model stages invocation (Point scope id code) size)

def Method : Prop :=
  ∀ {fuel scope id code types} (compiler : CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt policy body fuel compilation
      (.initial compiled.compatible.checked) invocation.source scope id reasonAt code),
    MethodCalls compiler root →
    DataExpressionSequence.Tree invocation.source
      (RecursiveStageTupleMeaning.Entries scope (compiler.arguments.zip compiler.codes)) scope compiler.arguments types compiler.codes →
    (∀ size, PreservesBelow bridge context model stages invocation
        (RecursiveStageTupleMeaning.Entries scope (compiler.arguments.zip compiler.codes)) faults size →
      PreservesAt bridge context model stages invocation (Point scope id code) faults size) ∧
    (∀ size, size ≤ budget →
      (∀ childSize, childSize < size → LiftsAt bridge context model stages invocation
        (RecursiveStageTupleMeaning.Entries scope (compiler.arguments.zip compiler.codes)) childSize) →
      (∀ childSize, PreservesAt bridge context model stages invocation
        (RecursiveStageTupleMeaning.Entries scope (compiler.arguments.zip compiler.codes)) faults childSize) →
      LiftsAt bridge context model stages invocation (Point scope id code) size)

def Indirect : Prop :=
  ∀ {fuel scope id callee ids metadata code types} (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation
      invocation.source scope id callee ids metadata reasonAt code),
    Calls compiler root →
    DataExpressionSequence.Tree invocation.source
      (RecursiveStageTupleMeaning.Entries scope compiler.entries) scope ids types compiler.codes →
    (∀ size, PreservesBelow bridge context model stages invocation
        (RecursiveStageTupleMeaning.Entries scope compiler.entries) faults size →
      PreservesAt bridge context model stages invocation (Point scope id code) faults size) ∧
    (∀ size, size ≤ budget →
      (∀ childSize, childSize < size → LiftsAt bridge context model stages invocation
        (RecursiveStageTupleMeaning.Entries scope compiler.entries) childSize) →
      (∀ childSize, PreservesAt bridge context model stages invocation
        (RecursiveStageTupleMeaning.Entries scope compiler.entries) faults childSize) →
      LiftsAt bridge context model stages invocation (Point scope id code) size)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCallerHeadHandlers
