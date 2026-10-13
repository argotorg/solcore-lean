import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodRootStaticSupport

/-! Static roots for expressions whose ordinary and trait calls use the actual
physical cache. Ports retain source selection and compilation evidence; the
numeric proof supplies every called-body law. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalMixedRootStaticSupport
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (RootData)

structure Root (compiled : SourceCoreUnifiedCompilation.Compiled)
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)))
    (stages : Staging.Recursive.Registry)
    (policy : SourceCoreFunctions.Policy) (lowerBody : SourceCoreFunctions.BodyLowerer)
    (compilation : SourceCoreFunctions.Context) (readFuel : Nat)
    (context : SourceSemantics.Context) (invocation : Staging.Recursive.Scope)
    (reasonAt : ExpressionId → Word) (scope : SourceCoreLocalCell.Scope)
    (expression : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr)
    (rawType : TypeSystem.Ty) (semanticFaults : FunctionCalls.FaultRep) extends
    RootData compiled policy lowerBody compilation readFuel context invocation
      reasonAt scope expression lowered rawType semanticFaults where
  directReady : ∀ {fuel callScope callId callee ids instantiation callCode}
    (compiler : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Receipt
      policy lowerBody fuel compilation (.initial compiled.compatible.checked)
      invocation.source callScope callId callee ids instantiation reasonAt callCode),
    DirectCalls compiler toRootData.certificate →
    Nonempty (CallableIndexedOwnedPreparedStagedDirectCallAuthority.PortWithEvidence
      compiler headers context invocation.evidence)
  indexReady : CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority.IndexReady toRootData.certificate
  methodReady : ∀ {fuel callScope callId callCode}
    (compiler : CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt
      policy lowerBody fuel compilation (.initial compiled.compatible.checked)
      invocation.source callScope callId reasonAt callCode),
    MethodCalls compiler toRootData.certificate →
    Nonempty (CallableIndexedOwnedPreparedStagedOperatorMethodAuthority.Port
      (compiled := compiled) compiler context invocation.evidence stages)

structure RootAt (compiled : SourceCoreUnifiedCompilation.Compiled)
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)))
    (stages : Staging.Recursive.Registry)
    (context : SourceSemantics.Context) (invocation : Staging.Recursive.Scope)
    (scope : SourceCoreLocalCell.Scope) (expression : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) (semanticFaults : FunctionCalls.FaultRep) where
  policy : SourceCoreFunctions.Policy
  lowerBody : SourceCoreFunctions.BodyLowerer
  compilation : SourceCoreFunctions.Context
  readFuel : Nat
  reasonAt : ExpressionId → Word
  rawType : TypeSystem.Ty
  support : Root compiled headers stages policy lowerBody compilation readFuel context invocation
    reasonAt scope expression lowered rawType semanticFaults

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {stages : Staging.Recursive.Registry}
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
    {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
    {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
    {expression : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {rawType : TypeSystem.Ty} {semanticFaults : FunctionCalls.FaultRep}

def RootAt.ofRoot
    (root : Root compiled headers stages policy lowerBody compilation readFuel context invocation
      reasonAt scope expression lowered rawType semanticFaults) :
    RootAt compiled headers stages context invocation scope expression lowered semanticFaults :=
  ⟨policy, lowerBody, compilation, readFuel, reasonAt, rawType, root⟩

/-- Existing method-only roots retain all their original static receipts. -/
def Root.ofMethod
    (root : CallableIndexedOwnedPreparedStagedMethodRootStaticSupport.Root
      compiled headers stages policy lowerBody compilation readFuel context invocation
      reasonAt scope expression lowered rawType semanticFaults) :
    Root compiled headers stages policy lowerBody compilation readFuel context invocation
      reasonAt scope expression lowered rawType semanticFaults :=
  ⟨root.toRootData, root.directReady, root.indexReady, root.methodReady⟩

def RootAt.ofMethod
    (root : CallableIndexedOwnedPreparedStagedMethodRootStaticSupport.RootAt
      compiled headers stages context invocation scope expression lowered semanticFaults) :
    RootAt compiled headers stages context invocation scope expression lowered semanticFaults :=
  ⟨root.policy, root.lowerBody, root.compilation, root.readFuel, root.reasonAt, root.rawType,
    Root.ofMethod root.support⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalMixedRootStaticSupport
