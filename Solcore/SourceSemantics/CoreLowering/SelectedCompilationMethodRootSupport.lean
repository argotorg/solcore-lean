import Solcore.SourceSemantics.CoreLowering.SelectedCompilationSourceSignatureFacts
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedSourceTyping
import Solcore.SourceSemantics.SelectedOperatorTypingCertificates
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationRootStaticSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOperatorMethodAuthority

/-! Static roots for expressions whose ordinary and trait calls use the actual
physical cache. Ports retain source selection and compilation evidence; the
numeric proof supplies every called-body law. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodRootSupport
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates
open SelectedCompilationRootStaticSupport (RootData)

/-- This first physical method family covers statically selected call sites. -/
def NoIndirect {compiled : SourceCoreUnifiedCompilation.Compiled}
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
    {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
    {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
    {expression : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (root : Certificate policy lowerBody compilation readFuel (.initial compiled.compatible.checked)
      invocation.source context reasonAt scope expression lowered) : Prop :=
  ∀ {fuel callScope callId callee ids metadata callCode}
    (compiler : CallableIndirectCallCertificates.Receipt policy lowerBody fuel compilation
      invocation.source callScope callId callee ids metadata reasonAt callCode),
    Calls compiler root → False

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
    Nonempty { port : CallableIndexedOwnedPreparedStagedDirectCallAuthority.PortWithEvidence
      compiler headers context invocation.evidence // SelectedCompilationNamedSourceTyping.Certified port.header ∧
        SelectedCompilationSourceSignatureFacts.Shape port.header }
  indexReady : CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority.IndexReady toRootData.certificate
  methodReady : ∀ {fuel callScope callId callCode}
    (compiler : CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt
      policy lowerBody fuel compilation (.initial compiled.compatible.checked)
      invocation.source callScope callId reasonAt callCode),
    MethodCalls compiler toRootData.certificate →
    Nonempty { port : CallableIndexedOwnedPreparedStagedOperatorMethodAuthority.Port
      (compiled := compiled) compiler context invocation.evidence stages //
      Dynamic.TypedOperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context invocation.evidence
        port.principal.traitName port.principal.methodName compiler.node.requirements
        port.principal.sourceBody port.principal.dictionary }
  noIndirect : NoIndirect (compiled := compiled) (invocation := invocation) toRootData.certificate

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

/-- Original syntax can exclude indirect calls independently of compiler certificates. -/
def NoIndirectSource (source : TypedSource) : Prop :=
  ∀ id node callee ids metadata, source.lookupExpression? id = some node →
    node.form = .call callee ids (.indirect metadata) → False

theorem NoIndirect.of_source
    (root : Certificate policy lowerBody compilation readFuel (.initial compiled.compatible.checked)
      invocation.source context reasonAt scope expression lowered)
    (syntaxOnly : NoIndirectSource invocation.source) :
    NoIndirect (compiled := compiled) (invocation := invocation) root := by
  intro fuel callScope callId callee ids metadata callCode compiler _path
  exact syntaxOnly callId compiler.original callee ids metadata compiler.found compiler.originalForm

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodRootSupport
