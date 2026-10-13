import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodRootStaticSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRawDirectAuthority
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionChain
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport

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

/-- Each conversion retains the genuine terminal method packet at its selected
Source body. Called-body execution is supplied by the shared induction. -/
def CoercionMethods {compiled : SourceCoreUnifiedCompilation.Compiled}
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)))
    {stages : Staging.Recursive.Registry} (semanticFaults : FunctionCalls.FaultRep)
    {project : SourceCoreEvidence.Projector} {compilation : SourceCoreFunctions.Context}
    {caller : SourceSpecialization.SpecializedFunction}
    {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {scope : SourceCoreBasic.Scope} {node : ExpressionNode}
    {policy : SourceCoreFunctions.CallablePolicy}
    {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
    {source target : TypeSystem.Ty} {input output : SourceCoreBasic.LoweredExpr}
    {steps : List CoercionStep} {calls : List CallableCoercionSpine.Call}
    (chain : CallableIndexedOwnedPreparedStagedCoercionChain.Chain
      compiled project compilation caller available scope node policy context invocation stages
      source target input steps output calls) : Prop :=
  match chain with
  | .nil => True
  | .cons _ port _ tail =>
      (∃ packet : CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport.Packet port.principal,
        packet.sourceAt = port.sourceAt ∧
        CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport.Support
          port.principal packet headers stages semanticFaults) ∧
      CoercionMethods headers semanticFaults tail

/-- The original call, its ordered argument roots and every conversion retain
actual compiler receipts. No source view is sanitized and no body law is stored. -/
structure CoercedDirectRoot (compiled : SourceCoreUnifiedCompilation.Compiled)
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)))
    (stages : Staging.Recursive.Registry)
    (policy : SourceCoreFunctions.Policy) (lowerBody : SourceCoreFunctions.BodyLowerer)
    (compilation : SourceCoreFunctions.Context) (readFuel : Nat)
    (context : SourceSemantics.Context) (invocation : Staging.Recursive.Scope)
    (reasonAt : ExpressionId → Word) (scope : SourceCoreLocalCell.Scope)
    (expression : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr)
    (resultType : TypeSystem.Ty) (semanticFaults : FunctionCalls.FaultRep) where
  compilerFuel : Nat
  accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody compilerFuel
    compilation invocation.source scope expression reasonAt = .ok lowered
  project : SourceCoreEvidence.Projector
  caller : SourceSpecialization.SpecializedFunction
  child : SourceCoreEvidence.Child
  fuel : Nat
  node : ExpressionNode
  callee : ExpressionId
  arguments : List ExpressionId
  instantiation : DeclarationInstantiation
  actual : CallableCoercionExpressionCertificates.Direct compiled.sourceProgram project caller
    compilation child fuel invocation.source scope expression callee arguments instantiation reasonAt
    policy.callables node lowered
  nonempty : node.coercions ≠ []
  result : node.type = resultType
  typed : ExpressionHasType invocation.source context expression node.type
  port : CallableIndexedOwnedPreparedStagedRawDirectAuthority.PortWithEvidence
    actual headers context invocation.evidence
  argumentTypes : List TypeSystem.Ty
  argumentCertificate : GenericExpressionMeaning.Certificate
  argumentTree : DataExpressionSequence.Tree invocation.source argumentCertificate
    scope arguments argumentTypes actual.loweredArguments
  argumentRoots : ∀ {current id code}, argumentCertificate current id code →
    ∃ rawType, Nonempty (Root compiled headers stages policy lowerBody compilation readFuel
      context invocation reasonAt current id code rawType semanticFaults)
  calls : List CallableCoercionSpine.Call
  chain : CallableIndexedOwnedPreparedStagedCoercionChain.Chain
    compiled project compilation caller actual.available scope node policy.callables context invocation stages
    node.rawType node.type actual.operand node.coercions lowered calls
  methods : CoercionMethods headers semanticFaults chain
  ledger : context.solvedRequirements = caller.function.solvedRequirements
  runtimeLedger : RuntimeRequirementLedgerValid context
  unique : NodeOccurrencesUnique invocation.source
  wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)
  runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
    context invocation.source
  covers : invocation.evidence.Covers context

/-- Both alternatives retain the same public expression and compiler indices. -/
inductive RootChoice (compiled : SourceCoreUnifiedCompilation.Compiled)
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)))
    (stages : Staging.Recursive.Registry)
    (policy : SourceCoreFunctions.Policy) (lowerBody : SourceCoreFunctions.BodyLowerer)
    (compilation : SourceCoreFunctions.Context) (readFuel : Nat)
    (context : SourceSemantics.Context) (invocation : Staging.Recursive.Scope)
    (reasonAt : ExpressionId → Word) (scope : SourceCoreLocalCell.Scope)
    (expression : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr)
    (rawType : TypeSystem.Ty) (semanticFaults : FunctionCalls.FaultRep) where
  | ordinary : Root compiled headers stages policy lowerBody compilation readFuel
      context invocation reasonAt scope expression lowered rawType semanticFaults →
      RootChoice compiled headers stages policy lowerBody compilation readFuel
        context invocation reasonAt scope expression lowered rawType semanticFaults
  | coercedDirect : CoercedDirectRoot compiled headers stages policy lowerBody compilation readFuel
      context invocation reasonAt scope expression lowered rawType semanticFaults →
      RootChoice compiled headers stages policy lowerBody compilation readFuel
        context invocation reasonAt scope expression lowered rawType semanticFaults

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
  support : RootChoice compiled headers stages policy lowerBody compilation readFuel context invocation
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
  ⟨policy, lowerBody, compilation, readFuel, reasonAt, rawType, .ordinary root⟩

def RootAt.ofChoice
    (root : RootChoice compiled headers stages policy lowerBody compilation readFuel context invocation
      reasonAt scope expression lowered rawType semanticFaults) :
    RootAt compiled headers stages context invocation scope expression lowered semanticFaults :=
  ⟨policy, lowerBody, compilation, readFuel, reasonAt, rawType, root⟩

instance : Coe (Root compiled headers stages policy lowerBody compilation readFuel context invocation
      reasonAt scope expression lowered rawType semanticFaults)
    (RootChoice compiled headers stages policy lowerBody compilation readFuel context invocation
      reasonAt scope expression lowered rawType semanticFaults) := ⟨RootChoice.ordinary⟩

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
    .ordinary (Root.ofMethod root.support)⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalMixedRootStaticSupport
