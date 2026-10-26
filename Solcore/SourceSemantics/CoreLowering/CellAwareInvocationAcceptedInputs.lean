import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedTerminals
import Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationAssignmentPolicy
import Solcore.SourceSemantics.CoreLowering.PreparedAssignmentReachedDiagnostics
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalCapturedScopes
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalDiagnosticIssuer
import Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationInitializerReceipt
import Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationResidualEntry

/-! Inputs of the accepted-body closure that are not statement flow: meaning of
the expressions the compiler actually accepted, the fault interpretation,
reached place diagnostics and identity views used by writes, and the inputs of
generalized declarations. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedInputs
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CellAwareInvocationAcceptedTerminals (children)

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {receiving : SourceCoreRawMetadata.Registry}
  {functions : FunctionModel whole.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions whole.indexed)}
  (index : ActualBodyInvocation.Index whole ActualBodyInvocation.ReachedView)
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep)

local notation "model" => CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions

/-- Accepted-expression meaning for every child the compiler lowered, at every
compiler fuel. This is the only expression input of the statement closure. -/
def Expressions (budget : Nat) : Prop :=
  ∀ fuel context, Dynamic.SourceRuntimeValid program context index.source →
    invocation.evidence.Covers context → context.solvedRequirements = index.compilation.solvedRequirements →
    CellAwareInvocationExpressionBounds.PreservesBelow (attachment := attachment) bridge context model index
      registry invocation (children index fuel) faults budget ∧
    CellAwareInvocationExpressionBounds.ReflectsBelow (attachment := attachment) bridge context model index
      registry invocation (children index fuel) faults budget

/-- Write inputs shared by statements and `for` header items: the metadata
registry extension, fault interpretation of the body's own diagnostic words,
reached place diagnostics at the actual compiler sites and identity views.
Operand and unary words are interpreted only at the typed assignment
occurrences of the Source, as reached place diagnostics are: a site without a
table entry yields the zero word for both kinds of fault. -/
structure Writes where
  extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial whole.compatible.checked).registry receiving
  operands : ∀ {context : SourceSemantics.Context} {site : SourceCoreElaboration.ErrorSite}
      {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId},
    AssignmentDiagnosticOrigins.Occurs invocation.source site assignment operator rhs →
    SourceAssignmentHasType invocation.source context assignment operator rhs →
    AssignmentOperandDiagnostics.OperandsLaw (fun reason token => faults (.semantic reason) token) operator
      (index.invalidOperand site assignment.target.root operator)
  unary : ∀ {context : SourceSemantics.Context} {site : SourceCoreElaboration.ErrorSite}
      {assignment : AssignmentResolution},
    GenericAssignmentUnaryDiagnostics.UnaryOccurs invocation.source site assignment →
    SourceBitNotAssignmentValid invocation.source context assignment →
    faults (.semantic (.invalidUnaryOperand .bitNot)) (index.invalidUnary site assignment.target.root)
  identities : Dynamic.Value → Word → Prop
  faithful : DataEquality.IdentityFaithful identities
  observations : CompatibleEquality.FunctionObservations whole.compatible.checked.catalog functions identities
  functionTypes : CompatiblePayload.FunctionRuntimeViews functions
  placeDiagnostics : PreparedAssignmentReachedDiagnostics.Ready (values := .initial whole.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions whole.indexed) functions protocol invocation.source
    index.invalidProjection index.missingDefault receiving (fun reason token => faults (.semantic reason) token)

/-- Inputs of generalized declarations: the captured-scope descriptor
attachment, the residual entry of a contextual invocation (trivial for named
rows), and the body's diagnostic issuer at every generalized initializer. -/
structure Generalized : Prop where
  attachment : attachment = GeneralizedLocalCapturedScopes.Attachment
  entry : index.ResidualEntry
  issuer : ∀ fuel scope initializer, GeneralizedLocalDiagnosticIssuer.Receipt whole.indexed
    (index.initializerInputs fuel scope initializer index.reasonAt)

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedInputs
