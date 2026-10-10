import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFiniteNamedInventories
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedHeaderPolicies

/-! The finite Header factory retains its selected diagnostic issuer. Transport
that actual preparation to the Header's literal owner and Source, then derive
the assignment table and every structural token equation from the same receipt.
No independent diagnostic identity or body execution law is supplied. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedDiagnosticSources
open Core Frontend SourceInference
open RecursiveNamedPublicSpecializationMeaning
open RecursiveNamedPreparedHeaderPolicies
open CallableIndexedOwnedPreparedFiniteNamedInventories
open CallableIndexedOwnedContextualLambdaSourceDiagnostics (IssuedSource)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {input : Input compiled}
  (receipt : Issued input)

/-- This is the freshly selected second pass used by the actual Header. -/
def prepared : Prepared compiled input.row :=
  CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared receipt.selected

theorem source : receipt.header.function.source = CallableIndexedNamedGeneration.source input.prepared.named := by
  rw [receipt.function]
  rfl

/-- Preserve the complete original preparation, including its first token,
inventory and typed Source. Only the owner and Source indices are transported. -/
def issuer : IssuedSource compiled receipt.header.owner receipt.header.function.source where
  first := receipt.selected.issued.first
  assignments := receipt.selected.issued.assignments
  assignmentsPrepared := by rw [source receipt]; exact receipt.selected.issued.assignmentsPrepared
  typing := by rw [source receipt]; exact receipt.selected.issued.typing
  plan := receipt.selected.issued.plan
  root := receipt.selected.issued.root
  extra := receipt.selected.issued.extra
  diagnostics := receipt.selected.issued.diagnostics
  prepared := receipt.selected.issued.prepared
  collected := by rw [receipt.aligned.owner, source receipt]; exact receipt.selected.issued.collected

theorem assignments : (issuer receipt).assignments = (prepared receipt).compilation.own.assignments :=
  receipt.selected.assignments

theorem assignments_prepared : SourceCoreAssignmentFaultSites.prepare receipt.header.function.source
    (issuer receipt).first = .ok (prepared receipt).compilation.own.assignments := by
  rw [← assignments receipt]
  exact (issuer receipt).assignmentsPrepared

theorem operand : (issuer receipt).invalidOperand = Prepared.invalidOperand (prepared receipt) := by
  funext site root operator
  simp only [IssuedSource.invalidOperand, Prepared.invalidOperand, GenericAssignmentDiagnostics.token,
    assignments receipt]

theorem unary : (issuer receipt).invalidUnary = Prepared.invalidUnary (prepared receipt) := by
  funext site root
  simp only [IssuedSource.invalidUnary, Prepared.invalidUnary, assignments receipt]

theorem projection : (issuer receipt).invalidProjection = Prepared.invalidProjection (prepared receipt) := by
  funext site root
  change receipt.selected.issued.diagnostics.program.placeReason receipt.header.owner site root none =
    (CallableIndexedOwnedSelectedDiagnosticIssuerReceipts.lowered compiled receipt.selected.diagnostics).placeReason
      input.prepared.named.signature.key site root none
  rw [receipt.aligned.owner]
  exact receipt.selected.places _ _ _ _

theorem missing : (issuer receipt).missingDefault = Prepared.missingDefault (prepared receipt) := by
  funext site root valueType
  change receipt.selected.issued.diagnostics.program.placeReason receipt.header.owner site root (some valueType) =
    (CallableIndexedOwnedSelectedDiagnosticIssuerReceipts.lowered compiled receipt.selected.diagnostics).placeReason
      input.prepared.named.signature.key site root (some valueType)
  rw [receipt.aligned.owner]
  exact receipt.selected.places _ _ _ _

/-- The receiving typed assignment factory comes from the retained issuer,
with the exact selected table; it does not demand another diagnostic receipt. -/
def factory : AssignmentDiagnosticOrigins.Factory true .reachable receipt.header.function.source
    (issuer receipt).invalidOperand :=
  AssignmentDiagnosticOrigins.Factory.prepared (issuer receipt).typing.2 (issuer receipt).assignmentsPrepared

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedDiagnosticSources
