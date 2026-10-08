import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicCatalogPreparedReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyReadyCatalog

/-! Genuine Source validity and typing supply sites independently from legacy
Catalog error receipts. Every predicate concerns this same selected Header;
the original reached Source receipt retains its heap and body typing. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedSourceSites
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open ProtectedStateTransition ProtectedStateImperativeCatalogReady
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  {expressionSyntax : ExpressionId → Prop}

/-- The complete solved ledger and independent Source validity travel together. -/
def Validity (context : SourceSemantics.Context) : Prop :=
  CompatibleRuntimeContextValidity.Valid header.solved context header.function.evidence ∧
    Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context header.function.source

theorem validity_at
    (source : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      header.context header.function.source) : Validity header header.context :=
  ⟨header.valid, source⟩

theorem validity_extend {context next : SourceSemantics.Context} {binder : TypedBinder}
    (valid : Validity header context)
    (extended : BinderExtends header.function.source.owner context binder next) : Validity header next :=
  ⟨valid.1.extend extended,
    valid.2.transport (Dynamic.RuntimeContextFields.ofBinderExtends extended)⟩

theorem signatures {context : SourceSemantics.Context} (valid : Validity header context) :
    context.signatures = compiled.compatible.checked.signatures :=
  valid.2.signatures.trans (CallableIndexedOwnedPublicSignatureCatalog.signatures compiled).symm

/-- Source body facts use independent Syntax and the actual typed parameter heap. -/
theorem body_facts {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    (source : CallableIndexedOwnedAdmittedBodyEntries.SourceReceipt (Program.ofChecked compiled.sourceProgram)
      header.function header.context environment heap)
    (syntaxTree : GenericImperativeMatch.Syntax header.function.source expressionSyntax header.context
      (.statements true header.function.body) header.function.resultType) :
    ProtectedStateImperativeTypedSourceSites.Facts header.function.source expressionSyntax
      header.context true header.function.body header.function.resultType := by
  obtain ⟨finalContext, facts, typed, _completes⟩ := source.bodyTyped
  exact ⟨syntaxTree, { returnType := header.function.resultType }, finalContext, facts, typed⟩

theorem assignment_sites : AssignmentSites
    (ProtectedStateImperativeTypedSourceSites.HeadFacts header.function.source expressionSyntax)
    (SourceAssignmentHasType header.function.source)
    (SourceBitNotAssignmentValid header.function.source) header.function.source where
  assignment := by
    intro context id expected node resolution operator rhs facts found form
    obtain ⟨mode, rest, _syntax, typed⟩ := facts
    exact ProtectedStateImperativeTypedSourceSites.assignment header.unique
      (ProtectedStateImperativeTypedSourceSites.head typed) found form
  snapshot := by
    intro context id expected node resolution facts found form
    obtain ⟨mode, rest, _syntax, typed⟩ := facts
    exact ProtectedStateImperativeTypedSourceSites.bit_not header.unique
      (ProtectedStateImperativeTypedSourceSites.head typed) found form

variable {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {protocol : Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (bindings : Bindings protocol)

/-- All static sites and state transfers are supplied by their original producers. -/
structure Inputs where
  sites : RecursiveNamedLexicalContracts.Stateful.WithReady.StaticSites
    (ProtectedStateImperativeTypedSourceSites.Facts header.function.source expressionSyntax)
    (ProtectedStateImperativeTypedSourceSites.HeadFacts header.function.source expressionSyntax)
    (ProtectedStateLexicalSourceSites.ExpressionFacts header.function.source)
    (Program.ofChecked compiled.sourceProgram) header.function.evidence header.function.source
  initializers : InitializerSites
    (ProtectedStateImperativeInitializerSourceSites.Facts header.function.source expressionSyntax)
    (CallableIndexedOwnedAdmittedForBounds.LoopFacts header.function.source expressionSyntax) header.function.source
  assignments : AssignmentSites
    (ProtectedStateImperativeTypedSourceSites.HeadFacts header.function.source expressionSyntax)
    (SourceAssignmentHasType header.function.source) (SourceBitNotAssignmentValid header.function.source) header.function.source
  transfers : RecursiveNamedLexicalContracts.Stateful.WithReady.AllocationTransfers
    protocol (readiness bridge) bindings header.function.source
  snapshots : ProtectedForHeader.Stateful.WithReady.SnapshotTransfers
    protocol (readiness bridge) (Validity header) (SourceBitNotAssignmentValid header.function.source)
    (Program.ofChecked compiled.sourceProgram) header.function.evidence header.function.source

/-- The actual Source graph and public well-formedness discharge these inputs. -/
theorem inputs (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (source : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) header.context header.function.source) :
    Inputs header bridge bindings (expressionSyntax := expressionSyntax) where
  sites := ProtectedStateImperativeTypedSourceSites.sites (Program.ofChecked compiled.sourceProgram)
    header.function.evidence source.graph
  initializers := ProtectedStateImperativeInitializerSourceSites.sites
  assignments := assignment_sites header
  transfers := CallableIndexedOwnedAdmittedLexicalReadiness.allocation_transfers bridge bindings header.function.source
  snapshots := CallableIndexedOwnedAdmittedForHeaderReadiness.snapshot_transfers bridge header.function.evidence
    wellFormed (Validity header) (fun _ valid => valid.2) (fun _ valid => valid.1.covers)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedSourceSites
