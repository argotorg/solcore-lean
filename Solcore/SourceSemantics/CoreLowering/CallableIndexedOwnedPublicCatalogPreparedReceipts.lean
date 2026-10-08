import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicTypedTokenReadyNamedExpressionBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicSignatureCatalog
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchCertificates

/-! Actual public Header extraction retains the chosen Catalog tree, diagnostic
plan and static match contexts together. The original body finish equation and
its independent Source syntax stay attached to the same compiler invocation. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicCatalogPreparedReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open RecursiveNamedCatalogNativeContexts NativeExpressionContextSupport
open RecursiveNamedCatalogRuntimeProfileFactory
open CallableIndexedOwnedPublicPreparedTokenReadyNamedExpressionBounds (PublicReceipt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {compilation : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → SourceCoreFunctions.Context}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  {administrative : Core.Context}

local notation "Γ" => SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative
local notation "certificates" => CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation header
local notation "headerScope" => bodyScope (prepared := compiled.indexed.ancestry)
  (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
  (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
  (program := Program.ofChecked compiled.sourceProgram) header

/-- Every field belongs to this public Header and its own retained diagnostic
producer. No interpreted profile or execution law is stored here. -/
structure CatalogReceipt (issued : PublicReceipt header) where
  first : Nat
  assignments : SourceCoreAssignmentFaultSites.prepare header.function.source first =
    .ok issued.original.prepared.compilation.own.assignments
  operandsTyped : AssignmentDiagnosticOrigins.OperandsTyped header.function.source
  unaryTyped : EmittedDiagnosticTokenPlan.UnaryTyped header.function.source
  catalog : SignatureCatalogWellFormed compiled.compatible.checked.signatures
  flow : Expr
  generated : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
    headerScope header.function.body header.output header.reasonAt true header.escaped = .ok flow
  finished : header.body = LocalControl.finish header.output (LocalLoop.toControl header.output flow header.escaped)
    (if header.output = .unit then LanguageResult.success .unit
      else LanguageResult.failure header.output (.word header.fellThrough))
  extracted : GenericImperativeMatch.CatalogCoupledExtractionFor .reachable header.layouts header.owner header.active
    compiled.indexed.ancestry.layout.frame header.globals header.onError (.initial compiled.compatible.checked)
    header.function.source (AssignmentDiagnosticOrigins.Factory.prepared operandsTyped assignments)
    (fun site root => issued.original.prepared.compilation.own.assignments.reasonAt site root .bitNot)
    (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection issued.original.prepared)
    (RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault issued.original.prepared)
    (expressionSyntax header) certificates compiled.indexed.layouts.definitions Γ header.solved
    header.context headerScope (.statements true header.function.body)
    header.function.resultType header.output flow

variable {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (complete : Complete (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
  (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers owner.key.locations 0 functions registry header arguments before initialStore mapping world
    administrative actualContext actual ξ frameLocation current ghost)

include functions owner complete entry in
/-- Real cached typing is transported to the actual ordinary parameter entry.
The same static Syntax traversal retains its genuine chosen Catalog receipts. -/
theorem at_entry (issued : PublicReceipt header)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (children : CallableIndexedOwnedNamedTokenProfileExtraction.Children
      (header := header) (headers := headers) (expressionSyntax := expressionSyntax) compilation Γ) :
    Nonempty (CatalogReceipt (headers := headers) (compilation := compilation)
      (expressionSyntax := expressionSyntax) (administrative := administrative) issued) := by
  obtain ⟨first, assignments⟩ := CallableIndexedOwnedPublicDiagnosticReceipts.assignments_at_header
    issued.original.prepared issued.diagnostic issued.original.aligned
  have rawTyped := SourceDiagnosticTyping.header_diagnostic_typed header wellFormed
  let sites := CallableIndexedOwnedNamedPublicProfileExtraction.policy_inputs
    issued.original.prepared issued.original.aligned compilation
    (CallableIndexedOwnedNamedTokenProfileExtraction.Children.to_static issued.original.prepared compilation
      rawTyped.2 assignments children)
  have typed := canonical_cached complete issued.original.aligned.globals
    (CallableIndexedOwnedNamedPublicProfileExtraction.cached_typed issued.original.prepared
      issued.original.aligned issued.original.nativeMember)
    (CallableIndexedOwnedNamedPublicProfileExtraction.cached_supported issued.original.accepted
      issued.original.prepared issued.original.aligned) entry
  have accepted := sites.accepted
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, same⟩ := CompatibleEncoding.bind_ok accepted
  have finished : header.body = LocalControl.finish header.output (LocalLoop.toControl header.output flow header.escaped)
      (if header.output = .unit then LanguageResult.success .unit
        else LanguageResult.failure header.output (.word header.fellThrough)) := (Except.ok.inj same).symm
  rw [finished] at typed
  obtain ⟨_, flowTyped⟩ := TypedLexicalWhile.Native.finished_flow typed
  obtain ⟨extracted⟩ := GenericImperativeMatch.extraction_of_typed_position_with_catalog_coupled true .reachable
    sites.factory sites.matchPolicy sites.matchValues sites.matchDefinitions sites.matchAllocator sites.matchChildStatic
    sites.readPolicy sites.binderPolicy sites.allocationPolicy sites.expressions sites.assignments sites.unaryPolicy
    header.unique sites.assignmentExpressions sites.syntaxTree
    (RecursiveNamedSourceContextFacts.header_typeVariables header) (RecursiveNamedSourceContextFacts.header_residual header)
    sites.sourceSignatures sites.declarations sites.projection generated flowTyped
  rw [sites.matchLedger] at extracted
  exact ⟨⟨first, assignments, rawTyped.2, rawTyped.1,
    CallableIndexedOwnedPublicSignatureCatalog.well_formed compiled wellFormed,
    flow, generated, finished, extracted⟩⟩

/-- The Header's original validity gives the exact solved ledger required by
the retained structural factory. It is independent of code and layout equality. -/
theorem ledger (_issued : PublicReceipt header) : header.context.solvedRequirements = header.solved :=
  header.valid.ledger

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicCatalogPreparedReceipts
