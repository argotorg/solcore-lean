import Solcore.SourceSemantics.CoreLowering.PreparedAssignmentDiagnosticProducers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicUnaryAssignmentDiagnostics
import Solcore.SourceSemantics.CoreLowering.PreparedBranchingAssignmentDiagnostics
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicAssignmentDiagnostics
import Solcore.SourceSemantics.CoreLowering.CallableMethodBodyCoherence
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodSelectionIssuer
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedBranchingCollectors
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedPhysicalMixedScopedRoots
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedScopedSupport

/-! The accepted named scoped compiler action issues physical mixed roots at
each reached lexical context. Exact header slots cover reached declarations;
full method cache slots remain the responsibility of the physical state. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedPhysicalMixedScopedCollectors
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedStagedNamedBranchingReceipts (Receipt parameterScope)
open CallableIndexedOwnedPreparedStagedLexicalTree (TypedCertificate)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {recipe : SourceCoreIndexedSession.Recipe}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)

include aligned in
/-- Static child receipts are assembled into the same named branching support
consumed by the numeric body theorem. Source and native execution are absent
from the factory's premises. -/
def of_imperative_compiler
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {semanticFaults : FunctionCalls.FaultRep}
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    (receipt : Receipt header)
    (operands : ∀ {site assignment operator rhs},
      AssignmentDiagnosticOrigins.Occurs header.function.source site assignment operator rhs →
      (operator = .equal ∨ assignment.target.type = .word) →
      AssignmentOperandDiagnostics.OperandsLaw semanticFaults operator
        (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidOperand prepared site assignment.target.root operator))
    (unary : ∀ {site assignment}, GenericAssignmentUnaryDiagnostics.UnaryOccurs header.function.source site assignment →
      assignment.target.type = .word → semanticFaults (.invalidUnaryOperand .bitNot)
        (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidUnary prepared site assignment.target.root))
    (stages : Staging.Recursive.Registry)
    {expressionSyntax : ExpressionId → Prop}
    (syntaxTree : GenericImperativeMatch.Syntax header.function.source expressionSyntax
      header.context (.statements true header.function.body) header.function.resultType)
    (children : ∀ child, stages.Closure header.function child →
      ∀ context, Dynamic.RuntimeContextFields header.context context →
      ∀ {scope fuel id node lowered},
      CompatibleExpressionReads.ScopeDeclarations header.function.source scope context →
      expressionSyntax id → header.function.source.lookupExpression? id = some node →
      ExpressionHasType header.function.source context id node.type →
      header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
      ∀ {nativeType}, HasType (SourceCoreLocalCell.coreContext scope ++
        RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
        lowered.expression nativeType compiled.indexed.layouts.definitions →
      SelectedCompilationNamedScopedSupport.Certificate
        headers stages semanticFaults context child scope id lowered) :
    SelectedCompilationNamedScopedSupport.Support
      headers header stages receipt semanticFaults := by
  refine ⟨certified,
    RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection prepared,
    RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault prepared,
    PreparedAssignmentDiagnosticProducers.named prepared diagnostic aligned, ?_⟩
  intro child selected
  rw [stages.source selected]
  exact ⟨expressionSyntax, SelectedCompilationNamedBranchingCollectors.collected_of_imperative prepared aligned ready certified bodies.signatures member receipt operands unary syntaxTree (children child selected)⟩


include aligned in
/-- The actual prepared Header, per-site slots and source metadata issue
all mixed children without exposing a child execution premise. -/
def of_actual_with_catalog
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    {directSites : DeclarationInstantiation → Prop}
    (supported : ∀ instantiation, directSites instantiation →
      CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported compiled.indexed.base.plan instantiation)
    (metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      compiled.indexed prepared.named header.function.source directSites)
    {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
    (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    (covered : ∀ instantiation, directSites instantiation → ∀ index signature,
      SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan instantiation = .ok signature.key →
      compiled.indexed.base.globals[index]? = some signature →
      ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows,
        header.slot = index ∧ header.named.signature = signature)
        (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
    (methods : CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog compiled)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    (receipt : Receipt header)
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
    (syntaxTree : GenericImperativeMatch.Syntax header.function.source (fun id => GeneralSyntax header.function.source id directSites)
      header.context (.statements true header.function.body) header.function.resultType) :
    SelectedCompilationNamedScopedSupport.Support
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) header
      (RecursiveNamedPreparedStageScopes.registry actual) receipt
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := by
  have operands : ∀ {site assignment operator rhs},
      AssignmentDiagnosticOrigins.Occurs header.function.source site assignment operator rhs →
      (operator = .equal ∨ assignment.target.type = .word) →
      AssignmentOperandDiagnostics.OperandsLaw
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) operator
        (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidOperand prepared site assignment.target.root operator) := by
    intro site assignment operator rhs origin profile
    obtain ⟨first, assignmentPrepared⟩ := CallableIndexedOwnedPublicDiagnosticReceipts.assignments_at_header
      prepared diagnostic aligned
    exact PreparedBranchingAssignmentDiagnostics.operands assignmentPrepared
      (fun _ _ represented => CallableIndexedOwnedPublicAssignmentDiagnostics.prepared_operands
        prepared diagnostic receiver represented) origin profile
  have unary : ∀ {site assignment}, GenericAssignmentUnaryDiagnostics.UnaryOccurs header.function.source site assignment →
      assignment.target.type = .word → CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics
        (.invalidUnaryOperand .bitNot)
        (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidUnary prepared site assignment.target.root) := by
    intro site assignment origin rawWord
    obtain ⟨first, assignmentPrepared⟩ := CallableIndexedOwnedPublicDiagnosticReceipts.assignments_at_header
      prepared diagnostic aligned
    exact GenericAssignmentUnaryDiagnostics.prepared_unary_included assignmentPrepared
      (fun _ _ represented => CallableIndexedOwnedPublicUnaryAssignmentDiagnostics.prepared_unary
        prepared diagnostic receiver represented) origin rawWord
  apply of_imperative_compiler prepared aligned ready diagnostic bodies certified member receipt operands
    unary
    (RecursiveNamedPreparedStageScopes.registry actual) syntaxTree
  intro child selected context fields scope fuel id node lowered declarations approved found typed accepted nativeType native
  have sameSource := (RecursiveNamedPreparedStageScopes.registry actual).source selected
  obtain ⟨root, prefixEq⟩ := SelectedCompilationNamedPhysicalMixedScopedRoots.of_accepted_sites_with_catalog
    prepared aligned diagnostic receiver bodies certified supported metadata rows covered checked catalog methods actual selected fields
    (by simpa only [sameSource] using declarations) (by simpa only [sameSource] using approved)
    (by simpa only [sameSource] using found) (by simpa only [sameSource] using typed)
    (by simpa only [sameSource] using accepted)
  exact ⟨root, prefixEq⟩



end Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedPhysicalMixedScopedCollectors
