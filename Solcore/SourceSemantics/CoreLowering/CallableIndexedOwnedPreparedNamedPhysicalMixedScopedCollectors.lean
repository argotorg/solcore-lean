import Solcore.SourceSemantics.CoreLowering.PreparedAssignmentDiagnosticProducers
import Solcore.SourceSemantics.CoreLowering.CallableMethodBodyCoherence
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodSelectionIssuer
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedBranchingCollectors
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedPhysicalMixedScopedRoots
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalMixedNamedScopedStaticSupport

/-! The accepted named scoped compiler action issues physical mixed roots at
each reached lexical context. Exact header slots cover reached declarations;
full method cache slots remain the responsibility of the physical state. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedPhysicalMixedScopedCollectors
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
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
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
    (syntaxTree : GenericImperativeMatch.PreparedSyntax header.function.source expressionSyntax
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
      CallableIndexedOwnedPreparedStagedPhysicalMixedNamedScopedStaticSupport.Certificate
        headers stages semanticFaults context child scope id lowered) :
    CallableIndexedOwnedPreparedStagedPhysicalMixedNamedScopedStaticSupport.Support
      headers header stages receipt semanticFaults := by
  refine ⟨wellFormed,
    RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection prepared,
    RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault prepared,
    PreparedAssignmentDiagnosticProducers.named prepared diagnostic aligned, ?_⟩
  intro child selected
  rw [stages.source selected]
  exact ⟨expressionSyntax, CallableIndexedOwnedPreparedNamedBranchingCollectors.collected_of_imperative prepared aligned ready wellFormed member receipt operands unary syntaxTree (children child selected)⟩


include aligned in
/-- The actual prepared Header, per-site slots and source metadata issue
all mixed children without exposing a child execution premise. -/
def of_actual_with_catalog
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
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
    (syntaxTree : GenericImperativeMatch.PreparedSyntax header.function.source (fun id => GeneralSyntax header.function.source id directSites)
      header.context (.statements true header.function.body) header.function.resultType) :
    CallableIndexedOwnedPreparedStagedPhysicalMixedNamedScopedStaticSupport.Support
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) header
      (RecursiveNamedPreparedStageScopes.registry actual) receipt
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := by
  apply of_imperative_compiler prepared aligned ready diagnostic wellFormed member receipt
    (CallableIndexedOwnedPreparedNamedBranchingCollectors.operands_of_diagnostic prepared aligned diagnostic receiver)
    (CallableIndexedOwnedPreparedNamedBranchingCollectors.unary_of_diagnostic prepared aligned diagnostic receiver)
    (RecursiveNamedPreparedStageScopes.registry actual) syntaxTree
  intro child selected context fields scope fuel id node lowered declarations approved found typed accepted nativeType native
  have sameSource := (RecursiveNamedPreparedStageScopes.registry actual).source selected
  obtain ⟨root, prefixEq⟩ := CallableIndexedOwnedPreparedStagedNamedPhysicalMixedScopedRoots.of_accepted_sites_with_catalog
    prepared aligned diagnostic receiver wellFormed supported metadata rows covered checked catalog methods actual selected fields
    (by simpa only [sameSource] using declarations) (by simpa only [sameSource] using approved)
    (by simpa only [sameSource] using found) (by simpa only [sameSource] using typed)
    (by simpa only [sameSource] using accepted)
  exact ⟨root, prefixEq⟩



include aligned in
def of_actual_generic
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
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
    (methods : CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog compiled.sourceProgram)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    (receipt : Receipt header)
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
    (syntaxTree : GenericImperativeMatch.PreparedSyntax header.function.source (fun id => GeneralSyntax header.function.source id directSites)
      header.context (.statements true header.function.body) header.function.resultType) :
    CallableIndexedOwnedPreparedStagedPhysicalMixedNamedScopedStaticSupport.Support
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) header
      (RecursiveNamedPreparedStageScopes.registry actual) receipt
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := by
  exact of_actual_with_catalog prepared aligned ready diagnostic receiver wellFormed supported metadata rows covered checked catalog (CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog.generic methods) member receipt actual syntaxTree




include aligned in
def of_actual_with_evidence
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
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
    (methods : CallableIndexedOwnedPreparedStagedEvidenceMethodSelection.Catalog compiled)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    (receipt : Receipt header)
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
    (syntaxTree : GenericImperativeMatch.PreparedSyntax header.function.source (fun id => GeneralSyntax header.function.source id directSites)
      header.context (.statements true header.function.body) header.function.resultType) :
    CallableIndexedOwnedPreparedStagedPhysicalMixedNamedScopedStaticSupport.Support
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) header
      (RecursiveNamedPreparedStageScopes.registry actual) receipt
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := by
  exact of_actual_with_catalog prepared aligned ready diagnostic receiver wellFormed supported metadata rows covered checked catalog (CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog.evidence methods) member receipt actual syntaxTree




include aligned in
def of_actual
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
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
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog compiled.sourceProgram)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    (receipt : Receipt header)
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
    (syntaxTree : GenericImperativeMatch.PreparedSyntax header.function.source (fun id => GeneralSyntax header.function.source id directSites)
      header.context (.statements true header.function.body) header.function.resultType) :
    CallableIndexedOwnedPreparedStagedPhysicalMixedNamedScopedStaticSupport.Support
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) header
      (RecursiveNamedPreparedStageScopes.registry actual) receipt
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := by
  exact of_actual_generic prepared aligned ready diagnostic receiver wellFormed supported metadata rows covered checked catalog (CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog.of_closed methods) member receipt actual syntaxTree

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedPhysicalMixedScopedCollectors
