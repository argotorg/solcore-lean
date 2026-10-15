import Solcore.SourceSemantics.CoreLowering.SelectedCompilationHeaderFacts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeBranchingCollectors
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLexicalContextCertificates
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBranchingReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedPublicProfileExtraction
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedHeaderPolicies
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedLexicalCollectors
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedDirectNamedProfileExtraction
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicSignatureCatalog

/-! The original checked named body supplies native typing of every actual
lexical child. Original Source syntax and binder context transport feed only
static expression factories, then the generic compiler traversal retains the
same accepted allocations and finish code. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedBranchingCollectors
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedStagedNamedBranchingReceipts (Receipt parameterScope)
open CallableIndexedOwnedPreparedStagedLexicalTree (TypedCertificate)
open CallableIndexedOwnedPreparedLexicalContextCertificates
open CallableLambdaViewEdits CallableLambdaBodyReachability

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {recipe : SourceCoreIndexedSession.Recipe}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)

include aligned in
/-- Child factories receive only original syntax/typing, actual callback
acceptance and native typing, at the context reached by real lexical binders. -/
theorem tree
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    (receipt : Receipt header)
    {expressionSyntax : ExpressionId → Prop}
    {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    (syntaxTree : GenericLexicalStatements.Syntax header.function.source expressionSyntax
      header.context true header.function.body header.function.resultType)
    (children : ∀ context, Dynamic.RuntimeContextFields header.context context →
      ∀ {scope fuel id node lowered},
      CompatibleExpressionReads.ScopeDeclarations header.function.source scope context →
      expressionSyntax id → header.function.source.lookupExpression? id = some node →
      ExpressionHasType header.function.source context id node.type →
      header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
      ∀ {nativeType}, HasType (SourceCoreLocalCell.coreContext scope ++
        RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
        lowered.expression nativeType compiled.indexed.layouts.definitions →
      certificates context scope id lowered) :
    GenericLexicalStatements.Tree header.layouts header.owner header.active compiled.indexed.ancestry.layout.frame
      header.globals header.onError (.initial compiled.compatible.checked) header.function.source
      (TypedCertificate header.function.source certificates)
      header.context (parameterScope header) true header.function.body header.function.resultType header.output receipt.flow := by
  have body := CallableIndexedOwnedPreparedNamedLexicalCollectors.body_typed prepared aligned ready member
  rw [receipt.emitted] at body
  obtain ⟨nativeType, flowTyped⟩ := TypedLexicalWhile.Native.finished_flow body
  have retained := certified
  obtain ⟨_, certificate⟩ := retained
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      header.function.context header.function.source := by
    rw [header.frame.context, header.frame.source]
    exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid
  have runtime := runtime.transport (RecursiveNamedInitialContextValidity.mono_fields header.extended)
  have declarations := RecursiveNamedHeaderScopeDeclarations.header_scope
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    (prepared := compiled.indexed.ancestry) (program := Program.ofChecked compiled.sourceProgram) header
  have extracted := CallableIndexedOwnedPreparedNativeLexicalCollectors.tree_of_typed_flow_with_residual true
    (values := .initial compiled.compatible.checked)
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned)
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_binder prepared aligned)
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_allocator prepared aligned)
    (certificates := fun context scope id lowered => Dynamic.RuntimeContextFields header.context context →
      TypedCertificate header.function.source certificates context scope id lowered)
    (fun context _closed _residual _signatures scope fuel id node lowered declarations approved found typed accepted nativeType native fields =>
      ⟨node, found, typed, children context fields declarations approved found typed accepted native⟩)
    syntaxTree runtime.variables_closed runtime.residual_variables_open
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_signatures (header := header)) declarations
    receipt.projection receipt.accepted flowTyped
  exact Tree.discharge_context extracted (.refl _)


include aligned in
/-- Child factories receive only original syntax/typing, actual callback
acceptance and native typing, at the context reached by real lexical binders. -/
theorem collected_of_imperative
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    (catalog : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    (receipt : Receipt header)
    {faults : FunctionCalls.FaultRep}
    (operands : ∀ {site assignment operator rhs},
      AssignmentDiagnosticOrigins.Occurs header.function.source site assignment operator rhs →
      (operator = .equal ∨ assignment.target.type = .word) →
      AssignmentOperandDiagnostics.OperandsLaw faults operator
        (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidOperand prepared site assignment.target.root operator))
    (unary : ∀ {site assignment}, GenericAssignmentUnaryDiagnostics.UnaryOccurs header.function.source site assignment →
      assignment.target.type = .word → faults (.invalidUnaryOperand .bitNot)
        (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidUnary prepared site assignment.target.root))
    {expressionSyntax : ExpressionId → Prop}
    {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    (syntaxTree : GenericImperativeMatch.Syntax header.function.source expressionSyntax
      header.context (.statements true header.function.body) header.function.resultType)
    (children : ∀ context, Dynamic.RuntimeContextFields header.context context →
      ∀ {scope fuel id node lowered},
      CompatibleExpressionReads.ScopeDeclarations header.function.source scope context →
      expressionSyntax id → header.function.source.lookupExpression? id = some node →
      ExpressionHasType header.function.source context id node.type →
      header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
      ∀ {nativeType}, HasType (SourceCoreLocalCell.coreContext scope ++
        RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
        lowered.expression nativeType compiled.indexed.layouts.definitions →
      certificates context scope id lowered) :
    CallableIndexedOwnedPreparedBranchingCatalogSites.Collected (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection prepared)
      (RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault prepared) (faults := faults) header.layouts header.owner header.active compiled.indexed.ancestry.layout.frame
      header.globals header.onError (.initial compiled.compatible.checked) header.function.source expressionSyntax
      (TypedCertificate header.function.source certificates) compiled.indexed.layouts.definitions
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      header.context (parameterScope header) (.statements true header.function.body) header.function.resultType header.output receipt.flow := by
  have body := CallableIndexedOwnedPreparedNamedLexicalCollectors.body_typed prepared aligned ready member
  rw [receipt.emitted] at body
  obtain ⟨nativeType, flowTyped⟩ := TypedLexicalWhile.Native.finished_flow body
  have retained := certified
  obtain ⟨_, certificate⟩ := retained
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      header.function.context header.function.source := by
    rw [header.frame.context, header.frame.source]
    exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid
  have runtime := runtime.transport (RecursiveNamedInitialContextValidity.mono_fields header.extended)
  have declarations := RecursiveNamedHeaderScopeDeclarations.header_scope
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    (prepared := compiled.indexed.ancestry) (program := Program.ofChecked compiled.sourceProgram) header
  have assignments : CompatibleAssignmentStatements.AssignmentPolicy header.policy
      (.initial compiled.compatible.checked)
      (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection prepared)
      (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidOperand prepared)
      (RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault prepared) := by
    rw [aligned.policy]
    exact RecursiveNamedPreparedHeaderPolicies.Prepared.assignments prepared
  have unaryPolicy : CompatibleBitNotStatements.Policy header.policy
      (.initial compiled.compatible.checked)
      (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection prepared)
      (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidUnary prepared)
      (RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault prepared) := by
    rw [aligned.policy]
    exact RecursiveNamedPreparedHeaderPolicies.Prepared.unary prepared
  exact CallableIndexedOwnedPreparedNativeBranchingCollectors.collected
    (expressionSyntax := expressionSyntax) (certificates := certificates) (LocalView.refl _)
    (by intro id member; cases member) header.unique
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned)
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_binder prepared aligned)
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_allocator prepared aligned)
    assignments unaryPolicy operands unary
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_match prepared aligned) rfl rfl
    (RecursiveNamedPreparedHeaderPolicies.Prepared.match_allocator prepared aligned)
    (SelectedCompilationHeaderFacts.hidden_fresh certified)
    ((CallableIndexedOwnedPublicSignatureCatalog.signatures compiled).symm ▸ catalog)
    (header.valid.ledger.trans aligned.solved)
    (fun context fields scope fuel id node lowered declarations approved _reached found typed accepted nativeType native =>
      children context fields (scope := scope) (fuel := fuel) (id := id) (node := node)
        (lowered := lowered) declarations approved found typed accepted (nativeType := nativeType) native)
    syntaxTree rfl receipt.shape (.refl _) runtime.variables_closed runtime.residual_variables_open
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_signatures (header := header))
    declarations (fun id member => .root (List.mem_map.mpr ⟨id, member, rfl⟩))
    receipt.projection receipt.accepted flowTyped


end Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedBranchingCollectors
