import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.MixedBodyCompiler
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedCanonicalSupport
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ProfileExtraction
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.RuntimeProfileFactories
import Solcore.SourceSemantics.CoreLowering.Internal.Diagnostics.PreparedAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ChosenStoredCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.PreparedBranching
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.DecodedCallFaults
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NativeCollectors
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.FormationReceipts
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CoercionSpine
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MethodScopedRoots
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedEvidenceRoots
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.PhysicalMixedFamilies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.OrdinaryCatalog
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.ScopedSourceBodies
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaOrigins

/-!
# Prepared callables: named collectors

Collectors of named bodies by form, and syntax, scoped and catalog admission.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedLexicalCollectors
/-! The original checked named body supplies native typing of every actual
lexical child. Original Source syntax and binder context transport feed only
static expression factories, then the generic compiler traversal retains the
same accepted allocations and finish code. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedLexicalCollectors
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedStagedNamedLexicalReceipts (Receipt parameterScope)
open CallableIndexedOwnedPreparedStagedLexicalTree (TypedCertificate)
open CallableIndexedOwnedPreparedLexicalContextCertificates

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {recipe : SourceCoreIndexedSession.Recipe}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)

include aligned in
/-- Successful public preparation bounds the real cached lambda's used
slots, so the original native input suffix can be removed. -/
theorem body_typed
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries) :
    HasType (SourceCoreLocalCell.coreContext (parameterScope header) ++
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      header.body (LanguageResult.resultType header.output) compiled.indexed.layouts.definitions := by
  have cached := CallableIndexedOwnedNamedPublicProfileExtraction.cached_typed prepared aligned member
  have original : HasType ((compiled.indexed.base.globals.map (·.referenceType) ++
      [.cell compiled.indexed.ancestry.layout.frame.type]) ++
        SourceCoreGeneralEntry.nativeInputContext entry.native.inputTypes)
      (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code)
      header.named.signature.functionType (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions := by
    simpa only [List.append_assoc, List.singleton_append] using cached
  have minimal := NativeExpressionContextSupport.prefix_typing (targetSuffix := []) original
    (by simpa only [List.length_append, List.length_map, List.length_singleton] using
      CallableIndexedOwnedNamedPublicProfileExtraction.cached_supported ready prepared aligned)
  have body := RecursiveNamedCatalogNativeContexts.body_of_cached (suffix := [])
    (values := .initial compiled.compatible.checked)
    (program := Program.ofChecked compiled.sourceProgram)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (header := header) (by simpa only [List.append_nil, List.append_assoc, List.singleton_append,
      CallableIndexedAmbient.ambientDefinitions, SourceCoreCompatibleValues.Context.initial] using minimal)
  change HasType _ _ _ compiled.indexed.layouts.definitions at body
  simpa only [parameterScope, RecursiveNamedCatalogNativeContexts.bodyPrefix, RecursiveNamedCatalogNativeContexts.bodyScope,
    RecursiveNamedLambdaFormationHeads.nativePrefix, List.append_nil, List.append_assoc, ← header.parameterType] using body

include aligned in
/-- Child factories receive only original syntax/typing, actual callback
acceptance and native typing, at the context reached by real lexical binders. -/
theorem tree
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
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
  have body := body_typed prepared aligned ready member
  rw [receipt.emitted] at body
  obtain ⟨nativeType, flowTyped⟩ := TypedLexicalWhile.Native.finished_flow body
  obtain ⟨_, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
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
/-- Static child receipts are assembled into the same named lexical support
consumed by the numeric body theorem. Source and native execution are absent
from the factory's premises. -/
def of_compiler
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
    {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
    (zero : ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys, owner.key.capturePrefix = 0)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    (receipt : Receipt header) (stages : Staging.Recursive.Registry)
    {expressionSyntax : ExpressionId → Prop}
    (syntaxTree : GenericLexicalStatements.Syntax header.function.source expressionSyntax
      header.context true header.function.body header.function.resultType)
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
      CallableIndexedOwnedPreparedStagedNamedLexicalSupport.Certificate
        header bodyRegistry semanticFaults context child scope id lowered) :
    CallableIndexedOwnedPreparedStagedNamedLexicalSupport.Support
      headers keys bodyRegistry header stages receipt semanticFaults := by
  refine ⟨complete, zero, wellFormed, ?_⟩
  intro child selected
  rw [stages.source selected]
  exact tree prepared aligned ready wellFormed member receipt syntaxTree (children child selected)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedLexicalCollectors
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedBranchingCollectors
/-! The original checked named body supplies native typing of every actual
lexical child. Original Source syntax and binder context transport feed only
static expression factories, then the generic compiler traversal retains the
same accepted allocations and finish code. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedBranchingCollectors
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
/-- The real named preparation and receiving issuer retain the exact operand diagnostic. -/
theorem operands_of_diagnostic
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    {site assignment operator rhs}
    (origin : AssignmentDiagnosticOrigins.Occurs header.function.source site assignment operator rhs)
    (profile : operator = .equal ∨ assignment.target.type = .word) :
    AssignmentOperandDiagnostics.OperandsLaw
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) operator
      (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidOperand prepared site assignment.target.root operator) := by
  obtain ⟨first, assignmentPrepared⟩ := CallableIndexedOwnedPublicDiagnosticReceipts.assignments_at_header
    prepared diagnostic aligned
  exact PreparedBranchingAssignmentDiagnostics.operands assignmentPrepared
    (fun _ _ represented => CallableIndexedOwnedPublicAssignmentDiagnostics.prepared_operands
      prepared diagnostic receiver represented) origin profile


include aligned in
/-- The prepared original table and actual public receiver retain unary tokens. -/
theorem unary_of_diagnostic
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    {site assignment}
    (origin : GenericAssignmentUnaryDiagnostics.UnaryOccurs header.function.source site assignment)
    (rawWord : assignment.target.type = .word) :
    CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics
      (.invalidUnaryOperand .bitNot)
      (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidUnary prepared site assignment.target.root) := by
  obtain ⟨first, assignmentPrepared⟩ := CallableIndexedOwnedPublicDiagnosticReceipts.assignments_at_header
    prepared diagnostic aligned
  exact GenericAssignmentUnaryDiagnostics.prepared_unary_included assignmentPrepared
    (fun _ _ represented => CallableIndexedOwnedPublicUnaryAssignmentDiagnostics.prepared_unary
      prepared diagnostic receiver represented) origin rawWord


include aligned in
/-- Child factories receive only original syntax/typing, actual callback
acceptance and native typing, at the context reached by real lexical binders. -/
theorem tree
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
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
  obtain ⟨_, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
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
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
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
    (syntaxTree : GenericImperativeMatch.PreparedSyntax header.function.source expressionSyntax
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
  obtain ⟨_, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
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
    (CallableIndexedOwnedPreparedDirectNamedProfileExtraction.hidden_fresh (header := header) wellFormed)
    (CallableIndexedOwnedPublicSignatureCatalog.well_formed compiled wellFormed)
    (header.valid.ledger.trans aligned.solved)
    (fun context fields scope fuel id node lowered declarations approved _reached found typed accepted nativeType native =>
      children context fields (scope := scope) (fuel := fuel) (id := id) (node := node)
        (lowered := lowered) declarations approved found typed accepted (nativeType := nativeType) native)
    syntaxTree rfl receipt.shape (.refl _) runtime.variables_closed runtime.residual_variables_open
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_signatures (header := header))
    declarations (fun id member => .root (List.mem_map.mpr ⟨id, member, rfl⟩))
    receipt.projection receipt.accepted flowTyped


include aligned in
/-- Static child receipts are assembled into the same named branching support
consumed by the numeric body theorem. Source and native execution are absent
from the factory's premises. -/
def of_imperative_compiler
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
    {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
    (zero : ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys, owner.key.capturePrefix = 0)
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
      CallableIndexedOwnedPreparedStagedNamedLexicalSupport.Certificate
        header bodyRegistry semanticFaults context child scope id lowered) :
    CallableIndexedOwnedPreparedStagedNamedBranchingSupport.Support
      headers keys bodyRegistry header stages receipt semanticFaults := by
  refine ⟨complete, zero, wellFormed,
    RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection prepared,
    RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault prepared,
    PreparedAssignmentDiagnosticProducers.named prepared diagnostic aligned, ?_⟩
  intro child selected
  rw [stages.source selected]
  exact ⟨expressionSyntax, collected_of_imperative prepared aligned ready wellFormed member receipt operands unary syntaxTree (children child selected)⟩


include aligned in
/-- Static child receipts are assembled into the same named branching support
consumed by the numeric body theorem. Source and native execution are absent
from the factory's premises. -/
def of_compiler
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
    {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
    (zero : ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys, owner.key.capturePrefix = 0)
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
    (syntaxTree : GenericLexicalStatements.Syntax header.function.source expressionSyntax
      header.context true header.function.body header.function.resultType)
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
      CallableIndexedOwnedPreparedStagedNamedLexicalSupport.Certificate
        header bodyRegistry semanticFaults context child scope id lowered) :
    CallableIndexedOwnedPreparedStagedNamedBranchingSupport.Support
      headers keys bodyRegistry header stages receipt semanticFaults :=
  of_imperative_compiler prepared aligned ready diagnostic wellFormed complete zero member receipt operands unary stages
    (.body syntaxTree) children

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedBranchingCollectors
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedPhysicalMixedScopedCollectors
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSyntaxAdmission
/-! Executable admission of original named source. The bounded scanner retains
actual lookups and complete declaration metadata. It constructs static syntax
and metadata receipts; no execution or body correspondence is a test. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSyntaxAdmission
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Supported)

/-- Exact ordinary inventory rows, including all retained raw replacements,
authenticate admitted direct sites. The range test is independent of native types. -/
def DirectSite (rows : List SourceSpecialization.SpecializedFunction)
    (instantiation : DeclarationInstantiation) : Prop :=
  ∃ row ∈ rows, instantiation = CallableNamedCanonicalOrder.retainedInstantiation row ∧
    CompatibleSourceInstantiationClosure.ClosedParameterRange instantiation.parameterSubstitution

/-- The executable table stores ordinary compiler data. Its later connection
to the semantic inventory is a proof and is never evaluated by the scanner. -/
def TableAligned {compiled : SourceCoreUnifiedCompilation.Compiled}
    (inputs : List (Input compiled)) (rows : List SourceSpecialization.SpecializedFunction) : Prop :=
  ∀ row ∈ rows, ∃ input ∈ inputs, input.row = row

theorem TableAligned.empty {compiled : SourceCoreUnifiedCompilation.Compiled}
    (inputs : List (Input compiled)) : TableAligned inputs [] := by
  intro row member
  cases member

private def allProof? {α : Type} (predicate : α → Prop)
    (check : (item : α) → Option (PLift (predicate item))) :
    (items : List α) → Option (PLift (∀ item ∈ items, predicate item))
  | [] => some ⟨by intro item member; cases member⟩
  | first :: rest => do
      let ⟨head⟩ ← check first
      let ⟨tail⟩ ← allProof? predicate check rest
      pure ⟨by
        intro item member
        rcases List.mem_cons.mp member with same | member
        · exact same ▸ head
        · exact tail item member⟩

private def closedRange? (substitution : TypeSystem.ParameterSubstitution) :
    Option (PLift (CompatibleSourceInstantiationClosure.ClosedParameterRange substitution)) :=
  if closed : substitution.all (fun item => SourceCoreDataCatalog.closed item.2) = true then
    some ⟨by intro parameter replacement member; exact List.all_eq_true.mp closed _ member⟩
  else none

def directSite?
    (inputs : List SourceSpecialization.SpecializedFunction) (instantiation : DeclarationInstantiation) :
    Option (PLift (DirectSite inputs instantiation)) := do
  let ⟨closed⟩ ← closedRange? instantiation.parameterSubstitution
  let rec find (remaining : List SourceSpecialization.SpecializedFunction) :
      Option (PLift (∃ input ∈ remaining,
        instantiation = CallableNamedCanonicalOrder.retainedInstantiation input)) :=
    match remaining with
    | [] => none
    | input :: rest =>
        if same : instantiation = CallableNamedCanonicalOrder.retainedInstantiation input then
          some ⟨⟨input, List.mem_cons_self, same⟩⟩
        else do
          let ⟨found⟩ ← find rest
          pure ⟨by obtain ⟨actual, member, same⟩ := found; exact ⟨actual, List.mem_cons_of_mem _ member, same⟩⟩
  let ⟨found⟩ ← find inputs
  pure ⟨by obtain ⟨input, member, same⟩ := found; exact ⟨input, member, same, closed⟩⟩

theorem DirectSite.supported {compiled : SourceCoreUnifiedCompilation.Compiled}
    {inputs : List (Input compiled)} {rawRows : List SourceSpecialization.SpecializedFunction}
    (aligned : TableAligned inputs rawRows) {instantiation : DeclarationInstantiation}
    (site : DirectSite rawRows instantiation) : Supported compiled.indexed.base.plan instantiation := by
  obtain ⟨row, member, same, range⟩ := site
  obtain ⟨input, _member, rowEq⟩ := aligned row member
  subst row
  refine ⟨range, ?_⟩
  intro key row target record
  rw [same] at target
  have keyEq := Except.ok.inj (target.symm.trans input.target)
  subst key
  have actual := CallableIndexedOwnedPreparedOrdinaryCachedInputs.cached_record compiled input.prepared.selected
  have rowEq := (Except.ok.inj (record.symm.trans actual)).trans input.prepared.same
  subst row
  simp only [same, CallableNamedCanonicalOrder.retainedInstantiation, List.map_reverse]

theorem DirectSite.covered {compiled : SourceCoreUnifiedCompilation.Compiled}
    {inputs : List (Input compiled)} (rows : Inventory inputs)
    {rawRows : List SourceSpecialization.SpecializedFunction} (aligned : TableAligned inputs rawRows)
    {instantiation : DeclarationInstantiation} (site : DirectSite rawRows instantiation)
    {index : Nat} {signature : SourceCoreCalls.Signature}
    (target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan instantiation = .ok signature.key)
    (global : compiled.indexed.base.globals[index]? = some signature) :
    ∃ header ∈ headers rows, header.slot = index ∧ header.named.signature = signature := by
  obtain ⟨row, rowMember, same, _range⟩ := site
  obtain ⟨input, member, rowEq⟩ := aligned row rowMember
  subst row
  have keys := Except.ok.inj ((same ▸ target).symm.trans input.target)
  have selected : (signature, index) ∈ compiled.indexed.base.globals.zipIdx.filter
      (fun item => decide (item.1.key = input.prepared.named.signature.key)) :=
    List.mem_filter.mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr global, by simpa using keys⟩
  rw [input.slot] at selected
  have samePair := List.mem_singleton.mp selected
  obtain ⟨packet, retained⟩ := rows.row_at input member
  exact ⟨packet.header, Inventory.header_member retained,
    packet.aligned.slot.trans (congrArg Prod.snd samePair).symm,
    (congrArg (·.signature) packet.aligned.named).trans (congrArg Prod.fst samePair).symm⟩

/-- Fuel bounds traversal of the original graph; failed admission adds no
hypothesis and does not alter any node or compiler metadata. -/
def expression?
    (inputs : List SourceSpecialization.SpecializedFunction) (source : TypedSource) :
    (fuel : Nat) → (id : ExpressionId) → Option (PLift (GeneralSyntax source id (DirectSite inputs)))
  | 0, _ => none
  | fuel + 1, id =>
      match found : source.lookupExpression? id with
      | none => none
      | some node =>
          match form : node.form with
          | .reference _name (.local _binder) => some ⟨.leaf (.read found form)⟩
          | .reference name (.builtinBoolean value) => some ⟨.leaf (.literal found (form ▸ .bool name value))⟩
          | .literal literal => some ⟨.leaf (.literal found (form ▸ .word literal))⟩
          | .integerLiteral literal resolution => some ⟨.leaf (.literal found (form ▸ .integer literal resolution))⟩
          | .tuple [] => some ⟨.leaf (.literal found (form ▸ .unit))⟩
          | .group inner => do
              let ⟨child⟩ ← expression? inputs source fuel inner
              pure ⟨.group found form child⟩
          | .unary _operator operand => do
              let ⟨child⟩ ← expression? inputs source fuel operand
              pure ⟨.unary found form child⟩
          | .binary left _operator right => do
              let ⟨first⟩ ← expression? inputs source fuel left
              let ⟨second⟩ ← expression? inputs source fuel right
              pure ⟨.binary found form first second⟩
          | .index base key =>
              match keyFound : source.lookupExpression? key with
              | none => none
              | some _keyNode => do
                  let ⟨container⟩ ← expression? inputs source fuel base
                  let ⟨lookup⟩ ← expression? inputs source fuel key
                  pure ⟨.index found form keyFound container lookup⟩
          | .constructor instantiation ids => do
              let ⟨ranges⟩ ← closedRange? instantiation.parameterSubstitution
              let ⟨children⟩ ← allProof? (fun child => GeneralSyntax source child (DirectSite inputs))
                (expression? inputs source fuel) ids
              pure ⟨.constructor found form ranges children⟩
          | .call _callee ids (.declaration instantiation) => do
              let ⟨site⟩ ← directSite? inputs instantiation
              let ⟨children⟩ ← allProof? (fun child => GeneralSyntax source child (DirectSite inputs))
                (expression? inputs source fuel) ids
              pure ⟨.direct found form site children⟩
          | .call callee ids (.indirect _metadata) => do
              let ⟨function⟩ ← expression? inputs source fuel callee
              let ⟨children⟩ ← allProof? (fun child => GeneralSyntax source child (DirectSite inputs))
                (expression? inputs source fuel) ids
              pure ⟨.call found form function children⟩
          | _ => none

def MetadataTest {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked)
    (named : SourceCoreGeneralFunctions.Function) (node : ExpressionNode) : Prop :=
  node.coercions = [] ∧
  prepared.base.locals.bindings.find? (fun binding => decide
    (binding.caller = (CallableIndexedNamedGeneration.context prepared named).owner ∧ binding.initializer = node.id)) = none ∧
  (match node.form with
    | .integerLiteral _ _ | .call _ _ (.declaration _) | .unary _ _ | .binary _ _ _ => True
    | _ => node.requirements = []) ∧
  (match node.form with | .call _ _ (.indirect metadata) => metadata.argumentCoercions = [] | _ => True) ∧
  (match node.form with
    | .reference _ (.local binder) => prepared.base.locals.bindings.any (fun binding => decide
        (binding.caller = (CallableIndexedNamedGeneration.context prepared named).owner ∧ binding.binder.id = binder)) = false
    | _ => True)

private instance metadataTestDecidable {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked)
    (named : SourceCoreGeneralFunctions.Function) (node : ExpressionNode) :
    Decidable (MetadataTest prepared named node) := by
  unfold MetadataTest
  cases node.form <;> try infer_instance
  case reference name resolution => cases resolution <;> infer_instance
  case call callee ids resolution => cases resolution <;> infer_instance

private def relevantForm : ExpressionForm → Bool
  | .proxy _ | .reference _ (.local _) | .reference _ (.builtinBoolean _) | .literal _ | .integerLiteral _ _
    | .unary _ _ | .binary _ _ _ | .index _ _ | .conditional _ _ _ | .group _ | .tuple _
    | .constructor _ _ | .call _ _ (.builtinFunction _) | .call _ _ (.declaration _)
    | .call _ _ (.indirect _) => true
  | _ => false

private theorem relevant_of_supported {form : ExpressionForm}
    (supported : CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.SupportedForm form) :
    relevantForm form = true := by
  cases supported with
  | literal atomic => cases atomic <;> rfl
  | proxy | read | unary | binary | index | conditional | group | tuple | constructor | builtin | direct | call => rfl

private def nodeMetadata? {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked)
    (named : SourceCoreGeneralFunctions.Function) (node : SourceInference.Node) :
    Option (PLift (∀ expression, node = .expression expression →
      relevantForm expression.form = true → MetadataTest prepared named expression)) :=
  match node with
  | .expression expression =>
      if relevant : relevantForm expression.form = true then
        if accepted : MetadataTest prepared named expression then
          some ⟨by intro actual same _; cases same; exact accepted⟩
        else none
      else some ⟨by intro actual same supported; cases same; exact False.elim (relevant supported)⟩
  | .statement _ => some ⟨by intro expression impossible; cases impossible⟩

/-- Every lookupable node in the admitted global grammar is checked, including
unused nodes. Unsupported forms have no GeneralSyntax witness and are skipped. -/
def metadata? {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked)
    (named : SourceCoreGeneralFunctions.Function) (source : TypedSource)
    (directSites : DeclarationInstantiation → Prop) :
    Option (PLift (CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      prepared named source directSites)) := do
  let ⟨all⟩ ← allProof? (fun node => ∀ expression, node = .expression expression →
    relevantForm expression.form = true → MetadataTest prepared named expression) (nodeMetadata? prepared named) source.nodes
  have metadataAt : ∀ id, GeneralSyntax source id directSites → ∀ node,
      source.lookupExpression? id = some node → MetadataTest prepared named node := by
    intro id tree node found
    obtain ⟨original, originalFound, supported⟩ :=
      CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.syntax_node tree
    cases Option.some.inj (originalFound.symm.trans found)
    exact all _ (lookupExpression?_sound found).1 node rfl (relevant_of_supported supported)
  pure ⟨{
    coercions := fun id tree node found => (metadataAt id tree node found).1
    initializer := by
      intro id tree
      obtain ⟨node, found⟩ := GeneralSyntax.syntax_found tree
      have nodeId := (lookupExpression?_sound found).2
      simpa only [nodeId] using (metadataAt id tree node found).2.1
    requirements := by
      intro id tree node found
      have accepted := (metadataAt id tree node found).2.2.1
      cases form : node.form <;> simp only [form] at accepted
      all_goals try exact .inl accepted
      case integerLiteral literal resolution => exact .inr (.inl ⟨literal, resolution, rfl⟩)
      case unary operator operand => exact .inr (.inr (.inr True.intro))
      case binary left operator right => exact .inr (.inr (.inr True.intro))
      case call callee ids resolution =>
        cases resolution <;> simp only at accepted
        all_goals try exact .inl accepted
        case declaration instantiation => exact .inr (.inr (.inl ⟨callee, ids, instantiation, rfl⟩))
    arguments := by
      intro id tree node found callee ids callMetadata form
      simpa only [form] using (metadataAt id tree node found).2.2.2.1
    localRead := by
      intro id tree node found name binder form
      simpa only [form] using (metadataAt id tree node found).2.2.2.2 }⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSyntaxAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedScopedAdmission
/-! Finite original-source statement admission supplies scoped named bodies.
Independent Header typing recovers lexical contexts and loop typing through
the shared scanner. The existing physical family consumes the issued support. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedScopedAdmission
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite TableAligned)
open CallableIndexedOwnedFunctionValues (Header)

/-- The named-body API selects top-level mode of the shared original-source scan. -/
abbrev BodyScan (source : TypedSource) (approved : ExpressionId → Prop)
    (expected : TypeSystem.Ty) (statements : List StatementId) : Prop :=
  ScopedSourceBodyAdmission.Scan source approved expected true statements

theorem BodyScan.shape {source : TypedSource} {approved : ExpressionId → Prop}
    {expected : TypeSystem.Ty} {statements : List StatementId}
    (scan : BodyScan source approved expected statements) :
    CallableIndexedOwnedPreparedStagedBranchingTree.Shape source true statements :=
  ScopedSourceBodyAdmission.Scan.shape scan

theorem BodyScan.syntax {source : TypedSource} {approved : ExpressionId → Prop}
    {expected : TypeSystem.Ty} {statements : List StatementId}
    (scan : BodyScan source approved expected statements) (unique : NodeOccurrencesUnique source)
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType source {returnType := expected} context statements final facts) :
    GenericImperativeMatch.PreparedSyntax source approved context (.statements true statements) expected :=
  ScopedSourceBodyAdmission.Scan.syntax scan unique rfl typed

/-- Fuel bounds both the original statement graph and expression traversal. -/
def scan?
    (inputs : List SourceSpecialization.SpecializedFunction) (source : TypedSource) (expected : TypeSystem.Ty) (fuel : Nat)
    (statements : List StatementId) : Option (PLift
      (BodyScan source (fun id => GeneralSyntax source id (DirectSite inputs)) expected statements)) :=
  ScopedSourceBodyAdmission.scan? source
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.expression? inputs source fuel) expected fuel true statements

structure SourceAdmission (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (source : TypedSource)
    (statements : List StatementId) (expected : TypeSystem.Ty)
    (directRows : List SourceSpecialization.SpecializedFunction) : Prop where
  metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
    compiled.indexed named source (DirectSite directRows)
  body : BodyScan source (fun id => GeneralSyntax source id (DirectSite directRows)) expected statements

abbrev Admission {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (directRows : List SourceSpecialization.SpecializedFunction) : Prop :=
  SourceAdmission compiled prepared.named header.function.source header.function.body
    header.function.resultType directRows

/-- This checker reads only compiler/source data. Neither Headers nor the
classically assembled inventory appear in the executable arguments. -/
def admitSource (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (source : TypedSource)
    (statements : List StatementId) (expected : TypeSystem.Ty)
    (directRows : List SourceSpecialization.SpecializedFunction) (fuel : Nat) :
    Option (PLift (SourceAdmission compiled named source statements expected directRows)) := do
  let ⟨metadata⟩ ← CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata?
    compiled.indexed named source (DirectSite directRows)
  let ⟨body⟩ ← scan? directRows source expected fuel statements
  pure ⟨⟨metadata, body⟩⟩

/-- Successful certification supplies all expression syntax and native hook
metadata from the original finite tables. It does not claim every accepted
program belongs to the supported statement and expression fragment. -/
def admitPrepared {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (directRows : List SourceSpecialization.SpecializedFunction) (fuel : Nat) :
    Option (PLift (Admission prepared header directRows)) :=
  admitSource compiled prepared.named header.function.source header.function.body
    header.function.resultType directRows fuel

/-- Actual Header typing and accepted body compilation close the existing
scoped static issuer. Syntax, metadata, direct support and slot callbacks are
all constructed from the certification result and inventory. -/
theorem of_actual {compiled : SourceCoreUnifiedCompilation.Compiled}
    {recipe : SourceCoreIndexedSession.Recipe}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    {inputs : List (Input compiled)} (rows : Inventory inputs)
    {directRows : List SourceSpecialization.SpecializedFunction}
    (table : TableAligned inputs directRows)
    (admission : Admission prepared header directRows)
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
        (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
    (methods : CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog compiled)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
    {bodyRegistry : SourceCoreRawMetadata.Registry} :
    Nonempty (Σ body : CallableIndexedOwnedPreparedStagedNamedBodies.Body header,
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.Support
        (headers := headers rows) (bodyRegistry := bodyRegistry)
        (stages := RecursiveNamedPreparedStageScopes.registry actual)
        (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
        header body) := by
  obtain ⟨final, facts, typed, _complete⟩ := RecursiveNamedHeaderSourceTyping.statements header wellFormed
  have syntaxTree := admission.body.syntax header.unique typed
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.of_accepted
    aligned.accepted admission.body.shape aligned.projection
  let support := CallableIndexedOwnedPreparedNamedPhysicalMixedScopedCollectors.of_actual_with_catalog
    prepared aligned ready diagnostic receiver wellFormed
    (fun _ site => site.supported table) admission.metadata rows
    (fun _ site _ _ target global => site.covered rows table target global)
    checked catalog methods member receipt actual syntaxTree
  let body : CallableIndexedOwnedPreparedStagedNamedBodies.Body header := {
    row := row, prepared := prepared, instantiation := instantiation, aligned := aligned,
    layouts := aligned.layouts, compilation := .canonicalBranching receipt }
  exact ⟨body, .scoped body receipt rfl support⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedScopedAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedCatalogAdmission
/-! One executable entry scans actual cached ordinary rows and original named
syntax. The proof-only issuer connects that finite result to the authentic
catalog and the existing physical body family. Static certification success
remains distinct from public compilation success. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedCatalogAdmission
open Core Frontend SourceInference
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedOrdinaryCatalogReceipts (Catalog)

/-- All executable fields come from compiler/source data. The certificate has
no supplied expression, metadata, slot, or body execution callback. -/
structure Certified (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (source : TypedSource)
    (statements : List StatementId) (expected : TypeSystem.Ty) where
  table : CallableIndexedOwnedPreparedOrdinarySyntaxTable.Table compiled
  sourceAdmission : CallableIndexedOwnedPreparedNamedScopedAdmission.SourceAdmission
    compiled named source statements expected table.rows

/-- The cache scanner conservatively omits rows outside static admission.
The source scanner then requires every actual direct call to match a retained
row, including its full metadata and closed raw replacement range. -/
def certifySource (compiled : SourceCoreUnifiedCompilation.Compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (named : SourceCoreGeneralFunctions.Function) (source : TypedSource)
    (statements : List StatementId) (expected : TypeSystem.Ty) (fuel : Nat) :
    Option (Certified compiled named source statements expected) := do
  let table := CallableIndexedOwnedPreparedOrdinarySyntaxTable.collect compiled wellFormed fuel
  let ⟨sourceAdmission⟩ ← CallableIndexedOwnedPreparedNamedScopedAdmission.admitSource
    compiled named source statements expected table.rows fuel
  pure ⟨table, sourceAdmission⟩

/-- The same certified source is connected to any authentic filtered catalog.
Independent Header typing supplies every lexical context; genuine compiler
and dictionary receipts issue the final physical scoped support. -/
theorem of_actual {compiled : SourceCoreUnifiedCompilation.Compiled}
    {recipe : SourceCoreIndexedSession.Recipe}
    {row : SourceSpecialization.SpecializedFunction}
    (catalog : Catalog compiled)
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    (certified : Certified compiled prepared.named header.function.source
      header.function.body header.function.resultType)
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
        (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (coercions : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
    (methods : CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog compiled)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
    {bodyRegistry : SourceCoreRawMetadata.Registry} :
    Nonempty (Σ body : CallableIndexedOwnedPreparedStagedNamedBodies.Body header,
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.Support
        (headers := headers catalog.rows) (bodyRegistry := bodyRegistry)
        (stages := RecursiveNamedPreparedStageScopes.registry actual)
        (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
        header body) :=
  CallableIndexedOwnedPreparedNamedScopedAdmission.of_actual prepared aligned catalog.rows
    (certified.table.aligned catalog) certified.sourceAdmission ready diagnostic receiver wellFormed
    checked coercions methods member actual

/-- A source with no declaration calls can be issued for any retained inventory.
The empty data-table alignment is constructed here, so callers supply only the
executable source certificate and the real compiler/Header receipts. -/
theorem of_empty_actual {compiled : SourceCoreUnifiedCompilation.Compiled}
    {recipe : SourceCoreIndexedSession.Recipe}
    {row : SourceSpecialization.SpecializedFunction}
    {inputs : List (Input compiled)} (rows : Inventory inputs)
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    (certified : CallableIndexedOwnedPreparedNamedScopedAdmission.SourceAdmission
      compiled prepared.named header.function.source header.function.body header.function.resultType [])
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
        (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (coercions : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
    (methods : CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog compiled)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
    {bodyRegistry : SourceCoreRawMetadata.Registry} :
    Nonempty (Σ body : CallableIndexedOwnedPreparedStagedNamedBodies.Body header,
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.Support
        (headers := headers rows) (bodyRegistry := bodyRegistry)
        (stages := RecursiveNamedPreparedStageScopes.registry actual)
        (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
        header body) :=
  CallableIndexedOwnedPreparedNamedScopedAdmission.of_actual prepared aligned rows
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.TableAligned.empty inputs) certified ready diagnostic receiver wellFormed
    checked coercions methods member actual

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedCatalogAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSourceAdmissionTransport
/-! Data-only source certificates transport to authentic Headers using actual
cache identity and compiled statement roots. Existing complete inventories
cover a scanned table through those same physical slots. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSourceAdmissionTransport
open Core Frontend SourceInference
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (TableAligned)
open CallableIndexedOwnedPreparedNamedScopedAdmission (SourceAdmission Admission)

def statements (source : TypedSource) : List StatementId :=
  source.roots.filterMap fun node => match node with
    | .statement id => some id
    | .expression _ => none

/-- Equal original cached rows identify the same prepared function and slot. -/
theorem cached_named {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (same : named.specialized = row) : prepared.named = named := by
  have slot := CallableIndexedOwnedPreparedOrdinaryCachedInputs.cached_slot compiled selected
  have global := CallableIndexedPreparedInventories.cached_global_at compiled prepared.selected
  have key : prepared.named.signature.key = named.signature.key := by
    rw [CallableIndexedOwnedPreparedOrdinaryCachedInputs.cached_key compiled prepared.selected,
      CallableIndexedOwnedPreparedOrdinaryCachedInputs.cached_key compiled selected,
      prepared.same, same]
  have member : (prepared.named.signature, prepared.index) ∈
      compiled.indexed.base.globals.zipIdx.filter
        (fun item => decide (item.1.key = named.signature.key)) :=
    List.mem_filter.mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr global, by simp only [key, decide_true]⟩
  rw [slot] at member
  have indexEq := (Prod.mk.inj (List.mem_singleton.mp member)).2
  exact Option.some.inj ((indexEq ▸ prepared.selected).symm.trans selected)

/-- The canonical data roots are exactly the accepted compiler roots. -/
theorem header_data {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header) :
    header.function.source = prepared.named.specialized.function.typedBody ∧
      header.function.body = statements prepared.named.specialized.function.typedBody ∧
      header.function.resultType = prepared.named.specialized.function.inferredBodyType := by
  rw [aligned.function]
  refine ⟨rfl, ?_, rfl⟩
  change prepared.compilation.statements = statements prepared.named.specialized.function.typedBody
  unfold statements
  rw [RecursiveNamedPreparedSourceFrames.compiled_roots_eq prepared.compilation]
  simp only [List.filterMap_map]
  induction prepared.compilation.statements with
  | nil => rfl
  | cons first rest ih => simpa only [List.filterMap_cons, Function.comp_apply] using congrArg (List.cons first) ih

/-- All source, body, result and contextual metadata indices are transported
from the real cached record; no independent equalities are requested. -/
theorem source_at_header {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (same : named.specialized = row)
    {directRows : List SourceSpecialization.SpecializedFunction}
    (certificate : SourceAdmission compiled named named.specialized.function.typedBody
      (statements named.specialized.function.typedBody)
      named.specialized.function.inferredBodyType directRows) :
    Admission prepared header directRows := by
  have namedEq := cached_named prepared selected same
  obtain ⟨source, body, result⟩ := header_data prepared aligned
  change SourceAdmission compiled prepared.named header.function.source header.function.body
    header.function.resultType directRows
  rw [source, body, result, namedEq]
  exact certificate

/-- A legacy complete inventory also covers every executable table row. The
proof uses the exact cache position, never evaluation of semantic Inputs. -/
theorem table_aligned_of_complete {compiled : SourceCoreUnifiedCompilation.Compiled}
    {inputs : List (Input compiled)} (rows : Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers rows))
    (table : CallableIndexedOwnedPreparedOrdinarySyntaxTable.Table compiled) :
    TableAligned inputs table.rows := by
  intro row member
  obtain ⟨index, named, selected, same, _eligible⟩ := table.admitted row member
  obtain ⟨header, headerMember, slot, _signature⟩ := complete index named.signature
    (CallableIndexedPreparedInventories.cached_global_at compiled selected)
  obtain ⟨input, packet, retained, packetEq⟩ := rows.mem_headers header headerMember
  have indexEq : input.prepared.index = index := packet.aligned.slot.symm.trans
    ((congrArg (·.slot) packetEq).trans slot)
  have namedEq : input.prepared.named = named :=
    Option.some.inj ((indexEq ▸ input.prepared.selected).symm.trans selected)
  exact ⟨input, Inventory.input_member retained,
    input.prepared.same.symm.trans ((congrArg (·.specialized) namedEq).trans same)⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSourceAdmissionTransport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedCanonicalScopedCollectors
/-! Authentic named compiler trees retain canonical or legacy static children.
The general-expression convenience derives every child from its original
Source typing and actual accepted contextual callback. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedCanonicalScopedCollectors
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
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
    {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
    (zero : ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys, owner.key.capturePrefix = 0)
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
      CallableIndexedOwnedPreparedStagedCanonicalScopedStaticSupport.Certificate
        headers header bodyRegistry semanticFaults context child scope id lowered) :
    CallableIndexedOwnedPreparedStagedCanonicalScopedStaticSupport.NamedSupport
      headers keys bodyRegistry header stages receipt semanticFaults := by
  refine ⟨complete, zero, wellFormed,
    RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection prepared,
    RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault prepared,
    PreparedAssignmentDiagnosticProducers.named prepared diagnostic aligned, ?_⟩
  intro child selected
  rw [stages.source selected]
  exact ⟨expressionSyntax, CallableIndexedOwnedPreparedNamedBranchingCollectors.collected_of_imperative prepared aligned ready wellFormed member receipt operands unary syntaxTree (children child selected)⟩


include aligned in
/-- The actual prepared Header, complete inventory and native metadata issue
all canonical children without exposing a child execution premise. -/
def of_actual
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (metadata : CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.NativeMetadataFor
      compiled.indexed prepared.named header.function.source)
    {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
    (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows))
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
    {bodyRegistry : SourceCoreRawMetadata.Registry}
    (zero : ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys, owner.key.capturePrefix = 0)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    (receipt : Receipt header)
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
    (syntaxTree : GenericImperativeMatch.PreparedSyntax header.function.source (GeneralSyntax header.function.source)
      header.context (.statements true header.function.body) header.function.resultType) :
    CallableIndexedOwnedPreparedStagedCanonicalScopedStaticSupport.NamedSupport
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) keys bodyRegistry header
      (RecursiveNamedPreparedStageScopes.registry actual) receipt
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := by
  apply of_imperative_compiler prepared aligned ready diagnostic wellFormed complete zero member receipt
    (CallableIndexedOwnedPreparedNamedBranchingCollectors.operands_of_diagnostic prepared aligned diagnostic receiver)
    (CallableIndexedOwnedPreparedNamedBranchingCollectors.unary_of_diagnostic prepared aligned diagnostic receiver)
    (RecursiveNamedPreparedStageScopes.registry actual) syntaxTree
  intro child selected context fields scope fuel id node lowered declarations approved found typed accepted nativeType native
  have sameSource := (RecursiveNamedPreparedStageScopes.registry actual).source selected
  obtain ⟨root, prefixEq⟩ := CallableIndexedOwnedPreparedStagedNamedCanonicalScopedRoots.of_accepted
    prepared aligned diagnostic receiver wellFormed metadata rows complete actual selected fields
    (by simpa only [sameSource] using declarations) (by simpa only [sameSource] using approved)
    (by simpa only [sameSource] using found) (by simpa only [sameSource] using typed)
    (by simpa only [sameSource] using accepted)
  exact .canonical root prefixEq

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedCanonicalScopedCollectors
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSourceFactoryFacts
/-! Actual selected Headers supply the raw Source parameter/result vectors and
native projections at each receiving Source context. Dictionaries stay intact;
neither ordinary evidence nor a completed expression Tree is required.
Coercions, generalized local branches, syntax and compiler policy coverage are
separate occurrence-specific obligations. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSourceFactoryFacts
open Core Frontend SourceInference RecursiveNamedCatalog

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions
    (Program.ofChecked compiled.sourceProgram)}
  {sourceContext : SourceSemantics.Context}

/-- The same actual source frame fixes ordered raw types. Accepted named
preparation supplies native projections, including for Headers with evidence. -/
theorem source_types
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (signatures : sourceContext.signatures = compiled.sourceProgram.signatures) :
    RecursiveNamedCallEvidenceHeads.SourceTypes headers sourceContext := by
  refine ⟨?_, ?_, ?_⟩
  · intro header _member signature member selected
    have actualMember : signature ∈ (Program.ofChecked compiled.sourceProgram).signatures.functions := by
      change signature ∈ compiled.sourceProgram.signatures.functions
      rw [← signatures]
      exact member
    exact (RecursiveNamedSourceSignatureFacts.header_shape header wellFormed actualMember selected).1
  · intro header _member signature member selected
    have actualMember : signature ∈ (Program.ofChecked compiled.sourceProgram).signatures.functions := by
      change signature ∈ compiled.sourceProgram.signatures.functions
      rw [← signatures]
      exact member
    exact (RecursiveNamedSourceSignatureFacts.header_shape header wellFormed actualMember selected).2
  · intro header _member
    exact RecursiveNamedHeaderParameterProjections.projections_of_record header rfl wellFormed
      (CallableIndexedActualNamedSourceReceipts.header_record compiled header)

/-- A selected declaration uses its actual full Header and Source signature
catalog. No assumption about other Headers' dictionaries is introduced. -/
theorem selected_validity
    (signatures : sourceContext.signatures = compiled.sourceProgram.signatures)
    (compilation : SourceCoreFunctions.Context) (source : TypedSource)
    (admitted : ExpressionId → Prop) :
    RecursiveNamedExpressionCompilerCertificates.SelectedDeclarationLaw headers compilation
      source sourceContext admitted :=
  RecursiveNamedSelectedExpressionFactory.selected_validity signatures

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSourceFactoryFacts
end
