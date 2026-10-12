import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLexicalContextCertificates
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedLexicalSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedPublicProfileExtraction
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedHeaderPolicies

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
