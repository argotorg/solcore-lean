import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedDirectNamedProfileExtraction
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPairedNativeImperativeCollectors
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCanonicalCaptureReceipts

/-! Actual ordinary entry typing and fixed canonical body typing come from the
same prepared cached code. One paired compiler induction then manufactures
both local native witnesses for the certificate factory. The original Receipt,
Plan, structural eliminator and actual administrative indices are preserved.
Source syntax, selected metadata and diagnostic issuance remain independent.
No semantic execution law or arbitrary child context transport is supplied. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPairedNamedProfileExtraction
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open RecursiveNamedPublicSpecializationMeaning RecursiveNamedPreparedHeaderPolicies
open CallableIndexedOwnedPreparedDirectNamedProfileExtraction (Receipt assignment_factory hidden_fresh)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {row : SourceSpecialization.SpecializedFunction} (prepared : Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry}
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  {administrative : Core.Context}
  {first : Nat}
  (operandsTyped : AssignmentDiagnosticOrigins.OperandsTyped header.function.source)
  (issued : SourceCoreAssignmentFaultSites.prepare header.function.source first = .ok prepared.compilation.own.assignments)

/-- Only authentic Source syntax and local static certificates remain here.
Every raw child typing is manufactured by the enclosing-code collector. -/
structure Children where
  expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = true →
    sourceContext.signatures = compiled.compatible.checked.signatures →
    ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext →
    expressionSyntax header id → header.function.source.lookupExpression? id = some node →
    ExpressionHasType header.function.source sourceContext id node.type →
    header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
    ∀ {nativeType fixedNativeType}, HasType (SourceCoreLocalCell.coreContext scope ++
      SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
      lowered.expression nativeType compiled.indexed.layouts.definitions →
    HasType (SourceCoreLocalCell.coreContext scope ++
      CallableIndexedOwnedPreparedCanonicalCaptureReceipts.«prefix» (compiled := compiled) header.named)
      lowered.expression fixedNativeType compiled.indexed.layouts.definitions → certificates header sourceContext scope id lowered
  syntaxTree : GenericImperativeMatch.Syntax header.function.source (expressionSyntax header) header.context
    (.statements true header.function.body) header.function.resultType

variable {recipe : SourceCoreIndexedSession.Recipe}
  (recipeAccepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
  {nativeEntry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
  (nativeMember : nativeEntry ∈ compiled.indexed.entries)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (prepared := compiled.indexed.ancestry)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
  (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers owner.key.locations 0 functions registry header arguments before initialStore mapping world
    administrative actualContext actual ξ frameLocation current ghost)


include prepared aligned recipeAccepted nativeMember in
/-- The exact cached native lambda and its actual bootstrap support derive the
literal parameter/global/frame body prefix, before any real entry transport. -/
theorem body_native_at_prefix :
    HasType (SourceCoreLocalCell.coreContext
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) ++
      CallableIndexedOwnedPreparedCanonicalCaptureReceipts.«prefix» (compiled := compiled) header.named)
      header.body (LanguageResult.resultType header.output) compiled.indexed.layouts.definitions := by
  have typed := CallableIndexedOwnedNamedPublicProfileExtraction.cached_typed prepared aligned nativeMember
  have support := CallableIndexedOwnedNamedPublicProfileExtraction.cached_supported recipeAccepted prepared aligned
  have original : HasType
      ((compiled.indexed.base.globals.map (·.referenceType) ++ [.cell compiled.indexed.ancestry.layout.frame.type]) ++
        SourceCoreGeneralEntry.nativeInputContext nativeEntry.native.inputTypes)
      (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code)
      header.named.signature.functionType
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions := by simpa using typed
  have minimal := NativeExpressionContextSupport.prefix_typing (targetSuffix := []) original (by simpa using support)
  have minimalTyped : HasType
      (compiled.indexed.base.globals.map (·.referenceType) ++
        .cell compiled.indexed.ancestry.layout.frame.type :: [])
      (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code)
      header.named.signature.functionType compiled.indexed.layouts.definitions := by
    simpa only [CallableIndexedAmbient.ambientDefinitions, List.append_nil, List.singleton_append] using minimal
  cases minimalTyped with
  | lambda parameterWF resultWF codeTyped =>
    obtain ⟨_, _, _, _, emitted⟩ := CallableIndexedFormation.namedBody_receipt compiled.indexed.ancestry header.hook
    rw [emitted] at codeTyped
    have parameters := CallableIndexedParameterNativeInversion.withFrame_body codeTyped
    have body := CallableIndexedParameterNativeInversion.accepted_body header.onError header.acceptedPrefix parameters
    rw [CallableIndexedParameterNativeInversion.final_context] at body
    simpa only [CallableIndexedOwnedPreparedCanonicalCaptureReceipts.«prefix», header.parameterType, header.resultType,
      List.append_assoc, List.cons_append, List.nil_append, List.append_nil] using body


include aligned recipeAccepted nativeMember functions owner complete entry in
/-- Actual cache and support proofs transport the exact body to its real entry;
one finite collector then derives every visited child native witness. -/
theorem extract_at
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (children : Children (certificates := certificates) (expressionSyntax := expressionSyntax)
      (header := header) (administrative := administrative)) :
    Nonempty (Receipt (certificates := certificates) (expressionSyntax := expressionSyntax)
      (administrative := administrative) prepared operandsTyped issued) := by
  have nativeTyped := RecursiveNamedCatalogNativeContexts.canonical_cached complete aligned.globals
    (CallableIndexedOwnedNamedPublicProfileExtraction.cached_typed prepared aligned nativeMember)
    (CallableIndexedOwnedNamedPublicProfileExtraction.cached_supported recipeAccepted prepared aligned) entry
  have fixedTyped := body_native_at_prefix prepared aligned recipeAccepted nativeMember
  have accepted := aligned.accepted
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, emitted⟩ := CompatibleEncoding.bind_ok accepted
  have finished : header.body = CompatibleStatements.finish header.output flow header.fellThrough header.escaped :=
    Except.ok.inj emitted.symm
  rw [finished] at nativeTyped fixedTyped
  obtain ⟨_, flowTyped⟩ := TypedLexicalWhile.Native.finished_flow nativeTyped
  obtain ⟨_, fixedFlowTyped⟩ := TypedLexicalWhile.Native.finished_flow fixedTyped
  have assignments : CompatibleAssignmentStatements.AssignmentPolicy header.policy (.initial compiled.compatible.checked)
      (Prepared.invalidProjection prepared) (Prepared.invalidOperand prepared) (Prepared.missingDefault prepared) := by
    rw [aligned.policy]
    exact Prepared.assignments prepared
  have unaries : CompatibleBitNotStatements.Policy header.policy (.initial compiled.compatible.checked)
      (Prepared.invalidProjection prepared) (Prepared.invalidUnary prepared) (Prepared.missingDefault prepared) := by
    rw [aligned.policy]
    exact Prepared.unary prepared
  obtain ⟨collected⟩ :=
    CallableIndexedOwnedPreparedPairedNativeImperativeCollectors.extraction_of_typed_position_with_catalog_coupled true .reachable
      (assignment_factory prepared operandsTyped issued)
      (Prepared.header_match prepared aligned) rfl rfl (Prepared.match_allocator prepared aligned)
      (GenericImperativeMatch.MatchChildStatic.of_hidden
        (matchCompilation := Prepared.ambientMatch prepared) (definitions := compiled.indexed.layouts.definitions)
        (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
        (certificates := certificates header) (hidden_fresh wellFormed))
      (Prepared.header_read prepared aligned) (Prepared.header_binder prepared aligned)
      (Prepared.header_allocator prepared aligned) children.expressions assignments unaries header.unique
      children.syntaxTree (RecursiveNamedSourceContextFacts.header_typeVariables header)
      (RecursiveNamedSourceContextFacts.header_residual header) (Prepared.header_signatures (header := header))
      (RecursiveNamedHeaderScopeDeclarations.header_scope
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (program := Program.ofChecked compiled.sourceProgram)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) header)
      aligned.projection generated flowTyped fixedFlowTyped
  exact ⟨⟨flow, generated, collected⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPairedNamedProfileExtraction
