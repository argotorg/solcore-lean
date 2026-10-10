import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedDirectTypedNamedBodyContinuations
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeImperativeCollectors
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedPublicProfileExtraction
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLocalIdentityFreshness
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderSourceTyping

/-! Actual cached named compilation and a real ordinary parameter entry supply
one enclosing native typing. The finite native-aware compiler induction derives
the same flow Tree, prepared diagnostic plan and structural eliminator. The
forward Profile view retains that Tree and omits universal CatalogSites.
Independent Source syntax, local expression certificates and exact assignment
issuance remain static inputs; this module supplies no execution law. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedDirectNamedProfileExtraction
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open RecursiveNamedPublicSpecializationMeaning
open RecursiveNamedPreparedHeaderPolicies

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
    ∀ {nativeType}, HasType (SourceCoreLocalCell.coreContext scope ++
      SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
      lowered.expression nativeType compiled.indexed.layouts.definitions → certificates header sourceContext scope id lowered
  syntaxTree : GenericImperativeMatch.Syntax header.function.source (expressionSyntax header) header.context
    (.statements true header.function.body) header.function.resultType

/-- This factory binds its operand token to the actual prepared assignment row.
The returned Plan retains actual reached missing/uninitialized interpretation
obligations for its own diagnostic fields. -/
def assignment_factory : AssignmentDiagnosticOrigins.Factory true .reachable header.function.source
    (Prepared.invalidOperand prepared) :=
  AssignmentDiagnosticOrigins.Factory.prepared operandsTyped issued

/-- Source ownership derives freshness for the same Header body, independently
of native types and compiler Tree extraction. -/
theorem hidden_fresh (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    GenericImperativeMatch.MatchHiddenFresh header.function.source := by
  obtain ⟨facts, certified⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
  apply CallableIndexedOwnedLocalIdentityFreshness.match_hidden_fresh
  rw [header.frame.source]
  exact certified.local_identity_ownership

/-- One actual coupled compiler receipt. The original prepared Plan and its
structural eliminator are retained alongside the finite flow Tree. -/
structure Receipt where
  flow : Expr
  generated : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body header.output header.reasonAt true header.escaped = .ok flow
  collected : GenericImperativeMatch.CatalogCoupledExtractionFor .reachable header.layouts header.owner header.active
    compiled.indexed.ancestry.layout.frame header.globals header.onError (.initial compiled.compatible.checked)
    header.function.source (assignment_factory prepared operandsTyped issued)
    (Prepared.invalidUnary prepared) (Prepared.invalidProjection prepared) (Prepared.missingDefault prepared)
    (expressionSyntax header) (certificates header) compiled.indexed.layouts.definitions
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
    (Prepared.ambientMatch prepared).solvedRequirements header.context (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    (.statements true header.function.body) header.function.resultType header.output flow

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
  have accepted := aligned.accepted
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, emitted⟩ := CompatibleEncoding.bind_ok accepted
  have finished : header.body = CompatibleStatements.finish header.output flow header.fellThrough header.escaped :=
    Except.ok.inj emitted.symm
  rw [finished] at nativeTyped
  obtain ⟨_, flowTyped⟩ := TypedLexicalWhile.Native.finished_flow nativeTyped
  have assignments : CompatibleAssignmentStatements.AssignmentPolicy header.policy (.initial compiled.compatible.checked)
      (Prepared.invalidProjection prepared) (Prepared.invalidOperand prepared) (Prepared.missingDefault prepared) := by
    rw [aligned.policy]
    exact Prepared.assignments prepared
  have unaries : CompatibleBitNotStatements.Policy header.policy (.initial compiled.compatible.checked)
      (Prepared.invalidProjection prepared) (Prepared.invalidUnary prepared) (Prepared.missingDefault prepared) := by
    rw [aligned.policy]
    exact Prepared.unary prepared
  obtain ⟨collected⟩ :=
    CallableIndexedOwnedPreparedNativeImperativeCollectors.extraction_of_typed_position_with_catalog_coupled true .reachable
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
      aligned.projection generated flowTyped
  exact ⟨⟨flow, generated, collected⟩⟩

/-- A forward view uses the exact collected Tree. Its prepared structure stays
in Receipt for the eventual reached-diagnostic flow fold. -/
def Receipt.profile
    (receipt : Receipt (certificates := certificates) (expressionSyntax := expressionSyntax)
      (administrative := administrative) prepared operandsTyped issued) :
    CallableIndexedOwnedDirectTypedNamedBodyContinuations.Profile
      (certificates := certificates) (expressionSyntax := expressionSyntax) true header administrative :=
  CallableIndexedOwnedDirectTypedNamedBodyContinuations.Profile.of_extracted
    header.valid aligned.accepted aligned.projection receipt.generated
    receipt.collected.original.original.original.original.tree

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedDirectNamedProfileExtraction
