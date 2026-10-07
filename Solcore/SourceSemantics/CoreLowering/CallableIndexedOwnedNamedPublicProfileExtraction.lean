import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReadyNamedFamilyClosure
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedHeaderReceipts
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedHeaderPolicies
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogPreparedInitialization

/-! The original public named compiler supplies exact cached code and its native
support at an actual ordinary parameter entry. Its existing static extraction
produces one actual Tree and diagnostics; Source Syntax and child certificates
remain independent original compiler inputs. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedPublicProfileExtraction
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open RecursiveNamedPublicSpecializationMeaning RecursiveNamedCatalogRuntimeProfileFactory

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {recipe : SourceCoreIndexedSession.Recipe}
  (recipeAccepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
  {row : SourceSpecialization.SpecializedFunction} (prepared : Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)

include prepared aligned in
/-- Full Header provenance identifies the exact cached lambda, including its
complete native signature and actual compiler output. -/
theorem cached_header : compiled.indexed.secondPass.closures[header.slot]? =
    some (.lambda header.named.signature.parameterType
      (LanguageResult.resultType header.named.signature.resultType) header.code) := by
  rw [aligned.slot, aligned.named, aligned.code]
  exact prepared.cached.trans (congrArg some prepared.compilation.emitted)

variable {nativeEntry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
  (nativeMember : nativeEntry ∈ compiled.indexed.entries)

include prepared aligned nativeMember in
/-- The real checked root supplies this cached native proof. No typing at an
arbitrary administrative context is requested. -/
theorem cached_typed :
    HasType (compiled.indexed.base.globals.map (·.referenceType) ++
      .cell compiled.indexed.ancestry.layout.frame.type ::
        SourceCoreGeneralEntry.nativeInputContext nativeEntry.native.inputTypes)
      (.lambda header.named.signature.parameterType
        (LanguageResult.resultType header.named.signature.resultType) header.code)
      header.named.signature.functionType (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions := by
  exact CallableIndexedCachedNativeTyping.prepared_native_closure compiled.indexedPrepared nativeMember
    (cached_header prepared aligned) (CallableIndexedPreparedInventories.cached_global_at compiled header.selected)

include recipeAccepted prepared aligned in
/-- Actual accepted bootstrap preparation bounds the same cached code's free
slots, without identifying its Source body from native typing. -/
theorem cached_supported :
    NativeExpressionContextSupport.supported (.lambda header.named.signature.parameterType
      (LanguageResult.resultType header.named.signature.resultType) header.code)
      (compiled.indexed.base.globals.length + 1) = true :=
  RecursiveNamedCatalogPreparedInitialization.supported_cached recipeAccepted (cached_header prepared aligned)

variable {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (compilation : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → SourceCoreFunctions.Context)
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
  (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers owner.key.locations 0 functions registry header arguments before initialStore mapping world
    administrative actualContext actual ξ frameLocation current ghost)
  {tracked : Bool}
  (sites : InputsWith (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    true tracked .reachable headers header (compilation header) (expressionSyntax header)
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))

include recipeAccepted prepared aligned nativeMember functions owner complete entry sites in
/-- One original compiler traversal uses the actual parameter entry and the
real checked cached code. Every retained child receipt and Syntax belongs to
this exact InputsWith packet. -/
theorem extract_at : Nonempty (ReceiptWith (prepared := compiled.indexed.ancestry)
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    true .reachable headers header (compilation header) (expressionSyntax header)
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) := by
  exact extract_source_with sites (cached_typed prepared aligned nativeMember)
    (cached_supported recipeAccepted prepared aligned) complete aligned.globals entry

include sites in
/-- Source Syntax is projected from the original input receipt, independently
of the returned compiler Tree and its erased declaration fields. -/
theorem syntax_at : GenericImperativeMatch.Syntax header.function.source (expressionSyntax header) header.context
    (.statements true header.function.body) header.function.resultType :=
  sites.to_for.syntaxTree

/-- Materialize an explicitly retained authentic extraction at its own
returned diagnostics. The full compiler flow and Tree remain unchanged. -/
def profile_at
    (extracted : ReceiptWith (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      true .reachable headers header (compilation header) (expressionSyntax header)
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))
    (catalog : SignatureCatalogWellFormed compiled.compatible.checked.signatures)
    (interpreted : extracted.extracted.diagnostics registry faults) :
    CallableIndexedOwnedAdmittedNamedExpressionHeads.Profile (registry := registry) (faults := faults)
      (certificates := CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation)
      (expressionSyntax := expressionSyntax) (diagnosticPolicy := .reachable) true header administrative :=
  extracted.profile catalog interpreted

include recipeAccepted prepared aligned nativeMember functions owner complete entry sites in
/-- The original extraction supplies an authentic static witness. Any
interpretation must refer to that witness's own returned diagnostics. -/
theorem extract_profile_at
    (catalog : SignatureCatalogWellFormed compiled.compatible.checked.signatures) :
    ∃ extracted : ReceiptWith (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      true .reachable headers header (compilation header) (expressionSyntax header)
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative),
      ∀ _interpreted : extracted.extracted.diagnostics registry faults,
        ∃ profile : CallableIndexedOwnedAdmittedNamedExpressionHeads.Profile (registry := registry) (faults := faults)
          (certificates := CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation)
          (expressionSyntax := expressionSyntax) (diagnosticPolicy := .reachable) true header administrative,
          profile.flow = extracted.flow ∧ HEq profile.tree extracted.extracted.tree := by
  obtain ⟨extracted⟩ := extract_at recipeAccepted prepared aligned nativeMember compilation functions owner complete entry sites
  refine ⟨extracted, ?_⟩
  intro interpreted
  exact ⟨profile_at compilation extracted catalog interpreted, rfl, HEq.rfl⟩

/-- These original child and Source receipts are the remaining static compiler
obligations. The authentic Header supplies all concrete read, binder, allocation,
assignment and match policy equalities. -/
structure StaticChildren (tracked : Bool) (Γ : Core.Context) where
  factory : AssignmentDiagnosticOrigins.Factory tracked .reachable header.function.source
    (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidOperand prepared)
  hidden : GenericImperativeMatch.MatchHiddenFresh header.function.source
  expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = true →
    sourceContext.signatures = compiled.compatible.checked.signatures →
    ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext →
    expressionSyntax header id → header.function.source.lookupExpression? id = some node →
    ExpressionHasType header.function.source sourceContext id node.type →
    header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
    CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation header sourceContext scope id lowered
  assignmentExpressions : ∀ sourceContext scope fuel id lowered,
    sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = true →
    sourceContext.signatures = compiled.compatible.checked.signatures →
    CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext →
    expressionSyntax header id → ∀ node, header.function.source.lookupExpression? id = some node →
    ExpressionHasType header.function.source sourceContext id node.type →
    header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
    CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation header sourceContext scope id lowered ∧
      HasType (SourceCoreLocalCell.coreContext scope ++ Γ) lowered.expression
        (LanguageResult.resultType lowered.type) compiled.indexed.layouts.definitions
  syntaxTree : GenericImperativeMatch.Syntax header.function.source (expressionSyntax header) header.context
    (.statements true header.function.body) header.function.resultType

/-- The same public Header factory derives all fixed compiler policy fields;
only genuine child certificates, raw Syntax and hidden freshness are retained. -/
def policy_inputs {Γ : Core.Context}
    (children : StaticChildren (header := header) (headers := headers) (expressionSyntax := expressionSyntax) prepared compilation tracked Γ) :
    InputsWith (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      true tracked .reachable headers header (compilation header) (expressionSyntax header) Γ :=
  RecursiveNamedPreparedHeaderPolicies.Prepared.inputs_with prepared aligned true
    children.factory children.hidden children.expressions children.assignmentExpressions children.syntaxTree

section Providers
variable (ordinary : owner.key.capturePrefix = 0)

/-- This equality reindexes the same complete actual BodyState at the genuine
ordinary public capture prefix. No captured context is inserted or removed. -/
def ordinary_entry
    (actualEntry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix functions registry header arguments before initialStore mapping world
      administrative actualContext actual ξ frameLocation current ghost) :
    BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations 0 functions registry header arguments before initialStore mapping world
      administrative actualContext actual ξ frameLocation current ghost := by
  simpa only [ordinary] using actualEntry

/-- The static compiler inputs are requested only at an actual ordinary body
entry. They retain original raw Syntax, exact child certificates and actual
native child typing; none is an execution law. -/
abbrev SitesFor (tracked : Bool) :=
  ∀ {arguments before initialStore mapping world administrative actualContext actual ξ frameLocation current ghost},
    BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations 0 functions registry header arguments before initialStore mapping world
      administrative actualContext actual ξ frameLocation current ghost →
    StaticChildren (header := header) (headers := headers) (expressionSyntax := expressionSyntax) prepared compilation tracked
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)

/-- These witnesses retain authentic compiler output and its own interpreted
diagnostics at each actual ordinary parameter entry. They are static receipts. -/
abbrev InterpretedReceiptsFor : Prop :=
  ∀ {arguments before initialStore mapping world administrative actualContext actual ξ frameLocation current ghost},
    BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations 0 functions registry header arguments before initialStore mapping world
      administrative actualContext actual ξ frameLocation current ghost →
    ∃ extracted : ReceiptWith (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      true .reachable headers header (compilation header) (expressionSyntax header)
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative),
      extracted.extracted.diagnostics registry faults

include ordinary in
/-- Authentic interpreted static receipts give a profile provider as a proof
witness. Selection occurs only inside this theorem; each profile materializes
that exact retained receipt and its own diagnostics at the same body entry. -/
theorem profiles_for
    (outputs : InterpretedReceiptsFor (headers := headers) (expressionSyntax := expressionSyntax)
      (registry := registry) (faults := faults) compilation functions owner (header := header))
    (catalog : SignatureCatalogWellFormed compiled.compatible.checked.signatures) :
    Nonempty (CallableIndexedOwnedAdmittedNamedExpressionHeads.ProfilesFor (headers := headers) (owner := owner)
      (functions := functions) (registry := registry) (faults := faults)
      (certificates := CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation)
      (expressionSyntax := expressionSyntax) (diagnosticPolicy := .reachable) (runtime := true) header) := by
  classical
  refine ⟨?_⟩
  intro arguments before initialStore mapping world administrative actualContext actual ξ frameLocation current ghost actualEntry
  let actualEntry := ordinary_entry functions owner ordinary actualEntry
  let extracted := Classical.choose (outputs actualEntry)
  exact profile_at compilation extracted catalog (Classical.choose_spec (outputs actualEntry))

end Providers

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedPublicProfileExtraction
