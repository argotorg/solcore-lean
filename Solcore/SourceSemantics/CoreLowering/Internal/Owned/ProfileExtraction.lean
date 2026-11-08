import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ReadyExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.NamedHeaderReceipts
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.RuntimeProfileFactories
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LambdaReadyFamilies
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.IndirectExpressionHeads
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ReadyContinuations
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.FunctionValuesAndState
import Solcore.Frontend.SourceCoreIndexedSession
import Solcore.SourceSemantics.Dynamic.Program
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LambdaFormation

/-!
# Owned callables: profile extraction

Extraction of named profiles in public, token and emitted form, general function selection and bootstrap receipts.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedPublicProfileExtraction
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedTokenProfileExtraction
/-! The genuine public compiler and its actual parameter entry retain unary
and operand token provenance. Their prepared table supplies these diagnostics
internally. Only unresolved place categories remain at actual assignment atoms. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedTokenProfileExtraction
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open RecursiveNamedPublicSpecializationMeaning RecursiveNamedCatalogRuntimeProfileFactory
open CallableIndexedOwnedNamedPublicProfileExtraction
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {recipe : SourceCoreIndexedSession.Recipe}
  (recipeAccepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
  {row : SourceSpecialization.SpecializedFunction} (prepared : Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)

variable {nativeEntry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
  (nativeMember : nativeEntry ∈ compiled.indexed.entries)

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

/-- Original compiler child and Source receipts do not contain a diagnostic
interpreter. The table factory is constructed at the actual prepared Header. -/
structure Children (Γ : Core.Context) where
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


variable {first : Nat}
  (operandsTyped : AssignmentDiagnosticOrigins.OperandsTyped header.function.source)
  (issued : SourceCoreAssignmentFaultSites.prepare header.function.source first =
    .ok prepared.compilation.own.assignments)

/-- Genuine table preparation supplies the factory; all child fields are copied
from their independent original compiler receipts. -/
def Children.to_static {Γ : Core.Context} (children : Children (header := header) (headers := headers)
    (expressionSyntax := expressionSyntax) compilation Γ) :
    StaticChildren (header := header) (headers := headers) (expressionSyntax := expressionSyntax)
      prepared compilation true Γ where
  factory := AssignmentDiagnosticOrigins.Factory.prepared operandsTyped issued
  hidden := children.hidden
  expressions := children.expressions
  assignmentExpressions := children.assignmentExpressions
  syntaxTree := children.syntaxTree

variable
  (unaryTyped : EmittedDiagnosticTokenPlan.UnaryTyped header.function.source)
  (operandIncluded : ∀ reason token, GenericAssignmentDiagnostics.OperandRep
    prepared.compilation.own.assignments reason token → faults reason token)
  (unaryIncluded : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep
    prepared.compilation.own.assignments reason token → faults reason token)
  (places : EmittedDiagnosticTokenPlan.PlaceReceipts (source := header.function.source)
    (tracked := true) (invalidOperand := GenericAssignmentDiagnostics.token prepared.compilation.own.assignments)
    registry faults)

include recipeAccepted prepared aligned nativeMember functions owner complete entry operandsTyped issued unaryTyped
  operandIncluded unaryIncluded places in
/-- The actual returned token plan interprets unary and operand diagnostics
from this table. Remaining place receipts are queried only at its genuine atoms. -/
theorem interpreted_at_prepared
    (children : Children (header := header) (headers := headers) (expressionSyntax := expressionSyntax) compilation
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) :
    ∃ receipt : ReceiptWith (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      true .reachable headers header (compilation header) (expressionSyntax header)
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative),
      receipt.extracted.diagnostics registry faults := by
  let sites := policy_inputs prepared aligned compilation (Children.to_static prepared compilation operandsTyped issued children)
  obtain ⟨produced⟩ := extract_source_with_tokens (cached_typed prepared aligned nativeMember)
    (cached_supported recipeAccepted prepared aligned) complete aligned.globals entry sites
  have tokens : EmittedDiagnosticTokenPlan.TokensFor
      (AssignmentDiagnosticOrigins.Factory.prepared operandsTyped issued)
      (fun site root => prepared.compilation.own.assignments.reasonAt site root .bitNot) produced.plan := produced.tokens
  have remaining := EmittedDiagnosticTokenPlan.TokensFor.place_faults
    (AssignmentDiagnosticOrigins.Factory.prepared operandsTyped issued)
    (fun site root => prepared.compilation.own.assignments.reasonAt site root .bitNot) tokens places
  have interpreted := tokens.interpret_prepared operandsTyped unaryTyped issued operandIncluded unaryIncluded remaining
  exact ⟨produced.original, (produced.equation registry faults).mpr interpreted⟩

/-- Child static receipts are requested only at real reached ordinary entries. -/
abbrev ChildrenFor :=
  ∀ {arguments before initialStore mapping world administrative actualContext actual ξ frameLocation current ghost},
    BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations 0 functions registry header arguments before initialStore mapping world
      administrative actualContext actual ξ frameLocation current ghost →
    Children (header := header) (headers := headers) (expressionSyntax := expressionSyntax) compilation
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)

include recipeAccepted aligned nativeMember complete operandsTyped issued unaryTyped operandIncluded unaryIncluded places in
omit entry in
/-- Authentic table interpretation constructs the returned static receipt at
each actual Entry. No unary or operand LocalReceipts provider is requested. -/
theorem interpreted_receipts_for_prepared
    (children : ChildrenFor (headers := headers) (expressionSyntax := expressionSyntax)
      (registry := registry) compilation functions owner (header := header)) :
    InterpretedReceiptsFor (headers := headers) (expressionSyntax := expressionSyntax) (registry := registry) (faults := faults)
      compilation functions owner (header := header) := by
  intro arguments before initialStore mapping world administrative actualContext actual ξ frameLocation current ghost actualEntry
  exact interpreted_at_prepared recipeAccepted prepared aligned nativeMember compilation functions owner complete actualEntry
    operandsTyped issued unaryTyped operandIncluded unaryIncluded places (children actualEntry)

include recipeAccepted aligned nativeMember complete operandsTyped issued unaryTyped operandIncluded unaryIncluded places in
omit entry in
/-- Genuine emitted table tokens provide the profile witness internally.
Source child/Syntax and unresolved place typing obligations remain explicit. -/
theorem profiles_for_prepared
    (ordinary : owner.key.capturePrefix = 0)
    (children : ChildrenFor (headers := headers) (expressionSyntax := expressionSyntax)
      (registry := registry) compilation functions owner (header := header))
    (catalog : SignatureCatalogWellFormed compiled.compatible.checked.signatures) :
    Nonempty (CallableIndexedOwnedAdmittedNamedExpressionHeads.ProfilesFor (headers := headers) (owner := owner)
      (functions := functions) (registry := registry) (faults := faults)
      (certificates := CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation)
      (expressionSyntax := expressionSyntax) (diagnosticPolicy := .reachable) (runtime := true) header) :=
  profiles_for compilation functions owner ordinary
    (interpreted_receipts_for_prepared recipeAccepted prepared aligned nativeMember compilation functions owner complete
      operandsTyped issued unaryTyped operandIncluded unaryIncluded places children) catalog
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedTokenProfileExtraction
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralFunctionSelection
/-! Exact selection in the shared rich function relation retains the same
Source value, native carrier and all authentic static receipts. Old ranked and
method closures keep their actual caller prefix; stronger invocation prefixes
need the genuine capture/formation receipt. The unrestricted ordinary branch
retains its full Header prefix and observed Globals1. The principal branch
retains actual Globals1 and the leading parameter bundle. This is finite
provenance inversion, with no execution premise or function-model inverse. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralFunctionSelection
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey NamedSourceAt NamedCapture NamedInstalledCode)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- Each alternative keeps the exact full constructor witness. In particular,
the prefix stored by an old or method closure is retained without strengthening. -/
inductive Selection (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping) : TypeSystem.Ty → Dynamic.Value → Value → Ty → Prop where
  | builtin {sourceType source native type}
      (related : CallableIndexedBuiltinValues.Represents compiled.indexed world sourceType source native type) :
      Selection headers keys registry faults mapping world sourceType source native type
  | named {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
      {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {source : Dynamic.GlobalFunction} {identity : Word}
      (owner : OwnedKey keys) (member : header ∈ headers)
      (sourceAt : NamedSourceAt header rawD source)
      (capture : NamedCapture headers owner.key header mapping world) (installed : NamedInstalledCode capture)
      (number : Word.ofNat? (header.slot + 1) = some identity)
      (projection : compiled.compatible.checked.catalog.project header.named.specialized.function.type = .ok
        (CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType))
      (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
        (.named header.named.signature.key))
      (typed : RuntimeValueHasType world (.closure header.named.signature.parameterType
        (LanguageResult.resultType header.named.signature.resultType) (header.code.rename capture.embedding.lift)
        capture.captured) header.named.signature.functionType compiled.indexed.layouts.definitions) :
      Selection headers keys registry faults mapping world header.named.specialized.function.type (.global source)
        (.pair (.pair (.inRight .unit (.word identity)) (.closure header.named.signature.parameterType
          (LanguageResult.resultType header.named.signature.resultType) (header.code.rename capture.embedding.lift)
          capture.captured)) (.word descriptor.id))
        (CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType)
  | ranked_lambda {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
      {actual : Environment} {callerPrefix : Nat}
      (owner : OwnedKey keys) (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code)
      (body : CallableIndexedOwnedFunctionValues.StaticSupport headers registry faults code)
      (origin : CallableIndexedOwnedFunctionValues.ActualSourceOrigin code history body)
      (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations callerPrefix scope captured.canonical owner.key.frameLocation)
      (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) compiled.indexed.layouts.definitions) :
      Selection headers keys registry faults mapping world (FunctionValues.sourceType function) (.closure function)
        (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)
  | method_lambda {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
      {actual : Environment} {callerPrefix : Nat}
      (owner : OwnedKey keys) (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code)
      (body : CallableIndexedOwnedMethodLambdaSupport.Support code registry faults)
      (origin : CallableIndexedOwnedMethodLambdaSupport.SourceOrigin body history)
      (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations callerPrefix scope captured.canonical owner.key.frameLocation)
      (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) compiled.indexed.layouts.definitions) :
      Selection headers keys registry faults mapping world (FunctionValues.sourceType function) (.closure function)
        (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)
  | principal_lambda {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
      {actual : Environment}
      (owner : OwnedKey keys) (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code)
      (body : CallableIndexedOwnedMethodLambdaSupport.Support code registry faults)
      (origin : CallableIndexedOwnedMethodLambdaSupport.SourceOrigin body history)
      (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
      (leading : captured.administrative[0]? = some body.principal.named.signature.parameterType)
      (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) compiled.indexed.layouts.definitions) :
      Selection headers keys registry faults mapping world (FunctionValues.sourceType function) (.closure function)
        (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)
  | ordinary_lambda {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
      (owner : OwnedKey keys) (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code)
      (body : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults)
      (origin : CallableIndexedOwnedOrdinaryLambdaSupport.SourceOrigin body history)
      (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
        (values := .initial compiled.compatible.checked) body.caller)
      (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
      (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) compiled.indexed.layouts.definitions) :
      Selection headers keys registry faults mapping world (FunctionValues.sourceType function) (.closure function)
        (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)
  | contextual_principal_lambda {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
      {actual : Environment}
      (owner : OwnedKey keys) (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code)
      (body : CallableIndexedOwnedMethodLambdaSupport.Support code registry faults)
      (origin : CallableIndexedOwnedMethodLambdaSupport.SourceOrigin body history)
      (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
      (leading : captured.administrative[0]? = some body.principal.named.signature.parameterType)
      (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) compiled.indexed.layouts.definitions)
      (provenance : CallableIndexedOwnedContextualLambdaProvenance.PrincipalAt code body) :
      Selection headers keys registry faults mapping world (FunctionValues.sourceType function) (.closure function)
        (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)
  | contextual_ordinary_lambda {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
      (owner : OwnedKey keys) (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code)
      (body : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults)
      (origin : CallableIndexedOwnedOrdinaryLambdaSupport.SourceOrigin body history)
      (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
        (values := .initial compiled.compatible.checked) body.caller)
      (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
      (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) compiled.indexed.layouts.definitions)
      (provenance : CallableIndexedOwnedContextualLambdaProvenance.OrdinaryAt code body) :
      Selection headers keys registry faults mapping world (FunctionValues.sourceType function) (.closure function)
        (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)

variable {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping}
  {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {native : Value} {type : Ty}

/-- Finite inversion keeps every receipt and the exact carrier from the
actual shared relation. No weaker projection is used to recover support. -/
theorem of_represents
    (related : CallableIndexedOwnedGeneralLambdaValues.Represents headers keys registry faults
      mapping world sourceType source native type) :
    Selection headers keys registry faults mapping world sourceType source native type := by
  cases related with
  | prior prior =>
    cases prior with
    | prior original =>
      cases original with
      | builtin related => exact .builtin related
      | named owner member sourceAt capture installed number projection descriptor typed =>
        exact .named owner member sourceAt capture installed number projection descriptor typed
      | lambda owner captured code history body origin globals referenceIndex typed =>
        exact .ranked_lambda owner captured code history body origin globals referenceIndex typed
    | method_lambda owner captured code history body origin globals referenceIndex typed =>
      exact .method_lambda owner captured code history body origin globals referenceIndex typed
  | principal_lambda owner captured code history body origin globals leading referenceIndex typed =>
    exact .principal_lambda owner captured code history body origin globals leading referenceIndex typed
  | contextual_principal_lambda owner captured code history body origin globals leading referenceIndex typed provenance =>
    exact .contextual_principal_lambda owner captured code history body origin globals leading referenceIndex typed provenance
  | ordinary_lambda owner captured code history body origin prefixContext globals referenceIndex typed =>
    exact .ordinary_lambda owner captured code history body origin prefixContext globals referenceIndex typed

  | contextual_ordinary_lambda owner captured code history body origin prefixContext globals referenceIndex typed provenance =>
    exact .contextual_ordinary_lambda owner captured code history body origin prefixContext globals referenceIndex typed provenance

/-- The retained receipts reconstruct exactly the same rich relation. This
uses the full witnesses in this selection, rather than a model inclusion. -/
theorem represents (selected : Selection headers keys registry faults mapping world sourceType source native type) :
    CallableIndexedOwnedGeneralLambdaValues.Represents headers keys registry faults mapping world sourceType source native type := by
  cases selected with
  | builtin related => exact .prior (.prior (.builtin related))
  | named owner member sourceAt capture installed number projection descriptor typed =>
    exact .prior (.prior (.named owner member sourceAt capture installed number projection descriptor typed))
  | ranked_lambda owner captured code history body origin globals referenceIndex typed =>
    exact .prior (.prior (.lambda owner captured code history body origin globals referenceIndex typed))
  | method_lambda owner captured code history body origin globals referenceIndex typed =>
    exact .prior (.method_lambda owner captured code history body origin globals referenceIndex typed)
  | principal_lambda owner captured code history body origin globals leading referenceIndex typed =>
    exact .principal_lambda owner captured code history body origin globals leading referenceIndex typed
  | contextual_principal_lambda owner captured code history body origin globals leading referenceIndex typed provenance =>
    exact .contextual_principal_lambda owner captured code history body origin globals leading referenceIndex typed provenance
  | ordinary_lambda owner captured code history body origin prefixContext globals referenceIndex typed =>
    exact .ordinary_lambda owner captured code history body origin prefixContext globals referenceIndex typed

  | contextual_ordinary_lambda owner captured code history body origin prefixContext globals referenceIndex typed provenance =>
    exact .contextual_ordinary_lambda owner captured code history body origin prefixContext globals referenceIndex typed provenance

/-- The exact model's actual value relation supplies finite selected provenance.
All heaps and maps remain those of the caller; no reverse inclusion is assumed. -/
theorem of_model (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {actualRegistry : SourceCoreRawMetadata.Registry}
    (related : (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile).Represents
      actualRegistry mapping world sourceType source native type) :
    Selection headers keys registry faults mapping world sourceType source native type := of_represents related

/-- Selection and the exact rich model describe the same full actual value. -/
theorem model_iff (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (actualRegistry : SourceCoreRawMetadata.Registry) :
    (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile).Represents
      actualRegistry mapping world sourceType source native type ↔
    Selection headers keys registry faults mapping world sourceType source native type :=
  ⟨of_represents, represents⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralFunctionSelection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedObservedGeneralCallee
/-! Selection uses the exact shared function model at the actual successful
callee post. Compatible payload wrappers retain the original raw Source type
view. The same reached state supplies Source value typing and all owned rows;
no model inclusion is inverted and no runtime traversal is introduced. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedObservedGeneralCallee
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {mapping : LocationMap} {world : StoreTyping} {raw : TypeSystem.Ty}
  {function : Dynamic.Closure} {native : Value} {type : Ty}

/-- The selected raw function type and complete provenance describe the same
Source closure and native value at the original reached map and world. -/
def Selected : Prop :=
  ∃ parameter result,
    SourceCoreRawMetadata.runtimeType raw = SourceCoreRawMetadata.runtimeType (.function parameter result) ∧
    CallableIndexedOwnedGeneralFunctionSelection.Selection headers keys registry faults mapping world
      (.function parameter result) (.closure function) native type

private theorem selected_of_representation {raw : TypeSystem.Ty} {sourceValue : Dynamic.Value}
    (related : ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile)
      mapping world raw sourceValue native type) (closure : sourceValue = .closure function) :
    Selected (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (mapping := mapping) (world := world) (raw := raw) (function := function) (native := native) (type := type) := by
  induction related using ValueRep.rec (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ => True) with
  | unit => cases closure
  | bool => cases closure
  | word => cases closure
  | integer => cases closure
  | product => cases closure
  | proxy => cases closure
  | constructed => cases closure
  | mappingValue => cases closure
  | function value =>
    cases closure
    exact ⟨_, _, rfl, CallableIndexedOwnedGeneralFunctionSelection.of_model profile value⟩
  | compatible same inner ih =>
    obtain ⟨parameter, result, view, selected⟩ := ih closure
    exact ⟨parameter, result, same.trans view, selected⟩
  | nil | cons | empty | entry | absent | present => trivial

/-- Only compatible representation wrappers are traversed. The function leaf
uses the exact model relation, retaining every original selected receipt. -/
theorem of_representation
    (related : ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile)
      mapping world raw (.closure function) native type) :
    Selected (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (mapping := mapping) (world := world) (raw := raw) (function := function) (native := native) (type := type) :=
  selected_of_representation profile related rfl

universe u
variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  (context : SourceSemantics.Context)
  {index : ProtectedStateTransition.Index} (reached : callerProtocol.State index)

/-- Real successful callee admission pairs complete selected provenance with
original Source typing and the actual reached owned pool. No captured history
is substituted for the current row and no argument/body meaning is assumed. -/
theorem at_success
    (post : PostAdmission bridge context raw (.value (.closure function)) reached)
    (related : ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile)
      index.mapping index.world raw (.closure function) native type) :
    Selected (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (mapping := index.mapping) (world := index.world) (raw := raw)
      (function := function) (native := native) (type := type) ∧
    Dynamic.ValueHasType context index.heap (.closure function) raw ∧ Admission bridge context reached := by
  exact ⟨of_representation (profile := profile) related, post.at_value⟩

/-- At an ordinary raw function type, the original Source post exposes exact
parameter/result types, complete code validity and capture agreement at this
same heap. These facts are independent of the selected native type vector. -/
theorem at_function_success {parameter result : TypeSystem.Ty}
    (post : PostAdmission bridge context (.function parameter result) (.value (.closure function)) reached)
    (related : ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile)
      index.mapping index.world (.function parameter result) (.closure function) native type) :
    Selected (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (mapping := index.mapping) (world := index.world) (raw := .function parameter result)
      (function := function) (native := native) (type := type) ∧
    Admission bridge context reached ∧
    parameter = TypeSystem.Ty.productMany (function.parameters.map (fun binder => binder.scheme.body)) ∧
    result = function.resultType ∧
    function.context.signatures = context.signatures ∧
    Dynamic.ClosureCodeValid function.context function ∧
    function.evidence.Covers function.context ∧
    Dynamic.EnvironmentAgrees index.heap function.context.locals function.captured := by
  obtain ⟨selected, typed, admitted⟩ := at_success profile bridge context reached post related
  exact ⟨selected, admitted, typed.closure_function_inv⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedObservedGeneralCallee
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedCallStageAcceptance
/-! An actual selected guard accepts only from its independent original stage
facts or from the exact original validator success equation. Effectful callers
and runtime callers retain distinct real premises; argument and result comptime
conditions stay explicit. These finite static adapters supply only the first
native gate. IndirectApplicationValid and prepareGuard success do not imply
stage acceptance, and staged rejection is not a plain Dynamic fault. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedCallStageAcceptance
open Core Frontend SourceInference
open Staging.CallGuard

variable {frame : Staging.CallBoundary.Frame} {site : SourceCoreCallableContracts.Callsite}
  {call : ExpressionId} {arguments : List ExpressionId} {source : Dynamic.Value} {native : Value}
  (dispatch : CallStageBoundary.Dispatch frame site call arguments source native)

/-- The real selected accepted guard yields the exact native first decision. -/
theorem before_arguments (accepted : Staging.CallBoundary.GuardAccepts frame call arguments source)
    (unknown : Word) :
    CallableContract.decision site.gates .beforeArguments unknown dispatch.contract = none := by
  rw [site.decision_known .beforeArguments unknown dispatch.contract dispatch.row dispatch.found]
  exact SourceCoreCallableContracts.reason_accepted dispatch.row site.reasonAt .beforeArguments
    (dispatch.accepted accepted)

include dispatch in
/-- Genuine effectful caller metadata bypasses only the original first guard. -/
theorem effectful (caller : Effectful frame.stages) :
    Staging.CallBoundary.GuardAccepts frame call arguments source :=
  .contract dispatch.bound (.effectful caller)

/-- Genuine runtime caller receipts keep every original ordered argument stage
and the independent result stage check. -/
theorem runtime (caller : ¬ Effectful frame.stages)
    (argumentsPass : ArgumentsAccept frame.stages dispatch.guard.contract.stagedResult 0
      dispatch.guard.contract.parameters arguments)
    (resultPass : ResultAccepts frame.stages call dispatch.guard.contract.stagedResult) :
    Staging.CallBoundary.GuardAccepts frame call arguments source :=
  .contract dispatch.bound (.ordinary caller argumentsPass resultPass)

/-- Exact validator success for this same retained guard constructs its
independent Source acceptance. Preparing a guard alone supplies no verdict. -/
theorem of_validator
    (checked : SourceCompilationPlan.validateStagedCallableContract dispatch.guard.sidecar.caller
      dispatch.guard.node dispatch.guard.arguments dispatch.guard.contract.parameters
      dispatch.guard.contract.stagedResult dispatch.guard.contract.owner = .ok ()) :
    Staging.CallBoundary.GuardAccepts frame call arguments source := by
  have passed : dispatch.guard.decision = .ok () := dispatch.guard.exact.symm.trans checked
  have accepted := (CallStageGuard.guard_accepts_iff dispatch.guard).mp passed
  apply Staging.CallBoundary.GuardAccepts.contract dispatch.bound
  simpa only [dispatch.call_eq, dispatch.arguments_eq, ← dispatch.stages] using accepted

/-- Exact original guard success closes the native stage gate at its retained
contract word, without observing or evaluating a child expression. -/
theorem before_arguments_of_validator
    (checked : SourceCompilationPlan.validateStagedCallableContract dispatch.guard.sidecar.caller
      dispatch.guard.node dispatch.guard.arguments dispatch.guard.contract.parameters
      dispatch.guard.contract.stagedResult dispatch.guard.contract.owner = .ok ())
    (unknown : Word) :
    CallableContract.decision site.gates .beforeArguments unknown dispatch.contract = none :=
  before_arguments dispatch (of_validator dispatch checked) unknown

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedCallStageAcceptance
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedBootstrapReceipts
/-! The named owner comes from the actual prepared bootstrap. Its zero
capture prefix is the literal key produced by initialization. An immutable
key embedding retains that complete key when the domain grows. Source
headers and their real cache ledger remain independent static inputs. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedBootstrapReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory RecursiveNamedCatalog
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey KeyEmbedding NamedCapture)
open CallableIndexedOwnedFunctionEntries (OwnedPool)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (Header compiled program)}

/-- This packet keeps the actual initialization authority and its static
recipe receipts. It contains no assumed capture-prefix equality. -/
structure Bootstrap
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    (registry : SourceCoreRawMetadata.Registry) (world : StoreTyping) where
  recipe : SourceCoreIndexedSession.Recipe
  accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe
  ledger : Ledger headers compiled.indexed.secondPass.closures
  sizes : ∀ header, header ∈ headers → header.globals = compiled.indexed.base.globals.length
  locals : ∀ header, header ∈ headers → header.function.context.locals = []
  heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions [] world ⟨[]⟩
    (RecursiveNamedCatalogPreparedInitialization.store compiled)
  entry : Entry (prepared := compiled.indexed.ancestry)
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers
    (fun header => RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot)
    0 0 [] [] world ⟨[]⟩ (RecursiveNamedCatalogPreparedInitialization.store compiled)
    (RecursiveNamedCatalogPreparedInitialization.environment compiled)

namespace Bootstrap

variable {functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {registry : SourceCoreRawMetadata.Registry} {world : StoreTyping}

def key (packet : Bootstrap (headers := headers) functions registry world) : Key compiled program :=
  ⟨(fun header => RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot),
    0, packet.entry.authority.frameLocation⟩

def keys (packet : Bootstrap (headers := headers) functions registry world) : List (Key compiled program) :=
  [packet.key]

def owner (packet : Bootstrap (headers := headers) functions registry world) : OwnedKey packet.keys :=
  ⟨⟨0, by simp [keys]⟩⟩

theorem owner_key (packet : Bootstrap (headers := headers) functions registry world) :
    packet.owner.key = packet.key := by
  rfl

theorem capture_zero (packet : Bootstrap (headers := headers) functions registry world) :
    packet.owner.key.capturePrefix = 0 := by
  rfl

/-- The original singleton producer retains the same complete authority. -/
def pool (packet : Bootstrap (headers := headers) functions registry world) :
    OwnedPool headers packet.keys [] world ⟨[]⟩
      (RecursiveNamedCatalogPreparedInitialization.store compiled) :=
  CallableIndexedAuthorityPool.Pool.singleton
    (CallableIndexedAuthorityPool.EntryValid.of_authority packet.entry.authority)

theorem frame_read (packet : Bootstrap (headers := headers) functions registry world) :
    (RecursiveNamedCatalogPreparedInitialization.store compiled).read? packet.owner.key.frameLocation =
      some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame
        (packet.pool.rows packet.owner.position).authority.current) :=
  CallableIndexedOwnedFunctionEntries.reached_frame_read packet.pool packet.owner.position

theorem global_locations (packet : Bootstrap (headers := headers) functions registry world)
    (header : Header compiled program) :
    packet.owner.key.locations header =
      RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot := by
  rfl

/-- Both the capture and installed-code witness come from the same live
bootstrap row. The cache ledger identifies the actual emitted full closure. -/
theorem named_capture (packet : Bootstrap (headers := headers) functions registry world)
    {header : Header compiled program} (member : header ∈ headers) :
    ∃ capture : NamedCapture headers packet.owner.key header [] world,
      CallableIndexedOwnedFunctionValues.NamedInstalledCode capture := by
  obtain ⟨capture⟩ := CallableIndexedOwnedFunctionEntries.capture_from_pool
    packet.pool packet.owner member
  refine ⟨NamedCapture.of_capture capture, ?_⟩
  exact CallableIndexedOwnedFunctionValues.NamedInstalledCode.of_bootstrap capture
    (packet.global_locations header) (packet.ledger.cached header member)

end Bootstrap

/-- Invoke the actual bootstrap entry factory once. Source inventory facts
are retained alongside that returned state; no arbitrary named capture is
upgraded to an initialization packet. -/
theorem of_recipe {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (ledger : Ledger headers compiled.indexed.secondPass.closures)
    (sizes : ∀ header, header ∈ headers → header.globals = compiled.indexed.base.globals.length)
    (locals : ∀ header, header ∈ headers → header.function.context.locals = [])
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    (registry : SourceCoreRawMetadata.Registry) :
    ∃ world, Nonempty (Bootstrap (headers := headers) functions registry world) := by
  obtain ⟨world, heaps, ⟨entry⟩⟩ :=
    RecursiveNamedCatalogPreparedInitialization.entry compiled
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers ledger sizes locals
      accepted rfl functions registry
  exact ⟨world, ⟨⟨recipe, accepted, ledger, sizes, locals, heaps, entry⟩⟩⟩

/-- Positive named-owner provenance. The selected owner is defined by the
real bootstrap token and a complete immutable-key embedding. -/
structure NamedOwner (keys : List (Key compiled program))
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    (registry : SourceCoreRawMetadata.Registry) where
  world : StoreTyping
  bootstrap : Bootstrap (headers := headers) functions registry world
  embedding : KeyEmbedding bootstrap.keys keys

namespace NamedOwner

variable {keys : List (Key compiled program)}
  {functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {registry : SourceCoreRawMetadata.Registry}

def owner (packet : NamedOwner (headers := headers) keys functions registry) : OwnedKey keys :=
  packet.embedding.map packet.bootstrap.owner

def of_bootstrap {world : StoreTyping}
    (packet : Bootstrap (headers := headers) functions registry world)
    (embedding : KeyEmbedding packet.keys keys) :
    NamedOwner (headers := headers) keys functions registry :=
  ⟨world, packet, embedding⟩

theorem key_eq (packet : NamedOwner (headers := headers) keys functions registry) :
    packet.owner.key = packet.bootstrap.owner.key :=
  packet.embedding.same packet.bootstrap.owner

theorem capture_zero (packet : NamedOwner (headers := headers) keys functions registry) :
    packet.owner.key.capturePrefix = 0 := by
  rw [packet.key_eq]
  exact packet.bootstrap.capture_zero

theorem globals (packet : NamedOwner (headers := headers) keys functions registry)
    {header : Header compiled program} (member : header ∈ headers) :
    header.globals = compiled.indexed.base.globals.length :=
  packet.bootstrap.sizes header member

theorem global_locations (packet : NamedOwner (headers := headers) keys functions registry)
    (header : Header compiled program) :
    packet.owner.key.locations header =
      RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot := by
  rw [packet.key_eq]
  exact packet.bootstrap.global_locations header

/-- Retain the same bootstrap capture through the whole-key embedding. This
does not infer bootstrap provenance from an arbitrary reached capture. -/
theorem named_capture (packet : NamedOwner (headers := headers) keys functions registry)
    {header : Header compiled program} (member : header ∈ headers) :
    ∃ capture : NamedCapture headers packet.owner.key header [] packet.world,
      CallableIndexedOwnedFunctionValues.NamedInstalledCode capture := by
  obtain ⟨capture, installed⟩ := packet.bootstrap.named_capture member
  let changed := capture.rekey packet.key_eq
  refine ⟨changed, ?_⟩
  simpa only [CallableIndexedOwnedFunctionValues.NamedInstalledCode, changed,
    NamedCapture.rekey_embedding] using installed

end NamedOwner
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedBootstrapReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedFailedSessionFaultObservation
/-! An actual failed ordinary root request keeps its exact native completion
and diagnostic receiver. RootStart fixes the selected request and key; the
completion receipt fixes the returned values and owned slot weakening.
Source failure origins and exported heap equality remain independent. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedFailedSessionFaultObservation
open Frontend SourceCoreIndexedSession

variable {artifact : Artifact} {origin returned : Session artifact}
  {checkpoint : Checkpoint artifact} {key : Key} {arguments : List SourceCoreIndexedSession.Value}
  {boundaryFuel fuel : Nat} {native : Core.Value} {store : Core.Store} {reason : Core.Word}
  {diagnostic : SourceCoreFaultSites.Diagnostic}

/-- The same pending request and returned values determine the same lookup.
This proof compares the original finite wrappers; it does not run a factory. -/
theorem failed_root_diagnostic
    (started : checkpoint.RootStart origin key arguments boundaryFuel)
    (completed : checkpoint.FailedResultAt fuel native store reason returned)
    (accepted : checkpoint.diagnostic reason = .ok (some diagnostic)) :
    returned.diagnostic key reason = .ok (some diagnostic) := by
  obtain ⟨root, found, _key, _length, encoded, _encoded, _origin, request,
      _world, _state, _registry, _values⟩ := started
  obtain ⟨_done, _decoded, _store, _future, values, owner, _authority, _prefix, _slots⟩ := completed
  unfold Checkpoint.diagnostic at accepted
  unfold Session.diagnostic
  simp only [found, pure, Except.pure, bind, Except.bind]
  simpa only [request, ← values, pure, Except.pure, bind, Except.bind] using accepted

/-- The receiver belongs to this actual failed request and returned session.
Its table retains the exact native token and actual decoded public diagnostic.
The original completion receipt supplies every current store and owner field. -/
structure Packet
    (checkpoint : Checkpoint artifact) (origin returned : Session artifact)
    (key : Key) (arguments : List SourceCoreIndexedSession.Value) (boundaryFuel fuel : Nat)
    (native : Core.Value) (store : Core.Store) (reason : Core.Word)
    (diagnostic : SourceCoreFaultSites.Diagnostic) : Prop where
  started : checkpoint.RootStart origin key arguments boundaryFuel
  completed : checkpoint.FailedResultAt fuel native store reason returned
  publicDecode : returned.diagnostic key reason = .ok (some diagnostic)
  receiver : ∃ table : SourceCoreFaultSites.Table,
    returned.DiagnosticTableAt key table ∧ table.diagnostic? reason = some diagnostic

/-- Actual pending diagnostic acceptance transfers to the failed session.
The existing receipt identifies the very table, whose genuine registry rebuild
and filtered callable append are supplied by DiagnosticTableAt.rebuild. -/
theorem packet_of_pending
    (started : checkpoint.RootStart origin key arguments boundaryFuel)
    (completed : checkpoint.FailedResultAt fuel native store reason returned)
    (accepted : checkpoint.diagnostic reason = .ok (some diagnostic)) :
    Packet checkpoint origin returned key arguments boundaryFuel fuel native store reason diagnostic := by
  have decoded := failed_root_diagnostic started completed accepted
  exact ⟨started, completed, decoded, returned.diagnostic_table_receipt decoded⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedFailedSessionFaultObservation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedEmittedProfileExtraction
/-! The genuine public compiler and its actual parameter entry produce the
retained diagnostic plan. Concrete local static receipts interpret that plan
internally; the authentic output then supplies the closed named family profile. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedEmittedProfileExtraction
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open RecursiveNamedPublicSpecializationMeaning RecursiveNamedCatalogRuntimeProfileFactory
open CallableIndexedOwnedNamedPublicProfileExtraction
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {recipe : SourceCoreIndexedSession.Recipe}
  (recipeAccepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
  {row : SourceSpecialization.SpecializedFunction} (prepared : Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)

variable {nativeEntry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
  (nativeMember : nativeEntry ∈ compiled.indexed.entries)

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
/-- Genuine emitted diagnostics are interpreted from concrete local static
receipts at the exact ordinary parameter entry. -/
theorem interpreted_at
    (localReceipts : EmittedDiagnosticPlan.Plan.LocalReceipts (factory := sites.factory) registry faults) :
    ∃ receipt : ReceiptWith (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      true .reachable headers header (compilation header) (expressionSyntax header)
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative),
      receipt.extracted.diagnostics registry faults := by
  exact interpreted_source_with (cached_typed prepared aligned nativeMember)
    (cached_supported recipeAccepted prepared aligned) complete aligned.globals entry sites localReceipts

include recipeAccepted aligned nativeMember complete in
omit entry sites in
/-- Each actual body entry supplies original Source Syntax and child static
receipts; the retained compiler plan derives its own diagnostic interpretation. -/
theorem interpreted_receipts_for
    (children : SitesFor (header := header) (headers := headers) (expressionSyntax := expressionSyntax)
      prepared compilation functions owner tracked)
    (localReceipts : ∀ {arguments before initialStore mapping world administrative actualContext actual ξ frameLocation current ghost}
      (actualEntry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers owner.key.locations 0 functions registry header arguments before initialStore mapping world
        administrative actualContext actual ξ frameLocation current ghost),
      EmittedDiagnosticPlan.Plan.LocalReceipts (factory := (children actualEntry).factory) registry faults) :
    InterpretedReceiptsFor (headers := headers) (expressionSyntax := expressionSyntax) (registry := registry) (faults := faults)
      compilation functions owner (header := header) := by
  intro arguments before initialStore mapping world administrative actualContext actual ξ frameLocation current ghost actualEntry
  let inputs := policy_inputs prepared aligned compilation (children actualEntry)
  exact interpreted_at recipeAccepted prepared aligned nativeMember compilation functions owner complete actualEntry inputs
    (localReceipts actualEntry)

include recipeAccepted aligned nativeMember complete in
omit entry sites in
/-- The actual public emitted receipts construct the static profile provider
as a proposition. No completed body or diagnostic-output provider is requested. -/
theorem profiles_for_emitted
    (ordinary : owner.key.capturePrefix = 0)
    (children : SitesFor (header := header) (headers := headers) (expressionSyntax := expressionSyntax)
      prepared compilation functions owner tracked)
    (localReceipts : ∀ {arguments before initialStore mapping world administrative actualContext actual ξ frameLocation current ghost}
      (actualEntry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers owner.key.locations 0 functions registry header arguments before initialStore mapping world
        administrative actualContext actual ξ frameLocation current ghost),
      EmittedDiagnosticPlan.Plan.LocalReceipts (factory := (children actualEntry).factory) registry faults)
    (catalog : SignatureCatalogWellFormed compiled.compatible.checked.signatures) :
    Nonempty (CallableIndexedOwnedAdmittedNamedExpressionHeads.ProfilesFor (headers := headers) (owner := owner)
      (functions := functions) (registry := registry) (faults := faults)
      (certificates := CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation)
      (expressionSyntax := expressionSyntax) (diagnosticPolicy := .reachable) (runtime := true) header) :=
  profiles_for compilation functions owner ordinary
    (interpreted_receipts_for recipeAccepted prepared aligned nativeMember compilation functions owner complete children localReceipts) catalog
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedEmittedProfileExtraction
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedProgramAdmission
/-! Actual named program outcomes supply successful Source value and heap
admission at the returned caller state. Saved stable rows follow the actual
administrative effects. The original program derivation identifies the
Header body and retains independent Source execution. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedProgramAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedSourceAdmission (PostAdmission)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)

/-- Genuine program success supplies raw typing at this returned state.
Fault outcomes retain every actual row's stable history. -/
theorem after_program_outcome
    (header : CallableIndexedOwnedFunctionValues.Header compiled program)
    {initial final : ProtectedStateTransition.Index}
    (first : callerProtocol.State initial) (last : callerProtocol.State final)
    (stable : StableRows (bridge.pool first))
    {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (executed : Dynamic.ProgramOutcome program
      (RecursiveNamedProgramEntrySource.entry header arguments) initial.heap outcome final.heap)
    (frame : AdministrativePreserved initial.mapping initial.store final.mapping final.store) :
    PostAdmission bridge header.function.context header.function.resultType outcome last := by
  refine ⟨StableRows.after_administrative (bridge.pool first) (bridge.pool last) stable frame, ?_⟩
  intro value same
  cases executed with
  | value evaluated =>
    cases same
    obtain ⟨bodyInstance, valid, preserved⟩ := evaluated.preserves
    have sameBody := BuiltinNamedCalls.instantiation_unique_of_wellFormed
      evaluated.program_well_formed valid.instantiates header.frame.instantiated
    cases sameBody
    exact ⟨by simpa only [← header.frame.context, ← header.frame.result] using preserved.result_typed,
      by simpa only [← header.frame.context] using preserved.heap_typed⟩
  | fault _ => cases same

/-- Eliminate the original transition once and retain that same returned
state, its actual relation and the program-derived post-admission. -/
theorem after_program_transition
    (header : CallableIndexedOwnedFunctionValues.Header compiled program)
    {initial final : ProtectedStateTransition.Index}
    (first : callerProtocol.State initial)
    (stable : StableRows (bridge.pool first))
    {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (executed : Dynamic.ProgramOutcome program
      (RecursiveNamedProgramEntrySource.entry header arguments) initial.heap outcome final.heap)
    (frame : AdministrativePreserved initial.mapping initial.store final.mapping final.store)
    (transition : ProtectedStateTransition.Transition callerProtocol first final) :
    ∃ last : callerProtocol.State final,
      callerProtocol.Relates first last ∧
        PostAdmission bridge header.function.context header.function.resultType outcome last := by
  obtain ⟨last, related⟩ := transition
  exact ⟨last, related, after_program_outcome bridge header first last stable executed frame⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedProgramAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedFormationHeads
/-! Actual literal lambda receipts select one finite formation branch. An
ordinary Header retains its nested packet; a genuine trait-generated lambda
retains its principal packet and full Source seed. Selection contains original
Code and Source observations, never an arbitrary callee classification law.
Both endpoints use already proved formation leaves without another fold. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedFormationHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission CallableIndexedLambdaNestedRuntimeBodyMeaning
open CallableIndexedOwnedMethodLambdaSupport

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)

/-- This is an actual ordinary lambda branch, including its full accepted
Code, Source occurrence, ranked body and current captured principal packet. -/
structure Ordinary where
  caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)
  owner : CallableIndexedOwnedFunctionValues.OwnedKey keys
  rank : Nat
  source : TypedSource
  context : SourceSemantics.Context
  evidence : Dynamic.EvidenceEnvironment
  scope : SourceCoreLocalCell.Scope
  id : ExpressionId
  lowered : SourceCoreBasic.LoweredExpr
  head : LambdaAt (values := .initial compiled.compatible.checked) headers caller registry faults rank
    source context evidence scope id lowered
  mapping : LocationMap
  world : StoreTyping
  heap : Dynamic.Heap
  store : Store
  canonical : Environment
  actual : Environment
  administrative : Core.Context
  actualContext : Core.Context
  environment : Dynamic.Environment
  embedding : Renaming
  initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩
  packet : CallableIndexedOwnedNestedCanonicalState.Packet owner caller _ initial
  complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers
  globals : caller.globals = compiled.indexed.base.globals.length
  slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length
  prefixZero : owner.key.capturePrefix = 0
  related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions
  agrees : EnvironmentsAgree embedding canonical actual
  nativeTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions
  wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)
  runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source
  covers : evidence.Covers context
  locals : Dynamic.EnvironmentAgrees heap context.locals environment
  typed : ExpressionHasType source context id head.code.sourceNode.type
  sameSource : source = CallableIndexedNamedGeneration.source caller.named
  unique : NodeOccurrencesUnique source
  heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile) mapping world heap store
  admitted : Admission (CallableIndexedOwnedIndirectCallerProtocol.forget_slots
    (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner caller)) context ⟨initial, packet⟩

/-- This is the actual Header-free lambda Code at its genuine method Source
occurrence. Captures and principal authority are the real input receipts. -/
structure Method where
  function : Dynamic.Closure
  owner : CallableIndexedOwnedFunctionValues.OwnedKey keys
  scope : SourceCoreLocalCell.Scope
  mapping : LocationMap
  world : StoreTyping
  heap : Dynamic.Heap
  store : Store
  actual : Environment
  captured : Captures compiled.indexed mapping world scope function.captured actual
  code : Code compiled.indexed function scope captured.administrative
  support : Support code registry faults
  initial : State headers keys ⟨scope, mapping, world, heap, store, captured.canonical⟩
  packet : CallableIndexedOwnedOriginCanonicalState.Packet owner support.principal.named _ initial
  wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)
  runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source
  covers : function.evidence.Covers function.context
  locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured
  typed : ExpressionHasType function.source function.context code.id code.sourceNode.type
  sourceType : code.sourceNode.type = FunctionValues.sourceType function
  copied : code.policy.snapshotLambda code.id = true
  ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions []
  coercions : code.sourceNode.coercions = []
  heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile) mapping world heap store
  admitted : Admission (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    function.context ⟨initial, packet⟩

/-- Branch construction requires the genuine actual compiler and Source
receipt itself; this sum supplies no classifier for arbitrary closure values. -/
inductive Selected where
  | ordinary (receipt : Ordinary (headers := headers) (keys := keys) (registry := registry) (faults := faults) profile)
  | method (receipt : Method (headers := headers) (keys := keys) (registry := registry) (faults := faults) profile)

/-- The selected branch retains its own authentic protocol without coercion. -/
def protocol (selected : Selected (headers := headers) (keys := keys) (registry := registry) (faults := faults) profile) :
    ProtectedStateTransition.Protocol (Records keys) :=
  match selected with
  | .ordinary receipt => CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) receipt.owner receipt.caller
  | .method receipt => CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) receipt.owner receipt.support.principal.named

/-- Original Source derivations refer to the selected actual occurrence. -/
def SourceAt (selected : Selected (headers := headers) (keys := keys) (registry := registry) (faults := faults) profile)
    (size : Nat) (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) : Prop :=
  match selected with
  | .ordinary receipt => RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      receipt.context receipt.evidence receipt.source receipt.environment receipt.heap receipt.id outcome after
  | .method receipt => RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      receipt.function.context receipt.function.evidence receipt.function.source receipt.function.captured
      receipt.heap receipt.code.id outcome after

/-- Native grades measure the original emitted branch at its actual captures. -/
def NativeAt (selected : Selected (headers := headers) (keys := keys) (registry := registry) (faults := faults) profile)
    (size : Nat) (result : Value) (finalStore : Store) : Prop :=
  match selected with
  | .ordinary receipt => EvaluationSize size receipt.actual receipt.store
      (receipt.lowered.expression.rename receipt.embedding) result finalStore
  | .method receipt => EvaluationSize size receipt.actual receipt.store
      (receipt.code.lowered.expression.rename receipt.captured.embedding) result finalStore

/-- The complete existing leaf result retains the branch's exact reached
packet, ordered pool, real relation and Source post admission. -/
def ResultAt (selected : Selected (headers := headers) (keys := keys) (registry := registry) (faults := faults) profile)
    (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) (result : Value) (finalStore : Store) : Prop :=
  match selected with
  | .ordinary receipt => CallableIndexedOwnedAdmittedOrdinaryLambdaFormation.ResultAt
      (actual := receipt.actual) (ξ := receipt.embedding) receipt.head profile receipt.owner receipt.initial receipt.packet
      outcome after result finalStore
  | .method receipt => CallableIndexedOwnedAdmittedMethodLambdaFormation.ResultAt receipt.captured receipt.code receipt.support
      receipt.owner receipt.initial receipt.packet profile outcome after result finalStore

/-- Source dispatch closes both selected literal branches from authentic
receipts. No completed expression or body meaning is an input. -/
theorem preserves_at (selected : Selected (headers := headers) (keys := keys) (registry := registry) (faults := faults) profile)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : SourceAt profile selected size outcome after) :
    ∃ result finalStore, ResultAt profile selected outcome after result finalStore := by
  cases selected with
  | ordinary receipt =>
    exact CallableIndexedOwnedAdmittedOrdinaryLambdaFormation.preserves_at receipt.head profile receipt.complete
      receipt.globals receipt.slots receipt.owner receipt.prefixZero receipt.initial receipt.packet receipt.related
      receipt.agrees receipt.nativeTyped receipt.wellFormed receipt.runtime receipt.covers receipt.locals receipt.typed
      receipt.sameSource receipt.unique receipt.heaps receipt.admitted trace
  | method receipt =>
    exact CallableIndexedOwnedAdmittedMethodLambdaFormation.preserves_at receipt.captured receipt.code receipt.support
      receipt.owner receipt.initial receipt.packet profile receipt.wellFormed receipt.runtime receipt.covers receipt.locals
      receipt.typed receipt.sourceType receipt.copied receipt.ordinary receipt.coercions receipt.heaps receipt.admitted
      trace

/-- Reflection reuses each original native producer and independently sized
Source result, preserving that branch's exact pool and principal packet. -/
theorem reflects_at (selected : Selected (headers := headers) (keys := keys) (registry := registry) (faults := faults) profile)
    {size : Nat} {result : Value} {finalStore : Store}
    (completed : NativeAt profile selected size result finalStore) :
    ∃ sourceSize outcome after, SourceAt profile selected sourceSize outcome after ∧
      ResultAt profile selected outcome after result finalStore := by
  cases selected with
  | ordinary receipt =>
    exact CallableIndexedOwnedAdmittedOrdinaryLambdaFormation.reflects_at receipt.head profile receipt.complete
      receipt.globals receipt.slots receipt.owner receipt.prefixZero receipt.initial receipt.packet receipt.related
      receipt.agrees receipt.nativeTyped receipt.wellFormed receipt.runtime receipt.covers receipt.locals receipt.typed
      receipt.sameSource receipt.unique receipt.heaps receipt.admitted completed
  | method receipt =>
    exact CallableIndexedOwnedAdmittedMethodLambdaFormation.reflects_at receipt.captured receipt.code receipt.support
      receipt.owner receipt.initial receipt.packet profile receipt.wellFormed receipt.runtime receipt.covers receipt.locals
      receipt.typed receipt.sourceType receipt.copied receipt.ordinary receipt.coercions receipt.heaps receipt.admitted
      completed

/-- The original ordinary producer retains its complete stronger closure
receipt, including exact captures, Header support and full Source history, for
a formed closure over its copies. -/
def ordinary_closure (receipt : Ordinary (headers := headers) (keys := keys) (registry := registry) (faults := faults) profile)
    (formedRecord : CallableIndexedOwnedLambdaFormationReceipts.FormedRecord receipt.head receipt.complete receipt.globals
      receipt.initial receipt.owner receipt.prefixZero receipt.packet.observed receipt.packet.carried receipt.packet.bundle
      receipt.related receipt.agrees receipt.nativeTyped
      (model := CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile))) :=
  CallableIndexedOwnedLambdaFormationReceipts.of_formation receipt.head profile receipt.complete receipt.globals receipt.slots
    receipt.initial receipt.owner receipt.prefixZero receipt.packet.observed receipt.packet.carried receipt.packet.bundle
    receipt.related receipt.agrees receipt.nativeTyped receipt.heaps formedRecord

/-- The method producer uses this same actual principal row's complete history. -/
def method_history (receipt : Method (headers := headers) (keys := keys) (registry := registry) (faults := faults) profile) :=
  CallableIndexedOwnedMethodLambdaFormationReceipts.history_at receipt.captured receipt.code receipt.support receipt.owner
    receipt.initial receipt.packet

/-- The exact method Source seed is established by that actual producer. -/
theorem method_source_origin (receipt : Method (headers := headers) (keys := keys) (registry := registry) (faults := faults) profile) :
    SourceOrigin receipt.support (method_history profile receipt) :=
  CallableIndexedOwnedMethodLambdaFormationReceipts.source_origin receipt.captured receipt.code receipt.support receipt.owner
    receipt.initial receipt.packet

/-- Invocation's leading bundle is the actual captured packet observation. -/
theorem method_leading (receipt : Method (headers := headers) (keys := keys) (registry := registry) (faults := faults) profile) :
    receipt.captured.administrative[0]? = some receipt.support.principal.named.signature.parameterType :=
  CallableIndexedOwnedMethodLambdaFormationReceipts.leading receipt.captured receipt.code receipt.support receipt.owner
    receipt.initial receipt.packet

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedFormationHeads
end
