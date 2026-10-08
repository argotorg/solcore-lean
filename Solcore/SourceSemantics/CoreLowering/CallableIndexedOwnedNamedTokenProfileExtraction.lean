import Solcore.SourceSemantics.CoreLowering.RecursiveNamedEmittedTokenRuntimeProfileFactory
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedPublicProfileExtraction

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
