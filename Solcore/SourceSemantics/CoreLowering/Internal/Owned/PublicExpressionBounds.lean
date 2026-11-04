import Solcore.SourceSemantics.CoreLowering.Internal.Owned.NamedHeaderReceipts
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ProfileExtraction
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceMissingTerminalDiagnostics
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceConcretePreparation
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StatePlaceAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StatementAdmission
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceProjectionDiagnosticCoverage
import Solcore.SourceSemantics.CoreLowering.GenericAssignmentPreparedOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.AssignmentHeads
import Solcore.SourceSemantics.CoreLowering.SourceDiagnosticTyping
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.AssignmentHeads
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LexicalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.ForHeaders
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NamedCatalog
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.ImperativeMatches
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogEntries
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.RuntimeBodies

/-!
# Owned callables: public expression bounds

Public bounds of ready named expressions, with token and prepared forms, place and shape diagnostics, and the prepared catalog.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicReadyNamedExpressionBounds
/-! Genuine public Header receipts and explicitly interpreted static compiler
outputs supply proof-local profile providers to the already closed named
family. Ordinary/direct calls retain actual Source typing and runtime ledgers;
residual compiler diagnostics and independent Syntax remain static inputs. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicReadyNamedExpressionBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedOwnedNamedReadyFamilyReceipts (body_protocol bridge origin Index)
open CallableIndexedOwnedExpressionHeads (Globals argumentProtocol)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {callerCompilation : SourceCoreFunctions.Context}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

/-- The complete actual public compiler packet retains its original cached
code, metadata, independent dictionary and checked native entry membership. -/
structure PublicReceipt (header : CallableIndexedOwnedFunctionValues.Header compiled
    (Program.ofChecked compiled.sourceProgram)) where
  recipe : SourceCoreIndexedSession.Recipe
  accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe
  row : SourceSpecialization.SpecializedFunction
  prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row
  instantiation : DeclarationInstantiation
  aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header
  nativeEntry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts
  nativeMember : nativeEntry ∈ compiled.indexed.entries

/-- This is the actual named compiler context, including its fixed bundle slot. -/
def compilation (header : CallableIndexedOwnedFunctionValues.Header compiled
    (Program.ofChecked compiled.sourceProgram)) : SourceCoreFunctions.Context :=
  CallableIndexedNamedGeneration.context compiled.indexed header.named

/-- The genuine public cached code and support feed the original extraction at
the exact ordinary parameter entry. Returned diagnostics remain that receipt's. -/
theorem extract_at (header : CallableIndexedOwnedFunctionValues.Header compiled
    (Program.ofChecked compiled.sourceProgram)) (issued : PublicReceipt header)
    {arguments before initialStore mapping world administrative actualContext actual ξ frameLocation current ghost}
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
    (entry : RecursiveNamedCatalogInvocationBounds.BodyState
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations 0 functions registry header arguments before initialStore mapping world
      administrative actualContext actual ξ frameLocation current ghost)
    {tracked : Bool}
    (sites : RecursiveNamedCatalogRuntimeProfileFactory.InputsWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      true tracked .reachable headers header (compilation header) (expressionSyntax header)
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) :
    Nonempty (RecursiveNamedCatalogRuntimeProfileFactory.ReceiptWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      true .reachable headers header (compilation header) (expressionSyntax header)
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) :=
  CallableIndexedOwnedNamedPublicProfileExtraction.extract_at issued.accepted issued.prepared issued.aligned
    issued.nativeMember compilation functions owner complete entry sites

/-- The original canonical caller wraps the same actual ordered pool. -/
private abbrev caller := CallableIndexedOwnedReadyNamedExpressionTreeBounds.caller (headers := headers)
  (compilation := callerCompilation) owner

variable {source : TypedSource} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}
  {faults : FunctionCalls.FaultRep}
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) (sourceRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context) (unique : NodeOccurrencesUnique source)
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  (idsUnique : RequirementIdsUnique context)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (ordinary : owner.key.capturePrefix = 0)
  (publicReceipts : ∀ header, header ∈ headers → PublicReceipt header)
  (catalog : SignatureCatalogWellFormed compiled.compatible.checked.signatures)
  (calleeUninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (calleeMissing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header, header ∈ headers → faults .controlEscapedFunction header.escaped)
  (outputs : ∀ header, header ∈ headers →
    CallableIndexedOwnedNamedPublicProfileExtraction.InterpretedReceiptsFor
      (headers := headers) (registry := registry) (faults := faults) (expressionSyntax := expressionSyntax)
      (header := header) compilation functions owner)
  (syntaxTrees : ∀ header, header ∈ headers → GenericImperativeMatch.Syntax header.function.source
    (expressionSyntax header) header.context (.statements true header.function.body) header.function.resultType)

include publicReceipts in
/-- Full layouts come from the real public Header construction. -/
theorem same_layouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts :=
  fun header member => (publicReceipts header member).aligned.layouts

include ordinary in
/-- The original named compiler's administrative prefix is the actual bundle
slot. Genuine ordinary capture prefix supplies the family boundary directly. -/
theorem prefix_matches : ∀ header, header ∈ headers →
    (compilation header).administrativePrefix = owner.key.capturePrefix + 1 := by
  intro header _member
  simp only [ordinary]
  rfl

include ordinary catalog outputs in
/-- Interpreted static output receipts construct profiles as proof witnesses at
each actual ordinary body entry; no completed body meaning is requested. -/
theorem profile_witnesses : ∀ header, header ∈ headers →
    Nonempty (CallableIndexedOwnedAdmittedNamedExpressionHeads.ProfilesFor
      (headers := headers) (owner := owner) (functions := functions) (registry := registry) (faults := faults)
      (certificates := CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation)
      (expressionSyntax := expressionSyntax) (diagnosticPolicy := .reachable) (runtime := true) header) :=
  fun header member => CallableIndexedOwnedNamedPublicProfileExtraction.profiles_for
    compilation functions owner ordinary (outputs header member) catalog

include extension faithful observations functionTypes wellFormed sourceRuntime covers unique owners idsUnique
  uninitialized missing ordinary publicReceipts catalog calleeUninitialized calleeMissing escaped outputs syntaxTrees in
theorem preserves_at_runtime (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots (caller (headers := headers) (callerCompilation := callerCompilation) owner))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CallableIndexedOwnedReadyNamedExpressionTreeBounds.RuntimeTree (headers := headers)
        (compilation := callerCompilation) (source := source) (context := context) (solved := solved)
        (reasonAt := reasonAt) (fuel := fuel) evidence) faults size := by
  classical
  let profiles : ∀ header, header ∈ headers →
      CallableIndexedOwnedAdmittedNamedExpressionHeads.ProfilesFor
        (headers := headers) (owner := owner) (functions := functions) (registry := registry) (faults := faults)
        (certificates := CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation)
        (expressionSyntax := expressionSyntax) (diagnosticPolicy := .reachable) (runtime := true) header :=
    fun header member => @Classical.choice _
      (profile_witnesses functions owner ordinary catalog outputs header member)
  intro scope id lowered
  exact CallableIndexedOwnedClosedReadyNamedExpressionRuntimeBounds.preserves_at_runtime
    (compilation := compilation) (callerCompilation := callerCompilation)
    (solved := solved) (reasonAt := reasonAt) (fuel := fuel)
    functions extension faithful observations functionTypes owner evidence wellFormed sourceRuntime covers unique owners idsUnique
    uninitialized missing (same_layouts publicReceipts) (prefix_matches owner ordinary)
    calleeUninitialized calleeMissing escaped profiles syntaxTrees sameLedger runtimeLedger budget size within

include extension faithful observations functionTypes wellFormed sourceRuntime covers unique
  uninitialized missing ordinary publicReceipts catalog calleeUninitialized calleeMissing escaped outputs syntaxTrees in
theorem reflects_at_runtime (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots (caller (headers := headers) (callerCompilation := callerCompilation) owner))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CallableIndexedOwnedReadyNamedExpressionTreeBounds.RuntimeTree (headers := headers)
        (compilation := callerCompilation) (source := source) (context := context) (solved := solved)
        (reasonAt := reasonAt) (fuel := fuel) evidence) faults size := by
  classical
  let profiles : ∀ header, header ∈ headers →
      CallableIndexedOwnedAdmittedNamedExpressionHeads.ProfilesFor
        (headers := headers) (owner := owner) (functions := functions) (registry := registry) (faults := faults)
        (certificates := CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation)
        (expressionSyntax := expressionSyntax) (diagnosticPolicy := .reachable) (runtime := true) header :=
    fun header member => @Classical.choice _
      (profile_witnesses functions owner ordinary catalog outputs header member)
  intro scope id lowered
  exact CallableIndexedOwnedClosedReadyNamedExpressionRuntimeBounds.reflects_at_runtime
    (compilation := compilation) (callerCompilation := callerCompilation)
    (solved := solved) (reasonAt := reasonAt) (fuel := fuel)
    functions extension faithful observations functionTypes owner evidence wellFormed sourceRuntime covers unique
    uninitialized missing (same_layouts publicReceipts) (prefix_matches owner ordinary)
    calleeUninitialized calleeMissing escaped profiles syntaxTrees sameLedger runtimeLedger budget size within

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicReadyNamedExpressionBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicTokenReadyNamedExpressionBounds
/-! Genuine public Headers supply their own unary and operand token meanings
inside the original closed named runtime family. Static child compilation and
Source typing remain separate from execution. Only actual assignment atoms
request the remaining place laws; no interpreted output provider is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicTokenReadyNamedExpressionBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPublicReadyNamedExpressionBounds (PublicReceipt compilation)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {callerCompilation : SourceCoreFunctions.Context}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

variable {faults : FunctionCalls.FaultRep}

/-- Genuine static inputs are tied to the actual public Header and requested
only at real ordinary parameter entries. They contain no interpreted output
predicate, profile provider or expression/body execution law. -/
structure StaticInputs (header : CallableIndexedOwnedFunctionValues.Header compiled
    (Program.ofChecked compiled.sourceProgram)) (issued : PublicReceipt header) where
  first : Nat
  assignments : SourceCoreAssignmentFaultSites.prepare header.function.source first =
    .ok issued.prepared.compilation.own.assignments
  operandsTyped : AssignmentDiagnosticOrigins.OperandsTyped header.function.source
  unaryTyped : EmittedDiagnosticTokenPlan.UnaryTyped header.function.source
  children : CallableIndexedOwnedNamedTokenProfileExtraction.ChildrenFor
    (header := header) (headers := headers) (registry := registry) (expressionSyntax := expressionSyntax)
    compilation functions owner
  operands : ∀ reason token, GenericAssignmentDiagnostics.OperandRep
    issued.prepared.compilation.own.assignments reason token → faults reason token
  unary : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep
    issued.prepared.compilation.own.assignments reason token → faults reason token
  places : EmittedDiagnosticTokenPlan.PlaceReceipts (source := header.function.source)
    (tracked := true)
    (invalidOperand := GenericAssignmentDiagnostics.token issued.prepared.compilation.own.assignments)
    registry faults

/-- The original canonical caller wraps the same actual ordered pool. -/
private abbrev caller := CallableIndexedOwnedReadyNamedExpressionTreeBounds.caller (headers := headers)
  (compilation := callerCompilation) owner

variable {source : TypedSource} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) (sourceRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context) (unique : NodeOccurrencesUnique source)
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  (idsUnique : RequirementIdsUnique context)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (ordinary : owner.key.capturePrefix = 0)
  (publicReceipts : ∀ header, header ∈ headers → PublicReceipt header)
  (catalog : SignatureCatalogWellFormed compiled.compatible.checked.signatures)
  (calleeUninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (calleeMissing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header, header ∈ headers → faults .controlEscapedFunction header.escaped)
  (complete : RecursiveNamedCatalogNativeContexts.Complete
    (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (staticInputs : ∀ header (member : header ∈ headers),
    StaticInputs (headers := headers) (functions := functions) (owner := owner) (registry := registry) (faults := faults)
      (expressionSyntax := expressionSyntax) header (publicReceipts header member))
  (syntaxTrees : ∀ header, header ∈ headers → GenericImperativeMatch.Syntax header.function.source
    (expressionSyntax header) header.context (.statements true header.function.body) header.function.resultType)

include complete publicReceipts staticInputs in
/-- Each reached Header's authentic producer interprets its own returned plan
and constructs the original static profile witness internally. -/
theorem interpreted_outputs : ∀ header, header ∈ headers →
    CallableIndexedOwnedNamedPublicProfileExtraction.InterpretedReceiptsFor
      (headers := headers) (registry := registry) (faults := faults) (expressionSyntax := expressionSyntax)
      (header := header) compilation functions owner := by
  intro header member
  let issued := publicReceipts header member
  let inputs : StaticInputs (functions := functions) (owner := owner) (headers := headers)
      (registry := registry) (faults := faults) (expressionSyntax := expressionSyntax) header issued :=
    staticInputs header member
  intro arguments before initialStore mapping world administrative actualContext actual ξ frameLocation current ghost actualEntry
  exact CallableIndexedOwnedNamedTokenProfileExtraction.interpreted_at_prepared
    issued.accepted issued.prepared issued.aligned issued.nativeMember compilation functions owner complete actualEntry
    inputs.operandsTyped inputs.assignments inputs.unaryTyped inputs.operands inputs.unary inputs.places (inputs.children actualEntry)

include extension faithful observations functionTypes wellFormed sourceRuntime covers unique owners idsUnique uninitialized missing ordinary publicReceipts catalog calleeUninitialized calleeMissing escaped complete staticInputs syntaxTrees in
theorem preserves_at_runtime (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots (caller (headers := headers) (callerCompilation := callerCompilation) owner))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CallableIndexedOwnedReadyNamedExpressionTreeBounds.RuntimeTree (headers := headers)
        (compilation := callerCompilation) (source := source) (context := context) (solved := solved)
        (reasonAt := reasonAt) (fuel := fuel) evidence) faults size := by
  exact CallableIndexedOwnedPublicReadyNamedExpressionBounds.preserves_at_runtime
    (callerCompilation := callerCompilation) (solved := solved) (reasonAt := reasonAt) (fuel := fuel)
    functions extension faithful observations functionTypes owner evidence wellFormed sourceRuntime covers unique owners idsUnique
    uninitialized missing ordinary publicReceipts catalog calleeUninitialized calleeMissing escaped
    (interpreted_outputs (functions := functions) (owner := owner) (complete := complete)
      (publicReceipts := publicReceipts) (staticInputs := staticInputs)) syntaxTrees
    sameLedger runtimeLedger budget size within

include extension faithful observations functionTypes wellFormed sourceRuntime covers unique uninitialized missing ordinary publicReceipts catalog calleeUninitialized calleeMissing escaped complete staticInputs syntaxTrees in
theorem reflects_at_runtime (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots (caller (headers := headers) (callerCompilation := callerCompilation) owner))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CallableIndexedOwnedReadyNamedExpressionTreeBounds.RuntimeTree (headers := headers)
        (compilation := callerCompilation) (source := source) (context := context) (solved := solved)
        (reasonAt := reasonAt) (fuel := fuel) evidence) faults size := by
  exact CallableIndexedOwnedPublicReadyNamedExpressionBounds.reflects_at_runtime
    (callerCompilation := callerCompilation) (solved := solved) (reasonAt := reasonAt) (fuel := fuel)
    functions extension faithful observations functionTypes owner evidence wellFormed sourceRuntime covers unique
    uninitialized missing ordinary publicReceipts catalog calleeUninitialized calleeMissing escaped
    (interpreted_outputs (functions := functions) (owner := owner) (complete := complete)
      (publicReceipts := publicReceipts) (staticInputs := staticInputs)) syntaxTrees
    sameLedger runtimeLedger budget size within

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicTokenReadyNamedExpressionBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedTokenReadyNamedExpressionBounds
/-! The actual public compiler constructs a Header together with its retained
diagnostic producer. Assignment preparation is derived internally at that same
Source; genuine typing, child compilation and residual place facts feed the
existing closed ordinary/direct named runtime family. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedTokenReadyNamedExpressionBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPublicReadyNamedExpressionBounds (compilation)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {callerCompilation : SourceCoreFunctions.Context}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

variable {faults : FunctionCalls.FaultRep}

/-- The Header keeps its complete existing public receipt and the diagnostic
identity selected by that same actual compiler preparation. -/
structure PublicReceipt (header : CallableIndexedOwnedFunctionValues.Header compiled
    (Program.ofChecked compiled.sourceProgram)) where
  original : CallableIndexedOwnedPublicReadyNamedExpressionBounds.PublicReceipt header
  diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt original.prepared

private theorem selected_key {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row) :
    prepared.named.signature.key = row.key := by
  have accepted := CallableIndexedActualNamedSourceReceipts.cached_record compiled prepared.selected prepared.compilation.hook
  rw [prepared.same] at accepted
  unfold SourceCompilationPlan.exactSpecialization at accepted
  split at accepted
  · cases accepted
  · next selected found =>
    cases accepted
    have member : row ∈ [row] := List.mem_singleton_self _
    rw [← found] at member
    exact (of_decide_eq_true (List.mem_filter.mp member).2).symm
  · cases accepted

/-- Actual public preparation chooses the Header from its own retained
Prepared receipt. The checked native membership remains authentic input. -/
theorem of_public_compile {program : CheckedProgram} {seeds : List SourceCompiler.Seed}
    {options : SourceCompiler.Options} {compiled : SourceCompiler.Compiled}
    {recipe : SourceCoreIndexedSession.Recipe} {row : SourceSpecialization.SpecializedFunction}
    (accepted : SourceCompiler.compileChecked program seeds options = .ok compiled)
    (issued : RecursiveNamedPreparedStageContracts.PublicRecipe compiled recipe)
    (member : row ∈ recipe.compiled.validationPlan.specializations)
    (wellFormed : ProgramWellFormed (Program.ofChecked recipe.compiled.sourceProgram))
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures recipe.compiled.sourceProgram.signatures) row.parameterSubstitution)
    (ordinaryReturn : row.function.returnComptime = false)
    (ordinaryParameters : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false)
    (target : SourceCompilationPlan.exactInstantiationKey recipe.compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation row) = .ok row.key)
    (nativeEntry : SourceCoreCallableIndexedPrograms.Entry recipe.compiled.indexed.layouts)
    (nativeMember : nativeEntry ∈ recipe.compiled.indexed.entries) :
    ∃ header : CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram),
      Nonempty (PublicReceipt header) := by
  obtain ⟨prepared, diagnostic⟩ := CallableIndexedOwnedPublicDiagnosticReceipts.of_public_compile accepted issued member
  obtain ⟨header, aligned⟩ := RecursiveNamedPreparedHeaders.Prepared.canonical_header_with_evidence prepared
    wellFormed range ordinaryReturn ordinaryParameters
    (target.trans (congrArg Except.ok (selected_key prepared).symm))
  obtain ⟨_source, _sourceAccepted, _cached, recipeAccepted⟩ :=
    RecursiveNamedPreparedStageContracts.public_compilation accepted issued
  let original : CallableIndexedOwnedPublicReadyNamedExpressionBounds.PublicReceipt header := {
    recipe := recipe, accepted := recipeAccepted, row := row, prepared := prepared,
    instantiation := CallableNamedMetadata.instantiation row, aligned := aligned,
    nativeEntry := nativeEntry, nativeMember := nativeMember }
  exact ⟨header, ⟨⟨original, diagnostic⟩⟩⟩

/-- Genuine static inputs are tied to the actual public Header and requested
only at real ordinary parameter entries. They contain no interpreted output
predicate, profile provider or expression/body execution law. -/
structure StaticInputs (header : CallableIndexedOwnedFunctionValues.Header compiled
    (Program.ofChecked compiled.sourceProgram)) (issued : PublicReceipt header) where
  operandsTyped : AssignmentDiagnosticOrigins.OperandsTyped header.function.source
  unaryTyped : EmittedDiagnosticTokenPlan.UnaryTyped header.function.source
  children : CallableIndexedOwnedNamedTokenProfileExtraction.ChildrenFor
    (header := header) (headers := headers) (registry := registry) (expressionSyntax := expressionSyntax)
    compilation functions owner
  operands : ∀ reason token, GenericAssignmentDiagnostics.OperandRep
    issued.original.prepared.compilation.own.assignments reason token → faults reason token
  unary : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep
    issued.original.prepared.compilation.own.assignments reason token → faults reason token
  places : EmittedDiagnosticTokenPlan.PlaceReceipts (source := header.function.source)
    (tracked := true)
    (invalidOperand := GenericAssignmentDiagnostics.token issued.original.prepared.compilation.own.assignments)
    registry faults

/-- The original canonical caller wraps the same actual ordered pool. -/
private abbrev caller := CallableIndexedOwnedReadyNamedExpressionTreeBounds.caller (headers := headers)
  (compilation := callerCompilation) owner

variable {source : TypedSource} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) (sourceRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context) (unique : NodeOccurrencesUnique source)
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  (idsUnique : RequirementIdsUnique context)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (ordinary : owner.key.capturePrefix = 0)
  (publicReceipts : ∀ header, header ∈ headers → PublicReceipt header)
  (catalog : SignatureCatalogWellFormed compiled.compatible.checked.signatures)
  (calleeUninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (calleeMissing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header, header ∈ headers → faults .controlEscapedFunction header.escaped)
  (complete : RecursiveNamedCatalogNativeContexts.Complete
    (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (staticInputs : ∀ header (member : header ∈ headers),
    StaticInputs (headers := headers) (functions := functions) (owner := owner) (registry := registry) (faults := faults)
      (expressionSyntax := expressionSyntax) header (publicReceipts header member))
  (syntaxTrees : ∀ header, header ∈ headers → GenericImperativeMatch.Syntax header.function.source
    (expressionSyntax header) header.context (.statements true header.function.body) header.function.resultType)

/-- The genuine retained diagnostic producer supplies the exact first token
and assignment table at this Header. Only proof-local selection is needed. -/
theorem ready_inputs (header : CallableIndexedOwnedFunctionValues.Header compiled
    (Program.ofChecked compiled.sourceProgram)) (issued : PublicReceipt header)
    (inputs : StaticInputs (functions := functions) (owner := owner) (headers := headers)
      (registry := registry) (faults := faults) (expressionSyntax := expressionSyntax) header issued) :
    Nonempty (CallableIndexedOwnedPublicTokenReadyNamedExpressionBounds.StaticInputs
      (functions := functions) (owner := owner) (headers := headers)
      (registry := registry) (faults := faults) (expressionSyntax := expressionSyntax) header issued.original) := by
  obtain ⟨first, assignments⟩ := CallableIndexedOwnedPublicDiagnosticReceipts.assignments_at_header
    issued.original.prepared issued.diagnostic issued.original.aligned
  exact ⟨⟨first, assignments, inputs.operandsTyped, inputs.unaryTyped,
    inputs.children, inputs.operands, inputs.unary, inputs.places⟩⟩

include extension faithful observations functionTypes wellFormed sourceRuntime covers unique owners idsUnique uninitialized missing ordinary publicReceipts catalog calleeUninitialized calleeMissing escaped complete staticInputs syntaxTrees in
theorem preserves_at_runtime (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots (caller (headers := headers) (callerCompilation := callerCompilation) owner))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CallableIndexedOwnedReadyNamedExpressionTreeBounds.RuntimeTree (headers := headers)
        (compilation := callerCompilation) (source := source) (context := context) (solved := solved)
        (reasonAt := reasonAt) (fuel := fuel) evidence) faults size := by
  exact CallableIndexedOwnedPublicTokenReadyNamedExpressionBounds.preserves_at_runtime
    (callerCompilation := callerCompilation) (solved := solved) (reasonAt := reasonAt) (fuel := fuel)
    functions extension faithful observations functionTypes owner evidence wellFormed sourceRuntime covers unique owners idsUnique
    uninitialized missing ordinary (fun header member => (publicReceipts header member).original) catalog calleeUninitialized calleeMissing escaped
    complete (fun header member => Classical.choice
      (ready_inputs functions owner header (publicReceipts header member) (staticInputs header member))) syntaxTrees
    sameLedger runtimeLedger budget size within

include extension faithful observations functionTypes wellFormed sourceRuntime covers unique uninitialized missing ordinary publicReceipts catalog calleeUninitialized calleeMissing escaped complete staticInputs syntaxTrees in
theorem reflects_at_runtime (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots (caller (headers := headers) (callerCompilation := callerCompilation) owner))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CallableIndexedOwnedReadyNamedExpressionTreeBounds.RuntimeTree (headers := headers)
        (compilation := callerCompilation) (source := source) (context := context) (solved := solved)
        (reasonAt := reasonAt) (fuel := fuel) evidence) faults size := by
  exact CallableIndexedOwnedPublicTokenReadyNamedExpressionBounds.reflects_at_runtime
    (callerCompilation := callerCompilation) (solved := solved) (reasonAt := reasonAt) (fuel := fuel)
    functions extension faithful observations functionTypes owner evidence wellFormed sourceRuntime covers unique
    uninitialized missing ordinary (fun header member => (publicReceipts header member).original) catalog calleeUninitialized calleeMissing escaped
    complete (fun header member => Classical.choice
      (ready_inputs functions owner header (publicReceipts header member) (staticInputs header member))) syntaxTrees
    sameLedger runtimeLedger budget size within

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedTokenReadyNamedExpressionBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPlaceMissingDiagnostics
/-! Genuine cached Header selection supplies its complete Source in the actual
public diagnostic inventory. The callable root-table override retains all
place reasons. Accepted catalog and place preparation then interpret the
actual unavailable mapping terminal at its own raw metadata header. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPlaceMissingDiagnostics
open Core Frontend SourceInference CompatiblePayload CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces

private theorem exact_collected {plan : SourceCompilationPlan.Plan} {key : SourceCompilationPlan.Key}
    {row : SourceSpecialization.SpecializedFunction}
    (selected : SourceCompilationPlan.exactSpecialization plan key = .ok row) :
    (key, row.function.typedBody) ∈ plan.specializations.map (fun specialized =>
      (specialized.key, specialized.function.typedBody)) := by
  unfold SourceCompilationPlan.exactSpecialization at selected
  split at selected
  · cases selected
  · next actual found =>
    cases selected
    have member : row ∈ plan.specializations.filter (fun specialized => decide (specialized.key = key)) := by
      rw [found]; exact List.mem_singleton_self _
    have keyEq := of_decide_eq_true (List.mem_filter.mp member).2
    exact List.mem_map.mpr ⟨row, (List.mem_filter.mp member).1, by rw [keyEq]⟩
  · cases selected

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))

/-- Exact cached specialization and original named Source agreement establish
membership of the whole Header Source, including every node and header item. -/
theorem header_collected :
    (header.named.signature.key, header.function.source) ∈
      compiled.indexed.base.plan.specializations.map (fun specialized =>
        (specialized.key, specialized.function.typedBody)) := by
  rw [header.agreement.source]
  exact exact_collected (CallableIndexedActualNamedSourceReceipts.header_record compiled header)

/-- The real sealed diagnostic preparation visits this same full Header Source. -/
theorem inventory_at_header
    {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (found : compiled.indexed.base.diagnostics = some diagnostics) :
    ∃ root sources,
      SourceCoreCompatibleDataPlaceFaultSites.prepare (.initial compiled.compatible.checked)
        compiled.indexed.base.plan root sources = .ok diagnostics ∧
      (header.named.signature.key, header.function.source) ∈
        compiled.indexed.base.plan.specializations.map (fun specialized =>
          (specialized.key, specialized.function.typedBody)) ++ sources := by
  obtain ⟨root, sources, accepted⟩ := CallableIndexedOwnedPublicDiagnosticReceipts.compiled_diagnostics compiled found
  exact ⟨root, sources, accepted, List.mem_append_left _ (header_collected header)⟩

/-- The existing public receipt chooses its own actual diagnostic inventory.
Only the real callable root-table replacement is present in the lowered table. -/
theorem public_inventory
    (receipt : CallableIndexedOwnedPublicPreparedTokenReadyNamedExpressionBounds.PublicReceipt header) :
    ∃ diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked),
      compiled.indexed.base.diagnostics = some diagnostics ∧
      receipt.original.prepared.diagnostics.places = diagnostics.program.places ∧
      ∃ root sources,
        SourceCoreCompatibleDataPlaceFaultSites.prepare (.initial compiled.compatible.checked)
          compiled.indexed.base.plan root sources = .ok diagnostics ∧
        (header.named.signature.key, header.function.source) ∈
          compiled.indexed.base.plan.specializations.map (fun specialized =>
            (specialized.key, specialized.function.typedBody)) ++ sources := by
  obtain ⟨diagnostics, found, lowered⟩ := receipt.diagnostic.actual
  refine ⟨diagnostics, found, ?_, inventory_at_header header found⟩
  rw [lowered]
  cases compiled.indexed.base.callableContext <;> rfl

private theorem public_placeReason
    (receipt : CallableIndexedOwnedPublicPreparedTokenReadyNamedExpressionBounds.PublicReceipt header)
    {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (found : compiled.indexed.base.diagnostics = some diagnostics)
    (owner : SourceSpecialization.SpecializationKey) (site : SourceCoreElaboration.ErrorSite)
    (binder : Resolved.LocalId) (valueType : Option TypeSystem.Ty) :
    receipt.original.prepared.diagnostics.placeReason owner site binder valueType =
      diagnostics.program.placeReason owner site binder valueType := by
  obtain ⟨actual, actualFound, lowered⟩ := receipt.diagnostic.actual
  have same := Option.some.inj (found.symm.trans actualFound)
  subst actual
  rw [lowered]
  cases compiled.indexed.base.callableContext <;> rfl

/-- Same public Header, diagnostic receipt and accepted compiler metadata
supply Source membership and the concrete gate internally. The original raw
projection typing and actual terminal/table are retained pointwise inputs. -/
theorem terminal_at_header
    (receipt : CallableIndexedOwnedPublicPreparedTokenReadyNamedExpressionBounds.PublicReceipt header)
    {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (found : compiled.indexed.base.diagnostics = some diagnostics)
    {node : StatementNode} (statement : .statement node ∈ header.function.source.nodes)
    {assignment : AssignmentResolution}
    (target : assignment ∈ CompatiblePlaceMissingPreparationCoverage.targets node)
    {route : Route}
    (described : describe (.initial compiled.compatible.checked) compiled.compatible.checked.signatures
      header.function.source (.occurrence node.id.occurrence) assignment = .ok route)
    {fuel : Nat} {invalid : Word} {prepared : Prepared}
    (generated : prepare (.initial compiled.compatible.checked) fuel route invalid
      (fun valueType => receipt.original.prepared.diagnostics.placeReason header.named.signature.key
        (.occurrence node.id.occurrence) assignment.target.root (some valueType)) = .ok prepared)
    {sourceContext : SourceSemantics.Context}
    (signatures : sourceContext.signatures = compiled.compatible.checked.signatures)
    (sourceTyped : ∀ binder, rootBinder header.function.source assignment.target.root = .ok binder →
      SourceProjectionsHaveType header.function.source sourceContext binder.scheme.body
        assignment.target.projections assignment.target.type)
    {root leaf : TypeSystem.Ty}
    {path : PreparedPath compiled.compatible.checked header.function.source (.occurrence node.id.occurrence)
      root assignment.target.projections 0 prepared.steps prepared.keys leaf}
    (rootView : SourceCoreRawMetadata.runtimeType root = SourceCoreRawMetadata.runtimeType route.rootSourceType)
    {registry : SourceCoreRawMetadata.Registry}
    {extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry}
    {table : SourceCoreFaultSites.Table} (rebuilt : diagnostics.tableForRegistry registry extension = .ok table)
    {ambient : AmbientDefinitions compiled.compatible.checked.catalog.definitions}
    {functions : FunctionModel compiled.compatible.checked.catalog ambient}
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping} {reason : Dynamic.SemanticFault} {token : Word}
    (terminal : MissingTerminal (registry := registry) functions mapping world path reason token) :
    ∃ rawValue diagnostic, reason = .missingMappingDefault rawValue ∧
      table.diagnostic? token = some diagnostic ∧ diagnostic.error = .typeMismatch rawValue none := by
  obtain ⟨rootKey, sources, issued, collected⟩ := inventory_at_header header found
  have missingEq : (fun valueType => receipt.original.prepared.diagnostics.placeReason header.named.signature.key
      (.occurrence node.id.occurrence) assignment.target.root (some valueType)) =
      (fun valueType => diagnostics.program.placeReason header.named.signature.key
        (.occurrence node.id.occurrence) assignment.target.root (some valueType)) := by
    funext valueType
    exact public_placeReason header receipt found _ _ _ _
  rw [missingEq] at generated
  exact CompatiblePlaceMissingTerminalDiagnostics.terminal_diagnostic issued collected statement target
    (CompatiblePlaceConcretePreparation.describe_concrete
      (CallableIndexedOwnedPublicCatalogClosedSources.compiled_closed compiled) described)
    described generated header.unique signatures sourceTyped rootView rebuilt terminal

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPlaceMissingDiagnostics
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPlaceReachedDiagnostics
/-! Genuine Source assignment typing and the actual writable root identify
the same raw projection row. The real reached missing phase then supplies its
own prepared terminal to the public diagnostic inventory and table. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPlaceReachedDiagnostics
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces ProtectedPlaceReachedDiagnostics
universe u v

/-- Two real first-match writable receipts identify the same raw root type.
The original Source place judgment supplies its ordered projection typing. -/
theorem projections_at_root {source : TypedSource} {context : SourceSemantics.Context}
    {place : PlaceResolution} {root type : TypeSystem.Ty}
    (typed : SourcePlaceHasType source context place type)
    (writable : WritableLocal context place.root root) :
    SourceProjectionsHaveType source context root place.projections place.type := by
  cases typed with
  | intro originalWritable projections stored =>
    obtain ⟨originalScheme, originalLookup, _, _, originalBody⟩ := originalWritable.scheme
    obtain ⟨scheme, lookup, _, _, body⟩ := writable.scheme
    have schemes := Option.some.inj
      ((Resolved.LocalScope.lookup?_iff.mpr originalLookup).symm.trans
        (Resolved.LocalScope.lookup?_iff.mpr lookup))
    have roots := originalBody.symm.trans ((congrArg TypeSystem.Scheme.body schemes).trans body)
    rw [stored]
    exact roots ▸ projections

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))

/-- This decoder consumes the actual retained phase and prepared compiler
equations. It preserves the same witness, raw metadata token and rebuilt table. -/
theorem missing_at_header
    (receipt : CallableIndexedOwnedPublicPreparedTokenReadyNamedExpressionBounds.PublicReceipt header)
    {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (found : compiled.indexed.base.diagnostics = some diagnostics)
    {node : StatementNode} (statement : .statement node ∈ header.function.source.nodes)
    {assignment : AssignmentResolution}
    (target : assignment ∈ CompatiblePlaceMissingPreparationCoverage.targets node)
    {operator : Syntax.ValueAssignOp} {rhs : ExpressionId} {context : SourceSemantics.Context}
    (typed : SourceAssignmentHasType header.function.source context assignment operator rhs)
    {route : Route}
    (described : describe (.initial compiled.compatible.checked) compiled.compatible.checked.signatures
      header.function.source (.occurrence node.id.occurrence) assignment = .ok route)
    {fuel : Nat} {invalid : Word} {prepared : Prepared}
    (generated : prepare (.initial compiled.compatible.checked) fuel route invalid
      (fun valueType => receipt.original.prepared.diagnostics.placeReason header.named.signature.key
        (.occurrence node.id.occurrence) assignment.target.root (some valueType)) = .ok prepared)
    (writable : WritableLocal context assignment.target.root prepared.route.rootSourceType)
    (signatures : context.signatures = compiled.compatible.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry}
    {extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry}
    {table : SourceCoreFaultSites.Table} (rebuilt : diagnostics.tableForRegistry registry extension = .ok table)
    {ambient : AmbientDefinitions compiled.compatible.checked.catalog.definitions}
    {functions : FunctionModel compiled.compatible.checked.catalog ambient} {Records : Type v}
    {protocol : ProtectedStateTransition.Protocol.{u, v} Records}
    {initialIndex reachedIndex : ProtectedStateTransition.Index}
    {initial : protocol.State initialIndex} {reached : protocol.State reachedIndex}
    {leaf : TypeSystem.Ty} {reason : Dynamic.SemanticFault} {token : Word}
    (witness : MissingWitness compiled.compatible.checked registry functions protocol
      header.function.source (.occurrence node.id.occurrence) assignment.target prepared leaf
      initial reached reason token) :
    ∃ rawValue diagnostic, reason = .missingMappingDefault rawValue ∧
      table.diagnostic? token = some diagnostic ∧ diagnostic.error = .typeMismatch rawValue none := by
  obtain ⟨type, placeTyped⟩ := CallableIndexedOwnedPlaceAdmission.assignment_target_typed typed
  have projections := projections_at_root placeTyped writable
  obtain ⟨binder, selected, description⟩ := CompatiblePlaceDescription.of_describe described
  have preparedRoute := (CompatibleMixedPreparation.of_prepare generated).1
  have sourceTyped : ∀ actualBinder, rootBinder header.function.source assignment.target.root = .ok actualBinder →
      SourceProjectionsHaveType header.function.source context actualBinder.scheme.body
        assignment.target.projections assignment.target.type := by
    intro actualBinder binding
    have binders := Except.ok.inj (binding.symm.trans description.binding)
    subst actualBinder
    simpa only [preparedRoute, description.rootSource] using projections
  obtain ⟨phaseIndex, phase, location, locationNative, cell, optional, root, value, path,
    _relatedIn, _relatedOut, _scope, _canonical, _index, _worlds, _frame, _read, rootType, terminal⟩ := witness.terminal
  have rootView : SourceCoreRawMetadata.runtimeType cell.type =
      SourceCoreRawMetadata.runtimeType route.rootSourceType :=
    congrArg SourceCoreRawMetadata.runtimeType (rootType.trans (congrArg Route.rootSourceType preparedRoute))
  exact CallableIndexedOwnedPublicPlaceMissingDiagnostics.terminal_at_header header receipt found statement target
    described generated signatures sourceTyped rootView rebuilt terminal

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPlaceReachedDiagnostics
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPlaceUninitializedDiagnostics
/-! An actual uninitialized root at a projected target uses the fixed row
emitted for that same accepted description. The public inventory and original
reached witness retain their full states and location. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPlaceUninitializedDiagnostics
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces ProtectedPlaceReachedDiagnostics
universe u v
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))

/-- The actual public receipt keeps all place reasons through the callable
root-table replacement. -/
theorem place_reason
    (receipt : CallableIndexedOwnedPublicPreparedTokenReadyNamedExpressionBounds.PublicReceipt header)
    {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (found : compiled.indexed.base.diagnostics = some diagnostics)
    (owner : SourceSpecialization.SpecializationKey) (site : SourceCoreElaboration.ErrorSite)
    (binder : Resolved.LocalId) :
    receipt.original.prepared.diagnostics.placeReason owner site binder none =
      diagnostics.program.placeReason owner site binder none := by
  obtain ⟨actual, actualFound, lowered⟩ := receipt.diagnostic.actual
  have same := Option.some.inj (found.symm.trans actualFound)
  subst actual
  rw [lowered]
  cases compiled.indexed.base.callableContext <;> rfl

/-- The same actual projected root witness receives its own fixed diagnostic.
The location and every reached state remain in the original witness. -/
theorem uninitialized_at_header
    (receipt : CallableIndexedOwnedPublicPreparedTokenReadyNamedExpressionBounds.PublicReceipt header)
    {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (found : compiled.indexed.base.diagnostics = some diagnostics)
    {node : StatementNode} (statement : .statement node ∈ header.function.source.nodes)
    {assignment : AssignmentResolution}
    (target : assignment ∈ CompatiblePlaceMissingPreparationCoverage.targets node)
    {route : Route}
    (described : describe (.initial compiled.compatible.checked) compiled.compatible.checked.signatures
      header.function.source (.occurrence node.id.occurrence) assignment = .ok route)
    {fuel : Nat} {prepared : Prepared}
    (generated : prepare (.initial compiled.compatible.checked) fuel route
      (receipt.original.prepared.diagnostics.placeReason header.named.signature.key
        (.occurrence node.id.occurrence) assignment.target.root none)
      (fun valueType => receipt.original.prepared.diagnostics.placeReason header.named.signature.key
        (.occurrence node.id.occurrence) assignment.target.root (some valueType)) = .ok prepared)
    {registry : SourceCoreRawMetadata.Registry}
    {extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry}
    {table : SourceCoreFaultSites.Table} (rebuilt : diagnostics.tableForRegistry registry extension = .ok table)
    {ambient : AmbientDefinitions compiled.compatible.checked.catalog.definitions}
    {functions : FunctionModel compiled.compatible.checked.catalog ambient} {Records : Type v}
    {protocol : ProtectedStateTransition.Protocol.{u, v} Records}
    {initialIndex reachedIndex : ProtectedStateTransition.Index}
    {initial : protocol.State initialIndex} {reached : protocol.State reachedIndex}
    {environment : Dynamic.Environment} {location : Dynamic.Location}
    (witness : UninitializedWitness compiled.compatible.checked registry functions protocol environment
      assignment.target prepared initial reached location) :
    UninitializedWitness compiled.compatible.checked registry functions protocol environment
      assignment.target prepared initial reached location ∧
    ∃ diagnostic, table.diagnostic? prepared.invalidProjection = some diagnostic ∧
      diagnostic.error = .invalidPlaceProjection := by
  have actual := CompatibleMixedPreparation.of_prepare generated
  have projected : prepared.steps ≠ [] := by
    obtain ⟨_phaseIndex, _phase, _target, _cell, _optional, _sources, _resolved,
      _in, _out, _scope, _canonical, _index, _world, _frame, _lookup, _read,
      _reference, _storeRead, _cellRep, _cellType, _empty, _notMapping, nonempty, _values, _resolvedNonempty⟩ := witness
    exact nonempty
  have nonempty : route.steps ≠ [] := by
    intro empty
    have steps := actual.2.2
    rw [empty] at steps
    have only_nil : ∀ {outputs keys}, CompatibleMixedPreparation.Steps compiled.compatible.checked fuel
        (fun valueType => receipt.original.prepared.diagnostics.placeReason header.named.signature.key
          (.occurrence node.id.occurrence) assignment.target.root (some valueType)) [] 0 outputs keys → outputs = [] := by
      intro outputs keys path
      cases path
      rfl
    exact projected (only_nil steps)
  obtain ⟨root, sources, issued, collected⟩ :=
    CallableIndexedOwnedPublicPlaceMissingDiagnostics.inventory_at_header header found
  have concrete := CompatiblePlaceConcretePreparation.describe_concrete
    (CallableIndexedOwnedPublicCatalogClosedSources.compiled_closed compiled) described
  obtain ⟨entry, member, kind, _first, reason⟩ :=
    CompatiblePlaceProjectionDiagnosticCoverage.prepare_coverage issued collected statement target concrete described nonempty
  obtain ⟨decoded, error⟩ := CompatiblePlaceProjectionDiagnosticPreparation.table_diagnostic issued member kind rebuilt
  have same : prepared.invalidProjection = entry.reason :=
    actual.2.1.trans ((place_reason header receipt found _ _ _).trans reason)
  exact ⟨witness, entry.diagnostic, by simpa only [same] using decoded, error⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPlaceUninitializedDiagnostics
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedShapeDiagnostics
/-! The same selected head retains its owning Source occurrence and actual
compiler preparation. Its real reached witnesses receive their public table
observations before the caller's explicit fault interpretation is applied. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedShapeDiagnostics
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces ProtectedPlaceReachedDiagnostics
universe u v

/-- Both ordered For rows keep their genuine parent statement and site. -/
theorem owning_target {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    (origin : AssignmentDiagnosticOrigins.Occurs source site assignment operator rhs) :
    ∃ node, .statement node ∈ source.nodes ∧ site = .occurrence node.id.occurrence ∧
      assignment ∈ CompatiblePlaceMissingPreparationCoverage.targets node := by
  cases origin with
  | statement found form =>
    refine ⟨_, (lookupStatement?_sound found).1, ?_, ?_⟩
    · exact (congrArg (fun id : StatementId => SourceCoreElaboration.ErrorSite.occurrence id.occurrence)
        (lookupStatement?_sound found).2).symm
    · simp only [CompatiblePlaceMissingPreparationCoverage.targets, form, List.mem_singleton]
  | header found form member =>
    refine ⟨_, (lookupStatement?_sound found).1, ?_, ?_⟩
    · exact (congrArg (fun id : StatementId => SourceCoreElaboration.ErrorSite.occurrence id.occurrence)
        (lookupStatement?_sound found).2).symm
    · rw [CompatiblePlaceMissingPreparationCoverage.targets, form]
      exact List.mem_filterMap.mpr ⟨_, member, rfl⟩

/-- Missing errors use precise raw table observations. Uninitialized errors
also retain the actual reached witness and its location. These inclusions are
the caller's explicit interpretation of the two decoded errors. -/
structure ReachedTableInterpretation
    (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) {Records : Type v}
    (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (environment : Dynamic.Environment) (place : PlaceResolution) (prepared : Prepared)
    {initialIndex : ProtectedStateTransition.Index} (initial : protocol.State initialIndex)
    (table : SourceCoreFaultSites.Table) (faults : FunctionCalls.FaultRep) : Prop where
  missing : ∀ {rawValue token diagnostic}, table.diagnostic? token = some diagnostic →
    diagnostic.error = .typeMismatch rawValue none → faults (.missingMappingDefault rawValue) token
  uninitialized : ∀ {reachedIndex} (reached : protocol.State reachedIndex) {location},
    protocol.Relates initial reached →
    UninitializedWitness checked registry functions protocol environment place prepared initial reached location →
    ∀ {diagnostic}, table.diagnostic? prepared.invalidProjection = some diagnostic →
      diagnostic.error = .invalidPlaceProjection → faults (.uninitializedLocation location) prepared.invalidProjection

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate}
  {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions compiled.compatible.checked.catalog.definitions}
  {functions : FunctionModel compiled.compatible.checked.catalog ambient}
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  (head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) header.function.source
    context certificate scope administrative ambient.definitions assignment operator rhs)
  {registry : SourceCoreRawMetadata.Registry} {Records : Type v}
  {protocol : ProtectedStateTransition.Protocol.{u, v} Records}
  {environment : Dynamic.Environment} {initialIndex : ProtectedStateTransition.Index}
  (initial : protocol.State initialIndex) {table : SourceCoreFaultSites.Table} {faults : FunctionCalls.FaultRep}

/-- Each contract is proved at its own actual reached state. The retained shape
equality selects the same implicit site and layout as the selected head. -/
theorem shape_errors_at_header
    (receipt : CallableIndexedOwnedPublicPreparedTokenReadyNamedExpressionBounds.PublicReceipt header)
    {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (found : compiled.indexed.base.diagnostics = some diagnostics)
    (projected : assignment.target.projections ≠ [])
    {site : SourceCoreElaboration.ErrorSite}
    (origin : AssignmentDiagnosticOrigins.Occurs header.function.source site assignment operator rhs)
    {fuel : Nat}
    (retained : head.PreparedAt site fuel
      (receipt.original.prepared.diagnostics.placeReason header.named.signature.key site assignment.target.root none)
      (fun rawValue => receipt.original.prepared.diagnostics.placeReason header.named.signature.key
        site assignment.target.root (some rawValue)))
    (typed : SourceAssignmentHasType header.function.source context assignment operator rhs)
    (signatures : context.signatures = compiled.compatible.checked.signatures)
    {extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry}
    (rebuilt : diagnostics.tableForRegistry registry extension = .ok table)
    (interprets : ReachedTableInterpretation compiled.compatible.checked registry functions protocol
      environment assignment.target head.prepared initial table faults) :
    ShapeErrors (.initial compiled.compatible.checked) registry functions protocol header.function.source context
      certificate scope administrative environment assignment.target head.prepared operator head.invalid initial faults head.shape := by
  obtain ⟨node, statement, sameSite, target⟩ := owning_target origin
  subst site
  cases retained with
  | bare empty => exact False.elim (projected empty)
  | projected route layout ordinary shape described preparedBy =>
    rw [shape]
    apply ShapeErrors.projected (layout := layout) (ordinary := ordinary)
    · intro reachedIndex reason token reached related witness
      obtain ⟨rawValue, diagnostic, sameReason, decoded, error⟩ :=
        CallableIndexedOwnedPublicPlaceReachedDiagnostics.missing_at_header header receipt found statement target
          typed described preparedBy head.writable signatures rebuilt witness
      rw [sameReason]
      exact interprets.missing decoded error
    · intro reachedIndex location reached related witness
      obtain ⟨actualWitness, diagnostic, decoded, error⟩ :=
        CallableIndexedOwnedPublicPlaceUninitializedDiagnostics.uninitialized_at_header header receipt found
          statement target described preparedBy rebuilt witness
      exact interprets.uninitialized reached related actualWitness decoded error

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedShapeDiagnostics
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicTypedTokenReadyNamedExpressionBounds
/-! The actual public Header and diagnostic receipt stay original. Complete
Source body typing derives every unary and assignment occurrence internally;
genuine compiler children and remaining fault facts feed the same closed
ordinary/direct named runtime family. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicTypedTokenReadyNamedExpressionBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPublicReadyNamedExpressionBounds (compilation)
open CallableIndexedOwnedPublicPreparedTokenReadyNamedExpressionBounds (PublicReceipt of_public_compile)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {callerCompilation : SourceCoreFunctions.Context}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

variable {faults : FunctionCalls.FaultRep}

/-- Genuine static inputs are tied to the actual public Header and requested
only at real ordinary parameter entries. They contain no interpreted output
predicate, profile provider or expression/body execution law. -/
structure StaticInputs (header : CallableIndexedOwnedFunctionValues.Header compiled
    (Program.ofChecked compiled.sourceProgram)) (issued : PublicReceipt header) where
  children : CallableIndexedOwnedNamedTokenProfileExtraction.ChildrenFor
    (header := header) (headers := headers) (registry := registry) (expressionSyntax := expressionSyntax)
    compilation functions owner
  operands : ∀ reason token, GenericAssignmentDiagnostics.OperandRep
    issued.original.prepared.compilation.own.assignments reason token → faults reason token
  unary : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep
    issued.original.prepared.compilation.own.assignments reason token → faults reason token
  places : EmittedDiagnosticTokenPlan.PlaceReceipts (source := header.function.source)
    (tracked := true)
    (invalidOperand := GenericAssignmentDiagnostics.token issued.original.prepared.compilation.own.assignments)
    registry faults

/-- The original canonical caller wraps the same actual ordered pool. -/
private abbrev caller := CallableIndexedOwnedReadyNamedExpressionTreeBounds.caller (headers := headers)
  (compilation := callerCompilation) owner

variable {source : TypedSource} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) (sourceRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context) (unique : NodeOccurrencesUnique source)
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  (idsUnique : RequirementIdsUnique context)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (ordinary : owner.key.capturePrefix = 0)
  (publicReceipts : ∀ header, header ∈ headers → PublicReceipt header)
  (catalog : SignatureCatalogWellFormed compiled.compatible.checked.signatures)
  (calleeUninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (calleeMissing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header, header ∈ headers → faults .controlEscapedFunction header.escaped)
  (complete : RecursiveNamedCatalogNativeContexts.Complete
    (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (staticInputs : ∀ header (member : header ∈ headers),
    StaticInputs (headers := headers) (functions := functions) (owner := owner) (registry := registry) (faults := faults)
      (expressionSyntax := expressionSyntax) header (publicReceipts header member))
  (syntaxTrees : ∀ header, header ∈ headers → GenericImperativeMatch.Syntax header.function.source
    (expressionSyntax header) header.context (.statements true header.function.body) header.function.resultType)

/-- Original complete Header typing supplies the two raw diagnostic
predicates internally. All remaining static fields are retained unchanged. -/
theorem ready_inputs (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (issued : PublicReceipt header)
    (inputs : StaticInputs (functions := functions) (owner := owner) (headers := headers)
      (registry := registry) (faults := faults) (expressionSyntax := expressionSyntax) header issued) :
    CallableIndexedOwnedPublicPreparedTokenReadyNamedExpressionBounds.StaticInputs
      (functions := functions) (owner := owner) (headers := headers)
      (registry := registry) (faults := faults) (expressionSyntax := expressionSyntax) header issued := by
  have typed := SourceDiagnosticTyping.header_diagnostic_typed header wellFormed
  exact ⟨typed.2, typed.1, inputs.children, inputs.operands, inputs.unary, inputs.places⟩

include extension faithful observations functionTypes wellFormed sourceRuntime covers unique owners idsUnique uninitialized missing ordinary publicReceipts catalog calleeUninitialized calleeMissing escaped complete staticInputs syntaxTrees in
theorem preserves_at_runtime (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots (caller (headers := headers) (callerCompilation := callerCompilation) owner))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CallableIndexedOwnedReadyNamedExpressionTreeBounds.RuntimeTree (headers := headers)
        (compilation := callerCompilation) (source := source) (context := context) (solved := solved)
        (reasonAt := reasonAt) (fuel := fuel) evidence) faults size := by
  exact CallableIndexedOwnedPublicPreparedTokenReadyNamedExpressionBounds.preserves_at_runtime
    (callerCompilation := callerCompilation) (solved := solved) (reasonAt := reasonAt) (fuel := fuel)
    functions extension faithful observations functionTypes owner evidence wellFormed sourceRuntime covers unique owners idsUnique
    uninitialized missing ordinary publicReceipts catalog calleeUninitialized calleeMissing escaped
    complete (fun header member => ready_inputs functions owner wellFormed header
      (publicReceipts header member) (staticInputs header member)) syntaxTrees
    sameLedger runtimeLedger budget size within

include extension faithful observations functionTypes wellFormed sourceRuntime covers unique uninitialized missing ordinary publicReceipts catalog calleeUninitialized calleeMissing escaped complete staticInputs syntaxTrees in
theorem reflects_at_runtime (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots (caller (headers := headers) (callerCompilation := callerCompilation) owner))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CallableIndexedOwnedReadyNamedExpressionTreeBounds.RuntimeTree (headers := headers)
        (compilation := callerCompilation) (source := source) (context := context) (solved := solved)
        (reasonAt := reasonAt) (fuel := fuel) evidence) faults size := by
  exact CallableIndexedOwnedPublicPreparedTokenReadyNamedExpressionBounds.reflects_at_runtime
    (callerCompilation := callerCompilation) (solved := solved) (reasonAt := reasonAt) (fuel := fuel)
    functions extension faithful observations functionTypes owner evidence wellFormed sourceRuntime covers unique
    uninitialized missing ordinary publicReceipts catalog calleeUninitialized calleeMissing escaped
    complete (fun header member => ready_inputs functions owner wellFormed header
      (publicReceipts header member) (staticInputs header member)) syntaxTrees
    sameLedger runtimeLedger budget size within

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicTypedTokenReadyNamedExpressionBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicCatalogPreparedReceipts
/-! Actual public Header extraction retains the chosen Catalog tree, diagnostic
plan and static match contexts together. The original body finish equation and
its independent Source syntax stay attached to the same compiler invocation. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicCatalogPreparedReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open RecursiveNamedCatalogNativeContexts NativeExpressionContextSupport
open RecursiveNamedCatalogRuntimeProfileFactory
open CallableIndexedOwnedPublicPreparedTokenReadyNamedExpressionBounds (PublicReceipt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {compilation : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → SourceCoreFunctions.Context}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  {administrative : Core.Context}

local notation "Γ" => SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative
local notation "certificates" => CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation header
local notation "headerScope" => bodyScope (prepared := compiled.indexed.ancestry)
  (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
  (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
  (program := Program.ofChecked compiled.sourceProgram) header

/-- Every field belongs to this public Header and its own retained diagnostic
producer. No interpreted profile or execution law is stored here. -/
structure CatalogReceipt (issued : PublicReceipt header) where
  first : Nat
  assignments : SourceCoreAssignmentFaultSites.prepare header.function.source first =
    .ok issued.original.prepared.compilation.own.assignments
  operandsTyped : AssignmentDiagnosticOrigins.OperandsTyped header.function.source
  unaryTyped : EmittedDiagnosticTokenPlan.UnaryTyped header.function.source
  catalog : SignatureCatalogWellFormed compiled.compatible.checked.signatures
  flow : Expr
  generated : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
    headerScope header.function.body header.output header.reasonAt true header.escaped = .ok flow
  finished : header.body = LocalControl.finish header.output (LocalLoop.toControl header.output flow header.escaped)
    (if header.output = .unit then LanguageResult.success .unit
      else LanguageResult.failure header.output (.word header.fellThrough))
  extracted : GenericImperativeMatch.CatalogCoupledExtractionFor .reachable header.layouts header.owner header.active
    compiled.indexed.ancestry.layout.frame header.globals header.onError (.initial compiled.compatible.checked)
    header.function.source (AssignmentDiagnosticOrigins.Factory.prepared operandsTyped assignments)
    (fun site root => issued.original.prepared.compilation.own.assignments.reasonAt site root .bitNot)
    (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection issued.original.prepared)
    (RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault issued.original.prepared)
    (expressionSyntax header) certificates compiled.indexed.layouts.definitions Γ header.solved
    header.context headerScope (.statements true header.function.body)
    header.function.resultType header.output flow

variable {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (complete : Complete (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
  (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers owner.key.locations 0 functions registry header arguments before initialStore mapping world
    administrative actualContext actual ξ frameLocation current ghost)

include functions owner complete entry in
/-- Real cached typing is transported to the actual ordinary parameter entry.
The same static Syntax traversal retains its genuine chosen Catalog receipts. -/
theorem at_entry (issued : PublicReceipt header)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (children : CallableIndexedOwnedNamedTokenProfileExtraction.Children
      (header := header) (headers := headers) (expressionSyntax := expressionSyntax) compilation Γ) :
    Nonempty (CatalogReceipt (headers := headers) (compilation := compilation)
      (expressionSyntax := expressionSyntax) (administrative := administrative) issued) := by
  obtain ⟨first, assignments⟩ := CallableIndexedOwnedPublicDiagnosticReceipts.assignments_at_header
    issued.original.prepared issued.diagnostic issued.original.aligned
  have rawTyped := SourceDiagnosticTyping.header_diagnostic_typed header wellFormed
  let sites := CallableIndexedOwnedNamedPublicProfileExtraction.policy_inputs
    issued.original.prepared issued.original.aligned compilation
    (CallableIndexedOwnedNamedTokenProfileExtraction.Children.to_static issued.original.prepared compilation
      rawTyped.2 assignments children)
  have typed := canonical_cached complete issued.original.aligned.globals
    (CallableIndexedOwnedNamedPublicProfileExtraction.cached_typed issued.original.prepared
      issued.original.aligned issued.original.nativeMember)
    (CallableIndexedOwnedNamedPublicProfileExtraction.cached_supported issued.original.accepted
      issued.original.prepared issued.original.aligned) entry
  have accepted := sites.accepted
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, same⟩ := CompatibleEncoding.bind_ok accepted
  have finished : header.body = LocalControl.finish header.output (LocalLoop.toControl header.output flow header.escaped)
      (if header.output = .unit then LanguageResult.success .unit
        else LanguageResult.failure header.output (.word header.fellThrough)) := (Except.ok.inj same).symm
  rw [finished] at typed
  obtain ⟨_, flowTyped⟩ := TypedLexicalWhile.Native.finished_flow typed
  obtain ⟨extracted⟩ := GenericImperativeMatch.extraction_of_typed_position_with_catalog_coupled true .reachable
    sites.factory sites.matchPolicy sites.matchValues sites.matchDefinitions sites.matchAllocator sites.matchChildStatic
    sites.readPolicy sites.binderPolicy sites.allocationPolicy sites.expressions sites.assignments sites.unaryPolicy
    header.unique sites.assignmentExpressions sites.syntaxTree
    (RecursiveNamedSourceContextFacts.header_typeVariables header) (RecursiveNamedSourceContextFacts.header_residual header)
    sites.sourceSignatures sites.declarations sites.projection generated flowTyped
  rw [sites.matchLedger] at extracted
  exact ⟨⟨first, assignments, rawTyped.2, rawTyped.1,
    CallableIndexedOwnedPublicSignatureCatalog.well_formed compiled wellFormed,
    flow, generated, finished, extracted⟩⟩

/-- The Header's original validity gives the exact solved ledger required by
the retained structural factory. It is independent of code and layout equality. -/
theorem ledger (_issued : PublicReceipt header) : header.context.solvedRequirements = header.solved :=
  header.valid.ledger

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicCatalogPreparedReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedSourceSites
/-! Genuine Source validity and typing supply sites independently from legacy
Catalog error receipts. Every predicate concerns this same selected Header;
the original reached Source receipt retains its heap and body typing. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedSourceSites
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open ProtectedStateTransition ProtectedStateImperativeCatalogReady
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  {expressionSyntax : ExpressionId → Prop}

/-- The complete solved ledger and independent Source validity travel together. -/
def Validity (context : SourceSemantics.Context) : Prop :=
  CompatibleRuntimeContextValidity.Valid header.solved context header.function.evidence ∧
    Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context header.function.source

theorem validity_at
    (source : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      header.context header.function.source) : Validity header header.context :=
  ⟨header.valid, source⟩

theorem validity_extend {context next : SourceSemantics.Context} {binder : TypedBinder}
    (valid : Validity header context)
    (extended : BinderExtends header.function.source.owner context binder next) : Validity header next :=
  ⟨valid.1.extend extended,
    valid.2.transport (Dynamic.RuntimeContextFields.ofBinderExtends extended)⟩

theorem signatures {context : SourceSemantics.Context} (valid : Validity header context) :
    context.signatures = compiled.compatible.checked.signatures :=
  valid.2.signatures.trans (CallableIndexedOwnedPublicSignatureCatalog.signatures compiled).symm

/-- Source body facts use independent Syntax and the actual typed parameter heap. -/
theorem body_facts {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    (source : CallableIndexedOwnedAdmittedBodyEntries.SourceReceipt (Program.ofChecked compiled.sourceProgram)
      header.function header.context environment heap)
    (syntaxTree : GenericImperativeMatch.Syntax header.function.source expressionSyntax header.context
      (.statements true header.function.body) header.function.resultType) :
    ProtectedStateImperativeTypedSourceSites.Facts header.function.source expressionSyntax
      header.context true header.function.body header.function.resultType := by
  obtain ⟨finalContext, facts, typed, _completes⟩ := source.bodyTyped
  exact ⟨syntaxTree, { returnType := header.function.resultType }, finalContext, facts, typed⟩

theorem assignment_sites : AssignmentSites
    (ProtectedStateImperativeTypedSourceSites.HeadFacts header.function.source expressionSyntax)
    (SourceAssignmentHasType header.function.source)
    (SourceBitNotAssignmentValid header.function.source) header.function.source where
  assignment := by
    intro context id expected node resolution operator rhs facts found form
    obtain ⟨mode, rest, _syntax, typed⟩ := facts
    exact ProtectedStateImperativeTypedSourceSites.assignment header.unique
      (ProtectedStateImperativeTypedSourceSites.head typed) found form
  snapshot := by
    intro context id expected node resolution facts found form
    obtain ⟨mode, rest, _syntax, typed⟩ := facts
    exact ProtectedStateImperativeTypedSourceSites.bit_not header.unique
      (ProtectedStateImperativeTypedSourceSites.head typed) found form

variable {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {protocol : Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (bindings : Bindings protocol)

/-- All static sites and state transfers are supplied by their original producers. -/
structure Inputs where
  sites : RecursiveNamedLexicalContracts.Stateful.WithReady.StaticSites
    (ProtectedStateImperativeTypedSourceSites.Facts header.function.source expressionSyntax)
    (ProtectedStateImperativeTypedSourceSites.HeadFacts header.function.source expressionSyntax)
    (ProtectedStateLexicalSourceSites.ExpressionFacts header.function.source)
    (Program.ofChecked compiled.sourceProgram) header.function.evidence header.function.source
  initializers : InitializerSites
    (ProtectedStateImperativeInitializerSourceSites.Facts header.function.source expressionSyntax)
    (CallableIndexedOwnedAdmittedForBounds.LoopFacts header.function.source expressionSyntax) header.function.source
  assignments : AssignmentSites
    (ProtectedStateImperativeTypedSourceSites.HeadFacts header.function.source expressionSyntax)
    (SourceAssignmentHasType header.function.source) (SourceBitNotAssignmentValid header.function.source) header.function.source
  transfers : RecursiveNamedLexicalContracts.Stateful.WithReady.AllocationTransfers
    protocol (readiness bridge) bindings header.function.source
  snapshots : ProtectedForHeader.Stateful.WithReady.SnapshotTransfers
    protocol (readiness bridge) (Validity header) (SourceBitNotAssignmentValid header.function.source)
    (Program.ofChecked compiled.sourceProgram) header.function.evidence header.function.source

/-- The actual Source graph and public well-formedness discharge these inputs. -/
theorem inputs (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (source : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) header.context header.function.source) :
    Inputs header bridge bindings (expressionSyntax := expressionSyntax) where
  sites := ProtectedStateImperativeTypedSourceSites.sites (Program.ofChecked compiled.sourceProgram)
    header.function.evidence source.graph
  initializers := ProtectedStateImperativeInitializerSourceSites.sites
  assignments := assignment_sites header
  transfers := CallableIndexedOwnedAdmittedLexicalReadiness.allocation_transfers bridge bindings header.function.source
  snapshots := CallableIndexedOwnedAdmittedForHeaderReadiness.snapshot_transfers bridge header.function.evidence
    wellFormed (Validity header) (fun _ valid => valid.2) (fun _ valid => valid.1.covers)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedSourceSites
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedProjectedAssignmentHeads
/-! Public projected endpoints derive reached diagnostics from the same
retained Source occurrence and accepted preparation. Existing admitted head
cores keep the actual ordered producers, pool and strict continuation bounds. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedProjectedAssignmentHeads
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof ReadOnly
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning CompatibleRenamedPlace DataPatternValues DataPlaceExecution
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
variable (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

section Heads
variable {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate} {scope : Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions compiled.compatible.checked.catalog.definitions}
  (functions : FunctionModel compiled.compatible.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations compiled.compatible.checked.catalog functions identities)
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  (head : GenericAssignmentStatements.Head (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (header.function.source) context certificate scope administrative ambient.definitions assignment operator rhs)
  (projected : assignment.target.projections ≠ [])
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {actualContext : Core.Context} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical)
  (heaps : HeapRepresents compiled.compatible.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  (unique : NodeOccurrencesUnique (header.function.source))
  (assignmentTyped : SourceAssignmentHasType (header.function.source) context assignment operator rhs)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context (header.function.source))
  (covers : evidence.Covers context)

variable (receipt : CallableIndexedOwnedPublicPreparedTokenReadyNamedExpressionBounds.PublicReceipt header)
  {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
  (diagnosticsFound : compiled.indexed.base.diagnostics = some diagnostics)
  {site : SourceCoreElaboration.ErrorSite}
  (origin : AssignmentDiagnosticOrigins.Occurs (header.function.source) site assignment operator rhs)
  {fuel : Nat}
  (retained : head.PreparedAt site fuel
    (receipt.original.prepared.diagnostics.placeReason header.named.signature.key site assignment.target.root none)
    (fun rawValue => receipt.original.prepared.diagnostics.placeReason header.named.signature.key
      site assignment.target.root (some rawValue)))
  (signatures : context.signatures = compiled.compatible.checked.signatures)
  {table : SourceCoreFaultSites.Table}
  (rebuilt : diagnostics.tableForRegistry registry extension = .ok table)
  (interprets : CallableIndexedOwnedPublicPreparedShapeDiagnostics.ReachedTableInterpretation
    compiled.compatible.checked registry functions callerProtocol environment assignment.target head.prepared initial table faults)

include observations faithful transport extension environments heaps locals agrees actualTyped initial admitted unique assignmentTyped wellFormed runtime covers projected receipt diagnosticsFound origin retained signatures rebuilt interprets in
/-- A fault retains the actual latest key, getter or RHS state and every row's
stable history without claiming deep typing of a fault heap. -/
theorem preserves_fault (budget : Nat)
    (boundedMeaning : RecursiveNamedBoundedContracts.Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge (payloadModel compiled.compatible.checked registry functions)
        context evidence (header.function.source) certificate faults size))
    {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    {size : Nat} (trace : SourceExecutionSize.SourcePlaceAssignmentFaults (Program.ofChecked compiled.sourceProgram) size context evidence (header.function.source) environment before assignment.target operator rhs reason after) (bounded : size ≤ budget)
    (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ StableRows (bridge.pool reached) := by
  have errors := CallableIndexedOwnedPublicPreparedShapeDiagnostics.shape_errors_at_header
    header head initial receipt diagnosticsFound projected origin retained assignmentTyped signatures rebuilt interprets
  exact CallableIndexedOwnedAdmittedPointwiseProjectedAssignmentHeads.preserves_fault_with_diagnostics
    (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (ambient := ambient)
    bridge functions extension evidence transport faithful observations head projected environments heaps locals agrees
    actualTyped initial admitted unique assignmentTyped wellFormed runtime covers budget boundedMeaning errors trace bounded next output

include observations faithful transport extension environments heaps locals agrees actualTyped initial admitted unique assignmentTyped wellFormed runtime covers projected receipt diagnosticsFound origin retained signatures rebuilt interprets in
/-- Native success restores admission at the actual written prefix and keeps
its strict remaining continuation, distinct from the eventual final store. -/
theorem reflects (budget : Nat)
    (boundedReflection : RecursiveNamedBoundedContracts.Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge (payloadModel compiled.compatible.checked registry functions)
        context evidence (header.function.source) certificate faults size)) (functionTypes : FunctionRuntimeViews functions)

    {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    {size : Nat} (completed : EvaluationSize size actual store ((head.emit next output).rename ξ) value finalStore) (bounded : size ≤ budget) :
    CallableIndexedOwnedAdmittedBareAssignmentHeads.ResultAt bridge size compiled.compatible.checked registry functions context evidence (header.function.source) faults
      scope (head.writtenContext actualContext) assignment operator rhs environment canonical actual
      before store mapping world initial (next.rename ξ) output value finalStore := by
  have errors := CallableIndexedOwnedPublicPreparedShapeDiagnostics.shape_errors_at_header
    header head initial receipt diagnosticsFound projected origin retained assignmentTyped signatures rebuilt interprets
  exact CallableIndexedOwnedAdmittedPointwiseProjectedAssignmentHeads.reflects_with_diagnostics
    (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (ambient := ambient)
    bridge functions extension evidence transport faithful observations head projected environments heaps locals agrees
    actualTyped initial admitted unique assignmentTyped wellFormed runtime covers budget boundedReflection functionTypes errors completed bounded

end Heads
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedProjectedAssignmentHeads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedAssignmentReadiness
/-! The actual public Source and issued table provide operand diagnostics.
The joint assignment packet keeps the same selected preparation. Projected
faults use precise table observations at the actual admitted state. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedAssignmentReadiness
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open ProtectedForHeader.Stateful.WithReady
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (receipt : CallableIndexedOwnedPublicPreparedTokenReadyNamedExpressionBounds.PublicReceipt header)
  {ambient : AmbientDefinitions compiled.compatible.checked.catalog.definitions}
  (functions : FunctionModel compiled.compatible.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  (evidence : Dynamic.EvidenceEnvironment)
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (unique : NodeOccurrencesUnique header.function.source)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {context : SourceSemantics.Context}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {administrative : Core.Context} {faults : FunctionCalls.FaultRep}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  {factory : AssignmentDiagnosticOrigins.Factory true diagnosticPolicy header.function.source
    (GenericAssignmentDiagnostics.token receipt.original.prepared.compilation.own.assignments)}

/-- The fault interpretation is requested only for a projected packet at its
actual admitted input. It retains the selected head, environment and state. -/
def ReachedInterpretations
    (table : SourceCoreFaultSites.Table) : Prop :=
  ∀ {scope assignment operator rhs}
    (head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) header.function.source
      context (certificates context) scope administrative ambient.definitions assignment operator rhs)
    {environment : Dynamic.Environment} {index : ProtectedStateTransition.Index}
    (initial : callerProtocol.State index), Admission bridge context initial →
    GenericForHeader.Structural.PreparedAssignment factory
      (fun site root => receipt.original.prepared.diagnostics.placeReason header.named.signature.key site root none)
      (fun site root rawValue => receipt.original.prepared.diagnostics.placeReason header.named.signature.key site root (some rawValue)) head →
    assignment.target.projections ≠ [] →
    CallableIndexedOwnedPublicPreparedShapeDiagnostics.ReachedTableInterpretation
      compiled.compatible.checked registry functions callerProtocol environment assignment.target head.prepared initial table faults

include wellFormed in
private theorem operand_law {scope assignment operator rhs}
    (head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) header.function.source
      context (certificates context) scope administrative ambient.definitions assignment operator rhs)
    {site : SourceCoreElaboration.ErrorSite}
    (origin : AssignmentDiagnosticOrigins.Occurs header.function.source site assignment operator rhs)
    (same : head.invalid = GenericAssignmentDiagnostics.token receipt.original.prepared.compilation.own.assignments site assignment.target.root operator)
    (included : ∀ reason token, GenericAssignmentDiagnostics.OperandRep receipt.original.prepared.compilation.own.assignments reason token → faults reason token) :
    AssignmentOperandDiagnostics.OperandsLaw faults operator head.invalid := by
  obtain ⟨first, issued⟩ := CallableIndexedOwnedPublicDiagnosticReceipts.assignments_at_header
    receipt.original.prepared receipt.diagnostic receipt.original.aligned
  exact same.symm ▸ origin.prepared (SourceDiagnosticTyping.header_diagnostic_typed header wellFormed).2 issued included

variable {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
  (diagnosticsFound : compiled.indexed.base.diagnostics = some diagnostics)
  {table : SourceCoreFaultSites.Table} (rebuilt : diagnostics.tableForRegistry registry extension = .ok table)
  (interprets : ReachedInterpretations header bridge receipt functions table)
  (included : ∀ reason token, GenericAssignmentDiagnostics.OperandRep receipt.original.prepared.compilation.own.assignments reason token → faults reason token)
  (signatures : context.signatures = compiled.compatible.checked.signatures)

include extension transport faithful observations unique wellFormed receipt diagnosticsFound rebuilt interprets included signatures in
theorem assignment_fault (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context header.function.source)
    (covers : evidence.Covers context) (budget : Nat)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence
        header.function.source (certificates context) faults size)) :
    AssignmentFaultPreservesWithPayloadAt callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge)
      (SourceAssignmentHasType header.function.source) (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      (ambient := ambient) functions (registry := registry)
      (Program.ofChecked compiled.sourceProgram) evidence header.function.source (certificates context) context administrative faults budget
      (fun head => GenericForHeader.Structural.PreparedAssignment factory
        (fun site root => receipt.original.prepared.diagnostics.placeReason header.named.signature.key site root none)
        (fun site root rawValue => receipt.original.prepared.diagnostics.placeReason header.named.signature.key site root (some rawValue)) head) := by
  intro scope assignment operator rhs head typed mapping world environment canonical actual before store actualContext ξ
    environments heaps locals agrees actualTyped initial admitted payload reason after size trace bounded next output
  have payload' := payload
  cases payload with
  | intro site origin same sourceTyped rightTyped profile fuel prepared =>
    by_cases bare : assignment.target.projections = []
    · exact CallableIndexedOwnedAdmittedPointwiseBareAssignmentHeads.preserves_fault_with_operands
        (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (ambient := ambient)
        bridge functions extension evidence observations head bare environments heaps locals agrees actualTyped initial admitted unique typed
        budget meaning (operand_law header receipt wellFormed head origin same included) trace bounded next output
    · exact CallableIndexedOwnedPublicPreparedProjectedAssignmentHeads.preserves_fault header bridge functions extension evidence transport
        faithful observations head bare environments heaps locals agrees actualTyped initial admitted unique typed wellFormed runtime covers
        receipt diagnosticsFound origin prepared signatures rebuilt (interprets head initial admitted payload' bare)
        budget meaning trace bounded next output

include extension transport faithful observations unique wellFormed receipt diagnosticsFound rebuilt interprets included signatures in
theorem assignment_reflection (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context header.function.source)
    (covers : evidence.Covers context) (budget : Nat) (functionTypes : FunctionRuntimeViews functions)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence
        header.function.source (certificates context) faults size)) :
    AssignmentReflectsWithPayloadAt callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge)
      (SourceAssignmentHasType header.function.source) (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      (ambient := ambient) functions (registry := registry)
      (Program.ofChecked compiled.sourceProgram) evidence header.function.source (certificates context) context administrative faults budget
      (fun head => GenericForHeader.Structural.PreparedAssignment factory
        (fun site root => receipt.original.prepared.diagnostics.placeReason header.named.signature.key site root none)
        (fun site root rawValue => receipt.original.prepared.diagnostics.placeReason header.named.signature.key site root (some rawValue)) head) := by
  intro scope assignment operator rhs head typed mapping world environment canonical actual before store actualContext ξ
    environments heaps locals agrees actualTyped initial admitted payload next output value finalStore size evaluated bounded
  have payload' := payload
  have result : CallableIndexedOwnedAdmittedBareAssignmentHeads.ResultAt bridge size compiled.compatible.checked registry functions
      context evidence header.function.source faults scope (head.writtenContext actualContext) assignment operator rhs
      environment canonical actual before store mapping world initial (next.rename ξ) output value finalStore := by
    cases payload with
    | intro site origin same sourceTyped rightTyped profile fuel prepared =>
      by_cases bare : assignment.target.projections = []
      · exact CallableIndexedOwnedAdmittedPointwiseBareAssignmentHeads.reflects_with_operands
          (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (ambient := ambient)
          bridge functions extension evidence transport observations head bare environments heaps locals agrees actualTyped initial admitted
          unique typed wellFormed runtime covers budget meaning (operand_law header receipt wellFormed head origin same included) evaluated bounded
      · exact CallableIndexedOwnedPublicPreparedProjectedAssignmentHeads.reflects header bridge functions extension evidence transport
          faithful observations head bare environments heaps locals agrees actualTyped initial admitted unique typed wellFormed runtime covers
          receipt diagnosticsFound origin prepared signatures rebuilt (interprets head initial admitted payload' bare)
          budget meaning functionTypes evaluated bounded
  cases result with
  | fault trace same matched heaps maps worlds frame metadata reached related stable =>
    exact .fault trace same matched heaps maps worlds frame metadata ⟨reached, related, stable⟩
  | success trace heaps maps worlds frame metadata count typed reached related admitted smaller remaining =>
    exact .success trace heaps maps worlds frame metadata count typed ⟨reached, related, admitted⟩ smaller remaining

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedAssignmentReadiness
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedCatalogBounds
/-! The actual public extraction supplies its own Tree, diagnostic plan and
match contexts. Genuine Source validity and strict expression children feed
the original prepared Catalog operations at the same reached states. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedCatalogBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory (NativeFrame)
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open ProtectedStateTransition ProtectedStateImperativeCatalogReady
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedOwnedPublicPreparedSourceSites (Validity)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {protocol : Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (issued : CallableIndexedOwnedPublicPreparedTokenReadyNamedExpressionBounds.PublicReceipt header)
  {compilation : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → SourceCoreFunctions.Context}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  {administrative : Core.Context}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}









variable (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (extension : SourceCoreRawMetadata.Extends ((SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (condition : Location → NativeFrame → Prop)
  (producer : MarkedAllocation.Producer protocol header.layouts compiled.indexed.ancestry.layout.frame
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
  (acquire : ∀ location native, condition location native → OrdinaryAllocation.ReadyAt producer.toOrdinary location native)
  (transport : AdministrativeTransport protocol) (bindings : Bindings protocol)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (sourceRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) header.context (header.function.source))
  {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)}
  (diagnosticsFound : compiled.indexed.base.diagnostics = some diagnostics)
  {table : SourceCoreFaultSites.Table} (rebuilt : diagnostics.tableForRegistry registry extension = .ok table)
  (operandIncluded : ∀ reason token, GenericAssignmentDiagnostics.OperandRep issued.original.prepared.compilation.own.assignments reason token → faults reason token)
  (unaryIncluded : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep issued.original.prepared.compilation.own.assignments reason token → faults reason token)

variable (receipt : CallableIndexedOwnedPublicCatalogPreparedReceipts.CatalogReceipt
  (headers := headers) (compilation := compilation) (expressionSyntax := expressionSyntax)
  (administrative := administrative) issued)







variable (interprets : ∀ context, Validity header context →
  CallableIndexedOwnedPublicPreparedAssignmentReadiness.ReachedInterpretations
    (context := context) (certificates := (CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation header)) (administrative := (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))
    (factory := (AssignmentDiagnosticOrigins.Factory.prepared receipt.operandsTyped receipt.assignments)) (faults := faults) (registry := registry) header bridge issued functions table)

include extension faithful observations producer acquire transport bindings wellFormed sourceRuntime
  diagnosticsFound rebuilt operandIncluded unaryIncluded interprets in
theorem preserves_flow (budget : Nat)
    (_meaning : ∀ context, Validity header context → RecursiveNamedHeaderContracts.AtMost budget
      (fun size => CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        context (header.function.evidence) (header.function.source) ((CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation header) context) faults size)) :
    ProtectedStateImperativeCatalogPayload.PreservesAtWithReceipt protocol (readiness bridge) condition
      (ProtectedStateImperativeTypedSourceSites.Facts (header.function.source) (expressionSyntax header))
      (CallableIndexedOwnedAdmittedForBounds.LoopFacts (header.function.source) (expressionSyntax header))
      (ProtectedStateImperativeInitializerSourceSites.Facts (header.function.source) (expressionSyntax header))
      functions (Program.ofChecked compiled.sourceProgram) (header.function.evidence) (Validity header) budget (ProtectedStateImperativeCatalogPayload.StructuralHeaderReceipt
  (layouts := header.layouts) (owner := header.owner) (active := header.active)
  (frame := compiled.indexed.ancestry.layout.frame) (globals := header.globals) (onError := header.onError)
  (values := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)) (source := (header.function.source)) (certificates := (CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation header))
  (definitions := compiled.indexed.layouts.definitions) (administrative := (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) ((fun head => GenericForHeader.Structural.PreparedAssignment (AssignmentDiagnosticOrigins.Factory.prepared receipt.operandsTyped receipt.assignments) (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection issued.original.prepared) (RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault issued.original.prepared) head)) ((fun head => GenericForHeader.Structural.PreparedUnary true (header.function.source)
  (fun site root => issued.original.prepared.compilation.own.assignments.reasonAt site root SourceCoreAssignmentFaultSites.Kind.bitNot) head)))
      (frame := compiled.indexed.ancestry.layout.frame) (globals := header.globals)
      (source := (header.function.source)) (administrative := (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) (registry := registry) (faults := faults)
      (values := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)) (ambient := (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
      header.context (RecursiveNamedCatalogNativeContexts.bodyScope (prepared := compiled.indexed.ancestry)
  (values := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)) (ambient := (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) (program := (Program.ofChecked compiled.sourceProgram)) header) (.statements true header.function.body) header.function.resultType header.output receipt.flow := by
  let inputs := CallableIndexedOwnedPublicPreparedSourceSites.inputs header bridge bindings wellFormed sourceRuntime
    (expressionSyntax := expressionSyntax header)
  have below : ∀ context, Validity header context → RecursiveNamedBoundedContracts.Below budget
      (fun size => CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        context (header.function.evidence) (header.function.source) ((CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation header) context) faults size) :=
    fun context valid child smaller => _meaning context valid child (Nat.le_of_lt smaller)
  let assignments : ∀ context, Validity header context →
      ProtectedForHeader.Stateful.WithReady.AssignmentFaultPreservesWithPayloadAt
        protocol (readiness bridge) (SourceAssignmentHasType (header.function.source))
        (values := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)) (ambient := (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) functions (registry := registry)
        (Program.ofChecked compiled.sourceProgram) (header.function.evidence) (header.function.source) ((CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation header) context) context (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) faults budget
        (fun head => ((fun head => GenericForHeader.Structural.PreparedAssignment (AssignmentDiagnosticOrigins.Factory.prepared receipt.operandsTyped receipt.assignments) (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection issued.original.prepared) (RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault issued.original.prepared) head)) head) := by
    intro context valid scope assignment operator rhs
    dsimp only [ProtectedForHeader.Stateful.WithReady.AssignmentFaultPreservesWithPayloadAt,
      ProtectedForHeader.Stateful.WithReady.AssignmentReflectsWithPayloadAt,
      RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection,
      RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault]
    unfold RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection
      RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault
    have key := congrArg (fun named : SourceCoreGeneralFunctions.Function => named.signature.key) issued.original.aligned.named
    rw [← key]
    exact (CallableIndexedOwnedPublicPreparedAssignmentReadiness.assignment_fault
      (context := context) (certificates := (CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation header)) (administrative := (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))
      (factory := (AssignmentDiagnosticOrigins.Factory.prepared receipt.operandsTyped receipt.assignments)) (registry := registry) (faults := faults)
      (scope := scope) (assignment := assignment) (operator := operator) (rhs := rhs)
      header bridge issued functions extension (header.function.evidence)
      transport faithful observations header.unique wellFormed diagnosticsFound rebuilt (interprets context valid)
      operandIncluded (CallableIndexedOwnedPublicPreparedSourceSites.signatures header valid) valid.2 valid.1.covers budget (below context valid))
  exact RecursiveNamedImperativeFor.Stateful.WithReady.preservesAt_match_catalog_coupled
    (values := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)) (ambient := (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) (layouts := header.layouts)
    (owner := header.owner) (active := header.active) (frame := compiled.indexed.ancestry.layout.frame)
    (globals := header.globals) (onError := header.onError) (source := (header.function.source))
    (expressionSyntax := expressionSyntax header) (certificates := (CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation header))
    (administrative := (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) (solved := header.solved) (factory := (AssignmentDiagnosticOrigins.Factory.prepared receipt.operandsTyped receipt.assignments))
    (invalidProjection := (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection issued.original.prepared)) (missingDefault := (RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault issued.original.prepared))
    (functions := functions) (definitions := header.definitions_eq) (registered := header.registered)
    (program := (Program.ofChecked compiled.sourceProgram)) (evidence := (header.function.evidence)) (protocol := protocol)
    (readiness := readiness bridge) (conditionGate := condition)
    (facts := ProtectedStateImperativeTypedSourceSites.Facts (header.function.source) (expressionSyntax header))
    (headFacts := ProtectedStateImperativeTypedSourceSites.HeadFacts (header.function.source) (expressionSyntax header))
    (exprFacts := ProtectedStateLexicalSourceSites.ExpressionFacts (header.function.source))
    (loopFacts := CallableIndexedOwnedAdmittedForBounds.LoopFacts (header.function.source) (expressionSyntax header))
    (initializerFacts := ProtectedStateImperativeInitializerSourceSites.Facts (header.function.source) (expressionSyntax header))
    (assignmentFacts := SourceAssignmentHasType (header.function.source)) (snapshotFacts := SourceBitNotAssignmentValid (header.function.source))
    (producer := producer) (stateTransport := transport) (stateBindings := bindings) (acquire := acquire)
    (validity := Validity header) (extend := fun valid extended => CallableIndexedOwnedPublicPreparedSourceSites.validity_extend header valid extended)
    (budget := budget)
    (sites := inputs.sites) (assignmentSites := inputs.assignments) (initializerSites := inputs.initializers)
    (transfers := inputs.transfers) (snapshots := inputs.snapshots)
    (assignments := fun context valid => CallableIndexedOwnedAdmittedForHeaderReadiness.assignment_prefix
      (values := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)) (ambient := (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) (certificate := (CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation header) context) (administrative := (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) (faults := faults)
      bridge functions extension (header.function.evidence) transport faithful observations header.unique wellFormed valid.2 valid.1.covers budget (below context valid))
    (meaningMost := fun context valid child within => CallableIndexedOwnedAdmittedLexicalReadiness.preserves_at bridge _ (_meaning context valid child within))
    receipt.unaryTyped receipt.assignments unaryIncluded receipt.catalog assignments header.unique
    (CallableIndexedOwnedPreparedCatalogProducers.preserving_heads
      (values := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)) (ambient := (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) (source := (header.function.source)) (expressionSyntax := expressionSyntax header)
      (certificates := (CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation header)) (administrative := (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) (factory := (AssignmentDiagnosticOrigins.Factory.prepared receipt.operandsTyped receipt.assignments)) (invalidProjection := (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection issued.original.prepared)) (missingDefault := (RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault issued.original.prepared))
      bridge functions header.definitions_eq header.registered extension (header.function.evidence) faithful observations condition producer acquire transport bindings header.unique wellFormed
      (Validity header) (fun _ valid => valid.2) (fun _ valid => valid.1.covers)
      (fun valid extended => CallableIndexedOwnedPublicPreparedSourceSites.validity_extend header valid extended)
      budget .reachable (fun _ valid => valid.1) receipt.unaryTyped receipt.assignments unaryIncluded below assignments)
    (CallableIndexedOwnedPreparedCatalogProducers.preserving_loops
      (values := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)) (ambient := (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) (source := (header.function.source)) (expressionSyntax := expressionSyntax header)
      (certificates := (CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation header)) (administrative := (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) (factory := (AssignmentDiagnosticOrigins.Factory.prepared receipt.operandsTyped receipt.assignments)) (invalidProjection := (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection issued.original.prepared)) (missingDefault := (RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault issued.original.prepared))
      bridge functions header.definitions_eq header.registered extension (header.function.evidence) faithful observations condition producer acquire transport bindings header.unique wellFormed
      (Validity header) (fun _ valid => valid.2) (fun _ valid => valid.1.covers)
      (fun valid extended => CallableIndexedOwnedPublicPreparedSourceSites.validity_extend header valid extended)
      budget .reachable receipt.unaryTyped receipt.assignments unaryIncluded below assignments)
    receipt.extracted (CallableIndexedOwnedPublicCatalogPreparedReceipts.ledger issued)

include extension observations producer acquire transport bindings wellFormed sourceRuntime
  diagnosticsFound rebuilt operandIncluded unaryIncluded interprets faithful in
theorem reflects_flow (budget : Nat) (_functionTypes : FunctionRuntimeViews functions)
    (_reflection : ∀ context, Validity header context → RecursiveNamedBoundedContracts.Below budget
      (fun size => CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        context (header.function.evidence) (header.function.source) ((CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation header) context) faults size)) :
    ProtectedStateImperativeCatalogPayload.ReflectsAtWithReceipt protocol (readiness bridge) condition
      (ProtectedStateImperativeTypedSourceSites.Facts (header.function.source) (expressionSyntax header))
      (CallableIndexedOwnedAdmittedForBounds.LoopFacts (header.function.source) (expressionSyntax header))
      (ProtectedStateImperativeInitializerSourceSites.Facts (header.function.source) (expressionSyntax header))
      functions (Program.ofChecked compiled.sourceProgram) (header.function.evidence) (Validity header) budget (ProtectedStateImperativeCatalogPayload.StructuralHeaderReceipt
  (layouts := header.layouts) (owner := header.owner) (active := header.active)
  (frame := compiled.indexed.ancestry.layout.frame) (globals := header.globals) (onError := header.onError)
  (values := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)) (source := (header.function.source)) (certificates := (CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation header))
  (definitions := compiled.indexed.layouts.definitions) (administrative := (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) ((fun head => GenericForHeader.Structural.PreparedAssignment (AssignmentDiagnosticOrigins.Factory.prepared receipt.operandsTyped receipt.assignments) (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection issued.original.prepared) (RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault issued.original.prepared) head)) ((fun head => GenericForHeader.Structural.PreparedUnary true (header.function.source)
  (fun site root => issued.original.prepared.compilation.own.assignments.reasonAt site root SourceCoreAssignmentFaultSites.Kind.bitNot) head)))
      (frame := compiled.indexed.ancestry.layout.frame) (globals := header.globals)
      (source := (header.function.source)) (administrative := (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) (registry := registry) (faults := faults)
      (values := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)) (ambient := (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
      header.context (RecursiveNamedCatalogNativeContexts.bodyScope (prepared := compiled.indexed.ancestry)
  (values := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)) (ambient := (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) (program := (Program.ofChecked compiled.sourceProgram)) header) (.statements true header.function.body) header.function.resultType header.output receipt.flow := by
  let inputs := CallableIndexedOwnedPublicPreparedSourceSites.inputs header bridge bindings wellFormed sourceRuntime
    (expressionSyntax := expressionSyntax header)
  let assignments : ∀ context, Validity header context →
      ProtectedForHeader.Stateful.WithReady.AssignmentReflectsWithPayloadAt
        protocol (readiness bridge) (SourceAssignmentHasType (header.function.source))
        (values := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)) (ambient := (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) functions (registry := registry)
        (Program.ofChecked compiled.sourceProgram) (header.function.evidence) (header.function.source) ((CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation header) context) context (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) faults budget
        (fun head => ((fun head => GenericForHeader.Structural.PreparedAssignment (AssignmentDiagnosticOrigins.Factory.prepared receipt.operandsTyped receipt.assignments) (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection issued.original.prepared) (RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault issued.original.prepared) head)) head) := by
    intro context valid scope assignment operator rhs
    dsimp only [ProtectedForHeader.Stateful.WithReady.AssignmentFaultPreservesWithPayloadAt,
      ProtectedForHeader.Stateful.WithReady.AssignmentReflectsWithPayloadAt,
      RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection,
      RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault]
    unfold RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection
      RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault
    have key := congrArg (fun named : SourceCoreGeneralFunctions.Function => named.signature.key) issued.original.aligned.named
    rw [← key]
    exact (CallableIndexedOwnedPublicPreparedAssignmentReadiness.assignment_reflection
      (context := context) (certificates := (CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation header)) (administrative := (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))
      (factory := (AssignmentDiagnosticOrigins.Factory.prepared receipt.operandsTyped receipt.assignments)) (registry := registry) (faults := faults)
      (scope := scope) (assignment := assignment) (operator := operator) (rhs := rhs)
      header bridge issued functions extension (header.function.evidence)
      transport faithful observations header.unique wellFormed diagnosticsFound rebuilt (interprets context valid)
      operandIncluded (CallableIndexedOwnedPublicPreparedSourceSites.signatures header valid) valid.2 valid.1.covers budget _functionTypes (_reflection context valid))
  exact RecursiveNamedImperativeFor.Stateful.WithReady.reflectsAt_match_catalog_coupled
    (values := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)) (ambient := (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) (layouts := header.layouts)
    (owner := header.owner) (active := header.active) (frame := compiled.indexed.ancestry.layout.frame)
    (globals := header.globals) (onError := header.onError) (source := (header.function.source))
    (expressionSyntax := expressionSyntax header) (certificates := (CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation header))
    (administrative := (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) (solved := header.solved) (factory := (AssignmentDiagnosticOrigins.Factory.prepared receipt.operandsTyped receipt.assignments))
    (invalidProjection := (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection issued.original.prepared)) (missingDefault := (RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault issued.original.prepared))
    (functions := functions) (definitions := header.definitions_eq) (registered := header.registered)
    (program := (Program.ofChecked compiled.sourceProgram)) (evidence := (header.function.evidence)) (protocol := protocol)
    (readiness := readiness bridge) (conditionGate := condition)
    (facts := ProtectedStateImperativeTypedSourceSites.Facts (header.function.source) (expressionSyntax header))
    (headFacts := ProtectedStateImperativeTypedSourceSites.HeadFacts (header.function.source) (expressionSyntax header))
    (exprFacts := ProtectedStateLexicalSourceSites.ExpressionFacts (header.function.source))
    (loopFacts := CallableIndexedOwnedAdmittedForBounds.LoopFacts (header.function.source) (expressionSyntax header))
    (initializerFacts := ProtectedStateImperativeInitializerSourceSites.Facts (header.function.source) (expressionSyntax header))
    (assignmentFacts := SourceAssignmentHasType (header.function.source)) (snapshotFacts := SourceBitNotAssignmentValid (header.function.source))
    (producer := producer) (stateTransport := transport) (stateBindings := bindings) (acquire := acquire)
    (validity := Validity header) (extend := fun valid extended => CallableIndexedOwnedPublicPreparedSourceSites.validity_extend header valid extended)
    (budget := budget) (sites := inputs.sites) (assignmentSites := inputs.assignments) (initializerSites := inputs.initializers)
    (transfers := inputs.transfers) (snapshots := inputs.snapshots)
    (reflection := fun context valid child within => CallableIndexedOwnedAdmittedLexicalReadiness.reflects_at bridge _ (_reflection context valid child within))
    receipt.unaryTyped receipt.assignments unaryIncluded receipt.catalog assignments header.unique
    (CallableIndexedOwnedPreparedCatalogProducers.reflecting_heads
      (values := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)) (ambient := (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) (source := (header.function.source)) (expressionSyntax := expressionSyntax header)
      (certificates := (CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation header)) (administrative := (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) (factory := (AssignmentDiagnosticOrigins.Factory.prepared receipt.operandsTyped receipt.assignments)) (invalidProjection := (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection issued.original.prepared)) (missingDefault := (RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault issued.original.prepared))
      bridge functions header.definitions_eq header.registered extension (header.function.evidence) condition producer acquire transport bindings header.unique wellFormed
      (Validity header) (fun _ valid => valid.2) (fun _ valid => valid.1.covers)
      (fun valid extended => CallableIndexedOwnedPublicPreparedSourceSites.validity_extend header valid extended)
      budget .reachable (fun _ valid => valid.1) receipt.unaryTyped receipt.assignments unaryIncluded _reflection assignments)
    (CallableIndexedOwnedPreparedCatalogProducers.reflecting_loops
      (values := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)) (ambient := (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) (source := (header.function.source)) (expressionSyntax := expressionSyntax header)
      (certificates := (CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation header)) (administrative := (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) (factory := (AssignmentDiagnosticOrigins.Factory.prepared receipt.operandsTyped receipt.assignments)) (invalidProjection := (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection issued.original.prepared)) (missingDefault := (RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault issued.original.prepared))
      bridge functions header.definitions_eq header.registered (header.function.evidence) condition producer acquire transport bindings header.unique wellFormed
      (Validity header) (fun _ valid => valid.2) (fun _ valid => valid.1.covers)
      (fun valid extended => CallableIndexedOwnedPublicPreparedSourceSites.validity_extend header valid extended)
      budget .reachable receipt.unaryTyped receipt.assignments unaryIncluded _reflection assignments)
    receipt.extracted (CallableIndexedOwnedPublicCatalogPreparedReceipts.ledger issued)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedCatalogBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedBodyBounds
/-! A genuine public parameter entry supplies the original Source receipt and
its chosen compiler flow. The existing finish proofs retain that same reached
pool, while successful Source body typing supplies its exact PostAdmission. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedBodyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory (NativeFrame GhostFrame)
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open ProtectedStateTransition ProtectedStateImperativeCatalogReady
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedOwnedPublicPreparedSourceSites (Validity)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {protocol : Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (issued : CallableIndexedOwnedPublicPreparedTokenReadyNamedExpressionBounds.PublicReceipt header)
  {compilation : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → SourceCoreFunctions.Context}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  {administrative : Core.Context}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}









variable (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (extension : SourceCoreRawMetadata.Extends ((SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (condition : Location → NativeFrame → Prop)
  (producer : MarkedAllocation.Producer protocol header.layouts compiled.indexed.ancestry.layout.frame
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
  (acquire : ∀ location native, condition location native → OrdinaryAllocation.ReadyAt producer.toOrdinary location native)
  (transport : AdministrativeTransport protocol) (bindings : Bindings protocol)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)}
  (diagnosticsFound : compiled.indexed.base.diagnostics = some diagnostics)
  {table : SourceCoreFaultSites.Table} (rebuilt : diagnostics.tableForRegistry registry extension = .ok table)
  (operandIncluded : ∀ reason token, GenericAssignmentDiagnostics.OperandRep issued.original.prepared.compilation.own.assignments reason token → faults reason token)
  (unaryIncluded : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep issued.original.prepared.compilation.own.assignments reason token → faults reason token)


open RecursiveNamedCatalogInvocationBounds (BodyState)
open RecursiveNamedCatalogNativeContexts (Complete)
open CallableIndexedOwnedAdmittedBodyEntries (SourceReceipt)
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)

variable (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (complete : Complete (prepared := compiled.indexed.ancestry) (values := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked))
    (ambient := (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) headers)
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
  (entry : BodyState (prepared := compiled.indexed.ancestry) (values := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked))
    (ambient := (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) headers owner.key.locations 0 functions registry header arguments before initialStore
    mapping world administrative actualContext actual ξ frameLocation current ghost)
  (sourceReceipt : SourceReceipt (Program.ofChecked compiled.sourceProgram) header.function header.context entry.environment entry.heap)
  (children : CallableIndexedOwnedNamedTokenProfileExtraction.Children
    (header := header) (headers := headers) (expressionSyntax := expressionSyntax) compilation (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))
  (initial : protocol.State ⟨(RecursiveNamedCatalogNativeContexts.bodyScope (prepared := compiled.indexed.ancestry)
  (values := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)) (ambient := (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) (program := (Program.ofChecked compiled.sourceProgram)) header), entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
  (stable : StableRows (bridge.pool initial))
  (gate : condition frameLocation current)
  (escapedFault : faults .controlEscapedFunction header.escaped)

/-- Every clause describes this body's actual returned state. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) (value : Value) (finalStore : Store) : Prop :=
  ∃ finalMap finalWorld,
    FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      finalMap finalWorld header.function.resultType header.output faults outcome value ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
    LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
    AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
    TypedMixedNamedBody.ReachedExit compiled.compatible.checked ((CallableIndexedAmbient.ambientDefinitions compiled.indexed)).definitions finalMap finalWorld (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
      (Program.ofChecked compiled.sourceProgram) header.function header.context (RecursiveNamedCatalogNativeContexts.bodyScope (prepared := compiled.indexed.ancestry)
  (values := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)) (ambient := (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) (program := (Program.ofChecked compiled.sourceProgram)) header) entry.environment entry.heap after outcome ∧
    ∃ reached : protocol.State ⟨(RecursiveNamedCatalogNativeContexts.bodyScope (prepared := compiled.indexed.ancestry)
  (values := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)) (ambient := (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) (program := (Program.ofChecked compiled.sourceProgram)) header), finalMap, finalWorld, after, finalStore, entry.canonical⟩,
      protocol.Relates initial reached ∧ PostAdmission bridge header.context header.function.resultType outcome reached

variable (interpretations : ∀ receipt : CallableIndexedOwnedPublicCatalogPreparedReceipts.CatalogReceipt
    (headers := headers) (compilation := compilation) (expressionSyntax := expressionSyntax)
    (administrative := administrative) issued,
  ∀ context, Validity header context →
    CallableIndexedOwnedPublicPreparedAssignmentReadiness.ReachedInterpretations
      (context := context) (certificates := (CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation header)) (administrative := (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))
      (factory := AssignmentDiagnosticOrigins.Factory.prepared receipt.operandsTyped receipt.assignments)
      (faults := faults) (registry := registry) header bridge issued functions table)

include extension faithful observations producer acquire transport bindings wellFormed diagnosticsFound rebuilt
  operandIncluded unaryIncluded complete sourceReceipt children stable gate escapedFault interpretations in
theorem preserves_at_entry (budget size : Nat) (within : size ≤ budget)
    (meaning : ∀ context, Validity header context → RecursiveNamedHeaderContracts.AtMost budget
      (fun child => CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        context (header.function.evidence) (header.function.source) ((CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation header) context) faults child))
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyTrace (Program.ofChecked compiled.sourceProgram) size header.function header.context
      entry.environment entry.heap outcome after) :
    ∃ value finalStore,
      Evaluates entry.actualBody entry.store (header.body.rename entry.embedding) value finalStore ∧
      ResultAt (faults := faults) header bridge functions owner entry initial outcome after value finalStore := by
  obtain ⟨receipt⟩ := CallableIndexedOwnedPublicCatalogPreparedReceipts.at_entry
    functions owner complete entry issued wellFormed children
  have flow := CallableIndexedOwnedPublicPreparedCatalogBounds.preserves_flow
    (header := header) (bridge := bridge) (issued := issued) (functions := functions)
    (extension := extension) (faithful := faithful) (observations := observations) (condition := condition)
    (producer := producer) (acquire := acquire) (transport := transport) (bindings := bindings)
    (wellFormed := wellFormed) (sourceRuntime := sourceReceipt.runtime) (diagnosticsFound := diagnosticsFound)
    (rebuilt := rebuilt) (operandIncluded := operandIncluded) (unaryIncluded := unaryIncluded)
    (receipt := receipt) (interprets := interpretations receipt) budget meaning
  have admitted : Admission bridge header.context initial := ⟨sourceReceipt.heapTyped, stable⟩
  have reference : entry.canonical[(RecursiveNamedCatalogNativeContexts.bodyScope (prepared := compiled.indexed.ancestry)
  (values := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)) (ambient := (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) (program := (Program.ofChecked compiled.sourceProgram)) header).length + 1 + header.globals]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type frameLocation) := by
    simpa only [RecursiveNamedCatalogNativeContexts.bodyScope, List.length_map, List.length_reverse] using entry.reference
  have unmapped : frameLocation ∉ entry.mapping :=
    Eq.mp (congrArg (fun location => location ∉ entry.mapping) entry.catalog_frame) entry.catalog.authority.unmapped
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, frame, metadata, lexical, reached, related, _post⟩ :=
    RecursiveNamedFunctionFinishBounds.WithReady.preserves_at_emitted_with_state_when
      (functions := functions) (program := (Program.ofChecked compiled.sourceProgram)) (tree := receipt.extracted.original.original.original.original.tree)
      (projection := issued.original.aligned.projection) (unique := header.unique) (escapedFault := escapedFault)
      protocol (readiness bridge) condition
      (ProtectedStateImperativeTypedSourceSites.Facts (header.function.source) (expressionSyntax header))
      receipt.finished (Validity header) size (flow size within)
      (CallableIndexedOwnedPublicPreparedSourceSites.validity_at header sourceReceipt.runtime)
      (CallableIndexedOwnedPublicPreparedSourceSites.body_facts header sourceReceipt children.syntaxTree)
      entry.environments entry.heaps entry.locals entry.lookups entry.actualTyped reference entry.state.read unmapped initial gate admitted trace
  refine ⟨value, finalStore, evaluated, finalMap, finalWorld, represented, heaps, maps, worlds, frame, metadata, lexical, reached, related, ?_⟩
  exact ⟨StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) stable frame,
    sourceReceipt.after_body_values wellFormed trace⟩

include extension faithful observations producer acquire transport bindings wellFormed diagnosticsFound rebuilt
  operandIncluded unaryIncluded complete sourceReceipt children stable gate escapedFault interpretations in
theorem reflects_at_entry (budget size : Nat) (within : size ≤ budget)
    (functionTypes : FunctionRuntimeViews functions)
    (reflection : ∀ context, Validity header context → RecursiveNamedBoundedContracts.Below budget
      (fun child => CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        context (header.function.evidence) (header.function.source) ((CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation header) context) faults child))
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size entry.actualBody entry.store (header.body.rename entry.embedding) value finalStore) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.BodyTrace (Program.ofChecked compiled.sourceProgram) sourceSize header.function header.context entry.environment entry.heap outcome after ∧
      ResultAt (faults := faults) header bridge functions owner entry initial outcome after value finalStore := by
  obtain ⟨receipt⟩ := CallableIndexedOwnedPublicCatalogPreparedReceipts.at_entry
    functions owner complete entry issued wellFormed children
  have flow := CallableIndexedOwnedPublicPreparedCatalogBounds.reflects_flow
    (header := header) (bridge := bridge) (issued := issued) (functions := functions)
    (extension := extension) (faithful := faithful) (observations := observations) (condition := condition)
    (producer := producer) (acquire := acquire) (transport := transport) (bindings := bindings)
    (wellFormed := wellFormed) (sourceRuntime := sourceReceipt.runtime) (diagnosticsFound := diagnosticsFound)
    (rebuilt := rebuilt) (operandIncluded := operandIncluded) (unaryIncluded := unaryIncluded)
    (receipt := receipt) (interprets := interpretations receipt) budget functionTypes reflection
  have admitted : Admission bridge header.context initial := ⟨sourceReceipt.heapTyped, stable⟩
  have reference : entry.canonical[(RecursiveNamedCatalogNativeContexts.bodyScope (prepared := compiled.indexed.ancestry)
  (values := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)) (ambient := (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) (program := (Program.ofChecked compiled.sourceProgram)) header).length + 1 + header.globals]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type frameLocation) := by
    simpa only [RecursiveNamedCatalogNativeContexts.bodyScope, List.length_map, List.length_reverse] using entry.reference
  have unmapped : frameLocation ∉ entry.mapping :=
    Eq.mp (congrArg (fun location => location ∉ entry.mapping) entry.catalog_frame) entry.catalog.authority.unmapped
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, frame, metadata, lexical, reached, related, _post⟩ :=
    RecursiveNamedFunctionFinishBounds.WithReady.reflects_at_emitted_with_state_when
      (functions := functions) (program := (Program.ofChecked compiled.sourceProgram)) (tree := receipt.extracted.original.original.original.original.tree)
      (projection := issued.original.aligned.projection) (unique := header.unique) (escapedFault := escapedFault)
      protocol (readiness bridge) condition
      (ProtectedStateImperativeTypedSourceSites.Facts (header.function.source) (expressionSyntax header))
      receipt.finished (Validity header) budget size within flow
      (CallableIndexedOwnedPublicPreparedSourceSites.validity_at header sourceReceipt.runtime)
      (CallableIndexedOwnedPublicPreparedSourceSites.body_facts header sourceReceipt children.syntaxTree)
      entry.environments entry.heaps entry.locals entry.lookups entry.actualTyped reference entry.state.read unmapped initial gate admitted completed
  refine ⟨sourceSize, outcome, after, trace, finalMap, finalWorld, represented, heaps, maps, worlds, frame, metadata, lexical, reached, related, ?_⟩
  exact ⟨StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) stable frame,
    sourceReceipt.after_body_values wellFormed trace⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedBodyBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedNamedFamilyClosure
/-! Actual public named parameter receipts close through the existing measured
family. Each child retains its own Header, Source input and administrative
context; the original expression support fold and finish proofs preserve the
same returned pool and independently sized Source reflection. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedNamedFamilyClosure
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableIndexedOwnedPreparedNamedParameterReceipts (Receipt)
open CallableIndexedOwnedPublicPreparedTokenReadyNamedExpressionBounds (PublicReceipt)
open CallableIndexedOwnedPublicPreparedSourceSites (Validity)
open RecursiveNamedCatalogInvocationBounds (BodyState)
open ProtectedStateTransition

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)

/-- The family index is the complete actual parameter input. -/
structure Index where
  header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)
  member : header ∈ headers
  initial : ProtectedStateTransition.Index
  argumentsPool : State headers keys initial
  arguments : List Dynamic.Value
  receipt : Receipt (registry := registry) functions owner argumentsPool header arguments

section Ordinary
variable {initial : ProtectedStateTransition.Index} {argumentsPool : State headers keys initial}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {arguments : List Dynamic.Value}
  (receipt : Receipt (registry := registry) functions owner argumentsPool header arguments)
  (prefixZero : owner.key.capturePrefix = 0)

private def ordinary_catalog : RecursiveNamedCatalog.Entry
    (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers owner.key.locations 0 1 (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    receipt.body.mapping receipt.body.world receipt.body.heap receipt.body.store receipt.body.canonical where
  authority := {
    frameLocation := receipt.body.catalog.authority.frameLocation
    unmapped := receipt.body.catalog.authority.unmapped
    typed := receipt.body.catalog.authority.typed
    current := receipt.body.catalog.authority.current
    ghost := receipt.body.catalog.authority.ghost
    frame := receipt.body.catalog.authority.frame
    records := receipt.body.catalog.authority.records
    snapshots := receipt.body.catalog.authority.snapshots
    distinct := receipt.body.catalog.authority.distinct
    captures := by simpa only [prefixZero] using receipt.body.catalog.authority.captures }
  globals := by simpa only [prefixZero, Nat.zero_add] using receipt.body.catalog.globals

/-- Reindex only the catalog prefix. Every runtime field is copied literally
from the original actual BodyState. -/
def ordinary_entry : BodyState (prepared := compiled.indexed.ancestry)
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers owner.key.locations 0 functions registry header arguments initial.heap
    (initial.store.set receipt.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state receipt.index)))
    initial.mapping initial.world receipt.administrative receipt.actualContext receipt.actual receipt.embedding
    receipt.frameLocation (.state receipt.index) (.named receipt.origin) :=
  BodyState.of_receipts receipt.body.environment receipt.body.heap receipt.body.canonical receipt.body.actualBody
    receipt.body.store receipt.body.mapping receipt.body.world receipt.body.embedding receipt.body.allocation
    receipt.body.environments receipt.body.heaps receipt.body.locals receipt.body.maps receipt.body.worlds
    receipt.body.frame receipt.body.metadata receipt.body.lookups receipt.body.actualTyped
    (ordinary_catalog functions owner receipt prefixZero) receipt.body.reference receipt.body.state
    receipt.body.catalog_frame receipt.body.catalog_current receipt.body.catalog_ghost

end Ordinary

/-- The principal packet and original pool accompany the actual selected
Header. The carrier projects only the unchanged base State. -/
def bridge (index : Index (headers := headers) (registry := registry) functions owner) :=
  CallableIndexedOwnedIndirectCallerProtocol.forget_slots
    (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner index.header)

variable {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  (publicReceipts : ∀ header, header ∈ headers → PublicReceipt header)
  {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
  {table : SourceCoreFaultSites.Table}

/-- Genuine child compilation and the precise reached table interpretation
belong to this receipt's own administrative context. No body meaning is stored. -/
structure Inputs (index : Index (headers := headers) (registry := registry) functions owner) where
  children : CallableIndexedOwnedNamedTokenProfileExtraction.Children
    (header := index.header) (headers := headers) (expressionSyntax := expressionSyntax)
    CallableIndexedOwnedPublicReadyNamedExpressionBounds.compilation
    (SourceCoreCompatibleCatalog.packTypes (index.header.bindings.map Prod.snd) :: index.receipt.administrative)
  interpretations : ∀ extracted : CallableIndexedOwnedPublicCatalogPreparedReceipts.CatalogReceipt
      (headers := headers) (compilation := CallableIndexedOwnedPublicReadyNamedExpressionBounds.compilation)
      (expressionSyntax := expressionSyntax) (administrative := index.receipt.administrative)
      (publicReceipts index.header index.member),
    ∀ context, Validity index.header context →
      CallableIndexedOwnedPublicPreparedAssignmentReadiness.ReachedInterpretations
        (context := context)
        (certificates := CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers)
          CallableIndexedOwnedPublicReadyNamedExpressionBounds.compilation index.header)
        (administrative := SourceCoreCompatibleCatalog.packTypes (index.header.bindings.map Prod.snd) :: index.receipt.administrative)
        (factory := AssignmentDiagnosticOrigins.Factory.prepared extracted.operandsTyped extracted.assignments)
        (faults := faults) (registry := registry) index.header (bridge functions owner index)
        (publicReceipts index.header index.member) functions table

variable (prefixZero : owner.key.capturePrefix = 0)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (complete : RecursiveNamedCatalogNativeContexts.Complete (prepared := compiled.indexed.ancestry)
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  (diagnosticsFound : compiled.indexed.base.diagnostics = some diagnostics)
  (rebuilt : diagnostics.tableForRegistry registry extension = .ok table)
  (operandIncluded : ∀ header member reason token, GenericAssignmentDiagnostics.OperandRep
    (publicReceipts header member).original.prepared.compilation.own.assignments reason token → faults reason token)
  (unaryIncluded : ∀ header member reason token, EmittedDiagnosticTokenPlan.UnaryRep
    (publicReceipts header member).original.prepared.compilation.own.assignments reason token → faults reason token)
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header, header ∈ headers → faults .controlEscapedFunction header.escaped)
  (inputs : ∀ index : Index (headers := headers) (registry := registry) functions owner,
    Inputs (table := table) (faults := faults) (expressionSyntax := expressionSyntax) functions owner publicReceipts index)

/-- Both meanings belong to the same actual parameter receipt. -/
def Family (index : Index (headers := headers) (registry := registry) functions owner) (size : Nat) : Prop :=
  CallableIndexedOwnedPreparedNamedParameterReceipts.PreservesAt index.receipt (faults := faults) size ∧
    CallableIndexedOwnedPreparedNamedParameterReceipts.ReflectsAt index.receipt (faults := faults) size

private def producer (index : Index (headers := headers) (registry := registry) functions owner) :
    MarkedAllocation.Producer (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner index.header)
      index.header.layouts compiled.indexed.ancestry.layout.frame
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) :=
  (publicReceipts index.header index.member).original.aligned.layouts.symm ▸
    CallableIndexedOwnedNestedCanonicalState.markedProducer owner index.header
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)

private theorem ready_layout {first second : SourceCoreAllocationLayouts.Prepared}
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    (index : Index (headers := headers) (registry := registry) functions owner) (same : first = second)
    (marked : MarkedAllocation.Producer (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner index.header)
      second compiled.indexed.ancestry.layout.frame model)
    {location : Location} {native : NativeFrame}
    (ready : OrdinaryAllocation.ReadyAt marked.toOrdinary location native) :
    OrdinaryAllocation.ReadyAt ((same.symm ▸ marked).toOrdinary) location native := by
  cases same
  exact ready

private theorem acquire (index : Index (headers := headers) (registry := registry) functions owner)
    (location : Location) (native : NativeFrame)
    (stable : CallableIndexedOwnedAllocationProducer.StableOwner keys location native) :
    OrdinaryAllocation.ReadyAt (producer functions owner publicReceipts index).toOrdinary location native :=
  ready_layout functions owner index (publicReceipts index.header index.member).original.aligned.layouts
    (CallableIndexedOwnedNestedCanonicalState.markedProducer owner index.header
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
    (CallableIndexedOwnedNestedCanonicalState.readyAt_of_stableOwner owner index.header
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) stable)

include prefixZero extension faithful observations functionTypes wellFormed complete owners diagnosticsFound rebuilt
  operandIncluded unaryIncluded uninitialized missing escaped inputs in
/-- Strict actual callee receipts close the original expression fold. The
chosen public flow and existing finish then return this same parameter pool. -/
private theorem preserves_step (budget : Nat)
    (below : ∀ index : Index (headers := headers) (registry := registry) functions owner,
      RecursiveNamedBoundedContracts.Below budget (Family (faults := faults) functions owner index))
    (index : Index (headers := headers) (registry := registry) functions owner) :
    CallableIndexedOwnedPreparedNamedParameterReceipts.PreservesAt index.receipt (faults := faults) budget := by
  intro outcome after trace
  have bodies : ∀ header, header ∈ headers →
      CallableIndexedOwnedPreparedNamedParameterReceipts.SourceBodiesFor
        (headers := headers) (functions := functions) (owner := owner) (registry := registry) (faults := faults) header budget := by
    intro header member initial argumentsPool arguments receipt _agreement size strict
    exact (below ⟨header, member, initial, argumentsPool, arguments, receipt⟩ size strict).1
  have meaning : ∀ context, Validity index.header context → RecursiveNamedHeaderContracts.AtMost budget
      (fun child => CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt (bridge functions owner index)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        context index.header.function.evidence index.header.function.source
        (CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers)
          CallableIndexedOwnedPublicReadyNamedExpressionBounds.compilation index.header context) faults child) := by
    intro context valid child within
    exact CallableIndexedOwnedPreparedNamedExpressionRuntimeBounds.preserves_at_runtime
      (compilation := CallableIndexedOwnedPublicReadyNamedExpressionBounds.compilation index.header)
      (fuel := index.header.readFuel) (solved := index.header.solved) (reasonAt := index.header.reasonAt)
      functions extension faithful observations functionTypes owner
      (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner index.header)
      (CallableIndexedOwnedNestedCanonicalState.administrativeTransport (headers := headers) owner index.header)
      index.header.function.evidence wellFormed valid.2 valid.1.covers index.header.unique owners valid.1.runtime.1
      (fun header member => (publicReceipts header member).original.aligned.layouts)
      (uninitialized index.header index.member) (missing index.header index.member)
      valid.1.ledger valid.1.runtime budget child within bodies
  obtain ⟨value, finalStore, evaluated, finalMap, finalWorld, represented, heaps, maps, worlds,
      frame, metadata, exit, reached, related, post⟩ :=
    CallableIndexedOwnedPublicPreparedBodyBounds.preserves_at_entry
      (header := index.header) (bridge := bridge functions owner index)
      (issued := publicReceipts index.header index.member) (functions := functions)
      (extension := extension) (faithful := faithful) (observations := observations)
      (condition := CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (producer := producer functions owner publicReceipts index)
      (acquire := acquire functions owner publicReceipts index)
      (transport := CallableIndexedOwnedNestedCanonicalState.administrativeTransport (headers := headers) owner index.header)
      (bindings := CallableIndexedOwnedNestedCanonicalState.bindings (headers := headers) owner index.header)
      (wellFormed := wellFormed) (diagnosticsFound := diagnosticsFound) (rebuilt := rebuilt)
      (operandIncluded := operandIncluded index.header index.member)
      (unaryIncluded := unaryIncluded index.header index.member) (owner := owner) (complete := complete)
      (entry := ordinary_entry functions owner index.receipt prefixZero)
      (sourceReceipt := index.receipt.source wellFormed) (children := (inputs index).children)
      (initial := index.receipt.nested prefixZero (publicReceipts index.header index.member).original.aligned.globals)
      (stable := index.receipt.rows) (gate := index.receipt.stable_owner)
      (escapedFault := escaped index.header index.member) (interpretations := (inputs index).interpretations)
      budget budget (Nat.le_refl budget) meaning trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
    frame, metadata, exit, reached.val, related, ⟨post.rows, post.successful⟩⟩

include prefixZero extension faithful observations functionTypes wellFormed complete diagnosticsFound rebuilt
  operandIncluded unaryIncluded uninitialized missing escaped inputs in
/-- Reflection recovers an independent Source grade at the same actual
parameter input, keeping its full reached exit and returned pool. -/
private theorem reflects_step (budget : Nat)
    (below : ∀ index : Index (headers := headers) (registry := registry) functions owner,
      RecursiveNamedBoundedContracts.Below budget (Family (faults := faults) functions owner index))
    (index : Index (headers := headers) (registry := registry) functions owner) :
    CallableIndexedOwnedPreparedNamedParameterReceipts.ReflectsAt index.receipt (faults := faults) budget := by
  intro value finalStore completed
  have bodies : ∀ header, header ∈ headers →
      CallableIndexedOwnedPreparedNamedParameterReceipts.NativeBodiesFor
        (headers := headers) (functions := functions) (owner := owner) (registry := registry) (faults := faults) header budget := by
    intro header member initial argumentsPool arguments receipt prefixSize bodyStore value finalStore
      _prefixRun _prefixWithin _restored size strict
    exact (below ⟨header, member, initial, argumentsPool, arguments, receipt⟩ size strict).2
  have meaning : ∀ context, Validity index.header context → RecursiveNamedBoundedContracts.Below budget
      (fun child => CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt (bridge functions owner index)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        context index.header.function.evidence index.header.function.source
        (CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers)
          CallableIndexedOwnedPublicReadyNamedExpressionBounds.compilation index.header context) faults child) := by
    intro context valid child strict
    exact CallableIndexedOwnedPreparedNamedExpressionRuntimeBounds.reflects_at_runtime
      (compilation := CallableIndexedOwnedPublicReadyNamedExpressionBounds.compilation index.header)
      (fuel := index.header.readFuel) (solved := index.header.solved) (reasonAt := index.header.reasonAt)
      functions extension faithful observations functionTypes owner
      (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner index.header)
      (CallableIndexedOwnedNestedCanonicalState.administrativeTransport (headers := headers) owner index.header)
      index.header.function.evidence wellFormed valid.2 valid.1.covers index.header.unique
      (fun header member => (publicReceipts header member).original.aligned.layouts)
      (uninitialized index.header index.member) (missing index.header index.member)
      valid.1.ledger valid.1.runtime budget child (Nat.le_of_lt strict) bodies
  obtain ⟨sourceSize, outcome, after, trace, finalMap, finalWorld, represented, heaps, maps, worlds,
      frame, metadata, exit, reached, related, post⟩ :=
    CallableIndexedOwnedPublicPreparedBodyBounds.reflects_at_entry
      (header := index.header) (bridge := bridge functions owner index)
      (issued := publicReceipts index.header index.member) (functions := functions)
      (extension := extension) (faithful := faithful) (observations := observations)
      (condition := CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (producer := producer functions owner publicReceipts index)
      (acquire := acquire functions owner publicReceipts index)
      (transport := CallableIndexedOwnedNestedCanonicalState.administrativeTransport (headers := headers) owner index.header)
      (bindings := CallableIndexedOwnedNestedCanonicalState.bindings (headers := headers) owner index.header)
      (wellFormed := wellFormed) (diagnosticsFound := diagnosticsFound) (rebuilt := rebuilt)
      (operandIncluded := operandIncluded index.header index.member)
      (unaryIncluded := unaryIncluded index.header index.member) (owner := owner) (complete := complete)
      (entry := ordinary_entry functions owner index.receipt prefixZero)
      (sourceReceipt := index.receipt.source wellFormed) (children := (inputs index).children)
      (initial := index.receipt.nested prefixZero (publicReceipts index.header index.member).original.aligned.globals)
      (stable := index.receipt.rows) (gate := index.receipt.stable_owner)
      (escapedFault := escaped index.header index.member) (interpretations := (inputs index).interpretations)
      budget budget (Nat.le_refl budget) functionTypes meaning completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, completed.sound, represented, heaps, maps, worlds,
    frame, metadata, exit, reached.val, related, ⟨post.rows, post.successful⟩⟩


include prefixZero extension faithful observations functionTypes wellFormed complete owners diagnosticsFound rebuilt
  operandIncluded unaryIncluded uninitialized missing escaped inputs in
/-- The existing measured closer closes both meanings of every actual public
parameter receipt. No completed body or expression law is an input. -/
theorem closed_at (size : Nat) :
    ∀ index : Index (headers := headers) (registry := registry) functions owner,
      Family (faults := faults) functions owner index size := by
  apply CallableRuntimeBodyMutualMeaning.close_family (Family (faults := faults) functions owner)
  intro budget below index
  constructor
  · exact preserves_step (functions := functions) (owner := owner) (publicReceipts := publicReceipts)
      (prefixZero := prefixZero) (extension := extension) (faithful := faithful) (observations := observations)
      (functionTypes := functionTypes) (wellFormed := wellFormed) (complete := complete) (owners := owners)
      (diagnosticsFound := diagnosticsFound) (rebuilt := rebuilt) (operandIncluded := operandIncluded)
      (unaryIncluded := unaryIncluded) (uninitialized := uninitialized) (missing := missing)
      (escaped := escaped) (inputs := inputs) budget below index
  · exact reflects_step (functions := functions) (owner := owner) (publicReceipts := publicReceipts)
      (prefixZero := prefixZero) (extension := extension) (faithful := faithful) (observations := observations)
      (functionTypes := functionTypes) (wellFormed := wellFormed) (complete := complete)
      (diagnosticsFound := diagnosticsFound) (rebuilt := rebuilt) (operandIncluded := operandIncluded)
      (unaryIncluded := unaryIncluded) (uninitialized := uninitialized) (missing := missing)
      (escaped := escaped) (inputs := inputs) budget below index

include prefixZero extension faithful observations functionTypes wellFormed complete owners diagnosticsFound rebuilt
  operandIncluded unaryIncluded uninitialized missing escaped inputs in
/-- The actual Source continuation consumes only the corresponding closed
strict child; original parameter continuation agreement stays unchanged. -/
theorem source_bodies (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (member : header ∈ headers) (budget : Nat) :
    CallableIndexedOwnedPreparedNamedParameterReceipts.SourceBodiesFor
      (headers := headers) (functions := functions) (owner := owner) (registry := registry) (faults := faults) header budget := by
  intro initial argumentsPool arguments receipt _agreement size _strict
  exact (closed_at (functions := functions) (owner := owner) (publicReceipts := publicReceipts)
      (prefixZero := prefixZero) (extension := extension) (faithful := faithful) (observations := observations)
      (functionTypes := functionTypes) (wellFormed := wellFormed) (complete := complete) (owners := owners)
      (diagnosticsFound := diagnosticsFound) (rebuilt := rebuilt) (operandIncluded := operandIncluded)
      (unaryIncluded := unaryIncluded) (uninitialized := uninitialized) (missing := missing)
      (escaped := escaped) (inputs := inputs) size
    ⟨header, member, initial, argumentsPool, arguments, receipt⟩).1

include prefixZero extension faithful observations functionTypes wellFormed complete owners diagnosticsFound rebuilt
  operandIncluded unaryIncluded uninitialized missing escaped inputs in
/-- The actual measured native prefix and saved caller restoration stay
original. Reflection returns the independent Source grade at this receipt. -/
theorem native_bodies (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (member : header ∈ headers) (budget : Nat) :
    CallableIndexedOwnedPreparedNamedParameterReceipts.NativeBodiesFor
      (headers := headers) (functions := functions) (owner := owner) (registry := registry) (faults := faults) header budget := by
  intro initial argumentsPool arguments receipt prefixSize bodyStore value finalStore
    _prefixRun _prefixWithin _restored size _strict
  exact (closed_at (functions := functions) (owner := owner) (publicReceipts := publicReceipts)
      (prefixZero := prefixZero) (extension := extension) (faithful := faithful) (observations := observations)
      (functionTypes := functionTypes) (wellFormed := wellFormed) (complete := complete) (owners := owners)
      (diagnosticsFound := diagnosticsFound) (rebuilt := rebuilt) (operandIncluded := operandIncluded)
      (unaryIncluded := unaryIncluded) (uninitialized := uninitialized) (missing := missing)
      (escaped := escaped) (inputs := inputs) size
    ⟨header, member, initial, argumentsPool, arguments, receipt⟩).2

section Expressions
universe u
variable {callerCompilation : SourceCoreFunctions.Context}
  {callerProtocol : Protocol.{u, 0} (Records keys)}
  (caller : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => CallableIndexedOwnedExpressionHeads.Globals (headers := headers)
      owner callerCompilation.administrativePrefix index.scope index.canonical) callerProtocol)
  (transport : AdministrativeTransport callerProtocol)
  {source : TypedSource} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}
  (sourceRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context) (unique : NodeOccurrencesUnique source)
  (idsUnique : RequirementIdsUnique context)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include prefixZero extension faithful observations functionTypes wellFormed complete owners diagnosticsFound rebuilt
  operandIncluded unaryIncluded uninitialized missing escaped inputs transport sourceRuntime covers unique idsUnique callerUninitialized callerMissing in
/-- Ordinary and direct named calls close internally at authentic actual
parameter receipts, while the original runtime expression fold keeps the
caller's complete packet and actual post. -/
theorem preserves_at_runtime (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CallableIndexedOwnedPreparedNamedExpressionRuntimeBounds.RuntimeTree (headers := headers)
        (compilation := callerCompilation) (source := source) (context := context)
        (solved := solved) (reasonAt := reasonAt) (fuel := fuel) evidence) faults size :=
  CallableIndexedOwnedPreparedNamedExpressionRuntimeBounds.preserves_at_runtime
    functions extension faithful observations functionTypes owner caller transport evidence
    wellFormed sourceRuntime covers unique owners idsUnique
    (fun header member => (publicReceipts header member).original.aligned.layouts)
    callerUninitialized callerMissing sameLedger runtimeLedger budget size within
    (fun header member => source_bodies (functions := functions) (owner := owner) (publicReceipts := publicReceipts)
      (prefixZero := prefixZero) (extension := extension) (faithful := faithful) (observations := observations)
      (functionTypes := functionTypes) (wellFormed := wellFormed) (complete := complete) (owners := owners)
      (diagnosticsFound := diagnosticsFound) (rebuilt := rebuilt) (operandIncluded := operandIncluded)
      (unaryIncluded := unaryIncluded) (uninitialized := uninitialized) (missing := missing)
      (escaped := escaped) (inputs := inputs) header member budget)

include prefixZero extension faithful observations functionTypes wellFormed complete owners diagnosticsFound rebuilt
  operandIncluded unaryIncluded uninitialized missing escaped inputs transport sourceRuntime covers unique callerUninitialized callerMissing in
/-- Native reflection retains the same caller pool and recovers a separate
Source grade using the closed actual parameter family. -/
theorem reflects_at_runtime (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CallableIndexedOwnedPreparedNamedExpressionRuntimeBounds.RuntimeTree (headers := headers)
        (compilation := callerCompilation) (source := source) (context := context)
        (solved := solved) (reasonAt := reasonAt) (fuel := fuel) evidence) faults size :=
  CallableIndexedOwnedPreparedNamedExpressionRuntimeBounds.reflects_at_runtime
    functions extension faithful observations functionTypes owner caller transport evidence
    wellFormed sourceRuntime covers unique
    (fun header member => (publicReceipts header member).original.aligned.layouts)
    callerUninitialized callerMissing sameLedger runtimeLedger budget size within
    (fun header member => native_bodies (functions := functions) (owner := owner) (publicReceipts := publicReceipts)
      (prefixZero := prefixZero) (extension := extension) (faithful := faithful) (observations := observations)
      (functionTypes := functionTypes) (wellFormed := wellFormed) (complete := complete) (owners := owners)
      (diagnosticsFound := diagnosticsFound) (rebuilt := rebuilt) (operandIncluded := operandIncluded)
      (unaryIncluded := unaryIncluded) (uninitialized := uninitialized) (missing := missing)
      (escaped := escaped) (inputs := inputs) header member budget)

end Expressions

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedNamedFamilyClosure
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDecodedAssignmentFaults
/-! The fault relation is constructed from the literal receiving diagnostic
 table. Its finite view keeps the error category and raw mapping or operand
 type. Source locations and reached heaps remain in the original semantic
 trace and reached witness; the public projected-place error has no location
 field. A decoded error does not manufacture a Source fault or an execution.

 The two reached-place interpretation fields follow from this definition.
 Assignment and unary rows still need a genuine producer preserving their
 issued-table lookups through program aggregation, compatible fixed-prefix
 rebuilding and the actual filtered callable append. This module supplies no
 arbitrary whole FaultRep, registry transport, or decoder-coverage premise.
-/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDecodedAssignmentFaults
open Core Frontend SourceInference GeneralHeap CompatiblePayload
universe u v

/-- The actual public errors erase the runtime location but retain the raw
 missing-default type and assignment operator. Native lookup is separate. -/
inductive ErrorView : Dynamic.SemanticFault → SourceTypedRuntime.RuntimeError → Prop where
  | missing (rawValue : TypeSystem.Ty) :
      ErrorView (.missingMappingDefault rawValue) (.typeMismatch rawValue none)
  | projectedUninitialized (location : Dynamic.Location) :
      ErrorView (.uninitializedLocation location) .invalidPlaceProjection
  | readUninitialized (location : Dynamic.Location) (binder : Resolved.LocalId) :
      ErrorView (.uninitializedLocation location) (.uninitializedLocal binder)
  | operand (operator : Syntax.ValueAssignOp) (rawType : TypeSystem.Ty) :
      ErrorView (.invalidAssignmentOperands operator)
        (.invalidAssignmentOperands operator none (some rawType))
  | unary : ErrorView (.invalidUnaryOperand .bitNot) (.invalidUnaryOperand .bitNot none)

/-- Every related token is decoded by this exact table. No other table or
 caller-supplied semantic verdict enters the concrete relation. -/
def faults (table : SourceCoreFaultSites.Table) : FunctionCalls.FaultRep :=
  fun reason token => ∃ diagnostic,
    table.diagnostic? token = some diagnostic ∧ ErrorView reason diagnostic.error

/-- The literal decoder equation and finite view construct the relation. -/
theorem of_decoded {table : SourceCoreFaultSites.Table} {reason : Dynamic.SemanticFault}
    {token : Word} {diagnostic : SourceCoreFaultSites.Diagnostic}
    (decoded : table.diagnostic? token = some diagnostic)
    (view : ErrorView reason diagnostic.error) : faults table reason token :=
  ⟨diagnostic, decoded, view⟩

/-- The original state, prepared place and actual reached witness are exactly
 the indices requested by the genuine shape-diagnostic API. Both inclusions
 are derived internally from the concrete table-indexed relation. -/
theorem reached_interpretation
    {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {Records : Type v}
    {protocol : ProtectedStateTransition.Protocol.{u, v} Records}
    {environment : Dynamic.Environment} {place : PlaceResolution}
    {prepared : SourceCoreCompatibleDataPlaces.Prepared}
    {initialIndex : ProtectedStateTransition.Index} (initial : protocol.State initialIndex)
    (table : SourceCoreFaultSites.Table) :
    CallableIndexedOwnedPublicPreparedShapeDiagnostics.ReachedTableInterpretation
      checked registry functions protocol environment place prepared initial table (faults table) := by
  constructor
  · intro rawValue token diagnostic decoded error
    refine ⟨diagnostic, decoded, ?_⟩
    rw [error]
    exact .missing rawValue
  · intro reachedIndex reached location related witness diagnostic decoded error
    refine ⟨diagnostic, decoded, ?_⟩
    rw [error]
    exact .projectedUninitialized location

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDecodedAssignmentFaults
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicEmittedReadyNamedExpressionBounds
/-! The actual public compiler traversals supply their own interpreted profile
receipts inside the ordinary named runtime endpoint. Independent Source Syntax,
real child compilation receipts and concrete local diagnostic facts remain
static inputs. The existing closed named family supplies all body semantics. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicEmittedReadyNamedExpressionBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPublicReadyNamedExpressionBounds (PublicReceipt compilation)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {callerCompilation : SourceCoreFunctions.Context}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

variable {faults : FunctionCalls.FaultRep}

/-- Genuine static inputs are tied to the actual public Header and requested
only at real ordinary parameter entries. They contain no interpreted output
predicate, profile provider or expression/body execution law. -/
structure StaticInputs (header : CallableIndexedOwnedFunctionValues.Header compiled
    (Program.ofChecked compiled.sourceProgram)) (issued : PublicReceipt header) where
  tracked : Bool
  children : CallableIndexedOwnedNamedPublicProfileExtraction.SitesFor
    (header := header) (headers := headers) (registry := registry) (expressionSyntax := expressionSyntax)
    issued.prepared compilation functions owner tracked
  localReceipts : ∀ {arguments before initialStore mapping world administrative actualContext actual ξ frameLocation current ghost}
    (actualEntry : RecursiveNamedCatalogInvocationBounds.BodyState
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations 0 functions registry header arguments before initialStore mapping world
      administrative actualContext actual ξ frameLocation current ghost),
    EmittedDiagnosticPlan.Plan.LocalReceipts (factory := (children actualEntry).factory) registry faults

/-- The original canonical caller wraps the same actual ordered pool. -/
private abbrev caller := CallableIndexedOwnedReadyNamedExpressionTreeBounds.caller (headers := headers)
  (compilation := callerCompilation) owner

variable {source : TypedSource} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) (sourceRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context) (unique : NodeOccurrencesUnique source)
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  (idsUnique : RequirementIdsUnique context)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (ordinary : owner.key.capturePrefix = 0)
  (publicReceipts : ∀ header, header ∈ headers → PublicReceipt header)
  (catalog : SignatureCatalogWellFormed compiled.compatible.checked.signatures)
  (calleeUninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (calleeMissing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header, header ∈ headers → faults .controlEscapedFunction header.escaped)
  (complete : RecursiveNamedCatalogNativeContexts.Complete
    (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (staticInputs : ∀ header (member : header ∈ headers),
    StaticInputs (headers := headers) (functions := functions) (owner := owner) (registry := registry) (faults := faults)
      (expressionSyntax := expressionSyntax) header (publicReceipts header member))
  (syntaxTrees : ∀ header, header ∈ headers → GenericImperativeMatch.Syntax header.function.source
    (expressionSyntax header) header.context (.statements true header.function.body) header.function.resultType)

include complete publicReceipts staticInputs in
/-- Each reached Header's authentic producer interprets its own returned plan
and constructs the original static profile witness internally. -/
theorem interpreted_outputs : ∀ header, header ∈ headers →
    CallableIndexedOwnedNamedPublicProfileExtraction.InterpretedReceiptsFor
      (headers := headers) (registry := registry) (faults := faults) (expressionSyntax := expressionSyntax)
      (header := header) compilation functions owner := by
  intro header member
  let issued := publicReceipts header member
  let inputs : StaticInputs (functions := functions) (owner := owner) (headers := headers)
      (registry := registry) (faults := faults) (expressionSyntax := expressionSyntax) header issued :=
    staticInputs header member
  intro arguments before initialStore mapping world administrative actualContext actual ξ frameLocation current ghost actualEntry
  let sites := CallableIndexedOwnedNamedPublicProfileExtraction.policy_inputs
    issued.prepared issued.aligned compilation (inputs.children actualEntry)
  exact CallableIndexedOwnedNamedEmittedProfileExtraction.interpreted_at
    issued.accepted issued.prepared issued.aligned issued.nativeMember compilation functions owner complete
    actualEntry sites (inputs.localReceipts actualEntry)

include extension faithful observations functionTypes wellFormed sourceRuntime covers unique owners idsUnique uninitialized missing ordinary publicReceipts catalog calleeUninitialized calleeMissing escaped complete staticInputs syntaxTrees in
theorem preserves_at_runtime (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots (caller (headers := headers) (callerCompilation := callerCompilation) owner))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CallableIndexedOwnedReadyNamedExpressionTreeBounds.RuntimeTree (headers := headers)
        (compilation := callerCompilation) (source := source) (context := context) (solved := solved)
        (reasonAt := reasonAt) (fuel := fuel) evidence) faults size := by
  exact CallableIndexedOwnedPublicReadyNamedExpressionBounds.preserves_at_runtime
    (callerCompilation := callerCompilation) (solved := solved) (reasonAt := reasonAt) (fuel := fuel)
    functions extension faithful observations functionTypes owner evidence wellFormed sourceRuntime covers unique owners idsUnique
    uninitialized missing ordinary publicReceipts catalog calleeUninitialized calleeMissing escaped
    (interpreted_outputs (functions := functions) (owner := owner) (complete := complete)
      (publicReceipts := publicReceipts) (staticInputs := staticInputs)) syntaxTrees
    sameLedger runtimeLedger budget size within

include extension faithful observations functionTypes wellFormed sourceRuntime covers unique uninitialized missing ordinary publicReceipts catalog calleeUninitialized calleeMissing escaped complete staticInputs syntaxTrees in
theorem reflects_at_runtime (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots (caller (headers := headers) (callerCompilation := callerCompilation) owner))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CallableIndexedOwnedReadyNamedExpressionTreeBounds.RuntimeTree (headers := headers)
        (compilation := callerCompilation) (source := source) (context := context) (solved := solved)
        (reasonAt := reasonAt) (fuel := fuel) evidence) faults size := by
  exact CallableIndexedOwnedPublicReadyNamedExpressionBounds.reflects_at_runtime
    (callerCompilation := callerCompilation) (solved := solved) (reasonAt := reasonAt) (fuel := fuel)
    functions extension faithful observations functionTypes owner evidence wellFormed sourceRuntime covers unique
    uninitialized missing ordinary publicReceipts catalog calleeUninitialized calleeMissing escaped
    (interpreted_outputs (functions := functions) (owner := owner) (complete := complete)
      (publicReceipts := publicReceipts) (staticInputs := staticInputs)) syntaxTrees
    sameLedger runtimeLedger budget size within

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicEmittedReadyNamedExpressionBounds
end
