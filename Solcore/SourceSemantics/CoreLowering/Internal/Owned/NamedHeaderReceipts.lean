import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.FunctionValuesAndState
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ReadyExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ReadyContinuations
import Solcore.Frontend.SourceSpecializationAcceptance
import Solcore.SourceSemantics.CoreLowering.ReachedNamedConditionalBodyFaultPaths
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.ImperativeControl
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NamedCatalog

/-!
# Owned callables: named header receipts

Receipts of named headers and ordinary callers, arity and range receipts, and faults of conditional named bodies.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedHeaderReceipts
/-! The actual prepared Header factories expose the complete compiler layout
and the original bootstrap global slot. Their full HeaderAt receipts retain
source metadata, dictionaries and substitution order. A later caller's global
slots are supplied separately by its actual input catalog observation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedHeaderReceipts
open Core Frontend SourceInference GeneralHeap
open RecursiveNamedCatalog RecursiveNamedPublicSpecializationMeaning

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}

/-- The original reserved environment contains the signature and physical
location of this actual cached Header slot. -/
theorem bootstrap_slot (header : CallableIndexedOwnedFunctionValues.Header compiled program) :
    (RecursiveNamedCatalogPreparedInitialization.environment compiled)[header.slot]? =
      some (.cellRef (OptionalCell.cellType header.named.signature.functionType)
        (RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot)) :=
  RecursiveNamedCatalogInitialization.global_reference compiled.indexed.base.globals
    compiled.indexed.ancestry.layout.frame
    (CallableIndexedPreparedInventories.cached_global_at compiled header.selected)

section Factory
variable {row : SourceSpecialization.SpecializedFunction}
  (prepared : Prepared compiled row) {instantiation : DeclarationInstantiation}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}

/-- This packet keeps the entire actual compiler/source receipt. The bootstrap
slot is an observation of the original reserved environment. -/
structure Receipt (prepared : Prepared compiled row) (instantiation : DeclarationInstantiation)
    (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)) : Prop where
  aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header
  bootstrap : (RecursiveNamedCatalogPreparedInitialization.environment compiled)[header.slot]? =
    some (.cellRef (OptionalCell.cellType header.named.signature.functionType)
      (RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot))

theorem Receipt.of_prepared
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header) :
    Receipt prepared instantiation header :=
  ⟨aligned, bootstrap_slot header⟩

/-- Equality of the full prepared layout is taken from the actual Header
construction, preserving more than its definitions projection. -/
theorem Receipt.same_layouts (receipt : Receipt prepared instantiation header) :
    header.layouts = compiled.indexed.layouts :=
  receipt.aligned.layouts

/-- Canonical metadata uses the original factory with its complete dictionary. -/
theorem canonical_with_evidence
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution)
    (ordinaryReturn : row.function.returnComptime = false)
    (ordinaryParameters : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false)
    (target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation row) = .ok prepared.named.signature.key) :
    ∃ header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram),
      Receipt prepared (CallableNamedMetadata.instantiation row) header := by
  obtain ⟨header, aligned⟩ := RecursiveNamedPreparedHeaders.Prepared.canonical_header_with_evidence
    prepared wellFormed range ordinaryReturn ordinaryParameters target
  exact ⟨header, Receipt.of_prepared prepared aligned⟩

/-- Retained metadata keeps its full reversed substitution order through the
same actual compiler Header factory. -/
theorem retained_with_evidence
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution)
    (ordinaryReturn : row.function.returnComptime = false)
    (ordinaryParameters : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false)
    (target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan
      (CallableNamedCanonicalOrder.retainedInstantiation row) = .ok prepared.named.signature.key) :
    ∃ header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram),
      Receipt prepared (CallableNamedCanonicalOrder.retainedInstantiation row) header := by
  obtain ⟨header, aligned⟩ := RecursiveNamedPreparedHeaders.Prepared.retained_header_with_evidence
    prepared wellFormed range ordinaryReturn ordinaryParameters target
  exact ⟨header, Receipt.of_prepared prepared aligned⟩
end Factory

/-- The public compiler supplies the original worklist row, full preparation,
Header layout and original bootstrap slot in one receipt. -/
theorem of_public_compile_with_evidence {sourceProgram : CheckedProgram} {seeds : List SourceCompiler.Seed}
    {options : SourceCompiler.Options} {publicCompiled : SourceCompiler.Compiled}
    {recipe : SourceCoreIndexedSession.Recipe} {row : SourceSpecialization.SpecializedFunction}
    (accepted : SourceCompiler.compileChecked sourceProgram seeds options = .ok publicCompiled)
    (issued : RecursiveNamedPreparedStageContracts.PublicRecipe publicCompiled recipe)
    (member : row ∈ recipe.compiled.validationPlan.specializations)
    (wellFormed : ProgramWellFormed (Program.ofChecked recipe.compiled.sourceProgram))
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures recipe.compiled.sourceProgram.signatures) row.parameterSubstitution)
    (ordinaryReturn : row.function.returnComptime = false)
    (ordinaryParameters : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false)
    (target : SourceCompilationPlan.exactInstantiationKey recipe.compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation row) = .ok row.key) :
    ∃ (prepared : Prepared recipe.compiled row)
      (header : CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)),
      Receipt prepared (CallableNamedMetadata.instantiation row) header := by
  obtain ⟨prepared, header, aligned⟩ := RecursiveNamedPreparedHeaders.of_public_compile_with_evidence
    accepted issued member wellFormed range ordinaryReturn ordinaryParameters target
  exact ⟨prepared, header, Receipt.of_prepared prepared aligned⟩

section Caller
variable {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}

/-- A caller's original canonical slots are independent from its reached pool. -/
def Globals (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (callerPrefix : Nat) (scope : SourceCoreLocalCell.Scope) (canonical : Environment) : Prop :=
  ∀ header, header ∈ headers → canonical[scope.length + callerPrefix + header.slot]? =
    some (.cellRef (OptionalCell.cellType header.named.signature.functionType) (owner.key.locations header))

/-- The actual input catalog provides exactly the global-slot family required
by owned expression heads, including its caller prefix and canonical order. -/
theorem globals_of_entry (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    {capturePrefix callerPrefix : Nat} {scope : SourceCoreLocalCell.Scope}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store} {canonical : Environment}
    (entry : Entry (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations capturePrefix callerPrefix scope mapping world heap store canonical) :
    Globals (headers := headers) owner callerPrefix scope canonical :=
  entry.globals

/-- The full captured canonical environment supplies its own original globals.
This observation retains the actual capture prefix and every captured value. -/
theorem globals_of_capture (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    {header : CallableIndexedOwnedFunctionValues.Header compiled program}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store} {frameLocation : Location}
    (capture : Capture (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix frameLocation header mapping world heap store) :
    Globals (headers := headers) owner owner.key.capturePrefix [] capture.canonical := by
  intro target member
  simpa only [List.length_nil, Nat.zero_add] using capture.coherent target member
end Caller

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedHeaderReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedClosedReadyNamedExpressionRuntimeBounds
/-! The internally closed named family supplies every strict callee body to
the original expression Tree. Runtime leaves retain their authentic ledger;
only original Source and compiler receipts are assumptions of these endpoints. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedClosedReadyNamedExpressionRuntimeBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedOwnedNamedReadyFamilyReceipts (body_protocol bridge origin Index)
open CallableIndexedOwnedExpressionHeads (Globals argumentProtocol)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (compilation : CallableIndexedOwnedFunctionValues.Header compiled program → SourceCoreFunctions.Context)
  {callerCompilation : SourceCoreFunctions.Context}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled program → ExpressionId → Prop}

/-- The original canonical caller wraps the same actual ordered pool. -/
private abbrev caller := CallableIndexedOwnedReadyNamedExpressionTreeBounds.caller (headers := headers)
  (compilation := callerCompilation) owner

variable {source : TypedSource} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}
  {faults : FunctionCalls.FaultRep}
  (wellFormed : ProgramWellFormed program) (sourceRuntime : Dynamic.SourceRuntimeValid program context source)
  (covers : evidence.Covers context) (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (idsUnique : RequirementIdsUnique context)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
  (prefixMatches : ∀ header, header ∈ headers → (compilation header).administrativePrefix = owner.key.capturePrefix + 1)
  (calleeUninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (calleeMissing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header, header ∈ headers → faults .controlEscapedFunction header.escaped)
  (profiles : ∀ header, header ∈ headers → CallableIndexedOwnedAdmittedNamedExpressionHeads.ProfilesFor
    (headers := headers) (owner := owner) (functions := functions) (registry := registry) (faults := faults)
    (certificates := CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation) (expressionSyntax := expressionSyntax)
    (diagnosticPolicy := .reachable) (runtime := true) header)
  (syntaxTrees : ∀ header, header ∈ headers → GenericImperativeMatch.Syntax header.function.source
    (expressionSyntax header) header.context (.statements true header.function.body) header.function.resultType)

include extension faithful observations functionTypes wellFormed sourceRuntime covers unique owners idsUnique
  uninitialized missing sameLayouts prefixMatches calleeUninitialized calleeMissing escaped profiles syntaxTrees in
theorem preserves_at_runtime (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots (caller (headers := headers) (callerCompilation := callerCompilation) owner))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CallableIndexedOwnedReadyNamedExpressionTreeBounds.RuntimeTree (headers := headers)
        (compilation := callerCompilation) (source := source) (context := context) (solved := solved)
        (reasonAt := reasonAt) (fuel := fuel) evidence) faults size := by
  exact CallableIndexedOwnedReadyNamedExpressionRuntimeBounds.preserves_at_runtime
    (certificates := CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation)
    (compilation := callerCompilation)
    functions extension faithful observations functionTypes owner evidence wellFormed sourceRuntime covers unique owners idsUnique
    uninitialized missing sameLayouts escaped profiles syntaxTrees sameLedger runtimeLedger budget size within
    (fun index child _strict => CallableIndexedOwnedReadyNamedFamilyClosure.preserves_at
      compilation functions owner extension faithful observations functionTypes
      wellFormed owners sameLayouts prefixMatches calleeUninitialized calleeMissing escaped profiles syntaxTrees child index)

include extension faithful observations functionTypes wellFormed sourceRuntime covers unique
  uninitialized missing sameLayouts prefixMatches calleeUninitialized calleeMissing escaped profiles syntaxTrees in
theorem reflects_at_runtime (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots (caller (headers := headers) (callerCompilation := callerCompilation) owner))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CallableIndexedOwnedReadyNamedExpressionTreeBounds.RuntimeTree (headers := headers)
        (compilation := callerCompilation) (source := source) (context := context) (solved := solved)
        (reasonAt := reasonAt) (fuel := fuel) evidence) faults size := by
  exact CallableIndexedOwnedReadyNamedExpressionRuntimeBounds.reflects_at_runtime
    (certificates := CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation)
    (compilation := callerCompilation)
    functions extension faithful observations functionTypes owner evidence wellFormed sourceRuntime covers unique
    uninitialized missing sameLayouts escaped profiles syntaxTrees sameLedger runtimeLedger budget size within
    (fun index child _strict => CallableIndexedOwnedReadyNamedFamilyClosure.reflects_at
      compilation functions owner extension faithful observations functionTypes
      wellFormed sameLayouts prefixMatches calleeUninitialized calleeMissing escaped profiles syntaxTrees child index)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedClosedReadyNamedExpressionRuntimeBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryCallerReceipts
/-! Ordinary closure formation retains the actual named preparation and its
complete dictionary. Lexical changes retain runtime context fields; native
capture typing alone does not establish this receipt. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryCallerReceipts
open Core Frontend SourceInference

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- The original actual named caller, reached lexical context and full evidence
are retained together before the capture environment is chosen. -/
structure CallerAt
    (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) where
  prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled caller.named.specialized
  aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared caller.instantiation caller
  fields : Dynamic.RuntimeContextFields caller.context context
  dictionary : evidence = prepared.view.evidence

variable {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {context next : SourceSemantics.Context} {evidence other : Dynamic.EvidenceEnvironment}

/-- Reindexing the actual preparation uses its retained Header identity. -/
def CallerAt.of_header
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation caller)
    (fields : Dynamic.RuntimeContextFields caller.context context)
    (dictionary : evidence = prepared.view.evidence) : CallerAt caller context evidence := by
  have same : row = caller.named.specialized :=
    prepared.same.symm.trans (congrArg (fun named => named.specialized) aligned.named.symm)
  subst row
  exact ⟨prepared, aligned.metadata.symm ▸ aligned, fields, dictionary⟩

/-- Parameter and lexical extensions preserve the original caller identity. -/
def CallerAt.extend (receipt : CallerAt caller context evidence)
    (fields : Dynamic.RuntimeContextFields context next) : CallerAt caller next evidence :=
  { receipt with fields := receipt.fields.trans fields }

/-- A selected stage supplies the same complete evidence environment. -/
def CallerAt.with_evidence (receipt : CallerAt caller context evidence)
    (same : other = evidence) : CallerAt caller context other :=
  { receipt with dictionary := same.trans receipt.dictionary }

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryCallerReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedPhysicalArityReceipts
/-! Actual named metadata identifies the full Source parameter list of the
selected Header. The physical count comes from the authenticated codebook and
its original guard. This does not infer arity from a packed native type or
establish the independent first-stage guard decision. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedPhysicalArityReceipts
open Core Frontend SourceInference SourceCoreStageContracts
open CallableIndexedOwnedFunctionValues

section Named
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {header : Header compiled program} {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment}
  {source : Dynamic.GlobalFunction} {contract : CallContractCertificates.SourceContract}

/-- The real matcher and selected named factory recover the same ordered
binders, including their Source flags and schemes. -/
theorem bound_parameters (sourceAt : NamedSourceAt header rawD source)
    (bound : CallableLedger.Binds compiled.indexed.base.plan (.global source) contract) :
    contract.parameters = header.function.parameters := by
  have target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan
      source.instantiation = .ok header.named.signature.key := by
    rw [sourceAt.retained]
    change SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan
      (CallableNamedReversal.instantiation (CallableNamedMetadata.instantiation header.named.specialized)) = _
    rw [CallableNamedReversal.target_reverse]
    exact sourceAt.row.target
  cases bound with
  | named selected prepared =>
    have same := Except.ok.inj (selected.symm.trans target)
    cases same
    obtain ⟨receipt⟩ := CallContractCertificates.named_of_accepted prepared
    have sourceEq := sourceAt.sourceOrigin.source receipt.prepared
    simp only [EmptySourceSubstitution.source] at sourceEq
    exact receipt.parameters.trans ((congrArg TypedSource.inputs sourceEq).symm.trans
      (header.inputs.trans header.parameters.symm))
end Named

section Selected
variable {sidecar : Sidecar} {site : SourceCoreCallableContracts.Callsite}
  {callee call : ExpressionId} {arguments : List ExpressionId}
  {metadata : IndirectCallResolution} {node : ExpressionNode}
  {source : Dynamic.Value} {carrier : Value}

/-- The original generated guard identifies the selected entry's retained
contract. Builtin rows cannot have this user dispatch attachment. -/
theorem dispatch_parameter_count
    (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) site call arguments source carrier)
    (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected
      sidecar site callee arguments metadata node dispatch.row) :
    dispatch.row.entry.parameterCount = dispatch.guard.contract.parameters.length := by
  cases retained : dispatch.row.entry.contract with
  | none =>
    have noGuard := selected.generated.builtin retained
    have impossible := dispatch.attached.symm.trans noGuard
    cases impossible
  | some contract =>
    obtain ⟨guard, prepared, attached, _⟩ := selected.generated.user contract retained
    have same := Option.some.inj (attached.symm.trans dispatch.attached)
    cases same
    obtain ⟨receipt⟩ := CallContractCertificates.guard_of_accepted prepared
    rw [receipt.contract_eq]
    exact selected.parameter_count retained
end Selected

section Actual
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {header : Header compiled program} {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment}
  {source : Dynamic.GlobalFunction} {sidecar : Sidecar}
  {site : SourceCoreCallableContracts.Callsite} {callee : ExpressionId}
  {arguments : List ExpressionId} {metadata : IndirectCallResolution}
  {node : ExpressionNode} {carrier : Value}

/-- The same public caller sidecar, selected row and actual named value supply
the physical Header count. No count equality is a premise. -/
theorem named_parameter_count (sourceAt : NamedSourceAt header rawD source)
    (caller : prepareSidecar compiled.indexed.base.plan site.caller = .ok sidecar)
    (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar)
      site site.call arguments (.global source) carrier)
    (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected
      sidecar site callee arguments metadata node dispatch.row) :
    dispatch.row.entry.parameterCount = header.function.parameters.length := by
  have samePlan := (CallContractCertificates.sidecar_of_accepted caller).1
  have bound : CallableLedger.Binds compiled.indexed.base.plan (.global source)
      ⟨dispatch.guard.contract.parameters, dispatch.guard.contract.stagedResult⟩ := by
    simpa only [CallableLedger.frame, samePlan] using dispatch.bound
  exact (dispatch_parameter_count dispatch selected).trans
    (congrArg List.length (bound_parameters sourceAt bound))

/-- Genuine Source arity closes the second gate. The first stage gate remains
the original independent decision. -/
theorem before_application (sourceAt : NamedSourceAt header rawD source)
    (caller : prepareSidecar compiled.indexed.base.plan site.caller = .ok sidecar)
    (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar)
      site site.call arguments (.global source) carrier)
    (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected
      sidecar site callee arguments metadata node dispatch.row)
    (arity : header.function.parameters.length = arguments.length) (unknown : Word) :
    CallableContract.decision site.gates .beforeApplication unknown dispatch.row.entry.id = none :=
  selected.before_application ((named_parameter_count sourceAt caller dispatch selected).trans arity) unknown
end Actual
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedPhysicalArityReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReachedNamedConcreteRangeReceipts
/-!
Genuine reached declaration metadata supplies nominal catalog membership and
arity. Actual specialization acceptance supplies concrete replacements. These
two receipts together form the complete canonical raw range at the catalog,
even when the original use-site admits flexible variables or rigid parameters.

This concerns the matched reached callee. An enclosing selected sidecar still
needs its own original occurrence or seed provenance for replacement formation.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReachedNamedConcreteRangeReceipts
open Frontend SourceInference TypeSystem

private theorem empty_orElse {α : Type} (left right : Option α)
    (empty : left.orElse (fun _ => right) = none) :
    left = none ∧ right = none := by
  cases left with
  | none => exact ⟨rfl, empty⟩
  | some value => cases empty

private theorem applyMany_concrete (head : Ty) (arguments : List Ty)
    (concrete : SourceSpecialization.firstNonConcrete (Ty.applyMany head arguments) = none) :
    SourceSpecialization.firstNonConcrete head = none ∧
      ∀ argument ∈ arguments, SourceSpecialization.firstNonConcrete argument = none := by
  induction arguments generalizing head with
  | nil => exact ⟨concrete, by simp⟩
  | cons argument rest ih =>
      change SourceSpecialization.firstNonConcrete
        (Ty.applyMany (.application head argument) rest) = none at concrete
      have tail := ih (.application head argument) concrete
      have parts := empty_orElse (SourceSpecialization.firstNonConcrete head)
        (SourceSpecialization.firstNonConcrete argument) tail.1
      refine ⟨parts.1, ?_⟩
      intro type member
      rcases List.mem_cons.mp member with same | member
      · subst type; exact parts.2
      · exact tail.2 type member

private theorem scoped_concrete_at_catalog
    {context : Context} {variables : List TypeVarId} {type : Ty}
    (typing : TypeWellScoped context variables type) :
    SourceSpecialization.firstNonConcrete type = none →
      TypeWellScoped (Context.ofSignatures context.signatures) [] type := by
  refine TypeWellScoped.rec
    (motive_1 := fun type _ => SourceSpecialization.firstNonConcrete type = none →
      TypeWellScoped (Context.ofSignatures context.signatures) [] type)
    (motive_2 := fun types _ =>
      (∀ type ∈ types, SourceSpecialization.firstNonConcrete type = none) →
        TypesWellScoped (Context.ofSignatures context.signatures) [] types)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typing
  · intro metavariable _ concrete
    cases concrete
  · intro parameter _ _ concrete
    cases concrete
  · intro builtin _concrete
    exact .builtin builtin
  · intro dataType arguments cataloged arity _ argumentsIH concrete
    exact .nominal dataType arguments cataloged arity
      (argumentsIH (applyMany_concrete (.constructor (.declaration dataType.id))
        arguments concrete).2)
  · intro contract arguments cataloged arity _ argumentsIH concrete
    exact .contractNominal contract arguments cataloged arity
      (argumentsIH (applyMany_concrete (.constructor (.declaration contract.id))
        arguments concrete).2)
  · intro parameter result _ _ parameterIH resultIH concrete
    have parts := empty_orElse (SourceSpecialization.firstNonConcrete parameter)
      (SourceSpecialization.firstNonConcrete result) concrete
    exact .function (parameterIH parts.1) (resultIH parts.2)
  · intro left right _ _ leftIH rightIH concrete
    have parts := empty_orElse (SourceSpecialization.firstNonConcrete left)
      (SourceSpecialization.firstNonConcrete right) concrete
    exact .product (leftIH parts.1) (rightIH parts.2)
  · intro key value _ _ keyIH valueIH concrete
    have parts := empty_orElse (SourceSpecialization.firstNonConcrete key)
      (SourceSpecialization.firstNonConcrete value) concrete
    exact .mapping (keyIH parts.1) (valueIH parts.2)
  · intro inner _ innerIH concrete
    exact .proxy (innerIH concrete)
  · intro inner _ innerIH concrete
    exact .comptime (innerIH concrete)
  · intro _concrete
    exact .nil
  · intro head tail _ _ headIH tailIH concrete
    exact .cons (headIH (concrete head (List.mem_cons_self)))
      (tailIH (fun type member => concrete type (List.mem_cons_of_mem head member)))

/-- Concrete metadata retains all genuine nominal membership and arity while
discarding flexible and rigid binders which the actual concrete check excludes. -/
theorem admissible_concrete_at_catalog {context : Context} {type : Ty}
    (admissible : TypeAdmissible context type)
    (concrete : SourceSpecialization.firstNonConcrete type = none) :
    TypeWellFormed (Context.ofSignatures context.signatures) type :=
  ⟨TypeParameterBindersWellFormed.ofSignatures context.signatures,
    scoped_concrete_at_catalog admissible.typeWellScoped concrete⟩

private theorem exact_binding_entry
    {substitution : TypeSystem.ParameterSubstitution}
    {parameter : TypeParameterId} {type : Ty}
    (found : SourceCompilationPlan.exactParameterBinding? substitution parameter = some type) :
    (parameter, type) ∈ substitution ∧ substitution.lookup? parameter = some type := by
  induction substitution with
  | nil => simp [SourceCompilationPlan.exactParameterBinding?] at found
  | cons entry rest ih =>
      rcases entry with ⟨candidate, replacement⟩
      by_cases same : candidate = parameter
      · subst candidate
        cases filtered : rest.filter (fun item => item.1 == parameter) with
        | nil =>
            have typeEq : replacement = type := by
              simpa [SourceCompilationPlan.exactParameterBinding?, filtered] using found
            subst type
            exact ⟨List.mem_cons_self, by simp [TypeSystem.ParameterSubstitution.lookup?]⟩
        | cons head tail =>
            simp [SourceCompilationPlan.exactParameterBinding?, filtered] at found
      · have tailFound : SourceCompilationPlan.exactParameterBinding? rest parameter = some type := by
          simpa [SourceCompilationPlan.exactParameterBinding?, same] using found
        obtain ⟨member, lookup⟩ := ih tailFound
        exact ⟨List.mem_cons_of_mem _ member, by
          simpa [TypeSystem.ParameterSubstitution.lookup?, same] using lookup⟩

/-- Actual matching transfers admissible source replacements. The genuine
specializer then closes precisely those canonical rows, including unused ones. -/
theorem range_of_admissible_match
    {context : Context} {signature : ProgramFunctionSignature} {generic : CheckedFunction}
    {supplied : TypeSystem.ParameterSubstitution}
    {specialized : SourceSpecialization.SpecializedFunction}
    {instantiation : DeclarationInstantiation}
    (matched : CallableNamedMetadata.Matches specialized instantiation)
    (admissible : SourceSemantics.DeclarationInstantiation.Admissible context instantiation)
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized) :
    SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures context.signatures) specialized.parameterSubstitution := by
  have equivalent := matched.substitution
  simp only [SourceCompilationPlan.parameterSubstitutionsEquivalent, Bool.and_eq_true,
    List.all_eq_true, beq_iff_eq] at equivalent
  cases admissible with
  | intro sourceSignature cataloged declaration exact range typeEq predicatesEq parameterFlags returnFlag =>
      intro parameter type member
      have rightFound := equivalent.1.2 (parameter, type) member
      have rightMember := (exact_binding_entry rightFound).1
      have leftFound := equivalent.2 (parameter, type) rightMember
      have lookup := (exact_binding_entry leftFound).2
      exact admissible_concrete_at_catalog (range parameter type rightMember)
        (SourceSpecializationAcceptance.specializeFunction_parameterReplacement_concrete
          accepted parameter type lookup)

/-- A real compiler selection and exact plan record supply the matcher for a
genuinely typed declaration occurrence. No use-site binder emptiness is needed. -/
theorem catalog_range_of_selected
    {context : Context} {policy : SourceCoreFunctions.Policy}
    {compilation : SourceCoreFunctions.Context} {source : TypedSource}
    {node : ExpressionNode} {instantiation : DeclarationInstantiation}
    {isReference : Bool} {index : Nat} {calleeSignature : SourceCoreCalls.Signature}
    {specialized : SourceSpecialization.SpecializedFunction}
    {signature : ProgramFunctionSignature} {generic : CheckedFunction}
    {supplied : TypeSystem.ParameterSubstitution}
    (admissible : SourceSemantics.DeclarationInstantiation.Admissible context instantiation)
    (selected : SourceCoreFunctions.selectedSignature policy compilation source node
      instantiation isReference = .ok (index, calleeSignature))
    (record : SourceCompilationPlan.exactSpecialization compilation.plan calleeSignature.key = .ok specialized)
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized) :
    SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures context.signatures) specialized.parameterSubstitution :=
  range_of_admissible_match
    (CallableNamedMetadata.matches_of_exact (NamedCalls.selected_signature_target selected).1 record)
    admissible accepted

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReachedNamedConcreteRangeReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedConditionalNamedBodyFaultBounds
/-! The genuine condition and selected explicit return each run the admitted
builtin producer once. Their actual middle State retains admission and rows. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedConditionalNamedBodyFaultBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission CallableIndexedOwnedIndirectExpressionHeads
open CallableIndexedOwnedAdmittedBodyEntries (SourceReceipt)
open CallableIndexedOwnedInvocationBounds NamedInvocationFaultPostContracts
open ReachedNamedConditionalBodyFaultPaths
open CompatibleExpressionPrimitives

private def poolBridge {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)} :
    CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) (protocol headers keys) :=
  CallableIndexedOwnedIndirectCallerProtocol.of_legacy CallableIndexedOwnedCallerProtocol.base

private def returnedControl : Dynamic.ExpressionOutcome → Dynamic.ControlOutcome
  | .value value => .returned value
  | .fault reason => .fault reason

section Finite
variable {checked : SourceCoreCompatibleCatalog.Checked}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} {program : Program}
  {function : Dynamic.Closure} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {statement : StatementId} {node : StatementNode} {condition : ExpressionId} {conditionNode : ExpressionNode}
  {conditionFuel : Nat} {branch : Bool → StatementId} {branchNode : Bool → StatementNode}
  {expression : Bool → ExpressionId} {expressionNode : Bool → ExpressionNode} {fuel : Bool → Nat}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {conditionCode : Expr} {code : Bool → Expr}
  {type : Ty} {body : Expr} {fellThrough escaped : Word}
  (conditional : ConditionalAt (.initial checked) function context scope statement node condition conditionNode conditionFuel
    branch branchNode expression expressionNode fuel solved reasonAt conditionCode code type body fellThrough escaped)

include conditional in
private theorem emitted_rename (ξ : Renaming) :
    body.rename ξ = CompatibleStatements.finish type
      (LocalLoop.sequence type
        (LocalLoop.conditional type (conditionCode.rename ξ)
          (LocalLoop.returnValue type ((code true).rename ξ)) (LocalLoop.returnValue type ((code false).rename ξ)))
        (LocalLoop.fallthrough type)) fellThrough escaped := by
  rw [conditional.emitted, ImperativeFunctionFinish.rename, LoopRenaming.sequence,
    LoopRenaming.conditional, LoopRenaming.returnValue, LoopRenaming.returnValue, LoopRenaming.fallthrough]

include conditional in
private theorem finished_condition {actual : Environment} {initialStore bodyStore : Store} {ξ : Renaming} {token : Word}
    (first : Evaluates actual initialStore (conditionCode.rename ξ) (.inLeft .bool (.word token)) bodyStore) :
    Evaluates actual initialStore (body.rename ξ) (.inLeft type (.word token)) bodyStore := by
  rw [emitted_rename conditional]
  exact LocalControl.finish_failure _ (LocalLoop.toControl_failure _ escaped
    (LocalLoop.sequence_failure _ (LocalControl.choose_failure _ first)))

include conditional in
private theorem selected_if {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {size : Nat} {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique function.source)
    (trace : RecursiveNamedLoopContracts.ExecutesAt size true program context function.evidence function.source
      environment before function.body finalContext outcome after) :
    finalContext = context ∧ ∃ statementSize,
      RecursiveNamedStatementSourceBounds.IfTrace program context function.evidence function.source environment before
        condition [branch true] (some [branch false]) statementSize outcome after := by
  rw [conditional.statements] at trace
  have contains := lookupStatement?_sound conditional.found
  have shape : ∀ other, ContainsStatement function.source statement other →
      other.form = .ifThen condition [branch true] (some [branch false]) := by
    intro other present
    have same : other = node := Option.some.inj ((lookupStatement?_complete unique present).symm.trans conditional.found)
    exact same ▸ conditional.form
  cases trace with
  | control executed =>
    cases executed with
    | tailExpression actual same _ =>
      have actualForm := shape _ actual
      simp_all
    | singleton _ _ executed =>
      obtain ⟨same, selected⟩ := RecursiveNamedStatementSourceBounds.if_inv unique contains conditional.form (.control executed)
      exact ⟨same, _, selected⟩
  | fault failed =>
    cases failed with
    | tailExpression actual same _ =>
      have actualForm := shape _ actual
      simp_all
    | singleton failed =>
      obtain ⟨same, selected⟩ := RecursiveNamedStatementSourceBounds.if_inv unique contains conditional.form (.fault failed)
      exact ⟨same, _, selected⟩

include conditional in
private theorem finish_branch {environment : Dynamic.Environment} {before middle after : Dynamic.Heap}
    {initialStore middleStore bodyStore : Store} {actual : Environment} {ξ : Renaming} {boolean : Bool}
    {value : Value} {outcome : Dynamic.ExpressionOutcome}
    {initialMap middleMap finalMap : LocationMap} {initialWorld middleWorld finalWorld : StoreTyping}
    (sourceFirst : Dynamic.ExpressionEvaluates program context function.evidence function.source environment before condition (.bool boolean) middle)
    (first : Evaluates actual initialStore (conditionCode.rename ξ) (.inRight .word (.bool boolean)) middleStore)
    (middleHeaps : CompatibleAmbientHeap.HeapRepresents checked registry functions middleMap middleWorld middle middleStore)
    (firstMaps : LocationMap.Extends initialMap middleMap) (firstWorlds : WorldExtends initialWorld middleWorld)
    (firstFrame : AdministrativePreserved initialMap initialStore middleMap middleStore) (firstMetadata : Dynamic.HeapMetadataExtend before middle)
    (maps : LocationMap.Extends middleMap finalMap) (worlds : WorldExtends middleWorld finalWorld)
    (frame : AdministrativePreserved middleMap middleStore finalMap bodyStore) (metadata : Dynamic.HeapMetadataExtend middle after)
    (sourceLast : Dynamic.ExpressionEvaluatesOutcome program context function.evidence function.source environment middle (expression boolean) outcome after)
    (second : Evaluates (.bool boolean :: actual) middleStore ((code boolean).rename (Renaming.comp (Renaming.insertion 0) ξ)) value bodyStore)
    (represented : FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel checked registry functions)
      finalMap finalWorld (expressionNode boolean).type type faults outcome value)
    (retained : ExpressionFailurePostContracts.OutcomePost (ReachedBuiltinExpressionFaultPaths.model_expressionPost checked functions registry)
      program context function.evidence function.source environment middle (expression boolean) type outcome after value finalMap finalWorld bodyStore) :
    ∃ result, Evaluates actual initialStore (body.rename ξ) result bodyStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel checked registry functions)
        finalMap finalWorld function.resultType type faults outcome result ∧
      OutcomePost (model_bodyPost checked functions registry) program function context environment before
        actual initialStore (body.rename ξ) type outcome after result finalMap finalWorld bodyStore := by
  have rawUnit : ∀ next, returnedControl outcome = Dynamic.ControlOutcome.fallthrough next → function.resultType = .unit := by
    cases outcome <;> intro next same <;> cases same
  have transfers : ImperativeFunctionFinish.TransferFaults faults escaped (returnedControl outcome) := by
    cases outcome <;> constructor <;> intro next same <;> cases same
  obtain ⟨flowValue, returnEvaluation, flowRelated⟩ : ∃ flowValue,
      Evaluates (.bool boolean :: actual) middleStore
        (LocalLoop.returnValue type ((code boolean).rename (Renaming.comp (Renaming.insertion 0) ξ))) flowValue bodyStore ∧
      TypedLexicalWhile.FlowRep (values := .initial checked) (ambient := ambient) (registry := registry)
        functions finalMap finalWorld faults function.resultType type (returnedControl outcome) flowValue := by
    cases represented with
    | value related => exact ⟨_, LocalLoop.returnValue_success _ second, .returned (conditional.resultType boolean ▸ related)⟩
    | fault matched => exact ⟨_, LocalLoop.returnValue_failure _ second, .fault matched⟩
  have branchEvaluation : Evaluates (.bool boolean :: actual) middleStore
      ((LocalLoop.returnValue type ((code boolean).rename ξ)).weakenAt 0) flowValue bodyStore := by
    rw [← LoopRenaming.returnValue, ← GenericExpressionMeaning.rename_prefix, LoopRenaming.returnValue]
    exact returnEvaluation
  have choiceEvaluation : Evaluates actual initialStore
      (LocalLoop.conditional type (conditionCode.rename ξ)
        (LocalLoop.returnValue type ((code true).rename ξ)) (LocalLoop.returnValue type ((code false).rename ξ))) flowValue bodyStore := by
    cases boolean with
    | false => exact LocalControl.choose_false _ first branchEvaluation
    | true => exact LocalControl.choose_true _ first branchEvaluation
  have flowEvaluation : Evaluates actual initialStore
      (LocalLoop.sequence type
        (LocalLoop.conditional type (conditionCode.rename ξ)
          (LocalLoop.returnValue type ((code true).rename ξ)) (LocalLoop.returnValue type ((code false).rename ξ)))
        (LocalLoop.fallthrough type)) flowValue bodyStore := by
    cases outcome with
    | value v => cases flowRelated with | returned _ => exact LocalLoop.sequence_returned _ choiceEvaluation
    | fault r => cases flowRelated with | fault _ => exact LocalLoop.sequence_failure _ choiceEvaluation
  obtain ⟨result, completed, finished⟩ := ImperativeFunctionFinish.from_flow_with_transfers
    (values := .initial checked) (ambient := ambient) (mapping := finalMap) (world := finalWorld)
    (faults := faults) (outcome := returnedControl outcome)
    functions rawUnit conditional.projection fellThrough escaped transfers flowRelated flowEvaluation
  have bodyEvaluation : Evaluates actual initialStore (body.rename ξ) result bodyStore := by
    rw [emitted_rename conditional]
    exact completed
  refine ⟨result, bodyEvaluation, ?_, ?_⟩
  · cases outcome with
    | value source => exact ImperativeFunctionFinish.result finished (CompatibleNamedBody.Exit.returned source)
    | fault reason => exact ImperativeFunctionFinish.result finished (CompatibleNamedBody.Exit.fault reason)
  · cases outcome with
    | value source => trivial
    | fault reason =>
      cases sourceLast with | fault failed =>
        obtain ⟨token, sameValue, origin⟩ := retained
        have faultChild : Evaluates (.bool boolean :: actual) middleStore
            ((code boolean).rename (Renaming.comp (Renaming.insertion 0) ξ)) (.inLeft type (.word token)) bodyStore := sameValue ▸ second
        have faultBranch : Evaluates (.bool boolean :: actual) middleStore
            ((LocalLoop.returnValue type ((code boolean).rename ξ)).weakenAt 0)
            (.inLeft (LocalLoop.controlType type) (.word token)) bodyStore := by
          rw [← LoopRenaming.returnValue, ← GenericExpressionMeaning.rename_prefix, LoopRenaming.returnValue]
          exact LocalLoop.returnValue_failure _ faultChild
        have faultChoice : Evaluates actual initialStore
            (LocalLoop.conditional type (conditionCode.rename ξ)
              (LocalLoop.returnValue type ((code true).rename ξ)) (LocalLoop.returnValue type ((code false).rename ξ)))
            (.inLeft (LocalLoop.controlType type) (.word token)) bodyStore := by
          cases boolean with
          | false => exact LocalControl.choose_false _ first faultBranch
          | true => exact LocalControl.choose_true _ first faultBranch
        have faultBody : Evaluates actual initialStore (body.rename ξ) (.inLeft type (.word token)) bodyStore := by
          rw [emitted_rename conditional]
          exact LocalControl.finish_failure _ (LocalLoop.toControl_failure _ escaped (LocalLoop.sequence_failure _ faultChoice))
        exact ⟨token, (evaluation_deterministic bodyEvaluation faultBody).1,
          model_bodyPost.of_branch conditional boolean sourceFirst first middleHeaps firstMaps firstWorlds firstFrame firstMetadata
            maps worlds frame metadata failed origin faultChild faultBody⟩

include conditional in
private theorem trace_condition {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {childSize : Nat} {reason : Dynamic.SemanticFault}
    (failed : SourceExecutionSize.ExpressionFaults program childSize context function.evidence function.source environment before condition reason after) :
    ∃ size, RecursiveNamedCallBounds.BodyTrace program size function context environment before (.fault reason) after := by
  refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [childSize]], .fault (finalContext := context) ?_⟩
  rw [conditional.statements]
  exact .singleton (.ifCondition (lookupStatement?_sound conditional.found) conditional.form failed)

include conditional in
private theorem trace_branch {environment : Dynamic.Environment} {before middle after : Dynamic.Heap}
    {boolean : Bool} {firstSize lastSize : Nat} {outcome : Dynamic.ExpressionOutcome}
    (first : SourceExecutionSize.ExpressionEvaluates program firstSize context function.evidence function.source environment before condition (.bool boolean) middle)
    (second : RecursiveNamedCallBounds.ExpressionOutcome program lastSize context function.evidence function.source environment middle (expression boolean) outcome after) :
    ∃ size, RecursiveNamedCallBounds.BodyTrace program size function context environment before outcome after := by
  cases outcome with
  | value value =>
    cases second with | value child =>
      have returning := SourceExecutionSize.StatementExecutes.returnValue
        (lookupStatement?_sound (conditional.branchFound boolean)) (conditional.branchForm boolean) child
      have selected := SourceExecutionSize.StatementsExecute.terminal (statements := []) returning (Dynamic.TerminalControl.returned value)
      refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [firstSize, SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [lastSize]]]],
        .returned (finalContext := context) ?_⟩
      rw [conditional.statements]
      apply SourceExecutionSize.FunctionStatementsExecute.singleton (lookupStatement?_sound conditional.found)
        (by intro expr; simp [conditional.form])
      cases boolean with
      | false => exact .ifFalseWithElse (lookupStatement?_sound conditional.found) conditional.form first selected
      | true => exact .ifTrue (lookupStatement?_sound conditional.found) conditional.form first selected
  | fault reason =>
    cases second with | fault child =>
      have returning := SourceExecutionSize.StatementFaults.returnValue
        (lookupStatement?_sound (conditional.branchFound boolean)) (conditional.branchForm boolean) child
      have selected := SourceExecutionSize.StatementsFault.head (statements := []) returning
      refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [firstSize, SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [lastSize]]]],
        .fault (finalContext := context) ?_⟩
      rw [conditional.statements]
      apply SourceExecutionSize.FunctionStatementsFault.singleton
      cases boolean with
      | false => exact .ifFalseBody (lookupStatement?_sound conditional.found) conditional.form first selected
      | true => exact .ifTrueBody (lookupStatement?_sound conditional.found) conditional.form first selected
end Finite

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {header : CallableIndexedOwnedFunctionValues.Header compiled program}
  {locations : CallableIndexedOwnedFunctionValues.Header compiled program → Location} {capturePrefix : Nat}
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
  (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
    administrative actualContext actual ξ frameLocation current ghost)
  (reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
    entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
  {statement : StatementId} {node : StatementNode} {condition : ExpressionId} {conditionNode : ExpressionNode}
  {conditionFuel : Nat} {branch : Bool → StatementId} {branchNode : Bool → StatementNode}
  {expression : Bool → ExpressionId} {expressionNode : Bool → ExpressionNode} {fuel : Bool → Nat}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {conditionCode : Expr} {code : Bool → Expr}
  {type : Ty} {fellThrough escaped : Word}
  (conditional : ConditionalAt (.initial compiled.compatible.checked) header.function header.context
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) statement node condition conditionNode conditionFuel
    branch branchNode expression expressionNode fuel solved reasonAt conditionCode code type header.body fellThrough escaped)
  (nativeType : type = header.output)
  (source : SourceReceipt program header.function header.context entry.environment entry.heap)
  (rows : StableRows reached)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (valid : CompatibleExpressionLiterals.ContextValid solved header.context header.function.evidence)
  (reads : ReachedLoweredReadOutcomePorts.ReadPolicies conditionFuel (.initial compiled.compatible.checked)
    header.function.source header.context reasonAt faults)
  (branchReads : ∀ b, ReachedLoweredReadOutcomePorts.ReadPolicies (fuel b) (.initial compiled.compatible.checked)
    header.function.source header.context reasonAt faults)
  (missing : IndexFaultPostContracts.MissingPolicies (.initial compiled.compatible.checked)
    header.function.source functions registry program header.context header.function.evidence reasonAt faults)
  (unique : NodeOccurrencesUnique header.function.source) (wellFormed : ProgramWellFormed program)

include conditional nativeType source rows extension faithful observations functionTypes valid reads branchReads missing unique wellFormed in
/-- Source inversion supplies the real condition and chosen return child. -/
theorem source_body_with_post (size : Nat) :
    SourceBodyAtWithPost (model_bodyPost compiled.compatible.checked functions registry) (faults := faults) entry reached size := by
  intro outcome after bodyTrace
  obtain ⟨finalContext, control, flowTrace, exit⟩ := RecursiveNamedFunctionFinishBounds.trace_flow bodyTrace
  obtain ⟨rfl, statementSize, selected⟩ := selected_if conditional unique flowTrace
  have admitted : Admission (poolBridge (headers := headers) (keys := keys)) header.context reached := ⟨source.heapTyped, rows⟩
  cases selected with
  | conditionFault failed _ =>
    cases exit
    obtain ⟨value, bodyStore, finalMap, finalWorld, first, represented, finalHeaps,
        maps, worlds, frame, metadata, finalState, related, _postAdmission, retained⟩ :=
      CallableIndexedOwnedAdmittedBuiltinFaultBounds.preserves (poolBridge (headers := headers) (keys := keys))
        functions header.function.evidence (administrativeTransport headers keys) extension faithful observations functionTypes
        valid reads missing unique wellFormed source.runtime source.covers conditional.conditionTree conditional.conditionFound conditional.conditionTyped
        entry.environments entry.heaps source.locals entry.lookups entry.actualTyped reached admitted (.fault failed)
    cases represented with | @fault _ oldToken matched =>
      obtain ⟨token, sameValue, origin⟩ := CallableIndexedOwnedAdmittedBuiltinFaultBounds.NativeFaultAt.at_fault retained first
      have tokenSame : oldToken = token := by simpa using sameValue
      subst token
      have bodyEvaluation := finished_condition conditional first
      refine ⟨_, bodyStore, finalMap, finalWorld, bodyEvaluation, ?_, finalHeaps, maps, worlds, frame, metadata, ⟨finalState, related⟩, ?_⟩
      · simpa only [nativeType] using (FunctionCalls.ResultRepresents.fault
          (model := CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          (mapping := finalMap) (world := finalWorld) (sourceType := header.function.resultType) (type := type) matched)
      · exact ⟨oldToken, by simp [nativeType], model_bodyPost.of_route conditional origin first failed.sound bodyEvaluation⟩
  | conditionType firstTrace notBoolean _ _ =>
    obtain ⟨value, bodyStore, finalMap, finalWorld, _first, represented, _finalHeaps,
        _maps, _worlds, _frame, _metadata, _finalState, _related, _postAdmission, _retained⟩ :=
      CallableIndexedOwnedAdmittedBuiltinFaultBounds.preserves (poolBridge (headers := headers) (keys := keys))
        functions header.function.evidence (administrativeTransport headers keys) extension faithful observations functionTypes
        valid reads missing unique wellFormed source.runtime source.covers conditional.conditionTree conditional.conditionFound conditional.conditionTyped
        entry.environments entry.heaps source.locals entry.lookups entry.actualTyped reached admitted (.value firstTrace)
    cases represented with | value payload =>
      have boolPayload := conditional.conditionType ▸ payload
      obtain ⟨_boolean, rfl, _⟩ := bool_fields boolPayload
      exact False.elim (notBoolean trivial)
  | @branch conditionSize bodySize boolean middle innerContext innerOutcome _ firstTrace branchTrace _ _ =>
    have selectedReturn : innerContext = header.context ∧ ∃ lastSize lastOutcome,
        RecursiveNamedCallBounds.ExpressionOutcome program lastSize header.context header.function.evidence header.function.source
          entry.environment middle (expression boolean) lastOutcome after ∧ innerOutcome = returnedControl lastOutcome ∧ lastSize < bodySize := by
      apply RecursiveNamedLexicalTreeSourceBounds.returning (mode := false) unique (conditional.branchFound boolean) (conditional.branchForm boolean)
      cases boolean <;> simpa only [RecursiveNamedLoopContracts.ExecutesAt, Bool.false_eq_true, if_false, if_true, Option.getD_some] using branchTrace
    obtain ⟨rfl, lastSize, lastOutcome, lastTrace, rfl, _strict⟩ := selectedReturn
    obtain ⟨firstValue, middleStore, middleMap, middleWorld, first, represented, middleHeaps,
        firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstAdmission, _retained⟩ :=
      CallableIndexedOwnedAdmittedBuiltinFaultBounds.preserves (poolBridge (headers := headers) (keys := keys))
        functions header.function.evidence (administrativeTransport headers keys) extension faithful observations functionTypes
        valid reads missing unique wellFormed source.runtime source.covers conditional.conditionTree conditional.conditionFound conditional.conditionTyped
        entry.environments entry.heaps source.locals entry.lookups entry.actualTyped reached admitted (.value firstTrace)
    cases represented with | @value _ payload representedFirst =>
      have boolPayload := conditional.conditionType ▸ representedFirst
      obtain ⟨actualBoolean, sourceEq, coreEq⟩ := bool_fields boolPayload
      have sameBoolean : actualBoolean = boolean := by simpa using sourceEq.symm
      subst actualBoolean
      subst payload
      obtain ⟨_sourceTyped, middleAdmission⟩ := firstAdmission.at_value
      obtain ⟨value, bodyStore, finalMap, finalWorld, second, represented, finalHeaps,
          maps, worlds, frame, metadata, finalState, finalRelated, _postAdmission, retained⟩ :=
        CallableIndexedOwnedAdmittedBuiltinFaultBounds.preserves (poolBridge (headers := headers) (keys := keys))
          functions header.function.evidence (administrativeTransport headers keys) extension faithful observations functionTypes
          valid (branchReads boolean) missing unique wellFormed source.runtime source.covers (conditional.tree boolean)
          (conditional.expressionFound boolean) (conditional.expressionTyped boolean)
          (entry.environments.extend firstMaps firstWorlds) middleHeaps (source.locals.mono firstMetadata)
          (GenericExpressionMeaning.agree_prefix entry.lookups (.bool boolean))
          (.cons .bool (entry.actualTyped.weaken firstWorlds)) middleState middleAdmission lastTrace
      have retainedAt : ExpressionFailurePostContracts.OutcomePost
          (ReachedBuiltinExpressionFaultPaths.model_expressionPost compiled.compatible.checked functions registry)
          program header.context header.function.evidence header.function.source entry.environment middle (expression boolean) type lastOutcome after value finalMap finalWorld bodyStore := by
        cases lastOutcome with
        | value v => trivial
        | fault reason => exact CallableIndexedOwnedAdmittedBuiltinFaultBounds.NativeFaultAt.at_fault retained second
      obtain ⟨result, bodyEvaluation, finished, retainedBody⟩ := finish_branch conditional firstTrace.sound first middleHeaps
        firstMaps firstWorlds firstFrame firstMetadata maps worlds frame metadata lastTrace.sound second represented retainedAt
      refine ⟨result, bodyStore, finalMap, finalWorld, bodyEvaluation, ?_, finalHeaps,
        firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata,
        ⟨finalState, (protocol headers keys).trans firstRelated finalRelated⟩, ?_⟩
      · cases lastOutcome <;> cases exit <;> simpa only [nativeType, SourceCoreCompatibleValues.Context.initial] using finished
      · cases lastOutcome <;> cases exit <;> simpa only [nativeType] using retainedBody

include conditional nativeType source rows extension faithful observations functionTypes valid reads branchReads missing unique wellFormed in
/-- Native finish, sequence and conditional inversion retain the actual selected
branch. Source sizes are reconstructed independently from its true children. -/
theorem native_body_with_post (size : Nat) :
    NativeBodyAtWithPost (model_bodyPost compiled.compatible.checked functions registry) (faults := faults) entry reached size := by
  intro value finalStore bodyCompletion
  have nativeFinish : EvaluationSize size entry.actualBody entry.store
      (CompatibleStatements.finish type
        (LocalLoop.sequence type
          (LocalLoop.conditional type (conditionCode.rename entry.embedding)
            (LocalLoop.returnValue type ((code true).rename entry.embedding)) (LocalLoop.returnValue type ((code false).rename entry.embedding)))
          (LocalLoop.fallthrough type)) fellThrough escaped) value finalStore := by
    rw [← emitted_rename conditional]
    exact bodyCompletion
  obtain ⟨flowSize, flowValue, flowStore, _flowStrict, flowCompletion⟩ := RecursiveNamedCallBounds.finish_flow nativeFinish
  obtain ⟨conditionalSize, conditionalStore, conditionalValue, _conditionalStrict, conditionalCompletion⟩ := flowCompletion.bind_computation
  obtain ⟨firstSize, middleStore, firstValue, _firstStrict, firstCompletion⟩ := conditionalCompletion.bind_computation
  have admitted : Admission (poolBridge (headers := headers) (keys := keys)) header.context reached := ⟨source.heapTyped, rows⟩
  obtain ⟨sourceSize, firstOutcome, middle, middleMap, middleWorld, firstTrace, firstRepresented,
      middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstAdmission, retained⟩ :=
    CallableIndexedOwnedAdmittedBuiltinFaultBounds.reflects (poolBridge (headers := headers) (keys := keys))
      functions header.function.evidence (administrativeTransport headers keys) extension faithful observations functionTypes
      valid reads missing unique wellFormed source.runtime source.covers conditional.conditionTree conditional.conditionFound conditional.conditionTyped
      entry.environments entry.heaps source.locals entry.lookups entry.actualTyped reached admitted firstCompletion
  cases firstRepresented with
  | @fault reason oldToken matched =>
    cases firstTrace with | fault failed =>
      obtain ⟨token, sameValue, origin⟩ := CallableIndexedOwnedAdmittedBuiltinFaultBounds.NativeFaultAt.at_fault retained firstCompletion.sound
      have tokenSame : oldToken = token := by simpa using sameValue
      subst token
      have bodyEvaluation := finished_condition conditional firstCompletion.sound
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic bodyCompletion.sound bodyEvaluation
      obtain ⟨bodySize, sourceTrace⟩ := trace_condition conditional failed
      refine ⟨bodySize, .fault reason, middle, middleMap, middleWorld, sourceTrace, ?_, middleHeaps,
        firstMaps, firstWorlds, firstFrame, firstMetadata, ⟨middleState, firstRelated⟩, ?_⟩
      · simpa only [nativeType] using (FunctionCalls.ResultRepresents.fault
          (model := CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          (mapping := middleMap) (world := middleWorld) (sourceType := header.function.resultType) (type := type) matched)
      · exact ⟨oldToken, by simp [nativeType], model_bodyPost.of_route conditional origin firstCompletion.sound failed.sound bodyEvaluation⟩
  | @value sourceValue payload representedFirst =>
    cases firstTrace with | value sourceFirst =>
      obtain ⟨boolean, sourceEq, coreEq⟩ := bool_fields representedFirst
      subst sourceValue
      subst payload
      obtain ⟨_sourceTyped, middleAdmission⟩ := firstAdmission.at_value
      obtain ⟨branchSize, _branchStrict, branchCompletion⟩ :
          ∃ branchSize, branchSize < conditionalSize ∧ EvaluationSize branchSize (.bool boolean :: entry.actualBody) middleStore
            ((LocalLoop.returnValue type ((code boolean).rename entry.embedding)).weakenAt 0) conditionalValue conditionalStore := by
        cases boolean with
        | false => exact conditionalCompletion.choose_false firstCompletion.sound
        | true => exact conditionalCompletion.choose_true firstCompletion.sound
      have returnCompletion : EvaluationSize branchSize (.bool boolean :: entry.actualBody) middleStore
          (LocalLoop.returnValue type ((code boolean).rename (Renaming.comp (Renaming.insertion 0) entry.embedding))) conditionalValue conditionalStore := by
        rw [← LoopRenaming.returnValue, GenericExpressionMeaning.rename_prefix, LoopRenaming.returnValue]
        exact branchCompletion
      obtain ⟨lastSize, bodyStore, lastValue, _lastStrict, lastCompletion⟩ := returnCompletion.bind_computation
      obtain ⟨lastSourceSize, lastOutcome, after, finalMap, finalWorld, lastTrace, represented, finalHeaps,
          maps, worlds, frame, metadata, finalState, finalRelated, _postAdmission, retained⟩ :=
        CallableIndexedOwnedAdmittedBuiltinFaultBounds.reflects (poolBridge (headers := headers) (keys := keys))
          functions header.function.evidence (administrativeTransport headers keys) extension faithful observations functionTypes
          valid (branchReads boolean) missing unique wellFormed source.runtime source.covers (conditional.tree boolean)
          (conditional.expressionFound boolean) (conditional.expressionTyped boolean)
          (entry.environments.extend firstMaps firstWorlds) middleHeaps (source.locals.mono firstMetadata)
          (GenericExpressionMeaning.agree_prefix entry.lookups (.bool boolean))
          (.cons .bool (entry.actualTyped.weaken firstWorlds)) middleState middleAdmission lastCompletion
      have retainedAt : ExpressionFailurePostContracts.OutcomePost
          (ReachedBuiltinExpressionFaultPaths.model_expressionPost compiled.compatible.checked functions registry)
          program header.context header.function.evidence header.function.source entry.environment middle (expression boolean) type lastOutcome after lastValue finalMap finalWorld bodyStore := by
        cases lastOutcome with
        | value v => trivial
        | fault reason => exact CallableIndexedOwnedAdmittedBuiltinFaultBounds.NativeFaultAt.at_fault retained lastCompletion.sound
      obtain ⟨result, bodyEvaluation, finished, retainedBody⟩ := finish_branch conditional sourceFirst.sound firstCompletion.sound middleHeaps
        firstMaps firstWorlds firstFrame firstMetadata maps worlds frame metadata lastTrace.sound lastCompletion.sound represented retainedAt
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic bodyCompletion.sound bodyEvaluation
      obtain ⟨bodySize, sourceTrace⟩ := trace_branch conditional sourceFirst lastTrace
      refine ⟨bodySize, lastOutcome, after, finalMap, finalWorld, sourceTrace, ?_, finalHeaps,
        firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata,
        ⟨finalState, (protocol headers keys).trans firstRelated finalRelated⟩, ?_⟩
      · simpa only [nativeType, SourceCoreCompatibleValues.Context.initial] using finished
      · simpa only [nativeType] using retainedBody

include conditional nativeType source rows extension faithful observations functionTypes valid reads branchReads missing unique wellFormed in
/-- Every strict Source body member comes from the same concrete conditional producer. -/
theorem source_below (budget : Nat) :
    RecursiveNamedBoundedContracts.Below budget
      (SourceBodyAtWithPost (model_bodyPost compiled.compatible.checked functions registry) (faults := faults) entry reached) := by
  intro child _strict
  exact source_body_with_post functions entry reached conditional nativeType source rows extension faithful observations functionTypes
    valid reads branchReads missing unique wellFormed child

include conditional nativeType source rows extension faithful observations functionTypes valid reads branchReads missing unique wellFormed in
/-- The native strict member consumes its own whole body completion. -/
theorem native_below (budget : Nat) :
    RecursiveNamedBoundedContracts.Below budget
      (NativeBodyAtWithPost (model_bodyPost compiled.compatible.checked functions registry) (faults := faults) entry reached) := by
  intro child _strict
  exact native_body_with_post functions entry reached conditional nativeType source rows extension faithful observations functionTypes
    valid reads branchReads missing unique wellFormed child

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedConditionalNamedBodyFaultBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedConditionalNamedBodyPostProviders
/-! Actual successful arguments construct the same parameter receipt. The
conditional producer runs internally and the original outer call core retains
its precise route, body store and caller restoration. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedConditionalNamedBodyPostProviders
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission CallableIndexedOwnedIndirectExpressionHeads
open CallableIndexedOwnedAdmittedBodyEntries (SourceReceipt)
open CallableIndexedOwnedInvocationBounds NamedInvocationFaultPostContracts
open RecursiveNamedBoundedContracts
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- Static receipts belong to the literal selected Header and its policy fields. -/
structure ConditionalInputs (header : CallableIndexedOwnedFunctionValues.Header compiled program) where
  statement : StatementId
  node : StatementNode
  condition : ExpressionId
  conditionNode : ExpressionNode
  conditionFuel : Nat
  branch : Bool → StatementId
  branchNode : Bool → StatementNode
  expression : Bool → ExpressionId
  expressionNode : Bool → ExpressionNode
  fuel : Bool → Nat
  conditionCode : Expr
  code : Bool → Expr
  conditional : ReachedNamedConditionalBodyFaultPaths.ConditionalAt (.initial compiled.compatible.checked)
    header.function header.context (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    statement node condition conditionNode conditionFuel branch branchNode expression expressionNode fuel
    header.solved header.reasonAt conditionCode code header.output header.body header.fellThrough header.escaped
  valid : CompatibleExpressionLiterals.ContextValid header.solved header.context header.function.evidence
  reads : ReachedLoweredReadOutcomePorts.ReadPolicies conditionFuel (.initial compiled.compatible.checked)
    header.function.source header.context header.reasonAt faults
  branchReads : ∀ b, ReachedLoweredReadOutcomePorts.ReadPolicies (fuel b) (.initial compiled.compatible.checked)
    header.function.source header.context header.reasonAt faults
  missing : IndexFaultPostContracts.MissingPolicies (.initial compiled.compatible.checked)
    header.function.source functions registry program header.context header.function.evidence header.reasonAt faults

/-- Only the genuine conditional causal post is admitted by this static domain. -/
def FaultPost : BodyFaultPost :=
  ReachedNamedConditionalBodyFaultPaths.model_bodyPost compiled.compatible.checked functions registry

section Factory
variable {functions} {header : CallableIndexedOwnedFunctionValues.Header compiled program}
  {statement : StatementId} {node : StatementNode} {nodeType : Ty}
  {condition : ExpressionId} {conditionNode : ExpressionNode} {conditionFuel : Nat}
  {branch : Bool → StatementId} {branchNode : Bool → StatementNode}
  {expression : Bool → ExpressionId} {expressionNode : Bool → ExpressionNode} {fuel : Bool → Nat}
  {conditionCode : Expr} {code : Bool → Expr} {lowerFuel : Nat}

/-- Finite static producer cases retain the actual accepted body and all three
accepted expression results. No body execution is an input. -/
def ConditionalInputs.of_accepted
    (statements : header.function.body = [statement])
    (found : header.function.source.lookupStatement? statement = some node)
    (form : node.form = .ifThen condition [branch true] (some [branch false]))
    (conditionFound : header.function.source.lookupExpression? condition = some conditionNode)
    (conditionTyped : ExpressionHasType header.function.source header.context condition conditionNode.type)
    (conditionType : conditionNode.type = .bool)
    (conditionTree : CompatibleExpressionBuiltins.Tree conditionFuel (.initial compiled.compatible.checked)
      header.function.source header.context header.solved header.reasonAt
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) condition ⟨.bool, conditionCode⟩)
    (branchFound : ∀ b, header.function.source.lookupStatement? (branch b) = some (branchNode b))
    (branchForm : ∀ b, (branchNode b).form = .returnStmt (some (expression b)))
    (expressionFound : ∀ b, header.function.source.lookupExpression? (expression b) = some (expressionNode b))
    (expressionTyped : ∀ b, ExpressionHasType header.function.source header.context (expression b) (expressionNode b).type)
    (resultType : ∀ b, (expressionNode b).type = header.function.resultType)
    (tree : ∀ b, CompatibleExpressionBuiltins.Tree (fuel b) (.initial compiled.compatible.checked)
      header.function.source header.context header.solved header.reasonAt
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) (expression b) ⟨header.output, code b⟩)
    (projection : compiled.compatible.checked.catalog.project header.function.resultType = .ok header.output)
    (actualFuel : header.fuel = lowerFuel + 2)
    (statementRead : header.policy.readStatement header.function.source statement = .ok (node, nodeType))
    (branchRead : ∀ b, header.policy.readStatement header.function.source (branch b) = .ok (branchNode b, header.output))
    (conditionAccepted : header.policy.lowerExpression (lowerFuel + 1) header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) condition header.reasonAt = .ok ⟨.bool, conditionCode⟩)
    (branchAccepted : ∀ b, header.policy.lowerExpression lowerFuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) (expression b) header.reasonAt = .ok ⟨header.output, code b⟩)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
      header.output header.reasonAt header.fellThrough header.escaped = .ok header.body)
    (valid : CompatibleExpressionLiterals.ContextValid header.solved header.context header.function.evidence)
    (reads : ReachedLoweredReadOutcomePorts.ReadPolicies conditionFuel (.initial compiled.compatible.checked)
      header.function.source header.context header.reasonAt faults)
    (branchReads : ∀ b, ReachedLoweredReadOutcomePorts.ReadPolicies (fuel b) (.initial compiled.compatible.checked)
      header.function.source header.context header.reasonAt faults)
    (missing : IndexFaultPostContracts.MissingPolicies (.initial compiled.compatible.checked)
      header.function.source functions registry program header.context header.function.evidence header.reasonAt faults) :
    ConditionalInputs (registry := registry) (faults := faults) functions header := by
  have emitted : header.body = CompatibleStatements.finish header.output
      (LocalLoop.sequence header.output
        (LocalLoop.conditional header.output conditionCode
          (LocalLoop.returnValue header.output (code true)) (LocalLoop.returnValue header.output (code false)))
        (LocalLoop.fallthrough header.output)) header.fellThrough header.escaped := by
    rw [actualFuel, statements] at accepted
    simp only [SourceCoreLoops.lowerStatementsWithPolicy, SourceCoreLoops.lowerFlowStatementsWithPolicy,
      statementRead, form, conditionAccepted, branchRead true, branchRead false, branchForm true, branchForm false,
      branchAccepted true, branchAccepted false, SourceCoreBasic.ensureType,
      bind, Except.bind, pure, Except.pure] at accepted
    exact (Except.ok.inj accepted).symm
  exact
    { statement := statement, node := node, condition := condition, conditionNode := conditionNode,
      conditionFuel := conditionFuel, branch := branch, branchNode := branchNode, expression := expression,
      expressionNode := expressionNode, fuel := fuel, conditionCode := conditionCode, code := code,
      conditional := ⟨statements, found, form, conditionFound, conditionTyped, conditionType, conditionTree,
        branchFound, branchForm, expressionFound, expressionTyped, resultType, tree, projection, emitted⟩,
      valid := valid, reads := reads, branchReads := branchReads, missing := missing }

end Factory

section Body
variable {functions}
  {header : CallableIndexedOwnedFunctionValues.Header compiled program}
  {locations : RecursiveNamedCatalog.Locations} {capturePrefix : Nat}
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
  (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
    administrative actualContext actual ξ frameLocation current ghost)
  (reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
    entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
  (source : SourceReceipt program header.function header.context entry.environment entry.heap)
  (rows : StableRows reached)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (wellFormed : ProgramWellFormed program)

include source rows extension faithful observations functionTypes wellFormed in
/-- The strict Source child is derived from the concrete conditional producer. -/
theorem ConditionalInputs.source_below
    (inputs : ConditionalInputs (program := program) (registry := registry) (faults := faults) functions header)
    (budget : Nat) : RecursiveNamedBoundedContracts.Below budget
      (SourceBodyAtWithPost (FaultPost functions (registry := registry)) (faults := faults) entry reached) :=
  CallableIndexedOwnedConditionalNamedBodyFaultBounds.source_below functions entry reached inputs.conditional rfl
    source rows extension faithful observations functionTypes inputs.valid inputs.reads inputs.branchReads inputs.missing
    header.unique wellFormed budget

include source rows extension faithful observations functionTypes wellFormed in
/-- The strict native child is derived from the same concrete conditional producer. -/
theorem ConditionalInputs.native_below
    (inputs : ConditionalInputs (program := program) (registry := registry) (faults := faults) functions header)
    (budget : Nat) : RecursiveNamedBoundedContracts.Below budget
      (NativeBodyAtWithPost (FaultPost functions (registry := registry)) (faults := faults) entry reached) :=
  CallableIndexedOwnedConditionalNamedBodyFaultBounds.native_below functions entry reached inputs.conditional rfl
    source rows extension faithful observations functionTypes inputs.valid inputs.reads inputs.branchReads inputs.missing
    header.unique wellFormed budget

end Body

section Providers
variable {functions}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {header : CallableIndexedOwnedFunctionValues.Header compiled program}
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId}
  {callerPrefix : Nat} {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => CallableIndexedOwnedExpressionHeads.Globals (headers := headers) owner callerPrefix index.scope index.canonical) callerProtocol)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {canonical : Environment} {environment : Dynamic.Environment}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission (CallableIndexedOwnedIndirectCallerProtocol.forget_slots bridge) context initial)
  {originalTypes : List TypeSystem.Ty} {rawResult : TypeSystem.Ty} {predicates : List ProgramPredicate}
  (wellFormed : ProgramWellFormed program)
  (sourceRuntime : Dynamic.SourceRuntimeValid program context source)
  (covers : evidence.Covers context)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (argumentTypes : ExpressionsHaveTypes source context ids originalTypes)
  (application : SourceSemantics.DeclarationApplicationValid context header.instantiation originalTypes rawResult predicates)
  (inputs : ConditionalInputs (program := program) (registry := registry) (faults := faults) functions header)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)

include admitted wellFormed sourceRuntime covers locals argumentTypes application inputs extension faithful observations functionTypes in
/-- The original successful arguments supply the exact parameter receipt;
only the concrete strict body producer is invoked. -/
theorem source_invocations (budget : Nat) :
    CallableIndexedOwnedExpressionHeads.SourceInvocationsForWithPost (post := FaultPost functions (registry := registry)) (source := source) (context := context)
      (evidence := evidence) (faults := faults) functions owner
      (CallableIndexedOwnedInvocationBounds.stableOwnerCondition (keys := keys) functions registry header) bridge initial
      (environment := environment) (ids := ids) budget := by
  intro sourceSize arguments middle middleMap middleWorld middleStore payloads evaluated argumentState
    _argumentRelated _maps _worlds frame _metadata _capture represented _heaps
    origin index metadata administrative actualContext actual ξ frameLocation physical selected history emitted
    entry agreement parameterPool parameterRelated _allowed child strict outcome after trace
  have arity : header.function.parameters.length = arguments.length :=
    (congrArg List.length header.parameters).trans ((List.length_map Prod.fst).trans represented.length.1)
  have sourceAdmission := CallableIndexedOwnedNamedArgumentAdmission.at_successful_arguments header wellFormed
    sourceRuntime covers locals admitted.heap argumentTypes application evaluated.sound arity
  have stable := StableRows.after_administrative (bridge.pool initial) (bridge.pool argumentState) admitted.rows frame
  let receipt : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt (registry := registry) functions owner (bridge.pool argumentState) header arguments :=
    { origin := origin, index := index, metadata := metadata, administrative := administrative,
      actualContext := actualContext, actual := actual, embedding := ξ, frameLocation := frameLocation,
      physical := physical, selected := selected, history := history, emitted := emitted,
      body := entry, reached := parameterPool, related := parameterRelated, stable := stable,
      heapTyped := sourceAdmission.1, argumentsTyped := sourceAdmission.2 }
  exact inputs.source_below receipt.body receipt.reached (receipt.source wellFormed) receipt.rows
    extension faithful observations functionTypes wellFormed budget child strict trace


include admitted wellFormed sourceRuntime covers locals argumentTypes application inputs extension faithful observations functionTypes in
/-- The original successful arguments supply the exact parameter receipt;
only the concrete strict body producer is invoked. -/
theorem native_invocations (budget : Nat) :
    CallableIndexedOwnedExpressionHeads.NativeInvocationsForWithPost (post := FaultPost functions (registry := registry)) (source := source) (context := context)
      (evidence := evidence) (faults := faults) functions owner
      (CallableIndexedOwnedInvocationBounds.stableOwnerCondition (keys := keys) functions registry header) bridge initial
      (environment := environment) (ids := ids) budget := by
  intro sourceSize arguments middle middleMap middleWorld middleStore payloads evaluated argumentState
    _argumentRelated _maps _worlds frame _metadata _capture represented _heaps
    origin index metadata administrative actualContext actual ξ frameLocation prefixSize bodyStore value finalStore
    physical selected history emitted prefixRun prefixWithin restored entry parameterPool parameterRelated _allowed child strict
    bodyValue bodyFinalStore completed
  have arity : header.function.parameters.length = arguments.length :=
    (congrArg List.length header.parameters).trans ((List.length_map Prod.fst).trans represented.length.1)
  have sourceAdmission := CallableIndexedOwnedNamedArgumentAdmission.at_successful_arguments header wellFormed
    sourceRuntime covers locals admitted.heap argumentTypes application evaluated.sound arity
  have stable := StableRows.after_administrative (bridge.pool initial) (bridge.pool argumentState) admitted.rows frame
  let receipt : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt (registry := registry) functions owner (bridge.pool argumentState) header arguments :=
    { origin := origin, index := index, metadata := metadata, administrative := administrative,
      actualContext := actualContext, actual := actual, embedding := ξ, frameLocation := frameLocation,
      physical := physical, selected := selected, history := history, emitted := emitted,
      body := entry, reached := parameterPool, related := parameterRelated, stable := stable,
      heapTyped := sourceAdmission.1, argumentsTyped := sourceAdmission.2 }
  exact inputs.native_below receipt.body receipt.reached (receipt.source wellFormed) receipt.rows
    extension faithful observations functionTypes wellFormed budget child strict completed


end Providers

section Heads
variable {functions}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {compilation : SourceCoreFunctions.Context}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (caller : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => CallableIndexedOwnedExpressionHeads.Globals (headers := headers) owner compilation.administrativePrefix index.scope index.canonical)
    callerProtocol)
  {source : TypedSource} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
  {certificate : GenericExpressionMeaning.Certificate}
  (wellFormed : ProgramWellFormed program) (sourceRuntime : Dynamic.SourceRuntimeValid program context source)
  (covers : evidence.Covers context) (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (idsUnique : RequirementIdsUnique context)
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)

/-- The admitted outer tuple also retains the exact selected low route. -/
def PreservesHeadAtWithPost (size : Nat) : Prop :=
  ∀ {scope id lowered}, RecursiveNamedCallEvidenceHeads.Head (prepared := compiled.indexed.ancestry)
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers compilation source context evidence certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node → ExpressionHasType source context id node.type →
  ∀ {mapping world administrative environment canonical actual actualContext before store ξ outcome after},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions →
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions →
  ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller) context initial →
    RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld node.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        PostAdmission (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller) context node.type outcome reached ∧
        NamedExpressionBodyFaultPostContracts.OuterCallRouteAt
          (functions := functions) (registry := registry) (source := source) (context := context)
          (evidence := evidence) (environment := environment) (actual := actual) (ξ := ξ)
          (FaultPost functions (registry := registry)) owner caller initial
          compilation.administrativePrefix compilation.internalReason size none
          id node lowered outcome after value finalMap finalWorld finalStore

/-- The admitted outer tuple also retains the exact selected low route. -/
def ReflectsHeadAtWithPost (size : Nat) : Prop :=
  ∀ {scope id lowered}, RecursiveNamedCallEvidenceHeads.Head (prepared := compiled.indexed.ancestry)
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers compilation source context evidence certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node → ExpressionHasType source context id node.type →
  ∀ {mapping world administrative environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions →
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions →
  ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller) context initial →
    EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment before id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld node.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        PostAdmission (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller) context node.type outcome reached ∧
        NamedExpressionBodyFaultPostContracts.OuterCallRouteAt
          (functions := functions) (registry := registry) (source := source) (context := context)
          (evidence := evidence) (environment := environment) (actual := actual) (ξ := ξ)
          (FaultPost functions (registry := registry)) owner caller initial
          compilation.administrativePrefix compilation.internalReason sourceSize (some size)
          id node lowered outcome after value finalMap finalWorld finalStore

include wellFormed sourceRuntime covers unique sameLayouts extension faithful observations functionTypes owners idsUnique in
/-- Strict actual argument children and a genuine selected static body domain
derive both providers internally, then retain the original reached admission. -/
theorem preserves_head_with_body_post (budget size : Nat) (within : size ≤ budget)
    (children : RecursiveNamedBoundedContracts.Below budget
      (CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
        (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        context evidence source certificate faults))
    (inputs : ∀ {id node}, source.lookupExpression? id = some node → ExpressionHasType source context id node.type →
      ∀ header, header ∈ headers → ∀ {callee ids}, node.form = .call callee ids (.declaration header.instantiation) →
      ConditionalInputs (program := program) (registry := registry) (faults := faults) functions header) :
    PreservesHeadAtWithPost (functions := functions) (registry := registry) (faults := faults)
      (source := source) (context := context) (certificate := certificate) owner caller evidence size := by
  intro scope id lowered head root found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial admitted trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, ⟨reached, related⟩, route⟩ :=
    CallableIndexedOwnedExpressionHeads.preserves_at_with_sequence_with_body_post functions owner sameLayouts
      (fun header => CallableIndexedOwnedInvocationBounds.stableOwnerCondition (keys := keys) functions registry header)
      (fun header _ => CallableIndexedOwnedInvocationBounds.stable_owner_authorized functions registry header owner)
      caller budget size within idsUnique unique owners head found initial environments heaps locals agrees typed
      (fun header _member callee ids codes form sequence _nativeTypes _packedType => by
        obtain ⟨originalTypes, rawResult, predicates, argumentTypes, _application⟩ :=
          CallableIndexedOwnedNamedArgumentAdmission.direct_arguments unique found form sourceTyped
        exact CallableIndexedOwnedAdmittedSequenceProducer.preserves
          (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller) initial admitted sequence unique argumentTypes
          environments heaps locals agrees typed budget children)
      (FaultPost functions (registry := registry))
      (fun header member callee ids form => by
        obtain ⟨originalTypes, rawResult, predicates, argumentTypes, application⟩ :=
          CallableIndexedOwnedNamedArgumentAdmission.direct_arguments unique found form sourceTyped
        exact source_invocations
          (owner := owner) (functions := functions) caller initial admitted wellFormed sourceRuntime covers locals
          argumentTypes application (inputs found sourceTyped header member form) extension faithful observations functionTypes budget) trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    after_expression_sized initial reached admitted wellFormed sourceRuntime covers locals sourceTyped trace frame, route⟩


include wellFormed sourceRuntime covers unique sameLayouts extension faithful observations functionTypes in
/-- Strict actual argument children and a genuine selected static body domain
derive both providers internally, then retain the original reached admission. -/
theorem reflects_head_with_body_post (budget size : Nat) (within : size ≤ budget)
    (children : RecursiveNamedBoundedContracts.Below budget
      (CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
        (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        context evidence source certificate faults))
    (inputs : ∀ {id node}, source.lookupExpression? id = some node → ExpressionHasType source context id node.type →
      ∀ header, header ∈ headers → ∀ {callee ids}, node.form = .call callee ids (.declaration header.instantiation) →
      ConditionalInputs (program := program) (registry := registry) (faults := faults) functions header) :
    ReflectsHeadAtWithPost (functions := functions) (registry := registry) (faults := faults)
      (source := source) (context := context) (certificate := certificate) owner caller evidence size := by
  intro scope id lowered head root found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed initial admitted completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, ⟨reached, related⟩, route⟩ :=
    CallableIndexedOwnedExpressionHeads.reflects_at_with_sequence_with_body_post functions owner sameLayouts
      (fun header => CallableIndexedOwnedInvocationBounds.stableOwnerCondition (keys := keys) functions registry header)
      (fun header _ => CallableIndexedOwnedInvocationBounds.stable_owner_authorized functions registry header owner)
      caller budget size within head found initial environments heaps locals agrees typed
      (fun header _member callee ids codes form sequence _nativeTypes _packedType => by
        obtain ⟨originalTypes, rawResult, predicates, argumentTypes, _application⟩ :=
          CallableIndexedOwnedNamedArgumentAdmission.direct_arguments unique found form sourceTyped
        exact CallableIndexedOwnedAdmittedSequenceProducer.reflects
          (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller) initial admitted sequence unique argumentTypes
          environments heaps locals agrees typed budget children)
      (FaultPost functions (registry := registry))
      (fun header member callee ids form => by
        obtain ⟨originalTypes, rawResult, predicates, argumentTypes, application⟩ :=
          CallableIndexedOwnedNamedArgumentAdmission.direct_arguments unique found form sourceTyped
        exact native_invocations
          (owner := owner) (functions := functions) caller initial admitted wellFormed sourceRuntime covers locals
          argumentTypes application (inputs found sourceTyped header member form) extension faithful observations functionTypes budget) completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    after_expression_sized initial reached admitted wellFormed sourceRuntime covers locals sourceTyped trace frame, route⟩


end Heads

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedConditionalNamedBodyPostProviders
end
