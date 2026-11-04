import Solcore.SourceSemantics.CoreLowering.Internal.Owned.InvocationBounds
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ExpressionHeads
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.NamedHeaderReceipts
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicRoots
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.CanonicalCallerState
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ReadyContinuations
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState

/-!
# Owned callables: principal methods

Captures, frames, support, values and continuations of principal methods, and method entries.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodCaptureReceipts
/-! An actual fresh bootstrap supplies complete method captures and canonical
named slots. Source attribution comes from the genuine method selector; cached
code or native typing supplies no Source body. Nonempty Source heap prefixes
require their separate initialization receipt. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodCaptureReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallablePreparedMethodRuntimeMeaning
open RecursiveGlobalInitializationMeaning RecursiveGlobalInitializationTyping

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {method : ExecutableImplMethods.CheckedMethod}
  (cached : CallablePreparedMethodSelection.Cached compiled method.specialized)
  (dictionary : Dynamic.EvidenceEnvironment)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))

abbrev sourceBody := CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram method

/-- Every native field comes from the actual initialized cache, while the
complete independent Source method frame remains a separate receipt. -/
structure BootstrapCapture (world : StoreTyping) where
  administrative : Core.Context
  installed : Installed cached.compilation (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (sourceBody := sourceBody (compiled := compiled) (method := method))
    (administrative := administrative) functions [] world ⟨[]⟩
    (RecursiveNamedCatalogPreparedInitialization.store compiled)
    (RecursiveNamedCatalogPreparedInitialization.environment compiled)
  sourceFrame : CallableCoercionMethodFrame.Frame (sourceBody (compiled := compiled) (method := method))
    (methodFunction cached.compilation (sourceBody (compiled := compiled) (method := method)) dictionary)
  canonical_eq : installed.canonical = RecursiveNamedCatalogPreparedInitialization.environment compiled
  captured_eq : installed.captured = List.replicate cached.index (Value.unit) ++
    RecursiveNamedCatalogPreparedInitialization.environment compiled
  embedding_eq : installed.embedding = shift cached.index
  frame_eq : installed.frameLocation = 0
  globals : ∀ header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram),
    installed.canonical[header.slot]? = some (.cellRef (OptionalCell.cellType header.named.signature.functionType)
      (RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot))

private theorem installed_of_typed {world : StoreTyping}
    (typed : RuntimeStoreHasTypes world (RecursiveNamedCatalogPreparedInitialization.store compiled) compiled.indexed.layouts.definitions)
    (localsEmpty : (sourceBody (compiled := compiled) (method := method)).context.locals = []) :
    ∃ administrative, ∃ installed : Installed cached.compilation (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (sourceBody := sourceBody (compiled := compiled) (method := method))
      (administrative := administrative) functions [] world ⟨[]⟩
      (RecursiveNamedCatalogPreparedInitialization.store compiled)
      (RecursiveNamedCatalogPreparedInitialization.environment compiled),
      installed.canonical = RecursiveNamedCatalogPreparedInitialization.environment compiled ∧
      installed.captured = List.replicate cached.index (Value.unit) ++ RecursiveNamedCatalogPreparedInitialization.environment compiled ∧
      installed.embedding = shift cached.index ∧ installed.frameLocation = 0 := by
  have cachedCode : compiled.indexed.secondPass.closures[cached.index]? = some
      (.lambda cached.named.signature.parameterType (LanguageResult.resultType cached.named.signature.resultType) cached.compilation.output) := by
    simpa only [cached.compilation.emitted] using cached.cached
  obtain ⟨row, _rowFound, same, read⟩ := RecursiveNamedPublicBootstrapGlobals.cached_slot compiled cachedCode
  rcases row with ⟨parameter, result, body⟩
  change Expr.lambda _ _ _ = Expr.lambda parameter result body at same
  cases same
  rw [← RecursiveNamedPublicBootstrapGlobals.environment_eq] at read
  obtain ⟨capturedContext, capturedTyped, _bodyTyped⟩ := stored_closure typed read
  obtain ⟨administrative, canonicalTyped⟩ := drop_installer_units cached.index capturedTyped
  have captureLayout : EnvironmentsAgree (shift cached.index)
      (RecursiveNamedCatalogPreparedInitialization.environment compiled)
      (List.replicate cached.index (Value.unit) ++ RecursiveNamedCatalogPreparedInitialization.environment compiled) := by
    intro index value found
    rw [List.getElem?_append_right (by simp [shift])]
    simpa [shift] using found
  have frameReference := RecursiveNamedCatalogInitialization.frame_reference compiled.indexed.base.globals compiled.indexed.ancestry.layout.frame
  have frameRead := RecursiveNamedCatalogInitialization.frame_read compiled.indexed.base.globals
    (RecursiveNamedCachedRows.rows compiled) compiled.indexed.ancestry.layout.frame
  have frameType : world[0]? = some compiled.indexed.ancestry.layout.frame.type := by
    rw [typed.world_eq, List.getElem?_map]
    change Option.map Value.type ((RecursiveNamedCatalogPreparedInitialization.store compiled).read? 0) = _
    change Option.map Value.type ((initialStore compiled.indexed.base.globals (RecursiveNamedCachedRows.rows compiled) compiled.indexed.ancestry.layout.frame).read? 0) = _
    rw [frameRead]
    rfl
  have globalReference := RecursiveNamedCatalogInitialization.global_reference compiled.indexed.base.globals
    compiled.indexed.ancestry.layout.frame (CallableIndexedPreparedInventories.cached_global_at compiled cached.selected)
  let installed : Installed cached.compilation (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (sourceBody := sourceBody (compiled := compiled) (method := method))
      (administrative := administrative) functions [] world ⟨[]⟩
      (RecursiveNamedCatalogPreparedInitialization.store compiled)
      (RecursiveNamedCatalogPreparedInitialization.environment compiled) := {
    canonical := RecursiveNamedCatalogPreparedInitialization.environment compiled
    captured := List.replicate cached.index (Value.unit) ++ RecursiveNamedCatalogPreparedInitialization.environment compiled
    capturedContext := capturedContext, embedding := shift cached.index
    environments := .nil canonicalTyped
    locals := by rw [localsEmpty]; exact .nil
    captureLayout := captureLayout, captureTyped := capturedTyped
    frameLocation := 0, canonicalReference := frameReference, capturedReference := captureLayout frameReference
    unmapped := by simp, frameTyped := frameType
    current := .empty, currentGhost := .empty, caller := ⟨frameRead, .stable .empty⟩
    records := [], snapshots := by simp [CallableIndexedSnapshots.All]
    globalIndex := cached.index
    globalLocation := RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals cached.index
    globalUnmapped := by simp, globalReference := globalReference, globalRead := by simpa only [installedValue, Store.read?] using read }
  exact ⟨administrative, installed, rfl, rfl, rfl, rfl⟩

/-- Actual preparation and the whole Source method selector construct this
capture packet without a body execution or arbitrary captured-slot premise. -/
theorem of_selected_with_heap {registry : SourceCoreRawMetadata.Registry} {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {context : SourceSemantics.Context} {caller : Dynamic.EvidenceEnvironment}
    {traitName methodName : String} {requirements : List RequirementId}
    (selected : Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context caller traitName methodName
      requirements (sourceBody (compiled := compiled) (method := method)) dictionary)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    ∃ world,
      RuntimeStoreHasTypes world (RecursiveNamedCatalogPreparedInitialization.store compiled) compiled.indexed.layouts.definitions ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions [] world ⟨[]⟩
        (RecursiveNamedCatalogPreparedInitialization.store compiled) ∧
      Nonempty (BootstrapCapture cached dictionary functions world) := by
  obtain ⟨world, typed⟩ := RecursiveNamedCatalogPreparedInitialization.typed accepted
  obtain ⟨_types, _context, _facts, certified, _valid⟩ := CallablePreparedMethodSelection.selected_typed selected wellFormed
  obtain ⟨administrative, installed, canonical, captured, embedding, frame⟩ :=
    installed_of_typed cached functions typed certified.locals_empty
  have heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions [] world ⟨[]⟩
      (RecursiveNamedCatalogPreparedInitialization.store compiled) := by
    refine ⟨rfl, ?_, typed, ?_⟩
    · intro left right target impossible; simp at impossible
    · intro source target impossible; simp at impossible
  refine ⟨world, typed, heaps, ⟨⟨administrative, installed, cached.frame selected, canonical, captured, embedding, frame, ?_⟩⟩⟩
  intro header
  rw [canonical]
  exact CallableIndexedOwnedNamedHeaderReceipts.bootstrap_slot header

/-- Compatibility forgets only the retained whole-store/heap typing receipts;
the bootstrap capture is the same actual one produced above. -/
theorem of_selected {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {context : SourceSemantics.Context} {caller : Dynamic.EvidenceEnvironment}
    {traitName methodName : String} {requirements : List RequirementId}
    (selected : Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context caller traitName methodName
      requirements (sourceBody (compiled := compiled) (method := method)) dictionary)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    ∃ world, Nonempty (BootstrapCapture cached dictionary functions world) := by
  obtain ⟨world, _typed, _heaps, capture⟩ := of_selected_with_heap (registry := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry)
    cached dictionary functions accepted selected wellFormed
  exact ⟨world, capture⟩

/-- An actual bootstrap owner's complete location association identifies the
same canonical slots. Physical pool ownership alone cannot supply this map. -/
theorem BootstrapCapture.globals_for_owner {world : StoreTyping}
    (capture : BootstrapCapture cached dictionary functions world)
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (locations : ∀ header, header ∈ headers → owner.key.locations header =
      RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot) :
    CallableIndexedOwnedExpressionHeads.Globals (headers := headers) owner 0 [] capture.installed.canonical := by
  intro header member
  simpa only [List.length_nil, Nat.zero_add, locations header member] using capture.globals header

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodCaptureReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodPrincipal
/-! A selected implementation method has independent Source authority and an
emitted named compiler seed. The compiler's synthetic function does not assert
top-level FunctionInstantiates. Exact cached preparation authenticates the full
Source seed; the real selector retains the method body and dictionary. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodPrincipal
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallablePreparedMethodRuntimeMeaning

/-- The original complete method selector accompanies its genuine cached row.
The Source dictionary and caller context are retained without projection. -/
structure Principal (compiled : SourceCoreUnifiedCompilation.Compiled)
    (method : ExecutableImplMethods.CheckedMethod) where
  cached : CallablePreparedMethodSelection.Cached compiled method.specialized
  callerContext : SourceSemantics.Context
  callerEvidence : Dynamic.EvidenceEnvironment
  traitName : String
  methodName : String
  requirements : List RequirementId
  dictionary : Dynamic.EvidenceEnvironment
  selected : Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram)
    callerContext callerEvidence traitName methodName requirements
    (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram method) dictionary

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {method : ExecutableImplMethods.CheckedMethod}

/-- Construction keeps the actual Source selector and cached compiler row. -/
def of_selected
    (cached : CallablePreparedMethodSelection.Cached compiled method.specialized)
    {context : SourceSemantics.Context} {caller dictionary : Dynamic.EvidenceEnvironment}
    {traitName methodName : String} {requirements : List RequirementId}
    (selected : Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram)
      context caller traitName methodName requirements
      (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram method) dictionary) :
    Principal compiled method :=
  ⟨cached, context, caller, traitName, methodName, requirements, dictionary, selected⟩

abbrev Principal.named (principal : Principal compiled method) : SourceCoreGeneralFunctions.Function :=
  principal.cached.named

abbrev Principal.sourceBody (principal : Principal compiled method) : Dynamic.BodyInstance :=
  let _ := principal
  CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram method

abbrev Principal.sourceFunction (principal : Principal compiled method) : Dynamic.Closure :=
  methodFunction principal.cached.compilation principal.sourceBody principal.dictionary

/-- The same cached specialization fixes every Source node of the method. -/
theorem Principal.source_eq (principal : Principal compiled method) :
    CallableIndexedNamedGeneration.source principal.named = principal.sourceBody.source := by
  simp only [Principal.named, Principal.sourceBody, CallableIndexedNamedGeneration.source,
    principal.cached.same, CallableCoercionMethodInstantiation.bodyInstance]

/-- The full selector yields the genuine method frame, including its exact
dictionary, empty captures and emitted ordered statement roots. -/
theorem Principal.source_frame (principal : Principal compiled method) :
    CallableCoercionMethodFrame.Frame principal.sourceBody principal.sourceFunction :=
  principal.cached.frame principal.selected

/-- The actual Source authority is TraitMethodInstantiates. No ordinary named
function declaration is supplied by the synthetic compiler signature. -/
theorem Principal.source_instantiation (principal : Principal compiled method) :
    ∃ implementation methodSignature trait definition substitution,
      Dynamic.TraitMethodInstantiates (Program.ofChecked compiled.sourceProgram)
        implementation methodSignature trait definition substitution principal.sourceBody := by
  rcases principal with ⟨cached, context, caller, traitName, methodName, requirements, dictionary, selected⟩
  cases selected with
  | intro _ _ _ _ _ _ _ _ _ _ _ instantiated _ _ =>
    exact ⟨_, _, _, _, _, instantiated⟩

/-- The caller's real selector retains its complete callee evidence coverage. -/
theorem Principal.dictionary_covers (principal : Principal compiled method) :
    principal.dictionary.Covers principal.sourceBody.context :=
  principal.source_frame.covers

/-- Full cached preparation authenticates the exact specialization selected by
the accepted named hook, even when the original body is a trait method. -/
theorem Principal.record (principal : Principal compiled method) :
    SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan
      principal.named.signature.key = .ok principal.named.specialized :=
  CallableIndexedActualNamedSourceReceipts.cached_record compiled
    principal.cached.selected principal.cached.compilation.hook

/-- The emitted hook installs the complete compiler Source seed. Its physical
frame is supplied separately by the actual method parameter entry. -/
theorem Principal.hook_history (principal : Principal compiled method) :
    ∃ origin,
      compiled.indexed.ancestry.graph.inputs.callable.table.idAt?
        (.named principal.named.signature.key) = some origin ∧
      Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
        (SourceCoreCallableIndexedDispatch.namedFrame compiled.indexed.ancestry.graph.table origin)
        (.named origin) (some (CallableIndexedNamedGeneration.state principal.named)) ∧
      principal.cached.compilation.output = SourceCoreCallableIndexedFrames.withFrame
        (.var (compiled.indexed.base.globals.length + 1))
        (SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame
          (SourceCoreCallableIndexedDispatch.namedFrame compiled.indexed.ancestry.graph.table origin))
        principal.cached.compilation.parameterCode :=
  principal.cached.compilation.history principal.record

/-- The real hook's original named history agrees with that same full Source
seed. Neither native typing nor a generic stable-owner gate identifies it. -/
theorem Principal.history_source (principal : Principal compiled method)
    {origin : Word} {native : NativeFrame} {metadata : MetadataState}
    (selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt?
      (.named principal.named.signature.key) = some origin)
    (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      native (.named origin) (some metadata)) :
    Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      native (.named origin) (some (CallableIndexedNamedGeneration.state principal.named)) := by
  have generated := CallableIndexedNamedGeneration.seed compiled.indexed selected principal.record
  have authenticated := history.authenticates
  cases authenticated with
  | named actual =>
    have same : metadata = CallableIndexedNamedGeneration.state principal.named :=
      Option.some.inj (actual.symm.trans generated)
    exact same ▸ history

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodPrincipal
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaSourceReceipts
/-! A selected method retains its genuine trait authority and full dictionary.
Its emitted compiler principal supplies a factory-created lambda site without
an ordinary function Header. Exact plan preparation authenticates that site's
Source graph and original stage descriptor. Body support and runtime captures
remain separate receipts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaSourceReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)

/-- The same selected method has canonical compiler Source provenance. Its
independent Source authority remains the original method selector. -/
theorem source_receipt :
    LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
      principal.named.signature.key [] principal.sourceBody.source := by
  rw [← principal.source_eq]
  exact .original principal.record

/-- Original whole-program validity and genuine trait instantiation establish
occurrence uniqueness for this exact selected method graph. -/
theorem source_unique (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    NodeOccurrencesUnique principal.sourceBody.source := by
  obtain ⟨implementation, methodSignature, trait, definition, substitution, instantiated⟩ :=
    principal.source_instantiation
  obtain ⟨inputTypes, context, facts, certificate⟩ := instantiated.certificate wellFormed
  exact certificate.graph_closed.wellFormed.nodeOccurrencesUnique

variable {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {environment : Dynamic.Environment} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (site : CallableIndexedLambdaGeneration.Site compiled.indexed principal.named parameters result statements
    context evidence environment scope administrative)

/-- The actual factory site retains its complete source and empty cumulative
substitution; neither is inferred from native callable typing. -/
theorem site_provenance
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
      site.code.compilation.owner site.code.active
      (CallableIndexedLambdaGeneration.closure principal.named parameters result statements context evidence environment).source ∧
    NodeOccurrencesUnique
      (CallableIndexedLambdaGeneration.closure principal.named parameters result statements context evidence environment).source := by
  constructor
  · rw [site.compilation, site.active]
    exact .original principal.record
  · change NodeOccurrencesUnique (CallableIndexedNamedGeneration.source principal.named)
    rw [principal.source_eq]
    exact source_unique principal wellFormed

/-- The real selected hook supplies the site's entire carried compiler seed.
The dictionary and lexical generation inputs remain those in the site. -/
theorem site_history :
    ∃ hook, compiled.indexed.ancestry.graph.inputs.callable.table.idAt?
      (.named principal.named.signature.key) = some hook ∧
      ∃ history : History site.code,
        history.native = SourceCoreCallableIndexedDispatch.namedFrame compiled.indexed.ancestry.graph.table hook ∧
        history.ghost = .named hook ∧ history.metadata = CallableIndexedNamedGeneration.state principal.named := by
  exact site.history principal.cached.compilation principal.record

variable {mapping : LocationMap} {world : StoreTyping} {actual : Environment}
  (captured : Captures compiled.indexed mapping world scope environment actual)
  (actualSite : CallableIndexedLambdaGeneration.Site compiled.indexed principal.named parameters result statements
    context evidence environment scope captured.administrative)
  (history : History actualSite.code)

/-- Original table preparation authenticates the actual emitted descriptor
and the same full lambda Source. Captures and carried history stay explicit. -/
theorem origin_of_site
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    CallableLedger.OriginRep compiled.indexed.base.plan compiled.indexed.ancestry.graph.inputs.callable.table
      (.closure (CallableIndexedLambdaGeneration.closure principal.named parameters result statements context evidence environment))
      (CallableIndexedLambdaValues.value actualSite.code captured.embedding history.native actual) := by
  have prepared := RecursiveNamedPreparedStageContracts.of_compiled compiled
    compiled.indexed.ancestry.graph.inputs.callableSelected
  obtain ⟨source, unique⟩ := site_provenance principal actualSite wellFormed
  exact CompatibleAmbientStageOrigins.actual_lambda_origin prepared.accepted actualSite.code.descriptor
    source actualSite.code.viewOfSource unique actualSite.code.found
    (actualSite.code.form.trans actualSite.code.sourceForm) _

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaSourceReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaFrames
/-! A method's actual lambda site obtains its Source closure frame from the
original typed occurrence at the reached lexical context. The full selected
method dictionary and Source graph remain genuine; no ordinary Header or
native callable type supplies Source authority or body support. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaFrames
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaGeneration CallableIndexedOwnedMethodLambdaSourceReceipts

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {context : SourceSemantics.Context} {environment : Dynamic.Environment}
  {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (site : Site compiled.indexed principal.named parameters result statements context
    principal.dictionary environment scope administrative)

/-- Static Source facts at this actual site establish its complete closure
frame. The original method certificate provides graph uniqueness, and the
same raw lambda typing determines the original monomorphic body occurrence. -/
theorem closure_frame
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      context principal.sourceBody.source)
    (covers : principal.dictionary.Covers context)
    (typed : ExpressionHasType principal.sourceBody.source context site.code.id site.code.sourceNode.type) :
    Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram)
      (closure principal.named parameters result statements context principal.dictionary environment) := by
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      context (CallableIndexedNamedGeneration.source principal.named) := by
    simpa only [principal.source_eq] using runtime
  have typed : ExpressionHasType (CallableIndexedNamedGeneration.source principal.named)
      context site.code.id site.code.sourceNode.type := by
    simpa only [principal.source_eq] using typed
  have unique : NodeOccurrencesUnique (CallableIndexedNamedGeneration.source principal.named) := by
    simpa only [principal.source_eq] using source_unique principal wellFormed
  refine ⟨runtime.signatures, runtime.owner, ?_, runtime.requirements.idsUnique, covers⟩
  generalize selectedType : site.code.sourceNode.type = annotation at typed
  cases typed with
  | @intro _ _ node rawType plan contains formTyped rawEq _ _ _ =>
    have sameNode : node = site.code.sourceNode := Option.some.inj
      ((lookupExpression?_complete unique contains).symm.trans site.code.sourceFound)
    subst node
    rw [site.code.sourceForm] at formTyped
    cases formTyped with
    | lambda names extended body completes =>
      have bodyTypes := Dynamic.MonoBindersExtend.bodyTypes_eq extended
      change parameters.map (fun binder => binder.scheme.body) = _ at bodyTypes
      exact {
        owner := runtime.owner
        closed := runtime.closed
        variables_closed := runtime.variables_closed
        residual_variables_open := runtime.residual_variables_open
        graph := runtime.graph
        requirement_ledger := runtime.requirements
        occurrence := ⟨site.code.id, site.code.sourceNode, lookupExpression?_sound site.code.sourceFound,
          site.code.sourceForm, by simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq extended] using rawEq,
          by rw [site.code.sourceForm]
             simpa only [closure, bodyTypes] using
               (ExpressionFormHasRawType.lambda names extended body completes)⟩ }

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaFrames
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaSupport
/-! Header-free static support retains a genuine method principal and the
same actual lambda Code. The complete generic body Tree, sites, context,
Source frame and dictionary remain static receipts. Original Header-ranked
support and its public interfaces stay separate and unchanged. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}

/-- This alternative stores genuine trait Source authority beside the emitted
compiler seed; it contains no body execution law. -/
structure Support (code : Code compiled.indexed function scope administrative)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) where
  method : ExecutableImplMethods.CheckedMethod
  principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method
  expressionSyntax : TypedSource → ExpressionId → Prop
  certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate
  source : function.source = CallableIndexedNamedGeneration.source principal.named
  compilation : code.compilation = CallableIndexedNamedGeneration.context compiled.indexed principal.named
  active : code.active = []
  body : CallableIndexedLambdaStaticBodySupport.BodyWith (values := .initial compiled.compatible.checked) expressionSyntax certificates
    code (Program.ofChecked compiled.sourceProgram) registry faults

variable {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {context : SourceSemantics.Context} {environment : Dynamic.Environment}
  (site : CallableIndexedLambdaGeneration.Site compiled.indexed principal.named parameters result statements
    context principal.dictionary environment scope administrative)

/-- Actual factory Code and original static body fields construct support.
The Source frame is established from the genuine method occurrence. -/
def Support.of_site {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context principal.sourceBody.source)
    (covers : principal.dictionary.Covers context)
    (typed : ExpressionHasType principal.sourceBody.source context site.code.id site.code.sourceNode.type)
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    (certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (body : CallableIndexedLambdaStaticBodySupport.BodyWith (values := .initial compiled.compatible.checked) expressionSyntax certificates
      site.code (Program.ofChecked compiled.sourceProgram) registry faults) :
    Support site.code registry faults :=
  ⟨method, principal, expressionSyntax, certificates, rfl, site.compilation, site.active,
    { body with frame := CallableIndexedOwnedMethodLambdaFrames.closure_frame principal site wellFormed runtime covers typed }⟩

variable {code : Code compiled.indexed function scope administrative}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (support : Support code registry faults)

include support in
/-- Source attribution is derived from the actual cached method record. -/
theorem Support.source_receipt :
    LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
      code.compilation.owner code.active function.source := by
  rw [support.compilation, support.active, support.source]
  exact .original support.principal.record

include support in
/-- The original static body retains uniqueness of this complete Source. -/
theorem Support.unique : NodeOccurrencesUnique function.source := support.body.unique

/-- Captured history retains the full genuine method compiler seed. -/
structure SourceOrigin (history : History code) : Prop where
  metadata : history.metadata = CallableIndexedNamedGeneration.state support.principal.named

/-- The genuine selected factory hook constructs this complete Source seed. -/
theorem Support.of_site_origin
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context principal.sourceBody.source)
    (covers : principal.dictionary.Covers context)
    (typed : ExpressionHasType principal.sourceBody.source context site.code.id site.code.sourceNode.type)
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    (certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (body : CallableIndexedLambdaStaticBodySupport.BodyWith (values := .initial compiled.compatible.checked) expressionSyntax certificates
      site.code (Program.ofChecked compiled.sourceProgram) registry faults)
    {hook : Word}
    (selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt?
      (.named principal.named.signature.key) = some hook) :
    SourceOrigin (Support.of_site principal site wellFormed runtime covers typed expressionSyntax certificates body)
      (site.historyAt selected principal.record) := ⟨rfl⟩

/-- The original stage descriptor authenticates the same actual lambda payload.
Source attribution is derived from support; captures and history remain real. -/
theorem Support.stage_origin {mapping : LocationMap} {world : StoreTyping} {actual : Environment}
    (captured : Captures compiled.indexed mapping world scope function.captured actual)
    (actualCode : Code compiled.indexed function scope captured.administrative)
    (actualSupport : Support actualCode registry faults) (history : History actualCode) :
    CallableLedger.OriginRep compiled.indexed.base.plan compiled.indexed.ancestry.graph.inputs.callable.table
      (.closure function) (value actualCode captured.embedding history.native actual) := by
  have prepared := RecursiveNamedPreparedStageContracts.of_compiled compiled
    compiled.indexed.ancestry.graph.inputs.callableSelected
  exact CompatibleAmbientStageOrigins.actual_lambda_origin prepared.accepted actualCode.descriptor
    actualSupport.source_receipt actualCode.viewOfSource actualSupport.unique actualCode.found
    (actualCode.form.trans actualCode.sourceForm) _

/-- Generic same-Code static body fields project to the shared body kernel.
No ordinary Header or function instantiation is introduced. -/
def Support.origin (escaped : faults .controlEscapedFunction code.compilation.internalReason) :
    CallableRuntimeBodyOrigins.StaticOrigin (.initial compiled.compatible.checked)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed) registry faults where
  layouts := compiled.indexed.layouts
  owner := code.compilation.owner
  active := code.active
  frameLayout := compiled.indexed.ancestry.layout.frame
  globals := compiled.indexed.base.globals.length
  onError := code.allocationError
  function := function
  expressionSyntax := support.expressionSyntax function.source
  certificates := support.certificates support.body.readFuel function.source
  validity := fun context => CompatibleRuntimeContextValidity.Valid code.compilation.solvedRequirements context function.evidence
  diagnosticPolicy := .reachable
  administrative := administrative
  context := support.body.context
  scope := code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope
  output := code.receipt.resultCore
  code := code.receipt.body
  fellThrough := code.compilation.internalReason
  escaped := code.compilation.internalReason
  solved := code.compilation.solvedRequirements
  body := { flow := support.body.flow
            tree := support.body.tree
            sites := support.body.sites
            initialValid := support.body.valid
            projection := support.body.projection
            unique := support.body.unique
            emitted := support.body.emitted }
  definitions := rfl
  registered := CallableIndexedAmbient.frame_registered compiled.indexed
  escapedFault := escaped
  extend := fun valid extended => valid.extend extended
  runtimeOf := fun valid => valid

/-- The actual static parameter context, full Source frame and emitted body
remain definitionally those of this same Code. -/
def Support.body_origin (escaped : faults .controlEscapedFunction code.compilation.internalReason) :
    CallableIndexedOwnedLambdaInvocationBounds.BodyOrigin (program := Program.ofChecked compiled.sourceProgram)
      code support.body.toContext registry faults :=
  ⟨support.origin escaped, support.body.frame, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaValues
/-! The original owned function relation is retained as one constructor.
A separate method-lambda constructor stores its authentic Header-free body
support, full Source seed, captures and immutable key. Forgetting only these
extra receipts reaches the existing low indexed function model. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaValues
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleEquality
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedMethodLambdaSupport (Support SourceOrigin)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}

/-- Method support is an explicit alternative to the unchanged original
Header-ranked support. Every lambda still retains full static body receipts. -/
inductive Represents (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping) : TypeSystem.Ty → Dynamic.Value → Value → Ty → Prop where
  | prior {sourceType source native type}
      (related : CallableIndexedOwnedFunctionValues.Represents headers keys registry faults mapping world sourceType source native type) :
      Represents headers keys registry faults mapping world sourceType source native type
  | method_lambda {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment} {callerPrefix : Nat}
      (owner : OwnedKey keys) (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code)
      (body : Support code registry faults) (origin : SourceOrigin body history)
      (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations callerPrefix scope captured.canonical owner.key.frameLocation)
      (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) compiled.indexed.layouts.definitions) :
      Represents headers keys registry faults mapping world (FunctionValues.sourceType function) (.closure function)
        (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)

theorem Represents.forget {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {native : Value} {type : Ty}
    (related : Represents headers keys registry faults mapping world sourceType source native type) :
    CallableIndexedLambdaValues.Represents compiled.indexed mapping world sourceType source native type := by
  cases related with
  | prior original => exact original.forget
  | method_lambda owner captured code history body origin globals referenceIndex typed =>
    exact .lambda captured code history typed

def model (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed) where
  Represents := fun _ mapping world => Represents headers keys bodyRegistry faults mapping world
  projection := fun related => (CallableIndexedLambdaValues.model compiled.indexed profile).projection
    (registry := bodyRegistry) related.forget
  runtime_hasType := fun related => (CallableIndexedLambdaValues.model compiled.indexed profile).runtime_hasType
    (registry := bodyRegistry) related.forget
  source_function := fun related => (CallableIndexedLambdaValues.model compiled.indexed profile).source_function
    (registry := bodyRegistry) related.forget
  extend := by
    intro registry futureRegistry mapping futureMap world futureWorld sourceType source native type related registries maps worlds
    cases related with
    | prior original => exact .prior ((CallableIndexedOwnedFunctionValues.model headers keys bodyRegistry faults profile).extend
        original registries maps worlds)
    | method_lambda owner captured code history body origin globals referenceIndex typed =>
      exact .method_lambda owner (captured.extend maps worlds) code history body origin globals referenceIndex (typed.weaken worlds)

theorem observations (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    FunctionObservations compiled.compatible.checked.catalog (model headers keys bodyRegistry faults profile)
      (CallableIndexedLambdaValues.Identity compiled.indexed) := by
  intro registry mapping world sourceType source native type related
  exact CallableIndexedLambdaValues.observations compiled.indexed profile (registry := registry) related.forget

theorem runtime_views (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    FunctionRuntimeViews (model headers keys bodyRegistry faults profile) := by
  intro registry mapping world parameter result source native type related
  exact CallableIndexedLambdaValues.runtime_views compiled.indexed profile (registry := registry) related.forget

/-- The complete original owned relation embeds without altering its payload. -/
theorem includes_original (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    (CallableIndexedOwnedFunctionValues.model headers keys bodyRegistry faults profile).Includes
      (model headers keys bodyRegistry faults profile) := fun related => .prior related

/-- Explicit domain embeddings retain the full immutable method-lambda key. -/
theorem Represents.map_keys {keys futureKeys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {native : Value} {type : Ty}
    (embedding : CallableIndexedOwnedFunctionValues.KeyEmbedding keys futureKeys)
    (related : Represents headers keys registry faults mapping world sourceType source native type) :
    Represents headers futureKeys registry faults mapping world sourceType source native type := by
  cases related with
  | prior original => exact .prior (original.map_keys embedding)
  | @method_lambda function scope actual callerPrefix owner captured code history body origin globals referenceIndex typed =>
    have actualGlobals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers (embedding.map owner).key.locations callerPrefix scope captured.canonical (embedding.map owner).key.frameLocation := by
      rw [embedding.same owner]
      exact globals
    exact .method_lambda (embedding.map owner) captured code history body origin actualGlobals referenceIndex typed

theorem includes {keys futureKeys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
    (embedding : CallableIndexedOwnedFunctionValues.KeyEmbedding keys futureKeys)
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    (model headers keys bodyRegistry faults profile).Includes (model headers futureKeys bodyRegistry faults profile) :=
  fun related => related.map_keys embedding

/-- The new constructor supplies the complete same-Code method receipt.
Existing closures retain their original complete owned representation. -/
theorem Represents.closure_cases {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {function : Dynamic.Closure} {native : Value} {type : Ty}
    (related : Represents headers keys registry faults mapping world sourceType (.closure function) native type) :
    CallableIndexedOwnedFunctionValues.Represents headers keys registry faults mapping world sourceType (.closure function) native type ∨
    ∃ owner : OwnedKey keys, ∃ scope actual callerPrefix,
      ∃ (captured : Captures compiled.indexed mapping world scope function.captured actual)
        (code : Code compiled.indexed function scope captured.administrative) (history : History code)
        (body : Support code registry faults),
        SourceOrigin body history ∧
        CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
          (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
          headers owner.key.locations callerPrefix scope captured.canonical owner.key.frameLocation ∧
        code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length ∧
        sourceType = FunctionValues.sourceType function ∧ native = value code captured.embedding history.native actual ∧
        type = CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore ∧
        RuntimeValueHasType world (value code captured.embedding history.native actual)
          (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) compiled.indexed.layouts.definitions := by
  cases related with
  | prior original => exact Or.inl original
  | method_lambda owner captured code history body origin globals referenceIndex typed =>
    exact Or.inr ⟨owner, _, _, _, captured, code, history, body, origin, globals, referenceIndex, rfl, rfl, rfl, typed⟩

/-- Recapture keeps the method support of the same code. -/
def recaptureSupport {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {code : Code compiled.indexed function scope administrative}
    (support : Support code registry faults) (environment : Dynamic.Environment) :
    Support (code.recapture environment) registry faults :=
  { support with
    body := RecursiveNamedLambdaFormationHeads.recaptureBodyWith (values := .initial compiled.compatible.checked)
      code support.body environment }

/-- Recapture keeps the full Source seed of the same history. -/
theorem recaptureOrigin {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {code : Code compiled.indexed function scope administrative} {history : History code}
    {support : Support code registry faults}
    (origin : SourceOrigin support history) (environment : Dynamic.Environment) :
    SourceOrigin (recaptureSupport support environment) (history.recapture environment) :=
  ⟨origin.metadata⟩

/-- Genuine method-site formation reads the existing physical frame and
retains its actual full owned row. The value copies its captured cells, and
the copies keep the catalog slots and the frame cell. -/
theorem method_lambda_of_formation
    {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
    {bodyRegistry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment} {callerPrefix : Nat}
    (pool : CallableIndexedAuthorityPool.Pool (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers keys mapping world heap store)
    (owner : OwnedKey keys) (captured : Captures compiled.indexed mapping world scope function.captured actual)
    (code : Code compiled.indexed function scope captured.administrative) (history : History code)
    (body : Support code bodyRegistry faults) (origin : SourceOrigin body history)
    (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
      headers owner.key.locations callerPrefix scope captured.canonical owner.key.frameLocation)
    (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
    (current : (pool.rows owner.position).authority.current = history.native)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) projects
      compiled.indexed.layouts.definitions}
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (copied : code.policy.snapshotLambda code.id = true)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed model captured code history heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding)
        (.inRight .word (value code formed.embedding history.native formed.closureActual)) formed.finalStore ∧
      Represents headers keys bodyRegistry faults formed.finalMap formed.finalWorld (FunctionValues.sourceType function)
        (.closure formed.closure) (value code formed.embedding history.native formed.closureActual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (value code formed.embedding history.native formed.closureActual) ∧
          finalStore = formed.finalStore) := by
  have reference : captured.canonical[code.referenceIndex]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
    rw [referenceIndex]
    exact globals.reference
  have read : store.read? owner.key.frameLocation =
      some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame history.native) := by
    have actualRead := (pool.rows owner.position).authority.frame.read
    rw [(pool.rows owner.position).frame_eq, current] at actualRead
    exact actualRead
  obtain ⟨formed⟩ := CallableIndexedLambdaValues.formation captured code history copied referenceIndex heaps reference read
  have typed := (CallableIndexedLambdaValues.model compiled.indexed profile).runtime_hasType
    (registry := bodyRegistry) (formed.represents heaps.runtime_hasTypes)
  exact ⟨formed, formed.source _ ordinary coercions, formed.evaluated,
    .method_lambda (function := formed.closure) owner formed.captures formed.closureCode formed.closureHistory
      (recaptureSupport body formed.captured) (recaptureOrigin origin formed.captured) (globals.of_slots formed.slots)
      referenceIndex typed,
    fun _ _ completed => Core.evaluation_deterministic completed formed.evaluated⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaValues
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodReadyContinuations
/-! The genuine selected method keeps its complete trait dictionary and
synthetic Source frame. Actual hook and parameter receipts establish admission
at the same reached pool before the shared family's strict body child. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodReadyContinuations
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallablePreparedMethodRuntimeMeaning
open CallableIndexedOwnedMethodInvocationBounds
open CallableIndexedOwnedParameterReadyContinuations (bridge)
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedOwnedBodySourceOrigin (source_origin)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {method : ExecutableImplMethods.CheckedMethod}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {expressionSyntax : ExpressionId → Prop} {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {validity : SourceSemantics.Context → Prop} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (profile : CallablePreparedMethodCatalogHookMeaning.ProfileFor principal.cached.compilation (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) principal.sourceBody principal.dictionary administrative registry faults
    expressionSyntax certificates validity diagnosticPolicy)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (escaped : faults .controlEscapedFunction principal.cached.compilation.own.table.escapedReason)
  (extend : ∀ {context next binder}, validity context → BinderExtends principal.sourceBody.source.owner context binder next → validity next)
  (runtimeOf : ∀ {context}, validity context →
    CompatibleRuntimeContextValidity.Valid principal.named.specialized.function.solvedRequirements context principal.dictionary)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
  (installed : Installed principal.cached.compilation (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (sourceBody := principal.sourceBody)
    (administrative := administrative) functions mapping world before store callerEnvironment)
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)

  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (beforeTyped : Dynamic.HeapWellTyped principal.sourceFunction.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes principal.sourceFunction.context before arguments profile.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)

include wellFormed beforeTyped argumentsTyped stable in
/-- Authentic Source method selection and the actual hook/parameter allocation
supply this complete admitted entry without inventing a top-level Header. -/
def source_admitted_entry {hook : Word} {index : Int} {metadata : MetadataState}
    (selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt?
      (.named principal.named.signature.key) = some hook)
    (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (.state index) (.named hook) (some metadata))
    {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
    (entry : ParameterEntry compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      owner.key.frameLocation (.state index) (.initial compiled.compatible.checked) functions registry
      principal.sourceFunction profile.context principal.named.inputs arguments before
      (store.set owner.key.frameLocation (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
      administrative actualContext actual ξ principal.cached.compilation.parameterCode principal.cached.compilation.body)
    (reached : State headers keys ⟨principal.named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    CallableIndexedOwnedAdmittedBodyEntries.Entry (bridge (headers := headers) (keys := keys))
      (condition := CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (origin := origin principal.cached.compilation profile escaped extend runtimeOf) (functions := functions) := by
  let original := parameter_entry_origin principal.cached.compilation profile functions escaped extend runtimeOf
    entry reached (CallableIndexedOwnedAllocationProducer.stableOwner_selected owner.position history)
  have source : CallableIndexedOwnedAdmittedBodyEntries.SourceReceipt (Program.ofChecked compiled.sourceProgram)
      (origin principal.cached.compilation profile escaped extend runtimeOf).function
      (origin principal.cached.compilation profile escaped extend runtimeOf).context original.environment original.heap := by
    change CallableIndexedOwnedAdmittedBodyEntries.SourceReceipt (Program.ofChecked compiled.sourceProgram)
      principal.sourceFunction profile.context entry.environment entry.heap
    exact CallableIndexedOwnedAdmittedBodyEntries.SourceReceipt.of_method wellFormed principal.selected principal.source_frame
      profile.extended entry.allocation beforeTyped argumentsTyped
  exact CallableIndexedOwnedAdmittedBodyEntries.Entry.of_parameters
    (bridge (headers := headers) (keys := keys)) original source caller stable owner.position
    (principal.history_source selected history) entry.frame

include wellFormed beforeTyped argumentsTyped stable in
/-- Native Prefix receipts retain their actual Source allocation, independent
body grade and the same carried hook at the exact reached pool. -/
def native_admitted_entry {hook : Word} {index : Int} {metadata : MetadataState}
    (selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt?
      (.named principal.named.signature.key) = some hook)
    (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (.state index) (.named hook) (some metadata))
    {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
    {prefixSize : Nat} {value : Value} {bodyStore : Store}
    (entry : CallablePreparedMethodRuntimeMeaning.Prefix compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      owner.key.frameLocation (.state index) (.initial compiled.compatible.checked) functions registry
      principal.sourceFunction profile.context principal.named.inputs arguments before
      (store.set owner.key.frameLocation (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
      administrative actualContext actual ξ principal.cached.compilation.parameterCode principal.cached.compilation.body prefixSize value bodyStore)
    (reached : State headers keys ⟨principal.named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    CallableIndexedOwnedAdmittedBodyEntries.Entry (bridge (headers := headers) (keys := keys))
      (condition := CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (origin := origin principal.cached.compilation profile escaped extend runtimeOf) (functions := functions) := by
  let original := prefix_entry_origin principal.cached.compilation profile functions escaped extend runtimeOf
    entry reached (CallableIndexedOwnedAllocationProducer.stableOwner_selected owner.position history)
  have source : CallableIndexedOwnedAdmittedBodyEntries.SourceReceipt (Program.ofChecked compiled.sourceProgram)
      (origin principal.cached.compilation profile escaped extend runtimeOf).function
      (origin principal.cached.compilation profile escaped extend runtimeOf).context original.environment original.heap := by
    change CallableIndexedOwnedAdmittedBodyEntries.SourceReceipt (Program.ofChecked compiled.sourceProgram)
      principal.sourceFunction profile.context entry.environment entry.heap
    exact CallableIndexedOwnedAdmittedBodyEntries.SourceReceipt.of_method wellFormed principal.selected principal.source_frame
      profile.extended entry.allocation beforeTyped argumentsTyped
  exact CallableIndexedOwnedAdmittedBodyEntries.Entry.of_parameters
    (bridge (headers := headers) (keys := keys)) original source caller stable owner.position
    (principal.history_source selected history) entry.frame

/-- The complete original method parameter entry and its pool are unchanged. -/
theorem source_original {hook : Word} {index : Int} {metadata : MetadataState}
    (selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt?
      (.named principal.named.signature.key) = some hook)
    (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (.state index) (.named hook) (some metadata))
    {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
    (entry : ParameterEntry compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      owner.key.frameLocation (.state index) (.initial compiled.compatible.checked) functions registry
      principal.sourceFunction profile.context principal.named.inputs arguments before
      (store.set owner.key.frameLocation (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
      administrative actualContext actual ξ principal.cached.compilation.parameterCode principal.cached.compilation.body)
    (reached : State headers keys ⟨principal.named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    (source_admitted_entry principal profile functions escaped extend runtimeOf owner caller wellFormed
      beforeTyped argumentsTyped stable selected history entry reached).original =
      parameter_entry_origin principal.cached.compilation profile functions escaped extend runtimeOf
        entry reached (CallableIndexedOwnedAllocationProducer.stableOwner_selected owner.position history) := rfl

/-- The complete original method parameter entry and its pool are unchanged. -/
theorem native_original {hook : Word} {index : Int} {metadata : MetadataState}
    (selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt?
      (.named principal.named.signature.key) = some hook)
    (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (.state index) (.named hook) (some metadata))
    {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
    {prefixSize : Nat} {value : Value} {bodyStore : Store}
    (entry : CallablePreparedMethodRuntimeMeaning.Prefix compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      owner.key.frameLocation (.state index) (.initial compiled.compatible.checked) functions registry
      principal.sourceFunction profile.context principal.named.inputs arguments before
      (store.set owner.key.frameLocation (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
      administrative actualContext actual ξ principal.cached.compilation.parameterCode principal.cached.compilation.body prefixSize value bodyStore)
    (reached : State headers keys ⟨principal.named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    (native_admitted_entry principal profile functions escaped extend runtimeOf owner caller wellFormed
      beforeTyped argumentsTyped stable selected history entry reached).original =
      prefix_entry_origin principal.cached.compilation profile functions escaped extend runtimeOf
        entry reached (CallableIndexedOwnedAllocationProducer.stableOwner_selected owner.position history) := rfl

variable (syntaxTree : GenericImperativeMatch.Syntax principal.sourceFunction.source expressionSyntax profile.context
    (.statements true principal.sourceFunction.body) principal.sourceFunction.resultType)
  {ι : Type} (origins : ι → CallableRuntimeBodyOrigins.StaticOrigin (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) registry faults)

include wellFormed beforeTyped argumentsTyped stable syntaxTree in
/-- The full actual hook/parameter packet selects its exact shared-family
origin; the callback uses only the strictly smaller body IH. -/
theorem source_continuation (budget : Nat)
    (selection : ∀ (hook : Word) (index : Int) (metadata : MetadataState)
      (selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt?
        (.named principal.named.signature.key) = some hook)
      (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
        (.state index) (.named hook) (some metadata))
      (_emitted : principal.cached.compilation.output = SourceCoreCallableIndexedFrames.withFrame
        (.var (compiled.indexed.base.globals.length + 1))
        (SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index))
        principal.cached.compilation.parameterCode)
      {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
      (entry : ParameterEntry compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      owner.key.frameLocation (.state index) (.initial compiled.compatible.checked) functions registry
      principal.sourceFunction profile.context principal.named.inputs arguments before
      (store.set owner.key.frameLocation (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
      administrative actualContext actual ξ principal.cached.compilation.parameterCode principal.cached.compilation.body)
      (added : Environment) (_length : added.length = principal.named.inputs.length)
      (_spine : entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical)
      (reached : State headers keys ⟨principal.named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) (_related : Relates caller reached),
      { i : ι // origins i = source_origin (origin principal.cached.compilation profile escaped extend runtimeOf)
        (source_admitted_entry principal profile functions escaped extend runtimeOf owner caller wellFormed
          beforeTyped argumentsTyped stable selected history entry reached).source.runtime })
    (below : RecursiveNamedCatalogInvocationBounds.Below budget (fun child => ∀ i,
      CallableRuntimeBodyReadyOrigins.PreservesAt (protocol headers keys)
        (readiness (bridge (headers := headers) (keys := keys))) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
        (ProtectedStateImperativeTypedSourceSites.Facts (origins i).function.source (origins i).expressionSyntax)
        functions (Program.ofChecked compiled.sourceProgram) (origins i) child)) :
    SourceContinuationWithHistory (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys)
      (arguments := arguments) (payloads := payloads) (owner := owner) (caller := caller)
      principal.cached.compilation profile functions escaped extend runtimeOf installed budget := by
  intro hook index metadata selected history emitted entry added length spine reached related
  let selectedOrigin := selection hook index metadata selected history emitted entry added length spine reached related
  exact CallableIndexedOwnedParameterReadyContinuations.source_at
    (source_admitted_entry principal profile functions escaped extend runtimeOf owner caller wellFormed
      beforeTyped argumentsTyped stable selected history entry reached)
    wellFormed syntaxTree origins selectedOrigin.val selectedOrigin.property budget below

include wellFormed beforeTyped argumentsTyped stable syntaxTree in
/-- The full actual hook/parameter packet selects its exact shared-family
origin; the callback uses only the strictly smaller body IH. -/
theorem native_continuation (budget : Nat)
    (selection : ∀ (hook : Word) (index : Int) (metadata : MetadataState)
      (selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt?
        (.named principal.named.signature.key) = some hook)
      (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
        (.state index) (.named hook) (some metadata))
      {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
      {prefixSize : Nat} {value : Value} {bodyStore : Store}
      (entry : CallablePreparedMethodRuntimeMeaning.Prefix compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      owner.key.frameLocation (.state index) (.initial compiled.compatible.checked) functions registry
      principal.sourceFunction profile.context principal.named.inputs arguments before
      (store.set owner.key.frameLocation (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
      administrative actualContext actual ξ principal.cached.compilation.parameterCode principal.cached.compilation.body prefixSize value bodyStore)
      (added : Environment) (_length : added.length = principal.named.inputs.length)
      (_spine : entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical)
      (reached : State headers keys ⟨principal.named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) (_related : Relates caller reached),
      { i : ι // origins i = source_origin (origin principal.cached.compilation profile escaped extend runtimeOf)
        (native_admitted_entry principal profile functions escaped extend runtimeOf owner caller wellFormed
          beforeTyped argumentsTyped stable selected history entry reached).source.runtime })
    (below : RecursiveNamedCatalogInvocationBounds.Below budget (fun child => ∀ i,
      CallableRuntimeBodyReadyOrigins.ReflectsAt (protocol headers keys)
        (readiness (bridge (headers := headers) (keys := keys))) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
        (ProtectedStateImperativeTypedSourceSites.Facts (origins i).function.source (origins i).expressionSyntax)
        functions (Program.ofChecked compiled.sourceProgram) (origins i) child)) :
    NativeContinuationWithHistory (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys)
      (arguments := arguments) (payloads := payloads) (owner := owner) (caller := caller)
      principal.cached.compilation profile functions escaped extend runtimeOf installed budget := by
  intro hook index metadata _prefixSize _bodyStore selected history _prefixWithin _value _finalStore
    _restored entry added length spine reached related
  let selectedOrigin := selection hook index metadata selected history entry added length spine reached related
  exact CallableIndexedOwnedParameterReadyContinuations.native_at
    (native_admitted_entry principal profile functions escaped extend runtimeOf owner caller wellFormed
      beforeTyped argumentsTyped stable selected history entry reached)
    wellFormed syntaxTree origins selectedOrigin.val selectedOrigin.property budget below

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodReadyContinuations
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodCanonicalEntries
/-! The actual installed method capture and real ordered parameter spine
supply canonical slots at the original body entry. Only the slot proof wrapper
is forgotten at the same actual returned pool. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodCanonicalEntries
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallablePreparedMethodRuntimeMeaning
open CallableIndexedOwnedExpressionHeads CallableIndexedOwnedMethodInvocationBounds
open RecursiveNamedCatalogInvocationBounds (Below)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}

variable {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
  {code : Expr} (generation : CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics code)
  {sourceBody : Dynamic.BodyInstance} {dictionary : Dynamic.EvidenceEnvironment}
  {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {expressionSyntax : ExpressionId → Prop} {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {validity : SourceSemantics.Context → Prop} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (profile : CallablePreparedMethodCatalogHookMeaning.ProfileFor generation (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) sourceBody dictionary administrative registry faults
    expressionSyntax certificates validity diagnosticPolicy)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (escaped : faults .controlEscapedFunction generation.own.table.escapedReason)
  (extend : ∀ {context next binder}, validity context → BinderExtends sourceBody.source.owner context binder next → validity next)
  (runtimeOf : ∀ {context}, validity context →
    CompatibleRuntimeContextValidity.Valid named.specialized.function.solvedRequirements context dictionary)

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
  (installed : Installed generation (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (sourceBody := sourceBody) (administrative := administrative)
    functions mapping world before store callerEnvironment)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)

variable (callerPrefix : Nat)
  (observed : Globals (headers := headers) owner callerPrefix [] installed.canonical)

include observed in
/-- The argument bundle occupies one administrative slot. Actual ordered
parameter additions account for every remaining slot shift. -/
theorem globals_after_prefix {canonical : Environment} (added : Environment)
    (length : added.length = named.inputs.length)
    (spine : canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical) :
    Globals (headers := headers) owner (callerPrefix + 1)
      (named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))) canonical := by
  intro header member
  rw [spine]
  simp only [List.length_map, List.length_reverse]
  have index : named.inputs.length + (callerPrefix + 1) + header.slot =
      added.length + (callerPrefix + header.slot + 1) := by omega
  rw [index, List.getElem?_append_right (by omega)]
  have slot : callerPrefix + header.slot + 1 = Nat.succ (callerPrefix + header.slot) := by omega
  simp only [Nat.add_sub_cancel_left]
  rw [slot, Nat.succ_eq_add_one, List.getElem?_cons_succ]
  simpa using observed header member

include observed in
/-- Every dynamic field and the reached pool come from the actual source parameter receipt. -/
def source_entry {initialStore : Store} {location : Location} {native : NativeFrame}
    {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
    (entry : ParameterEntry compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      location native (.initial compiled.compatible.checked) functions registry
      (methodFunction generation sourceBody dictionary) profile.context named.inputs arguments before initialStore mapping world
      administrative actualContext actual ξ generation.parameterCode generation.body)
    (added : Environment) (length : added.length = named.inputs.length)
    (spine : entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical)
    (reached : State headers keys ⟨named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
    (gate : CallableIndexedOwnedAllocationProducer.StableOwner keys location native) :
    CallableRuntimeBodyOrigins.Stateful.Entry (argumentProtocol (headers := headers) owner (callerPrefix + 1))
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) (origin generation profile escaped extend runtimeOf) functions :=
  CallableIndexedOwnedBodyCanonicalEntries.wrap functions owner (callerPrefix + 1)
    (parameter_entry_origin generation profile functions escaped extend runtimeOf entry reached gate)
    (globals_after_prefix (generation := generation) (functions := functions)
      (installed := installed) (owner := owner) (callerPrefix := callerPrefix)
      (observed := observed) (added := added) (length := length) (spine := spine))

/-- The shared strict family is requested only at this authentic parameter
entry; its underlying actual pool is returned verbatim. -/
theorem source_continuation_of_canonical (budget : Nat)
    (meaning : ∀ {initialStore : Store} {location : Location} {native : NativeFrame}
    {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
      (entry : ParameterEntry compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      location native (.initial compiled.compatible.checked) functions registry
      (methodFunction generation sourceBody dictionary) profile.context named.inputs arguments before initialStore mapping world
      administrative actualContext actual ξ generation.parameterCode generation.body)
      (added : Environment) (length : added.length = named.inputs.length)
    (spine : entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical)
    (reached : State headers keys ⟨named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
    (gate : CallableIndexedOwnedAllocationProducer.StableOwner keys location native),
      Below budget (CallableRuntimeBodyEntryContracts.PreservesAt
        (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (protocol := argumentProtocol (headers := headers) owner (callerPrefix + 1))
        (conditionGate := CallableIndexedOwnedAllocationProducer.StableOwner keys)
        functions program (source_entry (generation := generation) (profile := profile) (functions := functions)
        (escaped := escaped) (extend := extend) (runtimeOf := runtimeOf) (installed := installed)
        (owner := owner) (callerPrefix := callerPrefix) (observed := observed)
        (entry := entry) (added := added) (length := length) (spine := spine) (reached := reached) (gate := gate)))) :
    SourceContinuation (program := program) (headers := headers) (keys := keys)
      (arguments := arguments) (payloads := payloads)
      generation profile functions escaped extend runtimeOf installed budget := by
  intro initialStore location native actualContext actual ξ entry added length spine reached gate child strict
  exact CallableIndexedOwnedBodyCanonicalEntries.preserves_of_canonical functions owner (callerPrefix + 1)
    (parameter_entry_origin generation profile functions escaped extend runtimeOf entry reached gate)
    _ (meaning entry added length spine reached gate child strict)

include observed in
/-- Every dynamic field and the reached pool come from the actual native parameter receipt. -/
def native_entry {initialStore : Store} {location : Location} {native : NativeFrame}
    {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
    {size : Nat} {value : Value} {finalStore : Store}
    (entry : Prefix compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      location native (.initial compiled.compatible.checked) functions registry
      (methodFunction generation sourceBody dictionary) profile.context named.inputs arguments before initialStore mapping world
      administrative actualContext actual ξ generation.parameterCode generation.body size value finalStore)
    (added : Environment) (length : added.length = named.inputs.length)
    (spine : entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical)
    (reached : State headers keys ⟨named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
    (gate : CallableIndexedOwnedAllocationProducer.StableOwner keys location native) :
    CallableRuntimeBodyOrigins.Stateful.Entry (argumentProtocol (headers := headers) owner (callerPrefix + 1))
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) (origin generation profile escaped extend runtimeOf) functions :=
  CallableIndexedOwnedBodyCanonicalEntries.wrap functions owner (callerPrefix + 1)
    (prefix_entry_origin generation profile functions escaped extend runtimeOf entry reached gate)
    (globals_after_prefix (generation := generation) (functions := functions)
      (installed := installed) (owner := owner) (callerPrefix := callerPrefix)
      (observed := observed) (added := added) (length := length) (spine := spine))

/-- The shared strict family is requested only at this authentic parameter
entry; its underlying actual pool is returned verbatim. -/
theorem native_continuation_of_canonical (budget : Nat)
    (meaning : ∀ {initialStore : Store} {location : Location} {native : NativeFrame}
    {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
    {size : Nat} {value : Value} {finalStore : Store}
      (entry : Prefix compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      location native (.initial compiled.compatible.checked) functions registry
      (methodFunction generation sourceBody dictionary) profile.context named.inputs arguments before initialStore mapping world
      administrative actualContext actual ξ generation.parameterCode generation.body size value finalStore)
      (added : Environment) (length : added.length = named.inputs.length)
    (spine : entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical)
    (reached : State headers keys ⟨named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
    (gate : CallableIndexedOwnedAllocationProducer.StableOwner keys location native),
      Below budget (CallableRuntimeBodyEntryContracts.ReflectsAt
        (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (protocol := argumentProtocol (headers := headers) owner (callerPrefix + 1))
        (conditionGate := CallableIndexedOwnedAllocationProducer.StableOwner keys)
        functions program (native_entry (generation := generation) (profile := profile) (functions := functions)
        (escaped := escaped) (extend := extend) (runtimeOf := runtimeOf) (installed := installed)
        (owner := owner) (callerPrefix := callerPrefix) (observed := observed)
        (entry := entry) (added := added) (length := length) (spine := spine) (reached := reached) (gate := gate)))) :
    NativeContinuation (program := program) (headers := headers) (keys := keys)
      (arguments := arguments) (payloads := payloads)
      generation profile functions escaped extend runtimeOf installed budget := by
  intro initialStore location native actualContext actual ξ size value finalStore entry added length spine reached gate child strict
  exact CallableIndexedOwnedBodyCanonicalEntries.reflects_of_canonical functions owner (callerPrefix + 1)
    (prefix_entry_origin generation profile functions escaped extend runtimeOf entry reached gate)
    _ (meaning entry added length spine reached gate child strict)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodCanonicalEntries
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodNestedEntries
/-! Authentic method selectors retain an independent raw Source body and
complete dictionary. Their emitted compiler seed and real parameter prefix
supply the origin packet at the same actual reached pool, without a Header. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodNestedEntries
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallablePreparedMethodRuntimeMeaning
open CallableIndexedOwnedExpressionHeads CallableIndexedOwnedMethodInvocationBounds
open RecursiveNamedCatalogInvocationBounds (Below)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {expressionSyntax : ExpressionId → Prop} {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {validity : SourceSemantics.Context → Prop} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (profile : CallablePreparedMethodCatalogHookMeaning.ProfileFor principal.cached.compilation (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) principal.sourceBody principal.dictionary administrative registry faults
    expressionSyntax certificates validity diagnosticPolicy)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (escaped : faults .controlEscapedFunction principal.cached.compilation.own.table.escapedReason)
  (extend : ∀ {context next binder}, validity context → BinderExtends principal.sourceBody.source.owner context binder next → validity next)
  (runtimeOf : ∀ {context}, validity context →
    CompatibleRuntimeContextValidity.Valid principal.named.specialized.function.solvedRequirements context principal.dictionary)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
  (installed : Installed principal.cached.compilation (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (sourceBody := principal.sourceBody)
    (administrative := administrative) functions mapping world before store callerEnvironment)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (observed : Globals (headers := headers) owner 0 [] installed.canonical)
  {originId : Word} {native : NativeFrame} {metadata : MetadataState}
  (selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt? (.named principal.named.signature.key) = some originId)
  (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    native (.named originId) (some metadata))

include profile observed selected history in
/-- The real Source parameter spine supplies canonical globals, bundle tag and
physical frame read; the reached row authenticates its own full Source seed. -/
theorem source_packet {initialStore : Store} {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
    (entry : ParameterEntry compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      owner.key.frameLocation native (.initial compiled.compatible.checked) functions registry
      principal.sourceFunction profile.context principal.named.inputs arguments before initialStore mapping world
      administrative actualContext actual ξ principal.cached.compilation.parameterCode principal.cached.compilation.body)
    (added : Environment) (length : added.length = principal.named.inputs.length)
    (spine : entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical)
    (reached : State headers keys ⟨principal.named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    CallableIndexedOwnedOriginCanonicalState.Packet owner principal.named _ reached := by
  apply CallableIndexedOwnedOriginCanonicalState.packet_of_stable_read owner principal.named reached
  · exact ⟨CallableIndexedOwnedMethodCanonicalEntries.globals_after_prefix
      (generation := principal.cached.compilation) (functions := functions) (installed := installed)
      (owner := owner) (callerPrefix := 0) (observed := observed) added length spine, entry.reference⟩
  · exact entry.environments
  · simpa only [List.getElem?_cons_zero] using congrArg some profile.parameterType.symm
  · exact principal.history_source selected history
  · exact entry.read

include profile observed selected history in
/-- Native parameters retain their own measured prefix and exact reached pool. -/
theorem native_packet {initialStore : Store} {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
    {size : Nat} {value : Value} {finalStore : Store}
    (entry : Prefix compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      owner.key.frameLocation native (.initial compiled.compatible.checked) functions registry
      principal.sourceFunction profile.context principal.named.inputs arguments before initialStore mapping world
      administrative actualContext actual ξ principal.cached.compilation.parameterCode principal.cached.compilation.body size value finalStore)
    (added : Environment) (length : added.length = principal.named.inputs.length)
    (spine : entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical)
    (reached : State headers keys ⟨principal.named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    CallableIndexedOwnedOriginCanonicalState.Packet owner principal.named _ reached := by
  apply CallableIndexedOwnedOriginCanonicalState.packet_of_stable_read owner principal.named reached
  · exact ⟨CallableIndexedOwnedMethodCanonicalEntries.globals_after_prefix
      (generation := principal.cached.compilation) (functions := functions) (installed := installed)
      (owner := owner) (callerPrefix := 0) (observed := observed) added length spine, entry.reference⟩
  · exact entry.environments
  · simpa only [List.getElem?_cons_zero] using congrArg some profile.parameterType.symm
  · exact principal.history_source selected history
  · exact entry.read

include observed selected history in
/-- Every actual Source field and the same reached pool enter the generic
principal protocol. The independent method Source profile is preserved verbatim. -/
def source_entry {initialStore : Store} {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
    (entry : ParameterEntry compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      owner.key.frameLocation native (.initial compiled.compatible.checked) functions registry
      principal.sourceFunction profile.context principal.named.inputs arguments before initialStore mapping world
      administrative actualContext actual ξ principal.cached.compilation.parameterCode principal.cached.compilation.body)
    (added : Environment) (length : added.length = principal.named.inputs.length)
    (spine : entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical)
    (reached : State headers keys ⟨principal.named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    CallableRuntimeBodyOrigins.Stateful.Entry
      (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner principal.named)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (origin principal.cached.compilation profile escaped extend runtimeOf) functions :=
  { parameter_entry_origin principal.cached.compilation profile functions escaped extend runtimeOf entry reached
      ⟨owner.position, _, _, rfl, principal.history_source selected history⟩ with
    initial := ⟨reached, source_packet principal profile functions installed owner observed selected history entry added length spine reached⟩ }

include observed selected history in
/-- Native entry fields retain the original source dictionary, actual prefix
continuation and reached pool; only the proven principal packet is added. -/
def native_entry {initialStore : Store} {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
    {size : Nat} {value : Value} {finalStore : Store}
    (entry : Prefix compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      owner.key.frameLocation native (.initial compiled.compatible.checked) functions registry
      principal.sourceFunction profile.context principal.named.inputs arguments before initialStore mapping world
      administrative actualContext actual ξ principal.cached.compilation.parameterCode principal.cached.compilation.body size value finalStore)
    (added : Environment) (length : added.length = principal.named.inputs.length)
    (spine : entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical)
    (reached : State headers keys ⟨principal.named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    CallableRuntimeBodyOrigins.Stateful.Entry
      (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner principal.named)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (origin principal.cached.compilation profile escaped extend runtimeOf) functions :=
  { prefix_entry_origin principal.cached.compilation profile functions escaped extend runtimeOf entry reached
      ⟨owner.position, _, _, rfl, principal.history_source selected history⟩ with
    initial := ⟨reached, native_packet principal profile functions installed owner observed selected history entry added length spine reached⟩ }

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodNestedEntries
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodPrincipalReadyContinuations
/-! The genuine selected method keeps its complete trait dictionary and
synthetic Source frame. Actual hook and parameter receipts establish admission
at the same reached pool before the shared family's strict body child. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodPrincipalReadyContinuations
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallablePreparedMethodRuntimeMeaning
open CallableIndexedOwnedMethodInvocationBounds
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedOwnedBodySourceOrigin (source_origin)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {method : ExecutableImplMethods.CheckedMethod}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {expressionSyntax : ExpressionId → Prop} {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {validity : SourceSemantics.Context → Prop} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (profile : CallablePreparedMethodCatalogHookMeaning.ProfileFor principal.cached.compilation (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) principal.sourceBody principal.dictionary administrative registry faults
    expressionSyntax certificates validity diagnosticPolicy)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (escaped : faults .controlEscapedFunction principal.cached.compilation.own.table.escapedReason)
  (extend : ∀ {context next binder}, validity context → BinderExtends principal.sourceBody.source.owner context binder next → validity next)
  (runtimeOf : ∀ {context}, validity context →
    CompatibleRuntimeContextValidity.Valid principal.named.specialized.function.solvedRequirements context principal.dictionary)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
  (installed : Installed principal.cached.compilation (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (sourceBody := principal.sourceBody)
    (administrative := administrative) functions mapping world before store callerEnvironment)
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)

  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (beforeTyped : Dynamic.HeapWellTyped principal.sourceFunction.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes principal.sourceFunction.context before arguments profile.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)
  (observed : CallableIndexedOwnedExpressionHeads.Globals (headers := headers) owner 0 [] installed.canonical)

/-- Genuine globals and the complete principal seed accompany the same pool. -/
def bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True)
    (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner principal.named) :=
  CallableIndexedOwnedIndirectCallerProtocol.forget_slots
    (CallableIndexedOwnedOriginCanonicalState.carrier owner principal.named)

include wellFormed beforeTyped argumentsTyped stable observed in
/-- Authentic Source method selection and the actual hook/parameter allocation
supply this complete admitted entry without inventing a top-level Header. -/
def source_admitted_entry {hook : Word} {index : Int} {metadata : MetadataState}
    (selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt?
      (.named principal.named.signature.key) = some hook)
    (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (.state index) (.named hook) (some metadata))
    {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
    (entry : ParameterEntry compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      owner.key.frameLocation (.state index) (.initial compiled.compatible.checked) functions registry
      principal.sourceFunction profile.context principal.named.inputs arguments before
      (store.set owner.key.frameLocation (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
      administrative actualContext actual ξ principal.cached.compilation.parameterCode principal.cached.compilation.body)
    (added : Environment) (length : added.length = principal.named.inputs.length)
    (spine : entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical)
    (reached : State headers keys ⟨principal.named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    CallableIndexedOwnedAdmittedBodyEntries.Entry (bridge (headers := headers) principal owner)
      (condition := CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (origin := origin principal.cached.compilation profile escaped extend runtimeOf) (functions := functions) := by
  let base := CallableIndexedOwnedMethodReadyContinuations.source_admitted_entry principal profile functions escaped extend runtimeOf owner caller
    wellFormed beforeTyped argumentsTyped stable selected history entry reached
  exact ⟨CallableIndexedOwnedMethodNestedEntries.source_entry principal profile functions escaped extend runtimeOf
    installed owner observed selected history entry added length spine reached, base.source, base.rows⟩

/-- Native Prefix receipts retain their actual Source allocation, independent
body grade and the same carried hook at the exact reached pool. -/
def native_admitted_entry {hook : Word} {index : Int} {metadata : MetadataState}
    (selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt?
      (.named principal.named.signature.key) = some hook)
    (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (.state index) (.named hook) (some metadata))
    {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
    {prefixSize : Nat} {value : Value} {bodyStore : Store}
    (entry : CallablePreparedMethodRuntimeMeaning.Prefix compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      owner.key.frameLocation (.state index) (.initial compiled.compatible.checked) functions registry
      principal.sourceFunction profile.context principal.named.inputs arguments before
      (store.set owner.key.frameLocation (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
      administrative actualContext actual ξ principal.cached.compilation.parameterCode principal.cached.compilation.body prefixSize value bodyStore)
    (added : Environment) (length : added.length = principal.named.inputs.length)
    (spine : entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical)
    (reached : State headers keys ⟨principal.named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    CallableIndexedOwnedAdmittedBodyEntries.Entry (bridge (headers := headers) principal owner)
      (condition := CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (origin := origin principal.cached.compilation profile escaped extend runtimeOf) (functions := functions) := by
  let base := CallableIndexedOwnedMethodReadyContinuations.native_admitted_entry principal profile functions escaped extend runtimeOf owner caller
    wellFormed beforeTyped argumentsTyped stable selected history entry reached
  exact ⟨CallableIndexedOwnedMethodNestedEntries.native_entry principal profile functions escaped extend runtimeOf
    installed owner observed selected history entry added length spine reached, base.source, base.rows⟩

/-- The complete original method parameter entry and its pool are unchanged. -/
theorem source_original {hook : Word} {index : Int} {metadata : MetadataState}
    (selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt?
      (.named principal.named.signature.key) = some hook)
    (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (.state index) (.named hook) (some metadata))
    {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
    (entry : ParameterEntry compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      owner.key.frameLocation (.state index) (.initial compiled.compatible.checked) functions registry
      principal.sourceFunction profile.context principal.named.inputs arguments before
      (store.set owner.key.frameLocation (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
      administrative actualContext actual ξ principal.cached.compilation.parameterCode principal.cached.compilation.body)
    (added : Environment) (length : added.length = principal.named.inputs.length)
    (spine : entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical)
    (reached : State headers keys ⟨principal.named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    (source_admitted_entry principal profile functions escaped extend runtimeOf installed owner caller wellFormed
      beforeTyped argumentsTyped stable observed selected history entry added length spine reached).original =
      CallableIndexedOwnedMethodNestedEntries.source_entry principal profile functions escaped extend runtimeOf
        installed owner observed selected history entry added length spine reached := rfl

/-- The complete original method parameter entry and its pool are unchanged. -/
theorem native_original {hook : Word} {index : Int} {metadata : MetadataState}
    (selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt?
      (.named principal.named.signature.key) = some hook)
    (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (.state index) (.named hook) (some metadata))
    {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
    {prefixSize : Nat} {value : Value} {bodyStore : Store}
    (entry : CallablePreparedMethodRuntimeMeaning.Prefix compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      owner.key.frameLocation (.state index) (.initial compiled.compatible.checked) functions registry
      principal.sourceFunction profile.context principal.named.inputs arguments before
      (store.set owner.key.frameLocation (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
      administrative actualContext actual ξ principal.cached.compilation.parameterCode principal.cached.compilation.body prefixSize value bodyStore)
    (added : Environment) (length : added.length = principal.named.inputs.length)
    (spine : entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical)
    (reached : State headers keys ⟨principal.named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    (native_admitted_entry principal profile functions escaped extend runtimeOf installed owner caller wellFormed
      beforeTyped argumentsTyped stable observed selected history entry added length spine reached).original =
      CallableIndexedOwnedMethodNestedEntries.native_entry principal profile functions escaped extend runtimeOf
        installed owner observed selected history entry added length spine reached := rfl

variable (syntaxTree : GenericImperativeMatch.Syntax principal.sourceFunction.source expressionSyntax profile.context
    (.statements true principal.sourceFunction.body) principal.sourceFunction.resultType)
  {ι : Type} (origins : ι → CallableRuntimeBodyOrigins.StaticOrigin (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) registry faults)

include wellFormed beforeTyped argumentsTyped stable observed syntaxTree in
/-- The full actual hook/parameter packet selects its exact shared-family
origin; the callback uses only the strictly smaller body IH. -/
theorem source_continuation (budget : Nat)
    (selection : ∀ (hook : Word) (index : Int) (metadata : MetadataState)
      (selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt?
        (.named principal.named.signature.key) = some hook)
      (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
        (.state index) (.named hook) (some metadata))
      (_emitted : principal.cached.compilation.output = SourceCoreCallableIndexedFrames.withFrame
        (.var (compiled.indexed.base.globals.length + 1))
        (SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index))
        principal.cached.compilation.parameterCode)
      {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
      (entry : ParameterEntry compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      owner.key.frameLocation (.state index) (.initial compiled.compatible.checked) functions registry
      principal.sourceFunction profile.context principal.named.inputs arguments before
      (store.set owner.key.frameLocation (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
      administrative actualContext actual ξ principal.cached.compilation.parameterCode principal.cached.compilation.body)
      (added : Environment) (length : added.length = principal.named.inputs.length)
      (spine : entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical)
      (reached : State headers keys ⟨principal.named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) (_related : Relates caller reached),
      { i : ι // origins i = source_origin (origin principal.cached.compilation profile escaped extend runtimeOf)
        (source_admitted_entry principal profile functions escaped extend runtimeOf installed owner caller wellFormed
          beforeTyped argumentsTyped stable observed selected history entry added length spine reached).source.runtime })
    (below : RecursiveNamedCatalogInvocationBounds.Below budget (fun child => ∀ i,
      CallableRuntimeBodyReadyOrigins.PreservesAt (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner principal.named)
        (readiness (bridge (headers := headers) principal owner)) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
        (ProtectedStateImperativeTypedSourceSites.Facts (origins i).function.source (origins i).expressionSyntax)
        functions (Program.ofChecked compiled.sourceProgram) (origins i) child)) :
    SourceContinuationWithHistory (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys)
      (arguments := arguments) (payloads := payloads) (owner := owner) (caller := caller)
      principal.cached.compilation profile functions escaped extend runtimeOf installed budget := by
  intro hook index metadata selected history emitted entry added length spine reached related
  let selectedOrigin := selection hook index metadata selected history emitted entry added length spine reached related
  intro child strict outcome after trace
  have ready := below child strict selectedOrigin.val
  rw [selectedOrigin.property] at ready
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
      frame, metadata, exit, returned, actualRelated, _post⟩ :=
    CallableIndexedOwnedSourceBodyReadyBounds.preserves_at (bridge (headers := headers) principal owner)
      (source_admitted_entry principal profile functions escaped extend runtimeOf installed owner caller wellFormed
        beforeTyped argumentsTyped stable observed selected history entry added length spine reached).source.runtime
      wellFormed syntaxTree ready
      (source_admitted_entry principal profile functions escaped extend runtimeOf installed owner caller wellFormed
        beforeTyped argumentsTyped stable observed selected history entry added length spine reached) trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
    frame, metadata, exit, returned.val, actualRelated⟩

include wellFormed beforeTyped argumentsTyped stable observed syntaxTree in
/-- The full actual hook/parameter packet selects its exact shared-family
origin; the callback uses only the strictly smaller body IH. -/
theorem native_continuation (budget : Nat)
    (selection : ∀ (hook : Word) (index : Int) (metadata : MetadataState)
      (selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt?
        (.named principal.named.signature.key) = some hook)
      (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
        (.state index) (.named hook) (some metadata))
      {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
      {prefixSize : Nat} {value : Value} {bodyStore : Store}
      (entry : CallablePreparedMethodRuntimeMeaning.Prefix compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      owner.key.frameLocation (.state index) (.initial compiled.compatible.checked) functions registry
      principal.sourceFunction profile.context principal.named.inputs arguments before
      (store.set owner.key.frameLocation (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
      administrative actualContext actual ξ principal.cached.compilation.parameterCode principal.cached.compilation.body prefixSize value bodyStore)
      (added : Environment) (length : added.length = principal.named.inputs.length)
      (spine : entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical)
      (reached : State headers keys ⟨principal.named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) (_related : Relates caller reached),
      { i : ι // origins i = source_origin (origin principal.cached.compilation profile escaped extend runtimeOf)
        (native_admitted_entry principal profile functions escaped extend runtimeOf installed owner caller wellFormed
          beforeTyped argumentsTyped stable observed selected history entry added length spine reached).source.runtime })
    (below : RecursiveNamedCatalogInvocationBounds.Below budget (fun child => ∀ i,
      CallableRuntimeBodyReadyOrigins.ReflectsAt (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner principal.named)
        (readiness (bridge (headers := headers) principal owner)) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
        (ProtectedStateImperativeTypedSourceSites.Facts (origins i).function.source (origins i).expressionSyntax)
        functions (Program.ofChecked compiled.sourceProgram) (origins i) child)) :
    NativeContinuationWithHistory (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys)
      (arguments := arguments) (payloads := payloads) (owner := owner) (caller := caller)
      principal.cached.compilation profile functions escaped extend runtimeOf installed budget := by
  intro hook index metadata _prefixSize _bodyStore selected history _prefixWithin _value _finalStore
    _restored entry added length spine reached related
  let selectedOrigin := selection hook index metadata selected history entry added length spine reached related
  intro child strict value finalStore completed
  have ready := below child strict selectedOrigin.val
  rw [selectedOrigin.property] at ready
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
      frame, metadata, exit, returned, actualRelated, _post⟩ :=
    CallableIndexedOwnedSourceBodyReadyBounds.reflects_at (bridge (headers := headers) principal owner)
      (native_admitted_entry principal profile functions escaped extend runtimeOf installed owner caller wellFormed
        beforeTyped argumentsTyped stable observed selected history entry added length spine reached).source.runtime
      wellFormed syntaxTree ready
      (native_admitted_entry principal profile functions escaped extend runtimeOf installed owner caller wellFormed
        beforeTyped argumentsTyped stable observed selected history entry added length spine reached) completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
    frame, metadata, exit, returned.val, actualRelated⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodPrincipalReadyContinuations
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodReadyFamilyReceipts
/-! An authentic selected method and its complete Source profile construct a
principal-protocol family index at the actual parameter entry. The original
pointwise continuation consumes only that index's strict shared child. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodReadyFamilyReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallablePreparedMethodRuntimeMeaning
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedOwnedBodySourceOrigin (source_origin)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- The real trait selector, full compiler profile, dictionary and original
Syntax remain independent Source/static receipts. No Header is invented. -/
structure Index where
  method : ExecutableImplMethods.CheckedMethod
  principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method
  owner : CallableIndexedOwnedFunctionValues.OwnedKey keys
  administrative : Core.Context
  expressionSyntax : ExpressionId → Prop
  certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate
  validity : SourceSemantics.Context → Prop
  diagnosticPolicy : AssignmentDiagnosticPolicy
  profile : CallablePreparedMethodCatalogHookMeaning.ProfileFor principal.cached.compilation (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) principal.sourceBody principal.dictionary administrative registry faults
    expressionSyntax certificates validity diagnosticPolicy
  escaped : faults .controlEscapedFunction principal.cached.compilation.own.table.escapedReason
  extend : ∀ {context next binder}, validity context → BinderExtends principal.sourceBody.source.owner context binder next → validity next
  runtimeOf : ∀ {context}, validity context →
    CompatibleRuntimeContextValidity.Valid principal.named.specialized.function.solvedRequirements context principal.dictionary
  syntaxTree : GenericImperativeMatch.Syntax principal.sourceFunction.source expressionSyntax profile.context
    (.statements true principal.sourceFunction.body) principal.sourceFunction.resultType
  sourceRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
    (CallableIndexedOwnedMethodInvocationBounds.origin principal.cached.compilation profile escaped extend runtimeOf).context
    (CallableIndexedOwnedMethodInvocationBounds.origin principal.cached.compilation profile escaped extend runtimeOf).function.source

/-- The exact complete method origin retains its genuine Source domain. -/
def origin (index : Index (keys := keys) (registry := registry) (faults := faults)) :=
  source_origin (CallableIndexedOwnedMethodInvocationBounds.origin index.principal.cached.compilation
    index.profile index.escaped index.extend index.runtimeOf) index.sourceRuntime

/-- The genuine trait principal and physical owner select the stronger protocol. -/
def body_protocol (index : Index (keys := keys) (registry := registry) (faults := faults)) :=
  CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) index.owner index.principal.named

/-- Every packet accompanies the complete same actual ordered pool. -/
def bridge (index : Index (keys := keys) (registry := registry) (faults := faults)) :=
  CallableIndexedOwnedMethodPrincipalReadyContinuations.bridge (headers := headers) index.principal index.owner

variable {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  {administrative : Core.Context}
  {expressionSyntax : ExpressionId → Prop} {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {validity : SourceSemantics.Context → Prop} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (profile : CallablePreparedMethodCatalogHookMeaning.ProfileFor principal.cached.compilation (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) principal.sourceBody principal.dictionary administrative registry faults
    expressionSyntax certificates validity diagnosticPolicy)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (escaped : faults .controlEscapedFunction principal.cached.compilation.own.table.escapedReason)
  (extend : ∀ {context next binder}, validity context → BinderExtends principal.sourceBody.source.owner context binder next → validity next)
  (runtimeOf : ∀ {context}, validity context →
    CompatibleRuntimeContextValidity.Valid principal.named.specialized.function.solvedRequirements context principal.dictionary)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
  (installed : Installed principal.cached.compilation (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (sourceBody := principal.sourceBody)
    (administrative := administrative) functions mapping world before store callerEnvironment)
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)

  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (beforeTyped : Dynamic.HeapWellTyped principal.sourceFunction.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes principal.sourceFunction.context before arguments profile.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)
  (observed : CallableIndexedOwnedExpressionHeads.Globals (headers := headers) owner 0 [] installed.canonical)

variable (syntaxTree : GenericImperativeMatch.Syntax principal.sourceFunction.source expressionSyntax profile.context
    (.statements true principal.sourceFunction.body) principal.sourceFunction.resultType)

/-- The actual source parameter receipt constructs the index internally,
retaining the same original profile and its genuine Source runtime. -/
def of_source_entry {hook : Word} {index : Int} {metadata : MetadataState}
    (selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt?
      (.named principal.named.signature.key) = some hook)
    (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (.state index) (.named hook) (some metadata))
    {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
    (entry : CallableIndexedOwnedMethodInvocationBounds.ParameterEntry compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      owner.key.frameLocation (.state index) (.initial compiled.compatible.checked) functions registry
      principal.sourceFunction profile.context principal.named.inputs arguments before
      (store.set owner.key.frameLocation (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
      administrative actualContext actual ξ principal.cached.compilation.parameterCode principal.cached.compilation.body)
    (added : Environment) (length : added.length = principal.named.inputs.length)
    (spine : entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical)
    (reached : State headers keys ⟨principal.named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    Index (keys := keys) (registry := registry) (faults := faults) :=
  ⟨method, principal, owner, administrative, expressionSyntax, certificates, validity, diagnosticPolicy,
    profile, escaped, extend, runtimeOf, syntaxTree,
    (CallableIndexedOwnedMethodPrincipalReadyContinuations.source_admitted_entry principal profile functions escaped extend runtimeOf
      installed owner caller wellFormed beforeTyped argumentsTyped stable observed selected history
      entry added length spine reached).source.runtime⟩

/-- The actual native parameter receipt constructs the index internally,
retaining the same original profile and its genuine Source runtime. -/
def of_native_entry {hook : Word} {index : Int} {metadata : MetadataState}
    (selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt?
      (.named principal.named.signature.key) = some hook)
    (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (.state index) (.named hook) (some metadata))
    {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
    {prefixSize : Nat} {value : Value} {bodyStore : Store}
    (entry : CallablePreparedMethodRuntimeMeaning.Prefix compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      owner.key.frameLocation (.state index) (.initial compiled.compatible.checked) functions registry
      principal.sourceFunction profile.context principal.named.inputs arguments before
      (store.set owner.key.frameLocation (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
      administrative actualContext actual ξ principal.cached.compilation.parameterCode principal.cached.compilation.body prefixSize value bodyStore)
    (added : Environment) (length : added.length = principal.named.inputs.length)
    (spine : entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical)
    (reached : State headers keys ⟨principal.named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    Index (keys := keys) (registry := registry) (faults := faults) :=
  ⟨method, principal, owner, administrative, expressionSyntax, certificates, validity, diagnosticPolicy,
    profile, escaped, extend, runtimeOf, syntaxTree,
    (CallableIndexedOwnedMethodPrincipalReadyContinuations.native_admitted_entry principal profile functions escaped extend runtimeOf
      installed owner caller wellFormed beforeTyped argumentsTyped stable observed selected history
      entry added length spine reached).source.runtime⟩

include wellFormed beforeTyped argumentsTyped stable observed syntaxTree in
/-- The genuine Source entry constructs its exact index and invokes only the
strict shared-family child at that principal protocol. -/
theorem source_continuation (budget : Nat)
    (below : ∀ index : Index (keys := keys) (registry := registry) (faults := faults),
      RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyReadyOrigins.PreservesAt (body_protocol (headers := headers) index)
          (readiness (bridge (headers := headers) index)) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
          (ProtectedStateImperativeTypedSourceSites.Facts (origin index).function.source (origin index).expressionSyntax)
          functions (Program.ofChecked compiled.sourceProgram) (origin index))) :
    CallableIndexedOwnedMethodInvocationBounds.SourceContinuationWithHistory
      (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys)
      (arguments := arguments) (payloads := payloads) (owner := owner) (caller := caller)
      principal.cached.compilation profile functions escaped extend runtimeOf installed budget := by
  intro hook current metadata selected history _emitted entry added length spine reached _related
  intro child strict outcome after trace
  let index := of_source_entry principal profile functions escaped extend runtimeOf installed owner caller wellFormed
    beforeTyped argumentsTyped stable observed syntaxTree selected history entry added length spine reached
  let actualEntry := CallableIndexedOwnedMethodPrincipalReadyContinuations.source_admitted_entry
    principal profile functions escaped extend runtimeOf installed owner caller wellFormed
    beforeTyped argumentsTyped stable observed selected history entry added length spine reached
  have ready := below index child strict
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
      frame, metadata, exit, returned, related, _post⟩ :=
    CallableIndexedOwnedSourceBodyReadyBounds.preserves_at
      (CallableIndexedOwnedMethodPrincipalReadyContinuations.bridge (headers := headers) principal owner)
      actualEntry.source.runtime wellFormed syntaxTree ready actualEntry trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
    frame, metadata, exit, returned.val, related⟩

include wellFormed beforeTyped argumentsTyped stable observed syntaxTree in
/-- The original measured prefix constructs the index at its actual reached
pool; the resulting Source grade remains independent of native execution. -/
theorem native_continuation (budget : Nat)
    (below : ∀ index : Index (keys := keys) (registry := registry) (faults := faults),
      RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyReadyOrigins.ReflectsAt (body_protocol (headers := headers) index)
          (readiness (bridge (headers := headers) index)) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
          (ProtectedStateImperativeTypedSourceSites.Facts (origin index).function.source (origin index).expressionSyntax)
          functions (Program.ofChecked compiled.sourceProgram) (origin index))) :
    CallableIndexedOwnedMethodInvocationBounds.NativeContinuationWithHistory
      (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys)
      (arguments := arguments) (payloads := payloads) (owner := owner) (caller := caller)
      principal.cached.compilation profile functions escaped extend runtimeOf installed budget := by
  intro hook current metadata _prefixSize _bodyStore selected history _prefixWithin _value _finalStore
    _restored entry added length spine reached _related
  intro child strict value finalStore completed
  let index := of_native_entry principal profile functions escaped extend runtimeOf installed owner caller wellFormed
    beforeTyped argumentsTyped stable observed syntaxTree selected history entry added length spine reached
  let actualEntry := CallableIndexedOwnedMethodPrincipalReadyContinuations.native_admitted_entry
    principal profile functions escaped extend runtimeOf installed owner caller wellFormed
    beforeTyped argumentsTyped stable observed selected history entry added length spine reached
  have ready := below index child strict
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
      frame, metadata, exit, returned, related, _post⟩ :=
    CallableIndexedOwnedSourceBodyReadyBounds.reflects_at
      (CallableIndexedOwnedMethodPrincipalReadyContinuations.bridge (headers := headers) principal owner)
      actualEntry.source.runtime wellFormed syntaxTree ready actualEntry completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
    frame, metadata, exit, returned.val, related⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodReadyFamilyReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodPhysicalCaptures
/-! Selected methods recover their authentic installed captures at the reached
heap. Complete physical cache authority supplies native code; the independent
operator selector supplies the method Source frame and dictionary. The current
owner supplies the live frame and full ordered snapshots. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodPhysicalCaptures
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallablePreparedMethodRuntimeMeaning
open RecursiveGlobalInitializationMeaning RecursiveGlobalInitializationTyping
open CallableIndexedOwnedPhysicalGlobals

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {method : ExecutableImplMethods.CheckedMethod}
  (cached : CallablePreparedMethodSelection.Cached compiled method.specialized)
  (dictionary : Dynamic.EvidenceEnvironment)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}

abbrev sourceBody := CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram method

structure Capture (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap)
    (store : Store) (caller : Environment) where
  administrative : Core.Context
  installed : Installed cached.compilation (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (sourceBody := sourceBody (compiled := compiled) (method := method))
    (administrative := administrative) functions mapping world heap store caller
  sourceFrame : CallableCoercionMethodFrame.Frame (sourceBody (compiled := compiled) (method := method))
    (methodFunction cached.compilation (sourceBody (compiled := compiled) (method := method)) dictionary)
  canonical_eq : installed.canonical = environment compiled
  captured_eq : installed.captured = List.replicate cached.index .unit ++ environment compiled
  embedding_eq : installed.embedding = shift cached.index
  frame_eq : installed.frameLocation = 0

theorem of_selected
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {scope : SourceCoreLocalCell.Scope} {caller : Environment} {callerPrefix : Nat}
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (pool : CallableIndexedOwnedFunctionState.State headers keys ⟨scope, mapping, world, heap, store, caller⟩)
    (ownerFrame : owner.key.frameLocation = 0)
    (physical : Authority compiled mapping store)
    (typed : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions)
    (slots : Slots compiled callerPrefix scope caller)
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {traitName methodName : String} {requirements : List RequirementId}
    (selected : Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context evidence traitName methodName
      requirements (sourceBody (compiled := compiled) (method := method)) dictionary)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    Nonempty (Capture cached dictionary functions mapping world heap store caller) := by
  have cachedCode : compiled.indexed.secondPass.closures[cached.index]? = some
      (.lambda cached.named.signature.parameterType (LanguageResult.resultType cached.named.signature.resultType) cached.compilation.output) := by
    simpa only [cached.compilation.emitted] using cached.cached
  obtain ⟨globalUnmapped, globalRead⟩ := physical.cached cachedCode
  obtain ⟨capturedContext, capturedTyped, _bodyTyped⟩ := stored_closure typed globalRead
  obtain ⟨administrative, canonicalTyped⟩ := drop_installer_units cached.index capturedTyped
  have captureLayout : EnvironmentsAgree (shift cached.index) (environment compiled)
      (List.replicate cached.index .unit ++ environment compiled) := by
    intro index value found
    rw [List.getElem?_append_right (by simp [shift])]
    simpa [shift] using found
  have frameReference := RecursiveNamedCatalogInitialization.frame_reference compiled.indexed.base.globals compiled.indexed.ancestry.layout.frame
  change (RecursiveNamedCatalogPreparedInitialization.environment compiled)[compiled.indexed.base.globals.length]? = _ at frameReference
  rw [RecursiveNamedPublicBootstrapGlobals.environment_eq] at frameReference
  let row := pool.rows owner.position
  have frameEq : row.authority.frameLocation = 0 := row.frame_eq.trans ownerFrame
  have frameType := row.authority.typed
  have unmapped := row.authority.unmapped
  have frame := row.authority.frame
  rw [frameEq] at frameType unmapped frame
  obtain ⟨_types, _context, _facts, certified, _valid⟩ := CallablePreparedMethodSelection.selected_typed selected wellFormed
  let installed : Installed cached.compilation (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (sourceBody := sourceBody (compiled := compiled) (method := method))
      (administrative := administrative) functions mapping world heap store caller := {
    canonical := environment compiled
    captured := List.replicate cached.index .unit ++ environment compiled
    capturedContext := capturedContext, embedding := shift cached.index
    environments := .nil canonicalTyped
    locals := by rw [certified.locals_empty]; exact .nil
    captureLayout := captureLayout, captureTyped := capturedTyped
    frameLocation := 0, canonicalReference := frameReference, capturedReference := captureLayout frameReference
    unmapped := unmapped, frameTyped := frameType
    current := row.authority.current, currentGhost := row.authority.ghost, caller := frame
    records := row.authority.records, snapshots := row.authority.snapshots
    globalIndex := scope.length + callerPrefix + cached.index
    globalLocation := location compiled cached.index
    globalUnmapped := globalUnmapped
    globalReference := slots _ _ (CallableIndexedPreparedInventories.cached_global_at compiled cached.selected)
    globalRead := globalRead }
  exact ⟨⟨administrative, installed, cached.frame selected, rfl, rfl, rfl, rfl⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodPhysicalCaptures
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodPrincipalContinuations
/-! The actual selected hook history and ordered parameter post supply the
method principal packet before its strict body child. Both adapters consume the
same authentic method origin and forget only the returned packet proof; the
complete reached pool and relation remain intact. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodPrincipalContinuations
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallablePreparedMethodRuntimeMeaning
open CallableIndexedOwnedMethodInvocationBounds
open RecursiveNamedCatalogInvocationBounds (Below)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {method : ExecutableImplMethods.CheckedMethod}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {expressionSyntax : ExpressionId → Prop} {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {validity : SourceSemantics.Context → Prop} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (profile : CallablePreparedMethodCatalogHookMeaning.ProfileFor principal.cached.compilation (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) principal.sourceBody principal.dictionary administrative registry faults
    expressionSyntax certificates validity diagnosticPolicy)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (escaped : faults .controlEscapedFunction principal.cached.compilation.own.table.escapedReason)
  (extend : ∀ {context next binder}, validity context → BinderExtends principal.sourceBody.source.owner context binder next → validity next)
  (runtimeOf : ∀ {context}, validity context →
    CompatibleRuntimeContextValidity.Valid principal.named.specialized.function.solvedRequirements context principal.dictionary)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
  (installed : Installed principal.cached.compilation (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (sourceBody := principal.sourceBody)
    (administrative := administrative) functions mapping world before store callerEnvironment)
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (observed : CallableIndexedOwnedExpressionHeads.Globals (headers := headers) owner 0 [] installed.canonical)

include observed in
/-- A strict Source body family receives the exact authentic parameter Entry
and reached pool produced by the selected method hook. -/
theorem source_continuation (budget : Nat)
    (meaning : Below budget (CallableRuntimeBodyOrigins.Stateful.PreservesAt
      (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner principal.named)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions (Program.ofChecked compiled.sourceProgram)
      (origin principal.cached.compilation profile escaped extend runtimeOf))) :
    SourceContinuationWithHistory (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys)
      (arguments := arguments) (payloads := payloads) (owner := owner) (caller := caller)
      principal.cached.compilation profile functions escaped extend runtimeOf installed budget := by
  intro _origin _index _metadata selected history _emitted entry added length spine reached _related child strict _outcome _after trace
  let actual := CallableIndexedOwnedMethodNestedEntries.source_entry principal profile functions escaped extend runtimeOf
    installed owner observed selected history entry added length spine reached
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds, frame, metadata, exit, returned, related⟩ :=
    meaning child strict actual trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds, frame, metadata, exit, returned.val, related⟩

include observed in
/-- Native body reflection receives the actual measured Prefix and its same
reached pool, retaining an independently measured Source trace. -/
theorem native_continuation (budget : Nat)
    (meaning : Below budget (CallableRuntimeBodyOrigins.Stateful.ReflectsAt
      (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner principal.named)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions (Program.ofChecked compiled.sourceProgram)
      (origin principal.cached.compilation profile escaped extend runtimeOf))) :
    NativeContinuationWithHistory (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys)
      (arguments := arguments) (payloads := payloads) (owner := owner) (caller := caller)
      principal.cached.compilation profile functions escaped extend runtimeOf installed budget := by
  intro _origin _index _metadata _prefixSize _bodyStore selected history _prefixWithin _value _finalStore
    _restored entry added length spine reached _related child strict _bodyValue _bodyFinalStore completed
  let actual := CallableIndexedOwnedMethodNestedEntries.native_entry principal profile functions escaped extend runtimeOf
    installed owner observed selected history entry added length spine reached
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds, frame, metadata, exit, returned, related⟩ :=
    meaning child strict actual completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds, frame, metadata, exit, returned.val, related⟩
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodPrincipalContinuations
end
