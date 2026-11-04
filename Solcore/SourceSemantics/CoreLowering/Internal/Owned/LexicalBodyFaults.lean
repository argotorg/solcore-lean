import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LiteralReturns
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceDiagnostics
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.PublicExpressionBounds
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.CanonicalCallerState
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LambdaReadyFamilies
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ContextualOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.Paths
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.IndirectExpressionHeads
import Solcore.SourceSemantics.CoreLowering.ReachedNamedLexicalBodyFaultPaths
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LexicalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.ImperativeControl
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogEntries
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.InvocationBounds
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NamedCatalog

/-!
# Owned callables: physical origins and lexical faults

Physical associations, cell origins and function views, and fault bounds and post providers of lexical named bodies.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedNamedHeaderReceipts
/-! A named Header is constructed with the actual selected diagnostic issuer.
The public specialization retains its original Source, resolved dictionary and
substitution order. The second-pass action supplies the fresh compiler packet;
equality of cached native code is never used to identify diagnostic tables.
These static factories do not supply a body execution law or a runtime pool. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedNamedHeaderReceipts
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open CallableIndexedOwnedSelectedDiagnosticIssuerReceipts
open CallableIndexedOwnedSelectedReadIndexDiagnosticPolicies
open RecursiveNamedPublicSpecializationMeaning

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {row : SourceSpecialization.SpecializedFunction}

/-- Whole original body typing supplies the issuer's assignment and unary
certificates, including nested bodies and statically typed suffixes. -/
theorem diagnostic_typed (prepared : Prepared compiled row)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution) :
    EmittedDiagnosticTokenPlan.UnaryTyped (source prepared.named) ∧
      AssignmentDiagnosticOrigins.OperandsTyped (source prepared.named) := by
  obtain ⟨types, context, facts, certificate⟩ :=
    (prepared.instantiated wellFormed range).certificate wellFormed
  have typed := SourceDiagnosticTyping.diagnostic_typed_of_certificate certificate.toBodyInstanceTypingCertificate
  change EmittedDiagnosticTokenPlan.UnaryTyped row.function.typedBody ∧
    AssignmentDiagnosticOrigins.OperandsTyped row.function.typedBody at typed
  simpa only [source, prepared.same] using typed

/-- Reuse the real worklist origin and complete resolved evidence. Replace
only the compiler fields with the actual selected second-pass packet. -/
def reissued (prepared : Prepared compiled row)
    (selected : SelectedReceipt compiled prepared.named prepared.index) : Prepared compiled row :=
  { prepared with
    diagnostics := lowered compiled selected.diagnostics
    code := selected.code
    compilation := selected.compilation
    cached := selected.cached }

/-- Both genuine compiler actions extract the same complete statement roots.
The source closure, including its ordered dictionary, is therefore unchanged. -/
theorem reissued_view (prepared : Prepared compiled row)
    (selected : SelectedReceipt compiled prepared.named prepared.index) :
    (reissued prepared selected).view = prepared.view := by
  have roots : selected.compilation.statements = prepared.compilation.statements :=
    Except.ok.inj (selected.compilation.roots.symm.trans prepared.compilation.roots)
  simp only [RecursiveNamedPublicSpecializationMeaning.Prepared.view,
    RecursiveNamedPreparedSourceFrames.view, reissued, roots]

/-- This is an observation of the fresh Header factory's actual policy.
The desired identifier equality is obtained from HeaderAt, not supplied. -/
theorem reason_at (prepared : Prepared compiled row)
    (selected : SelectedReceipt compiled prepared.named prepared.index)
    {instantiation : DeclarationInstantiation}
    {header : CallableIndexedOwnedFunctionValues.Header compiled
      (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt
      (reissued prepared selected) instantiation header) :
    header.reasonAt = reasonAt selected := by
  simpa only [reissued, reasonAt] using aligned.reasonAt

/-- Canonical source metadata uses a freshly selected issuer and the original
evidence-aware Header construction. No synthetic Header or empty dictionary
is inferred from the cached slot. -/
theorem canonical_at_prepared (prepared : Prepared compiled row)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution)
    (ordinaryReturn : row.function.returnComptime = false)
    (ordinaryParameters : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false)
    (target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation row) = .ok prepared.named.signature.key) :
    ∃ (selected : SelectedReceipt compiled prepared.named prepared.index)
      (header : CallableIndexedOwnedFunctionValues.Header compiled
        (Program.ofChecked compiled.sourceProgram)),
      RecursiveNamedPreparedHeaders.Prepared.HeaderAt (reissued prepared selected)
        (CallableNamedMetadata.instantiation row) header ∧
      header.function = prepared.view ∧ header.reasonAt = reasonAt selected := by
  obtain ⟨selected⟩ := at_selected prepared.selected (diagnostic_typed prepared wellFormed range)
  obtain ⟨header, aligned⟩ :=
    RecursiveNamedPreparedHeaders.Prepared.canonical_header_with_evidence
      (reissued prepared selected) wellFormed range ordinaryReturn ordinaryParameters target
  exact ⟨selected, header, aligned, aligned.function.trans (reissued_view prepared selected),
    reason_at prepared selected aligned⟩

/-- Retained metadata keeps the original reversed substitution order and
complete resolved dictionary, with the same authentic selected issuer. -/
theorem retained_at_prepared (prepared : Prepared compiled row)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution)
    (ordinaryReturn : row.function.returnComptime = false)
    (ordinaryParameters : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false)
    (target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan
      (CallableNamedCanonicalOrder.retainedInstantiation row) = .ok prepared.named.signature.key) :
    ∃ (selected : SelectedReceipt compiled prepared.named prepared.index)
      (header : CallableIndexedOwnedFunctionValues.Header compiled
        (Program.ofChecked compiled.sourceProgram)),
      RecursiveNamedPreparedHeaders.Prepared.HeaderAt (reissued prepared selected)
        (CallableNamedCanonicalOrder.retainedInstantiation row) header ∧
      header.function = prepared.view ∧ header.reasonAt = reasonAt selected := by
  obtain ⟨selected⟩ := at_selected prepared.selected (diagnostic_typed prepared wellFormed range)
  obtain ⟨header, aligned⟩ :=
    RecursiveNamedPreparedHeaders.Prepared.retained_header_with_evidence
      (reissued prepared selected) wellFormed range ordinaryReturn ordinaryParameters target
  exact ⟨selected, header, aligned, aligned.function.trans (reissued_view prepared selected),
    reason_at prepared selected aligned⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedNamedHeaderReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReceivingPreparedShapeInterpretations
/-! The accepted compatible issuer bounds every token decoded by its actual
receiving-registry table. The sealed callable allocation and genuine completion
retain that same lookup in the public filtered append. Missing-default and
projected-uninitialized interpretation therefore follow from the literal public
decoder. No FaultRep inclusion, hypothetical decoder law, registry inverse or
execution is supplied. Source occurrence ownership remains independent. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReceivingPreparedShapeInterpretations
open Core Frontend SourceInference GeneralHeap CompatiblePayload
open SourceCoreCompatibleDataPlaceFaultSites
open CompatiblePlaceMissingReservedReceipts
open CallableIndexedOwnedPublicFaultReceiverTables
open CallableIndexedOwnedPublicDecodedAssignmentFaults
universe u v

private theorem extra_token_below
    {context : SourceCoreCompatibleDataPlaceFaultSites.Context} {plan : Plan} {root : Key}
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program context}
    {base : SourceCoreProgramFaultSites.Program} {initialExtra : List (Word × Diagnostic)}
    (reserved : ReservedAt context plan root issued base initialExtra)
    {registry : SourceCoreRawMetadata.Registry}
    {extension : SourceCoreRawMetadata.Extends issued.context.registry registry}
    {table : SourceCoreFaultSites.Table}
    (rebuilt : issued.tableForRegistry registry extension = .ok table)
    {row : Word × Diagnostic} (origin : MissingDiagnosticOrigin registry issued.missing row) :
    row.1.val < issued.nextReason := by
  obtain ⟨site, member, rawKey, rawValue, header, lookup, _keys, _values, within, token, _diagnostic⟩ :=
    origin.mapping_header
  have metadata : MetadataRep registry (.mapping rawKey rawValue) header := ⟨lookup⟩
  have bounded := Nat.le_trans (CompatiblePlaceMissingDiagnosticRows.metadata_headerBound metadata)
    (CompatiblePlaceMissingDiagnosticRows.tableForRegistry_budget rebuilt)
  have limits : registry.limits.maxEntries = context.registry.limits.maxEntries :=
    congrArg SourceCoreRawMetadata.Limits.maxEntries extension.limits
  rw [limits] at bounded
  have number : row.1.val = site.base.val + header.val := by
    rw [← token]
    change (site.base.val + header.val) % wordModulus = site.base.val + header.val
    exact Nat.mod_eq_of_lt within
  have below := reserved.missingBelow site member
  rw [number]
  omega

/-- Decode the actual table's existing priority branches. Original fixed rows,
reads, escaped control and zero retain their producer bounds; expanded rows
use their authentic receiving header and reserved range. -/
theorem decoded_token_below
    {context : SourceCoreCompatibleDataPlaceFaultSites.Context} {plan : Plan} {root : Key}
    {sources : List (Key × TypedSource)}
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program context}
    (accepted : SourceCoreCompatibleDataPlaceFaultSites.prepare context plan root sources = .ok issued)
    {registry : SourceCoreRawMetadata.Registry}
    {extension : SourceCoreRawMetadata.Extends issued.context.registry registry}
    {table : SourceCoreFaultSites.Table}
    (rebuilt : issued.tableForRegistry registry extension = .ok table)
    {token : Word} {diagnostic : Diagnostic}
    (decoded : table.diagnostic? token = some diagnostic) : token.val < issued.nextReason := by
  obtain ⟨base, initialExtra, reserved⟩ := CompatiblePlaceMissingPreparationRanges.prepare_reserved_receipt accepted
  obtain ⟨extra, _extraAccepted, tableEq, origins⟩ := issued.tableForRegistry_receipt rebuilt
  by_cases zero : token = Word.zero
  · rw [zero]
    exact reserved.positive
  · by_cases escaped : token = table.escapedReason
    · have same : table.escapedReason = base.rootTable.escapedReason := by
        rw [tableEq, reserved.sameRoot]
      rw [escaped, same]
      exact reserved.escapedBelow
    · simp only [SourceCoreFaultSites.Table.diagnostic?, zero, escaped, ↓reduceIte] at decoded
      cases first : table.additional.find? (fun row => decide (row.1 = token)) with
      | some row =>
        have matched : row.1 = token := of_decide_eq_true (List.find?_some
          (p := fun candidate : Word × Diagnostic => decide (candidate.1 = token)) first)
        have member : row ∈ issued.fixed ++ extra := by
          simpa only [tableEq] using List.mem_of_find?_eq_some first
        rw [← matched]
        rcases List.mem_append.mp member with fixed | expanded
        · exact reserved.fixedBelow row fixed
        · exact extra_token_below reserved rebuilt (origins row expanded)
      | none =>
        simp only [first] at decoded
        cases found : table.reads.find? (fun read => decide (read.reason = token)) with
        | none => simp [found] at decoded
        | some read =>
          have matched : read.reason = token := of_decide_eq_true (List.find?_some
            (p := fun candidate : SourceCoreFaultSites.ReadSite => decide (candidate.reason = token)) found)
          have member : read ∈ base.rootTable.reads := by
            simpa only [tableEq, reserved.sameRoot] using List.mem_of_find?_eq_some found
          rw [← matched]
          exact reserved.readsBelow read member

/-- The sealed compiler supplies compatible preparation and callable allocation.
The actual completion supplies the receiving rebuild and exact public append;
the separately named preappend table is identified by that same successful action. -/
theorem receiver_lookup (compiled : SourceCoreUnifiedCompilation.Compiled)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (present : compiled.indexed.base.diagnostics = some issued)
    {table : SourceCoreFaultSites.Table}
    (rebuilt : issued.tableForRegistry completion.result.context.registry completion.result.extension = .ok table)
    {token : Word} {diagnostic : Diagnostic}
    (decoded : table.diagnostic? token = some diagnostic) :
    completion.result.diagnostics.diagnostic? token = some diagnostic := by
  obtain ⟨root, sources, accepted⟩ :=
    CallableIndexedOwnedPublicDiagnosticReceipts.compiled_diagnostics compiled present
  obtain ⟨actual, actualRebuilt, tableEq⟩ := receiver
  rw [present] at actualRebuilt
  have same : actual = table := Except.ok.inj (actualRebuilt.symm.trans rebuilt)
  subst actual
  rw [tableEq, appendCallable_diagnostic_of_below
    ((CompatiblePublicCallableAllocationReceipts.of_compiled compiled present).below
      (decoded_token_below accepted rebuilt decoded))]
  exact decoded

/-- Both reached-place fields are constructed internally from the same exact
preappend decoder and public receiver. The actual reached state, prepared place
and runtime location are retained; no Source fault or execution is manufactured. -/
theorem reached_interpretation (compiled : SourceCoreUnifiedCompilation.Compiled)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (present : compiled.indexed.base.diagnostics = some issued)
    {table : SourceCoreFaultSites.Table}
    (rebuilt : issued.tableForRegistry completion.result.context.registry completion.result.extension = .ok table)
    {ambient : AmbientDefinitions compiled.compatible.checked.catalog.definitions}
    {functions : FunctionModel compiled.compatible.checked.catalog ambient} {Records : Type v}
    {protocol : ProtectedStateTransition.Protocol.{u, v} Records}
    {environment : Dynamic.Environment} {place : PlaceResolution}
    {prepared : SourceCoreCompatibleDataPlaces.Prepared}
    {initialIndex : ProtectedStateTransition.Index} (initial : protocol.State initialIndex) :
    CallableIndexedOwnedPublicPreparedShapeDiagnostics.ReachedTableInterpretation
      compiled.compatible.checked completion.result.context.registry functions protocol
      environment place prepared initial table (faults completion.result.diagnostics) := by
  constructor
  · intro rawValue token diagnostic decoded error
    refine ⟨diagnostic, receiver_lookup compiled receiver present rebuilt decoded, ?_⟩
    rw [error]
    exact .missing rawValue
  · intro reachedIndex reached location related witness diagnostic decoded error
    refine ⟨diagnostic, receiver_lookup compiled receiver present rebuilt decoded, ?_⟩
    rw [error]
    exact .projectedUninitialized location

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReceivingPreparedShapeInterpretations
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalNamedAssociation
/-! A positive named handle retains the actual installed capture, including
method slots. Equal code alone does not identify its captured environment. The
receipt survives map/world growth and reconstructs the same physical capture
at call time from genuine cache authority. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalNamedAssociation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey NamedCapture NamedSourceAt NamedInstalledCode)
open CallableIndexedOwnedPhysicalGlobals

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {mapping futureMap : LocationMap} {world futureWorld : StoreTyping}
  {sourceType : TypeSystem.Ty} {function : Dynamic.GlobalFunction} {native : Value} {type : Ty}

structure Association
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (mapping : LocationMap) (world : StoreTyping)
    (sourceType : TypeSystem.Ty) (function : Dynamic.GlobalFunction) (native : Value) (type : Ty) where
  owner : OwnedKey keys
  header : Header compiled (Program.ofChecked compiled.sourceProgram)
  rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment
  identity : Word
  capture : NamedCapture headers owner.key header mapping world
  descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
    (.named header.named.signature.key)
  member : header ∈ headers
  sourceAt : NamedSourceAt header rawD function
  installed : NamedInstalledCode capture
  number : Word.ofNat? (header.slot + 1) = some identity
  projection : compiled.compatible.checked.catalog.project header.named.specialized.function.type = .ok
    (CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType)
  typed : RuntimeValueHasType world (.closure header.named.signature.parameterType
    (LanguageResult.resultType header.named.signature.resultType)
    (header.code.rename capture.embedding.lift) capture.captured)
    header.named.signature.functionType compiled.indexed.layouts.definitions
  canonical_eq : capture.canonical = environment compiled
  captured_eq : capture.captured = List.replicate header.slot .unit ++ environment compiled
  embedding_eq : capture.embedding = RecursiveGlobalInitializationMeaning.shift header.slot
  sourceType_eq : sourceType = header.named.specialized.function.type
  native_eq : native = .pair (.pair (.inRight .unit (.word identity))
    (.closure header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType)
      (header.code.rename capture.embedding.lift) capture.captured)) (.word descriptor.id)
  type_eq : type = CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType

variable (association : Association headers keys mapping world sourceType function native type)

/-- Extension keeps the exact original installed environment and code. -/
def Association.extend (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld) :
    Association headers keys futureMap futureWorld sourceType function native type :=
  { association with capture := association.capture.extend maps worlds, typed := association.typed.weaken worlds }

include association in
/-- Forward erasure is used for existing callable classification only. -/
theorem Association.represents {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} :
    CallableIndexedOwnedGeneralLambdaValues.Represents headers keys registry faults mapping world
      sourceType (.global function) native type := by
  rcases association with ⟨owner, header, rawD, identity, capture, descriptor, member, sourceAt,
    installed, number, projection, typed, _canonical, _captured, _embedding, sourceEq, nativeEq, typeEq⟩
  subst sourceType native type
  exact .prior (.prior (.named owner member sourceAt capture installed number projection descriptor typed))


/-- Actual installed captures produce positive named handles without inferring
capture identity from native typing or ordinary Header coverage. -/
def of_capture
    (owner : OwnedKey keys) (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    {store : Store} (capture : CallableIndexedOwnedNamedPhysicalCaptures.Capture headers owner.key header mapping world store)
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} (sourceAt : NamedSourceAt header rawD function)
    (member : header ∈ headers) (installed : NamedInstalledCode capture.named)
    (identity : Word) (number : Word.ofNat? (header.slot + 1) = some identity)
    (projection : compiled.compatible.checked.catalog.project header.named.specialized.function.type = .ok
      (CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType))
    (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key))
    (typed : RuntimeValueHasType world (.closure header.named.signature.parameterType
      (LanguageResult.resultType header.named.signature.resultType)
      (header.code.rename capture.named.embedding.lift) capture.named.captured)
      header.named.signature.functionType compiled.indexed.layouts.definitions) :
    Association headers keys mapping world header.named.specialized.function.type function
      (.pair (.pair (.inRight .unit (.word identity)) (.closure header.named.signature.parameterType
        (LanguageResult.resultType header.named.signature.resultType)
        (header.code.rename capture.named.embedding.lift) capture.named.captured)) (.word descriptor.id))
      (CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType) :=
  ⟨owner, header, rawD, identity, capture.named, descriptor, member, sourceAt, installed, number,
    projection, typed, capture.canonical_eq, capture.captured_eq, capture.embedding_eq, rfl, rfl, rfl⟩

/-- The real cache receipt gives the same retained closure at this later store. -/
theorem Association.at_store {store : Store}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation association.header)
    (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical association.owner.key headers)
    (physical : Authority compiled mapping store) :
    Nonempty { capture : CallableIndexedOwnedNamedPhysicalCaptures.Capture headers association.owner.key
        association.header mapping world store // capture.named = association.capture } := by
  have cached : compiled.indexed.secondPass.closures[association.header.slot]? = some
      (.lambda association.header.named.signature.parameterType
        (LanguageResult.resultType association.header.named.signature.resultType) association.header.code) := by
    rw [aligned.slot, aligned.named, aligned.code]
    exact prepared.cached.trans (congrArg some prepared.compilation.emitted)
  have read := (physical.cached cached).2
  have actualRead : store.read? (association.owner.key.locations association.header) = some (.inRight .unit
      (.closure association.header.named.signature.parameterType
        (LanguageResult.resultType association.header.named.signature.resultType)
        (association.header.code.rename association.capture.embedding.lift) association.capture.captured)) := by
    rw [keyPhysical.locations _ association.member, association.embedding_eq, association.captured_eq]
    exact read
  exact ⟨⟨⟨keyPhysical, association.capture, actualRead, association.canonical_eq, association.captured_eq,
    association.embedding_eq, by rw [association.canonical_eq]; exact environment_slots compiled⟩, rfl⟩⟩

abbrev StaticMember
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (mapping : LocationMap) (world : StoreTyping)
    (sourceType : TypeSystem.Ty) (function : Dynamic.GlobalFunction) (native : Value) (type : Ty) : Prop :=
  Nonempty (Association headers keys mapping world sourceType function native type)

theorem StaticMember.represents {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (member : StaticMember headers keys mapping world sourceType function native type) :
    CallableIndexedOwnedGeneralLambdaValues.Represents headers keys registry faults mapping world
      sourceType (.global function) native type := by
  obtain ⟨association⟩ := member
  exact association.represents

theorem StaticMember.extend (member : StaticMember headers keys mapping world sourceType function native type)
    (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld) :
    StaticMember headers keys futureMap futureWorld sourceType function native type := by
  obtain ⟨association⟩ := member
  exact ⟨association.extend maps worlds⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalNamedAssociation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalCellOrigins
/-! The generic recursive payload and optional-cell relations carry positive
closure associations with every physical cache slot. Actual writes and growth
use the existing generic heap proofs; forward erasure preserves the previous
contextual model. No old closure representation is upgraded by inversion. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalCellOrigins
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPhysicalClosureAssociation (StaticMember)
open CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- A closure leaf carries its exact positive static member. Named leaves retain the actual installed capture, while builtin leaves
retain their original source-shaped receipt. Neither branch admits an erased closure. The body registry is independent of outer payload metadata. -/
inductive FunctionOrigins
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping) :
    TypeSystem.Ty → Dynamic.Value → Value → Ty → Prop where
  | closure {function : Dynamic.Closure} {native : Value}
      {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}
      (member : StaticMember headers keys bodyRegistry faults mapping world
        function native bindings parameter result) :
      FunctionOrigins headers keys bodyRegistry faults mapping world
        (FunctionValues.sourceType function) (.closure function) native
        (CallableContract.functionType parameter result)
  | global {function : Dynamic.GlobalFunction} {sourceType : TypeSystem.Ty}
      {native : Value} {type : Ty}
      (related : CallableIndexedOwnedPhysicalNamedAssociation.StaticMember headers keys
        mapping world sourceType function native type) :
      FunctionOrigins headers keys bodyRegistry faults mapping world
        sourceType (.global function) native type
  | builtin {function : Dynamic.BuiltinFunction} {sourceType : TypeSystem.Ty}
      {native : Value} {type : Ty}
      (related : CallableIndexedOwnedGeneralLambdaValues.Represents headers keys
        bodyRegistry faults mapping world sourceType (.builtin function) native type) :
      FunctionOrigins headers keys bodyRegistry faults mapping world
        sourceType (.builtin function) native type

/-- Erasure retains the original positive contextual association. -/
theorem FunctionOrigins.forget {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {native : Value} {type : Ty}
    (origin : FunctionOrigins headers keys bodyRegistry faults mapping world
      sourceType source native type) :
    CallableIndexedOwnedContextualCellOrigins.FunctionOrigins headers keys bodyRegistry faults
      mapping world sourceType source native type := by
  cases origin with
  | closure member => exact .closure member.forget
  | global related => exact .global related.represents
  | builtin related => exact .builtin related

/-- Only map/world extension acts on a positive member; it does not assert that
any source or native cell still contains that member after a write. -/
def functions (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed) where
  Represents := fun _ mapping world => FunctionOrigins headers keys bodyRegistry faults mapping world
  projection := fun origin =>
    (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).projection
      (registry := bodyRegistry) origin.forget.forget
  runtime_hasType := fun origin =>
    (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).runtime_hasType
      (registry := bodyRegistry) origin.forget.forget
  source_function := fun origin =>
    (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).source_function
      (registry := bodyRegistry) origin.forget.forget
  extend := by
    intro registry futureRegistry mapping futureMapping world futureWorld sourceType source native type
      origin registries maps worlds
    cases origin with
    | closure member => exact .closure (member.extend maps worlds)
    | global related =>
        exact .global (related.extend maps worlds)
    | builtin related =>
        exact .builtin ((CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).extend
          related registries maps worlds)

theorem functions_include_general
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    (functions headers keys bodyRegistry faults profile).Includes
      (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile) :=
  fun origin => origin.forget.forget

theorem functions_include_contextual
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    (functions headers keys bodyRegistry faults profile).Includes
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile) :=
  fun origin => origin.forget

/-- Existing payload constructors recurse over positive function leaves. -/
abbrev PayloadOrigins
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :=
  ValueRep compiled.compatible.checked registry (functions headers keys bodyRegistry faults profile)

abbrev CellOrigins
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :=
  CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (functions headers keys bodyRegistry faults profile)

section Payload
variable (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {mapping : LocationMap} {world : StoreTyping}
  {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {native : Value} {type : Ty}

/-- Attach a newly formed member to that exact value, without changing the
original formation action or its receiving model. -/
theorem payload_static_member {function : Dynamic.Closure}
    {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}
    (member : StaticMember headers keys bodyRegistry faults mapping world function native bindings parameter result) :
    PayloadOrigins headers keys bodyRegistry registry faults profile mapping world
      (FunctionValues.sourceType function) (.closure function) native
      (CallableContract.functionType parameter result) :=
  .function (.closure member)

theorem PayloadOrigins.forget
    (origin : PayloadOrigins headers keys bodyRegistry registry faults profile mapping world
      sourceType source native type) :
    ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile)
      mapping world sourceType source native type :=
  origin.map_functions (functions_include_general profile)

theorem PayloadOrigins.forget_contextual
    (origin : PayloadOrigins headers keys bodyRegistry registry faults profile mapping world
      sourceType source native type) :
    CallableIndexedOwnedContextualCellOrigins.PayloadOrigins headers keys bodyRegistry registry faults profile
      mapping world sourceType source native type :=
  origin.map_functions (functions_include_contextual profile)

/-- Positive source-shape projection includes compatible raw-type wrappers.
It does not inspect an erased general-model representation. -/
theorem PayloadOrigins.closure_member
    (origin : PayloadOrigins headers keys bodyRegistry registry faults profile mapping world
      sourceType source native type) :
    ∀ function, source = .closure function →
      ∃ bindings parameter result,
        StaticMember headers keys bodyRegistry faults mapping world function native bindings parameter result ∧
        type = CallableContract.functionType parameter result := by
  induction origin using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) with
  | function related =>
      cases related with
      | closure member =>
          intro function same
          cases same
          exact ⟨_, _, _, member, rfl⟩
      | global related => intro function impossible; cases impossible
      | builtin related => intro function impossible; cases impossible
  | compatible _ _ ih => exact ih
  | unit | bool | word | integer | product | proxy | constructed | mappingValue =>
      intro function impossible
      cases impossible
  | nil | cons | empty | entry | absent | present => trivial

/-- Named inputs retain their exact original installed capture through compatible
raw-type wrappers; call dispatch does not infer it from native typing. -/
theorem PayloadOrigins.named_member
    (origin : PayloadOrigins headers keys bodyRegistry registry faults profile mapping world
      sourceType source native type) :
    ∀ function, source = .global function →
      ∃ originalType,
        CallableIndexedOwnedPhysicalNamedAssociation.StaticMember headers keys mapping world originalType function native type ∧
        SourceCoreRawMetadata.runtimeType sourceType = SourceCoreRawMetadata.runtimeType originalType := by
  induction origin using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) with
  | function related =>
      cases related with
      | global member => intro function same; cases same; exact ⟨_, member, rfl⟩
      | closure member => intro function impossible; cases impossible
      | builtin related => intro function impossible; cases impossible
  | compatible same _ ih =>
      intro function selected
      obtain ⟨originalType, member, rawType⟩ := ih function selected
      exact ⟨originalType, member, same.trans rawType⟩
  | unit | bool | word | integer | product | proxy | constructed | mappingValue =>
      intro function impossible; cases impossible
  | nil | cons | empty | entry | absent | present => trivial

end Payload

section Heap
variable (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {mapping : LocationMap} {world : StoreTyping}
  {heap after : Dynamic.Heap} {store : Store}

/-- The initial empty heap has no manufactured closure leaves. -/
theorem CellOrigins.empty :
    CellOrigins headers keys bodyRegistry registry faults profile [] [] ⟨[]⟩ [] :=
  GenericHeap.HeapRepresents.empty

theorem CellOrigins.forget
    (origins : CellOrigins headers keys bodyRegistry registry faults profile mapping world heap store) :
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile)
      mapping world heap store :=
  CompatibleAmbientHeap.extend_definitions (functions_include_general profile)
    (.refl _) origins

theorem CellOrigins.forget_contextual
    (origins : CellOrigins headers keys bodyRegistry registry faults profile mapping world heap store) :
    CallableIndexedOwnedContextualCellOrigins.CellOrigins headers keys bodyRegistry registry faults profile
      mapping world heap store :=
  CompatibleAmbientHeap.extend_definitions (functions_include_contextual profile)
    (.refl _) origins

/-- Real administrative allocation appends a typed native cell while preserving
all mapped source cells. No blanket administrative write premise is used. -/
theorem CellOrigins.allocate_administrative {native : Value} {type : Ty}
    (origins : CellOrigins headers keys bodyRegistry registry faults profile mapping world heap store)
    (typed : RuntimeValueHasType world native type compiled.indexed.layouts.definitions) :
    CellOrigins headers keys bodyRegistry registry faults profile mapping (world ++ [type])
      heap (store.allocate native).1 :=
  GenericHeap.HeapRepresents.allocate_administrative origins typed

/-- Actual source allocation and its optional payload grow both stores at their
independent lengths. Every old leaf is transported by the original generic
heap proof. -/
theorem CellOrigins.allocate
    {sourceType : TypeSystem.Ty} {sourceValue : Option Dynamic.Value} {location : Dynamic.Location}
    {native : Value} {payload : Ty}
    (origins : CellOrigins headers keys bodyRegistry registry faults profile mapping world heap store)
    (cell : GenericHeap.CellRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (functions headers keys bodyRegistry faults profile)) mapping world
      ⟨sourceType, sourceValue, none⟩ native payload)
    (allocated : Dynamic.Heap.Allocates heap sourceType sourceValue location after) :
    CellOrigins headers keys bodyRegistry registry faults profile
      (mapping ++ [store.length]) (world ++ [OptionalCell.cellType payload]) after (store.allocate native).1 ∧
    ReferenceRepresents (mapping ++ [store.length]) (world ++ [OptionalCell.cellType payload])
      location store.length payload :=
  GenericHeap.HeapRepresents.allocate origins cell allocated

/-- Only the real write and an authenticated replacement payload update a
mapped cell. The replacement may contain positive closure leaves at any depth. -/
theorem CellOrigins.write_initialized
    {location : Dynamic.Location} {target : Location} {payload : Ty}
    {cell : Dynamic.Cell} {sourceValue : Dynamic.Value} {native : Value}
    (origins : CellOrigins headers keys bodyRegistry registry faults profile mapping world heap store)
    (reference : ReferenceRepresents mapping world location target payload)
    (read : Dynamic.Heap.Reads heap location cell)
    (replacement : PayloadOrigins headers keys bodyRegistry registry faults profile mapping world
      cell.type sourceValue native payload)
    (written : Dynamic.Heap.Writes heap location (some sourceValue) after) :
    ∃ updated, store.write? target (.inRight .unit native) = some updated ∧
      CellOrigins headers keys bodyRegistry registry faults profile mapping world after updated ∧
      AdministrativePreserved mapping store mapping updated :=
  GenericHeap.HeapRepresents.write_initialized origins reference read replacement written

/-- A real typed write to an unmapped administrative cell retains every
positive source-visible leaf. An arbitrary administrative-frame relation does
not replace these actual write, type and separation receipts. -/
theorem CellOrigins.write_administrative
    {updated : Store} {target : Location} {native : Value} {type : Ty}
    (origins : CellOrigins headers keys bodyRegistry registry faults profile mapping world heap store)
    (absent : ∀ {source : Nat}, mapping[source]? ≠ some target)
    (found : world[target]? = some type)
    (typed : RuntimeValueHasType world native type compiled.indexed.layouts.definitions)
    (written : store.write? target native = some updated) :
    CellOrigins headers keys bodyRegistry registry faults profile mapping world heap updated :=
  GenericHeap.HeapRepresents.write_administrative origins absent found typed written

/-- A real initialized read extracts the stronger member and the exact native
cell without recovering physical slots from an erased representation. -/
theorem CellOrigins.stored_at {location : Dynamic.Location} {function : Dynamic.Closure}
    (origins : CellOrigins headers keys bodyRegistry registry faults profile mapping world heap store)
    (read : Dynamic.Heap.Reads heap location
      ⟨FunctionValues.sourceType function, some (.closure function), none⟩) :
    ∃ native bindings parameter result,
      StaticMember headers keys bodyRegistry faults mapping world function native bindings parameter result ∧
      ∃ target, ReferenceRepresents mapping world location target
        (CallableContract.functionType parameter result) ∧
        store.read? target = some (.inRight .unit native) := by
  obtain ⟨target, value, payload, reference, nativeRead, represented⟩ := origins.read read
  cases represented with
  | initialized positive =>
      obtain ⟨bindings, parameter, result, member, sameType⟩ :=
        PayloadOrigins.closure_member profile positive function rfl
      subst payload
      exact ⟨_, bindings, parameter, result, member, target, reference, nativeRead⟩

end Heap

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalCellOrigins
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPositiveFunctionModels
/-! Shared indirect prefix proofs keep their full receiving payload relation.
Only callable classification uses a forward map to the existing positive
contextual origins. Both concrete models supply this map internally. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPositiveFunctionModels
open Core Frontend GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- The receiving model keeps the old header/registry/profile indices in
prefix interfaces while allowing any payload relation at those indices. -/
abbrev Receiving
    (_headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (_keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (_bodyRegistry : SourceCoreRawMetadata.Registry) (_faults : FunctionCalls.FaultRep)
    (_profile : compiled.compatible.checked.catalog.callableContracts = true) :=
  FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)

class ErasesToContextual
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) : Prop where
  erase : functions.Includes
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)

instance contextual (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    ErasesToContextual headers keys bodyRegistry faults profile
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile) :=
  ⟨fun value => value⟩

instance physical (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    ErasesToContextual headers keys bodyRegistry faults profile
      (CallableIndexedOwnedPhysicalCellOrigins.functions headers keys bodyRegistry faults profile) :=
  ⟨CallableIndexedOwnedPhysicalCellOrigins.functions_include_contextual profile⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPositiveFunctionModels
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalFunctionViews
/-! Physical callable values expose their runtime types and identities through
the existing general representation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalFunctionViews
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPhysicalCellOrigins (functions PayloadOrigins CellOrigins)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)

theorem observations :
    FunctionObservations compiled.compatible.checked.catalog
      (functions headers keys bodyRegistry faults profile)
      (CallableIndexedLambdaValues.Identity compiled.indexed) := by
  intro registry mapping world sourceType source native type origin
  exact CallableIndexedOwnedGeneralLambdaValues.observations keys bodyRegistry faults profile
    (registry := registry) (CallableIndexedOwnedPhysicalCellOrigins.functions_include_general profile origin)

theorem runtime_views :
    FunctionRuntimeViews (functions headers keys bodyRegistry faults profile) := by
  intro registry mapping world parameter result source native type origin
  exact CallableIndexedOwnedGeneralLambdaValues.runtime_views keys bodyRegistry faults profile
    (registry := registry) (CallableIndexedOwnedPhysicalCellOrigins.functions_include_general profile origin)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalFunctionViews
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLexicalNamedBodyFaultBounds
/-! Static builtin receipts populate the original lexical Tree factors at each
actual reached input. Named body endpoints use the same flow and finish once;
the first concrete profile is finite discard prefixes with a tail or return. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLexicalNamedBodyFaultBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open NamedLexicalFlowFaultPostContracts
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {source : TypedSource} (evidence : Dynamic.EvidenceEnvironment)
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}

/-- Each accepted expression has its own actual fuel, evidence and primitive
certificate. These are static receipts, not a completed expression meaning. -/
def BuiltinInputs (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope)
    (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) : Prop :=
  ∃ fuel solved reasonAt,
    CompatibleExpressionBuiltins.Tree fuel (.initial compiled.compatible.checked) source context solved reasonAt scope id lowered ∧
    CompatibleExpressionLiterals.ContextValid solved context evidence ∧
    ReachedLoweredReadOutcomePorts.ReadPolicies fuel (.initial compiled.compatible.checked) source context reasonAt faults ∧
    IndexFaultPostContracts.MissingPolicies (.initial compiled.compatible.checked) source functions registry
      program context evidence reasonAt faults

structure StaticContext (context : SourceSemantics.Context) : Prop where
  runtime : Dynamic.SourceRuntimeValid program context source
  covers : evidence.Covers context
  children : ∀ {scope id lowered}, certificates context scope id lowered →
    BuiltinInputs (compiled := compiled) (program := program) (registry := registry) (faults := faults) (source := source) functions evidence context scope id lowered

variable
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (unique : NodeOccurrencesUnique source) (wellFormed : ProgramWellFormed program)

include transport extension faithful observations functionTypes unique wellFormed in
theorem expression_preserves {context : SourceSemantics.Context}
    (inputs : StaticContext (compiled := compiled) (program := program) (registry := registry) (faults := faults) (source := source) (certificates := certificates) functions evidence context)
    (size : Nat) :
    NamedLexicalFlowFaultPostContracts.ExpressionPreservesAt
      (post := ReachedBuiltinExpressionFaultPaths.model_expressionPost compiled.compatible.checked functions registry)
      callerProtocol (readiness bridge) program evidence
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      (ProtectedStateLexicalSourceSites.ExpressionFacts source) (certificates context)
      (context := context) (source := source) (faults := faults) size := by
  intro scope id lowered certificate node found typed mapping world administrative environment canonical actual
    actualContext before store ξ outcome after environments heaps locals agrees actualTyped initial admitted trace
  obtain ⟨fuel, solved, reasonAt, tree, valid, reads, missing⟩ := inputs.children certificate
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related, postAdmission, retained⟩ :=
    CallableIndexedOwnedAdmittedBuiltinFaultBounds.preserves bridge functions evidence transport extension faithful observations
      functionTypes valid reads missing unique wellFormed inputs.runtime inputs.covers tree found typed
      environments heaps locals agrees actualTyped initial admitted trace
  refine ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame,
    metadata, ⟨reached, related, CallableIndexedOwnedAdmittedLexicalReadiness.expression_post bridge postAdmission⟩, ?_⟩
  cases outcome with
  | value sourceValue => trivial
  | fault reason => exact CallableIndexedOwnedAdmittedBuiltinFaultBounds.NativeFaultAt.at_fault retained evaluated

include transport extension faithful observations functionTypes unique wellFormed in
theorem expression_reflects {context : SourceSemantics.Context}
    (inputs : StaticContext (compiled := compiled) (program := program) (registry := registry) (faults := faults) (source := source) (certificates := certificates) functions evidence context)
    (size : Nat) :
    NamedLexicalFlowFaultPostContracts.ExpressionReflectsAt
      (post := ReachedBuiltinExpressionFaultPaths.model_expressionPost compiled.compatible.checked functions registry)
      callerProtocol (readiness bridge) program evidence
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      (ProtectedStateLexicalSourceSites.ExpressionFacts source) (certificates context)
      (context := context) (source := source) (faults := faults) size := by
  intro scope id lowered certificate node found typed mapping world administrative environment canonical actual
    actualContext before store ξ value finalStore environments heaps locals agrees actualTyped initial admitted completed
  obtain ⟨fuel, solved, reasonAt, tree, valid, reads, missing⟩ := inputs.children certificate
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related, postAdmission, retained⟩ :=
    CallableIndexedOwnedAdmittedBuiltinFaultBounds.reflects bridge functions evidence transport extension faithful observations
      functionTypes valid reads missing unique wellFormed inputs.runtime inputs.covers tree found typed
      environments heaps locals agrees actualTyped initial admitted completed
  refine ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame,
    metadata, ⟨reached, related, CallableIndexedOwnedAdmittedLexicalReadiness.expression_post bridge postAdmission⟩, ?_⟩
  cases outcome with
  | value sourceValue => trivial
  | fault reason => exact CallableIndexedOwnedAdmittedBuiltinFaultBounds.NativeFaultAt.at_fault retained completed.sound

section Flows
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {expressionSyntax : ExpressionId → Prop}
  (definitions : layouts.definitions = (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (registered : frame.Registered (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (condition : Location → NativeFrame → Prop)
  (producer : ProtectedStateTransition.OrdinaryAllocation.Producer callerProtocol layouts frame
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
  (bindings : ProtectedStateTransition.Bindings callerProtocol)
  (acquire : ∀ location native, condition location native → ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer location native)
  (validity : SourceSemantics.Context → Prop)
  (contexts : ∀ context, validity context → StaticContext (compiled := compiled) (program := program) (registry := registry) (faults := faults) (source := source) (certificates := certificates) functions evidence context)
  (extend : ∀ {context nextContext binder}, validity context → BinderExtends source.owner context binder nextContext → validity nextContext)

include definitions registered producer bindings acquire unique transport extension faithful observations functionTypes wellFormed contexts extend in
theorem flow_preserves (budget size : Nat) (bounded : size ≤ budget)
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericLexicalStatements.Tree layouts owner active frame globals onError (.initial compiled.compatible.checked)
      source certificates context scope mode statements expected type code) :
    NamedLexicalFlowFaultPostContracts.PreservesAtFor
      (post := FlowPost (ReachedBuiltinExpressionFaultPaths.model_expressionPost compiled.compatible.checked functions registry))
      callerProtocol (readiness bridge) condition (GenericLexicalStatements.Syntax source expressionSyntax)
      (values := .initial compiled.compatible.checked) (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frame) (globals := globals) size (scope := scope) mode statements expected type code := by
  intro valid sourceFacts mapping world administrative actualContext environment canonical actual before after store ξ
    contextLocation native outcome finalContext environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
  exact RecursiveNamedLexicalTreeBounds.Stateful.WithReady.preserves_at_for_with_post
    (expressionPost := ReachedBuiltinExpressionFaultPaths.model_expressionPost compiled.compatible.checked functions registry)
    (headPost := HeadPost (ReachedBuiltinExpressionFaultPaths.model_expressionPost compiled.compatible.checked functions registry))
    (flowPost := FlowPost (ReachedBuiltinExpressionFaultPaths.model_expressionPost compiled.compatible.checked functions registry))
    (joins := origin_joins _ program evidence source)
    (protocol := callerProtocol) (condition := condition) (producer := producer) (stateBindings := bindings) (acquire := acquire)
    (readiness := readiness bridge) (facts := GenericLexicalStatements.Syntax source expressionSyntax)
    (headFacts := ProtectedStateLexicalSourceSites.HeadFacts source expressionSyntax)
    (exprFacts := ProtectedStateLexicalSourceSites.ExpressionFacts source)
    (sites := ProtectedStateLexicalSourceSites.sites program evidence unique)
    (transfers := CallableIndexedOwnedAdmittedLexicalReadiness.allocation_transfers bridge bindings source)
    functions definitions registered program evidence validity extend budget size bounded
    (fun child _ context valid => expression_preserves bridge functions evidence transport extension faithful observations functionTypes unique wellFormed (contexts context valid) child)
    tree valid sourceFacts unique environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace

include definitions registered producer bindings acquire unique transport extension faithful observations functionTypes wellFormed contexts extend in
theorem flow_reflects (budget size : Nat) (bounded : size ≤ budget)
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericLexicalStatements.Tree layouts owner active frame globals onError (.initial compiled.compatible.checked)
      source certificates context scope mode statements expected type code) :
    NamedLexicalFlowFaultPostContracts.ReflectsAtFor
      (post := FlowPost (ReachedBuiltinExpressionFaultPaths.model_expressionPost compiled.compatible.checked functions registry))
      callerProtocol (readiness bridge) condition (GenericLexicalStatements.Syntax source expressionSyntax)
      (values := .initial compiled.compatible.checked) (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frame) (globals := globals) size (scope := scope) mode statements expected type code := by
  intro valid sourceFacts mapping world administrative actualContext environment canonical actual before store finalStore ξ
    contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted evaluated
  exact RecursiveNamedLexicalTreeBounds.Stateful.WithReady.reflects_at_for_with_post
    (expressionPost := ReachedBuiltinExpressionFaultPaths.model_expressionPost compiled.compatible.checked functions registry)
    (headPost := HeadPost (ReachedBuiltinExpressionFaultPaths.model_expressionPost compiled.compatible.checked functions registry))
    (flowPost := FlowPost (ReachedBuiltinExpressionFaultPaths.model_expressionPost compiled.compatible.checked functions registry))
    (joins := origin_joins _ program evidence source)
    (protocol := callerProtocol) (condition := condition) (producer := producer) (stateBindings := bindings) (acquire := acquire)
    (readiness := readiness bridge) (facts := GenericLexicalStatements.Syntax source expressionSyntax)
    (headFacts := ProtectedStateLexicalSourceSites.HeadFacts source expressionSyntax)
    (exprFacts := ProtectedStateLexicalSourceSites.ExpressionFacts source)
    (sites := ProtectedStateLexicalSourceSites.sites program evidence unique)
    (transfers := CallableIndexedOwnedAdmittedLexicalReadiness.allocation_transfers bridge bindings source)
    functions definitions registered program evidence validity extend budget size bounded
    (fun child _ context valid => expression_reflects bridge functions evidence transport extension faithful observations functionTypes unique wellFormed (contexts context valid) child)
    tree valid sourceFacts environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted evaluated

end Flows

/-- The first concrete grammar has only executed discards before one real tail
or explicit return. This is a static shape receipt, not a semantic traversal. -/
inductive DiscardReturnProfile (source : TypedSource) : List StatementId → Prop where
  | tail {id node expression} (found : source.lookupStatement? id = some node)
      (form : node.form = .expression expression false) : DiscardReturnProfile source [id]
  | returning {id node expression} (found : source.lookupStatement? id = some node)
      (form : node.form = .returnStmt (some expression)) : DiscardReturnProfile source [id]
  | discard {id node expression semicolon rest} (found : source.lookupStatement? id = some node)
      (form : node.form = .expression expression semicolon)
      (notTail : (!semicolon && true && rest.isEmpty) = false)
      (remaining : DiscardReturnProfile source rest) : DiscardReturnProfile source (id :: rest)

section NamedBodies
open RecursiveNamedCatalogInvocationBounds CallableIndexedHistory
open CallableIndexedOwnedInvocationBounds CallableIndexedOwnedIndirectExpressionHeads
open CallableIndexedOwnedAdmittedBodyEntries (SourceReceipt)

private def poolBridge {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)} :
    CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) (protocol headers keys) :=
  CallableIndexedOwnedIndirectCallerProtocol.of_legacy CallableIndexedOwnedCallerProtocol.base

variable {header : CallableIndexedOwnedFunctionValues.Header compiled program}
  {expressionSyntax : ExpressionId → Prop} {flow : Expr}
  (validity : SourceSemantics.Context → Prop)

/-- The compiler acceptances, literal source grammar and actual child domains
all refer to this Header. No expression, flow or body meaning is a field. -/
structure BodyInputs : Prop where
  profile : DiscardReturnProfile header.function.source header.function.body
  syntaxTree : GenericLexicalStatements.Syntax header.function.source expressionSyntax header.context true
    header.function.body header.function.resultType
  tree : GenericLexicalStatements.Tree compiled.indexed.layouts header.owner header.active
    compiled.indexed.ancestry.layout.frame header.globals header.onError (.initial compiled.compatible.checked)
    header.function.source certificates header.context
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) true
    header.function.body header.function.resultType header.output flow
  accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
    header.output header.reasonAt header.fellThrough header.escaped = .ok header.body
  generated : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
    header.output header.reasonAt true header.escaped = .ok flow
  projection : compiled.compatible.checked.catalog.project header.function.resultType = .ok header.output
  valid : validity header.context
  contexts : ∀ context, validity context → StaticContext (compiled := compiled) (program := program)
    (registry := registry) (faults := faults) (source := header.function.source) (certificates := certificates)
    functions header.function.evidence context
  extend : ∀ {context nextContext binder}, validity context →
    BinderExtends header.function.source.owner context binder nextContext → validity nextContext

/-- The same literal static inputs without restricting the grammar profile. -/
structure StaticBodyInputs : Prop where
  syntaxTree : GenericLexicalStatements.Syntax header.function.source expressionSyntax header.context true
    header.function.body header.function.resultType
  tree : GenericLexicalStatements.Tree compiled.indexed.layouts header.owner header.active
    compiled.indexed.ancestry.layout.frame header.globals header.onError (.initial compiled.compatible.checked)
    header.function.source certificates header.context
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) true
    header.function.body header.function.resultType header.output flow
  accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
    header.output header.reasonAt header.fellThrough header.escaped = .ok header.body
  generated : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
    header.output header.reasonAt true header.escaped = .ok flow
  projection : compiled.compatible.checked.catalog.project header.function.resultType = .ok header.output
  valid : validity header.context
  contexts : ∀ context, validity context → StaticContext (compiled := compiled) (program := program)
    (registry := registry) (faults := faults) (source := header.function.source) (certificates := certificates)
    functions header.function.evidence context
  extend : ∀ {context nextContext binder}, validity context →
    BinderExtends header.function.source.owner context binder nextContext → validity nextContext

/-- The original profile contributes no dynamic hypothesis to this finite receipt. -/
theorem BodyInputs.static_inputs (inputs : BodyInputs (functions := functions) (header := header)
    (registry := registry) (faults := faults) (certificates := certificates)
    (expressionSyntax := expressionSyntax) (flow := flow) validity) :
    StaticBodyInputs (functions := functions) (header := header) (registry := registry)
      (faults := faults) (certificates := certificates) (expressionSyntax := expressionSyntax)
      (flow := flow) validity := {
  syntaxTree := inputs.syntaxTree,
  tree := inputs.tree,
  accepted := inputs.accepted,
  generated := inputs.generated,
  projection := inputs.projection,
  valid := inputs.valid,
  contexts := inputs.contexts,
  extend := inputs.extend }

variable (inputs : BodyInputs (functions := functions) (header := header) (registry := registry)
  (faults := faults) (certificates := certificates) (expressionSyntax := expressionSyntax) (flow := flow) validity)

include inputs in
private theorem BodyInputs.emitted : header.body = CompatibleStatements.finish header.output flow header.fellThrough header.escaped := by
  exact with_static (staticInputs := BodyInputs.static_inputs functions validity inputs)
where
  with_static (staticInputs : StaticBodyInputs (functions := functions) (header := header)
        (registry := registry) (faults := faults) (certificates := certificates)
        (expressionSyntax := expressionSyntax) (flow := flow) validity) : header.body = CompatibleStatements.finish header.output flow header.fellThrough header.escaped := by
    have accepted := staticInputs.accepted
    unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
    rw [staticInputs.generated] at accepted
    exact Except.ok.inj accepted.symm

include inputs in
private theorem BodyInputs.transfers {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {sourceSize : Nat} {finalContext : SourceSemantics.Context} {control : Dynamic.ControlOutcome}
    (trace : RecursiveNamedLoopContracts.ExecutesAt sourceSize true program header.context header.function.evidence
      header.function.source environment before header.function.body finalContext control after) :
    ImperativeFunctionFinish.TransferFaults faults header.escaped control := by
  exact with_static (staticInputs := BodyInputs.static_inputs functions validity inputs) trace
where
  with_static (staticInputs : StaticBodyInputs (functions := functions) (header := header)
        (registry := registry) (faults := faults) (certificates := certificates)
        (expressionSyntax := expressionSyntax) (flow := flow) validity) {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {sourceSize : Nat} {finalContext : SourceSemantics.Context} {control : Dynamic.ControlOutcome}
    (trace : RecursiveNamedLoopContracts.ExecutesAt sourceSize true program header.context header.function.evidence
      header.function.source environment before header.function.body finalContext control after) :
    ImperativeFunctionFinish.TransferFaults faults header.escaped control := by
    cases trace with
    | fault failed => constructor <;> intro next same <;> cases same
    | control executed =>
      cases GenericLexicalStatements.syntax_control_shape staticInputs.syntaxTree header.unique executed.sound <;>
        constructor <;> intro next same <;> cases same

variable {locations : CallableIndexedOwnedFunctionValues.Header compiled program → Location} {capturePrefix : Nat}
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
  (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
    administrative actualContext actual ξ frameLocation current ghost)
  (reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
    entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
  (sourceReceipt : SourceReceipt program header.function header.context entry.environment entry.heap)
  (rows : StableRows reached)
  (stable : CallableIndexedOwnedAllocationProducer.StableOwner keys frameLocation current)

private theorem body_reference : entry.canonical[
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))).length + 1 + header.globals]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type frameLocation) := by
  simpa only [List.length_map, List.length_reverse] using entry.reference

private theorem body_unmapped : frameLocation ∉ entry.mapping := by
  have unmapped := entry.catalog.authority.unmapped
  simpa only [entry.catalog_frame] using unmapped

include inputs sourceReceipt rows stable extension faithful observations functionTypes wellFormed in
/-- Authentic static child certificates populate the shared Tree and finish
at this actual parameter state. The fault post remains at the body store. -/
theorem source_body_with_post (size : Nat) :
    SourceBodyAtWithPost (ReachedNamedLexicalBodyFaultPaths.model_bodyPost compiled.compatible.checked functions registry)
      (faults := faults) entry reached size := by
  exact with_static (extension := extension) (faithful := faithful) (observations := observations)
    (functionTypes := functionTypes) (wellFormed := wellFormed) (sourceReceipt := sourceReceipt)
    (rows := rows) (stable := stable) (staticInputs := BodyInputs.static_inputs functions validity inputs) size
where
  with_static (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
      (faithful : DataEquality.IdentityFaithful identities)
      (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
      (functionTypes : FunctionRuntimeViews functions) (wellFormed : ProgramWellFormed program)
      (sourceReceipt : SourceReceipt program header.function header.context entry.environment entry.heap)
      (rows : StableRows reached)
      (stable : CallableIndexedOwnedAllocationProducer.StableOwner keys frameLocation current)
      (staticInputs : StaticBodyInputs (functions := functions) (header := header)
        (registry := registry) (faults := faults) (certificates := certificates)
        (expressionSyntax := expressionSyntax) (flow := flow) validity) (size : Nat) :
    SourceBodyAtWithPost (ReachedNamedLexicalBodyFaultPaths.model_bodyPost compiled.compatible.checked functions registry)
      (faults := faults) entry reached size := by
    intro outcome after trace
    let bodyBridge := poolBridge (headers := headers) (keys := keys)
    let model := CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
    let producer := CallableIndexedOwnedAllocationProducer.producer headers keys model
    let condition := CallableIndexedOwnedAllocationProducer.StableOwner keys
    have meaning := flow_preserves bodyBridge functions header.function.evidence
      (administrativeTransport headers keys) extension faithful observations functionTypes header.unique wellFormed
      (layouts := compiled.indexed.layouts) (owner := header.owner) (active := header.active)
      (frame := compiled.indexed.ancestry.layout.frame) (globals := header.globals) (onError := header.onError)
      (expressionSyntax := expressionSyntax) rfl header.registered condition producer
      (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
      (fun _ _ seed => CallableIndexedOwnedAllocationProducer.readyAt_of_stableOwner model seed)
      validity staticInputs.contexts staticInputs.extend size size (Nat.le_refl size) staticInputs.tree
    have lifted := NamedLexicalFunctionFaultPostContracts.PreservesAtWith.of_lexical
      (protocol := protocol headers keys) (readiness := readiness bodyBridge) (condition := condition)
      (facts := GenericLexicalStatements.Syntax header.function.source expressionSyntax)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (functions := functions) (program := program) (evidence := header.function.evidence)
      (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
      (meaning := meaning)
    have matchTree := GenericImperativeMatch.Tree.body
      (definitions := (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
      (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
      staticInputs.syntaxTree staticInputs.tree
    obtain ⟨value, bodyStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame,
      metadata, _exit, finalTransition, retained⟩ :=
      RecursiveNamedFunctionFinishBounds.WithReady.preserves_at_emitted_with_state_when_with_transfers_with_post
        (functions := functions) (program := program) (tree := matchTree) (projection := staticInputs.projection) (unique := header.unique)
        (FlowPost (ReachedBuiltinExpressionFaultPaths.model_expressionPost compiled.compatible.checked functions registry))
        (protocol headers keys) (readiness bodyBridge) condition
        (GenericLexicalStatements.Syntax header.function.source expressionSyntax) (BodyInputs.emitted.with_static (functions := functions) (validity := validity) (staticInputs := staticInputs))
        validity size lifted staticInputs.valid staticInputs.syntaxTree
        entry.environments entry.heaps sourceReceipt.locals entry.lookups entry.actualTyped
        (body_reference functions entry) entry.state.read (body_unmapped functions entry) reached stable
        (show Admission bodyBridge header.context reached from ⟨sourceReceipt.heapTyped, rows⟩)
        (BodyInputs.transfers.with_static (functions := functions) (validity := validity) (staticInputs := staticInputs)) trace
    exact ⟨value, bodyStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame,
      metadata, ProtectedStateTransition.FunctionFinish.Reached.forget finalTransition,
      ReachedNamedLexicalBodyFaultPaths.outcome_post_of_finished staticInputs.syntaxTree header.unique retained evaluated⟩

include inputs sourceReceipt rows stable extension faithful observations functionTypes wellFormed in
/-- Native finish selects its genuine strict flow child. The Source grade is
constructed independently by the same shared producer at the reached state. -/
theorem native_body_with_post (size : Nat) :
    NativeBodyAtWithPost (ReachedNamedLexicalBodyFaultPaths.model_bodyPost compiled.compatible.checked functions registry)
      (faults := faults) entry reached size := by
  exact with_static (extension := extension) (faithful := faithful) (observations := observations)
    (functionTypes := functionTypes) (wellFormed := wellFormed) (sourceReceipt := sourceReceipt)
    (rows := rows) (stable := stable) (staticInputs := BodyInputs.static_inputs functions validity inputs) size
where
  with_static (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
      (faithful : DataEquality.IdentityFaithful identities)
      (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
      (functionTypes : FunctionRuntimeViews functions) (wellFormed : ProgramWellFormed program)
      (sourceReceipt : SourceReceipt program header.function header.context entry.environment entry.heap)
      (rows : StableRows reached)
      (stable : CallableIndexedOwnedAllocationProducer.StableOwner keys frameLocation current)
      (staticInputs : StaticBodyInputs (functions := functions) (header := header)
        (registry := registry) (faults := faults) (certificates := certificates)
        (expressionSyntax := expressionSyntax) (flow := flow) validity) (size : Nat) :
    NativeBodyAtWithPost (ReachedNamedLexicalBodyFaultPaths.model_bodyPost compiled.compatible.checked functions registry)
      (faults := faults) entry reached size := by
    intro value bodyStore evaluated
    let bodyBridge := poolBridge (headers := headers) (keys := keys)
    let model := CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
    let producer := CallableIndexedOwnedAllocationProducer.producer headers keys model
    let condition := CallableIndexedOwnedAllocationProducer.StableOwner keys
    have meaning : RecursiveNamedBoundedContracts.Below size (fun child =>
        NamedLexicalFunctionFaultPostContracts.ReflectsAtWith
          (post := FlowPost (ReachedBuiltinExpressionFaultPaths.model_expressionPost compiled.compatible.checked functions registry))
          (protocol headers keys) (readiness bodyBridge) condition
          (GenericLexicalStatements.Syntax header.function.source expressionSyntax)
          (values := .initial compiled.compatible.checked) functions program header.function.evidence validity
          (source := header.function.source) (context := header.context) (registry := registry) (faults := faults)
          (frameLayout := compiled.indexed.ancestry.layout.frame) (globals := header.globals)
          (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
          child (scope := header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) true
          header.function.body header.function.resultType header.output flow) := by
      intro child smaller
      exact NamedLexicalFunctionFaultPostContracts.ReflectsAtWith.of_lexical
        (protocol := protocol headers keys) (readiness := readiness bodyBridge) (condition := condition)
        (facts := GenericLexicalStatements.Syntax header.function.source expressionSyntax)
        (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (functions := functions) (program := program) (evidence := header.function.evidence)
        (meaning := flow_reflects bodyBridge functions header.function.evidence
          (administrativeTransport headers keys) extension faithful observations functionTypes header.unique wellFormed
          (layouts := compiled.indexed.layouts) (owner := header.owner) (active := header.active)
          (frame := compiled.indexed.ancestry.layout.frame) (globals := header.globals) (onError := header.onError)
          (expressionSyntax := expressionSyntax) rfl header.registered condition producer
          (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
          (fun _ _ seed => CallableIndexedOwnedAllocationProducer.readyAt_of_stableOwner model seed)
          validity staticInputs.contexts staticInputs.extend size child (Nat.le_of_lt smaller) staticInputs.tree)
    have matchTree := GenericImperativeMatch.Tree.body
      (definitions := (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
      (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
      staticInputs.syntaxTree staticInputs.tree
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame,
      metadata, _exit, finalTransition, retained⟩ :=
      RecursiveNamedFunctionFinishBounds.WithReady.reflects_at_emitted_with_state_when_with_transfers_with_post
        (functions := functions) (program := program) (tree := matchTree) (projection := staticInputs.projection) (unique := header.unique)
        (FlowPost (ReachedBuiltinExpressionFaultPaths.model_expressionPost compiled.compatible.checked functions registry))
        (protocol headers keys) (readiness bodyBridge) condition
        (GenericLexicalStatements.Syntax header.function.source expressionSyntax) (BodyInputs.emitted.with_static (functions := functions) (validity := validity) (staticInputs := staticInputs))
        validity size size (Nat.le_refl size) meaning staticInputs.valid staticInputs.syntaxTree
        entry.environments entry.heaps sourceReceipt.locals entry.lookups entry.actualTyped
        (body_reference functions entry) entry.state.read (body_unmapped functions entry) reached stable
        (show Admission bodyBridge header.context reached from ⟨sourceReceipt.heapTyped, rows⟩)
        (BodyInputs.transfers.with_static (functions := functions) (validity := validity) (staticInputs := staticInputs)) evaluated
    exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame,
      metadata, ProtectedStateTransition.FunctionFinish.Reached.forget finalTransition,
      ReachedNamedLexicalBodyFaultPaths.outcome_post_of_finished staticInputs.syntaxTree header.unique retained evaluated.sound⟩

include inputs sourceReceipt rows stable extension faithful observations functionTypes wellFormed in
/-- Strict membership retains the same concrete Source body producer. -/
theorem source_below (budget : Nat) :
    RecursiveNamedBoundedContracts.Below budget
      (SourceBodyAtWithPost (ReachedNamedLexicalBodyFaultPaths.model_bodyPost compiled.compatible.checked functions registry)
        (faults := faults) entry reached) := by
  intro child _strict
  exact source_body_with_post functions extension faithful observations functionTypes wellFormed
    validity inputs entry reached sourceReceipt rows stable child

include inputs sourceReceipt rows stable extension faithful observations functionTypes wellFormed in
/-- Each native member uses its own actual measured body completion. -/
theorem native_below (budget : Nat) :
    RecursiveNamedBoundedContracts.Below budget
      (NativeBodyAtWithPost (ReachedNamedLexicalBodyFaultPaths.model_bodyPost compiled.compatible.checked functions registry)
        (faults := faults) entry reached) := by
  intro child _strict
  exact native_body_with_post functions extension faithful observations functionTypes wellFormed
    validity inputs entry reached sourceReceipt rows stable child

section Parameters
variable (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {initial : ProtectedStateTransition.Index} {argumentsPool : State headers keys initial}
  {parameterArguments : List Dynamic.Value}
  (parameters : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt (registry := registry)
    functions owner argumentsPool header parameterArguments)

include inputs parameters extension faithful observations functionTypes wellFormed in
/-- The actual parameter receipt supplies deep Source admission, all rows and
its literal stable hook. No body semantics is supplied by the caller. -/
theorem source_at_parameters (size : Nat) :
    SourceBodyAtWithPost (ReachedNamedLexicalBodyFaultPaths.model_bodyPost compiled.compatible.checked functions registry)
      (faults := faults) parameters.body parameters.reached size :=
  source_body_with_post functions extension faithful observations functionTypes wellFormed
    validity inputs parameters.body parameters.reached (parameters.source wellFormed) parameters.rows parameters.stable_owner size

include inputs parameters extension faithful observations functionTypes wellFormed in
/-- Native reflection starts at the same real hook and parameter state. -/
theorem native_at_parameters (size : Nat) :
    NativeBodyAtWithPost (ReachedNamedLexicalBodyFaultPaths.model_bodyPost compiled.compatible.checked functions registry)
      (faults := faults) parameters.body parameters.reached size :=
  native_body_with_post functions extension faithful observations functionTypes wellFormed
    validity inputs parameters.body parameters.reached (parameters.source wellFormed) parameters.rows parameters.stable_owner size
end Parameters

end NamedBodies

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLexicalNamedBodyFaultBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAbsentAllocationNamedBodyFaultBounds
/-! One actual absent local allocation precedes the supported discard/return
suffix. Static constructor receipts build the whole lexical Tree; the original
Tree and finish producers supply allocation, readiness and fault provenance. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAbsentAllocationNamedBodyFaultBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedLexicalNamedBodyFaultBounds
open CallableIndexedOwnedInvocationBounds CallableIndexedOwnedIndirectExpressionHeads
open RecursiveNamedCatalogInvocationBounds
open CallableIndexedOwnedAdmittedBodyEntries (SourceReceipt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {header : CallableIndexedOwnedFunctionValues.Header compiled program}
  {expressionSyntax : ExpressionId → Prop}
  {id : StatementId} {node : StatementNode} {binder : TypedBinder}
  {nextContext : SourceSemantics.Context} {rest : List StatementId} {payload : Ty} {suffixFlow : Expr}
  (allocation : SourceCoreAllocationLayouts.Allocation compiled.indexed.layouts header.owner header.active
    (GenericLexicalStatements.absentRequest header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) binder payload))
  (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated compiled.indexed.ancestry.layout.frame
    header.globals (compiled.indexed.layouts.allocatorAt header.owner header.active header.onError)
    (GenericLexicalStatements.absentRequest header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) binder payload))
  (validity : SourceSemantics.Context → Prop)

/-- Every field refers to the same Header, binder and actual allocator layout.
The suffix has static certificates; no expression or body semantics is supplied. -/
structure AbsentInputs : Prop where
  body : header.function.body = id :: rest
  found : header.function.source.lookupStatement? id = some node
  form : node.form = .letDecl binder none
  declaration : SourceCoreDataPlaces.rootBinder header.function.source binder.id = .ok binder
  monomorphic : binder.scheme.quantified = []
  extended : BinderExtends header.function.source.owner header.context binder nextContext
  ordinary : header.function.source.inputs.any (fun input => decide (input.id = binder.id)) = false
  projected : compiled.compatible.checked.catalog.project binder.scheme.body = .ok payload
  same : annotation.original = allocation.expression
  suffixProfile : DiscardReturnProfile header.function.source rest
  suffixSyntax : GenericLexicalStatements.Syntax header.function.source expressionSyntax nextContext true
    rest header.function.resultType
  suffixTree : GenericLexicalStatements.Tree compiled.indexed.layouts header.owner header.active
    compiled.indexed.ancestry.layout.frame header.globals header.onError (.initial compiled.compatible.checked)
    header.function.source certificates nextContext
    ((binder.id, payload) :: header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) true
    rest header.function.resultType header.output suffixFlow
  accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
    header.output header.reasonAt header.fellThrough header.escaped = .ok header.body
  generated : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
    header.output header.reasonAt true header.escaped = .ok (.letE annotation.expression suffixFlow)
  projection : compiled.compatible.checked.catalog.project header.function.resultType = .ok header.output
  valid : validity header.context
  contexts : ∀ context, validity context → StaticContext (compiled := compiled) (program := program)
    (registry := registry) (faults := faults) (source := header.function.source) (certificates := certificates)
    functions header.function.evidence context
  extend : ∀ {context nextContext binder}, validity context →
    BinderExtends header.function.source.owner context binder nextContext → validity nextContext

variable (inputs : AbsentInputs (functions := functions) (registry := registry) (faults := faults)
  (certificates := certificates) (expressionSyntax := expressionSyntax) (id := id) (node := node)
  (nextContext := nextContext) (rest := rest) (suffixFlow := suffixFlow) allocation annotation validity)

include inputs in
/-- Only the genuine absent-let constructors are added to the static suffix.
Its real accepted flow remains indexed by the actual annotation expression. -/
theorem static_inputs :
    StaticBodyInputs (functions := functions) (header := header) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (flow := .letE annotation.expression suffixFlow) validity := by
  refine {
    syntaxTree := ?_
    tree := ?_
    accepted := inputs.accepted
    generated := inputs.generated
    projection := inputs.projection
    valid := inputs.valid
    contexts := inputs.contexts
    extend := inputs.extend }
  · rw [inputs.body]
    exact .uninitialized inputs.found inputs.form inputs.declaration inputs.monomorphic inputs.extended
      inputs.ordinary inputs.suffixSyntax
  · rw [inputs.body]
    exact .uninitialized inputs.found inputs.form inputs.monomorphic inputs.extended inputs.ordinary
      inputs.projected allocation annotation inputs.same inputs.suffixTree

variable
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions) (wellFormed : ProgramWellFormed program)
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
  (sourceReceipt : SourceReceipt program header.function header.context entry.environment entry.heap)
  (rows : StableRows reached)
  (stable : CallableIndexedOwnedAllocationProducer.StableOwner keys frameLocation current)

include inputs sourceReceipt rows stable extension faithful observations functionTypes wellFormed in
/-- The original lexical allocation/readiness and finish producers run once.
The genuine fault post stays at the returned bodyStore. -/
theorem source_body_with_post (size : Nat) :
    SourceBodyAtWithPost (ReachedNamedLexicalBodyFaultPaths.model_bodyPost compiled.compatible.checked functions registry)
      (faults := faults) entry reached size :=
  CallableIndexedOwnedLexicalNamedBodyFaultBounds.source_body_with_post.with_static functions validity entry reached
    extension faithful observations functionTypes wellFormed sourceReceipt rows stable
    (static_inputs functions allocation annotation validity inputs) size

include inputs sourceReceipt rows stable extension faithful observations functionTypes wellFormed in
/-- Native reflection selects the actual allocation suffix completion; its
Source grade is reconstructed independently by the shared lexical producer. -/
theorem native_body_with_post (size : Nat) :
    NativeBodyAtWithPost (ReachedNamedLexicalBodyFaultPaths.model_bodyPost compiled.compatible.checked functions registry)
      (faults := faults) entry reached size :=
  CallableIndexedOwnedLexicalNamedBodyFaultBounds.native_body_with_post.with_static functions validity entry reached
    extension faithful observations functionTypes wellFormed sourceReceipt rows stable
    (static_inputs functions allocation annotation validity inputs) size

include inputs sourceReceipt rows stable extension faithful observations functionTypes wellFormed in
theorem source_below (budget : Nat) :
    RecursiveNamedBoundedContracts.Below budget
      (SourceBodyAtWithPost (ReachedNamedLexicalBodyFaultPaths.model_bodyPost compiled.compatible.checked functions registry)
        (faults := faults) entry reached) := by
  intro child _strict
  exact source_body_with_post functions allocation annotation validity inputs extension faithful observations
    functionTypes wellFormed entry reached sourceReceipt rows stable child

include inputs sourceReceipt rows stable extension faithful observations functionTypes wellFormed in
theorem native_below (budget : Nat) :
    RecursiveNamedBoundedContracts.Below budget
      (NativeBodyAtWithPost (ReachedNamedLexicalBodyFaultPaths.model_bodyPost compiled.compatible.checked functions registry)
        (faults := faults) entry reached) := by
  intro child _strict
  exact native_body_with_post functions allocation annotation validity inputs extension faithful observations
    functionTypes wellFormed entry reached sourceReceipt rows stable child

section Parameters
variable (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {initial : ProtectedStateTransition.Index} {argumentsPool : State headers keys initial}
  {parameterArguments : List Dynamic.Value}
  (parameters : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt (registry := registry)
    functions owner argumentsPool header parameterArguments)

include inputs parameters extension faithful observations functionTypes wellFormed in
/-- The actual parameter receipt supplies native frame/read facts, deep Source
admission, all live rows and its stable hook at this same body entry. -/
theorem source_at_parameters (size : Nat) :
    SourceBodyAtWithPost (ReachedNamedLexicalBodyFaultPaths.model_bodyPost compiled.compatible.checked functions registry)
      (faults := faults) parameters.body parameters.reached size :=
  source_body_with_post functions allocation annotation validity inputs extension faithful observations
    functionTypes wellFormed parameters.body parameters.reached
    (parameters.source wellFormed) parameters.rows parameters.stable_owner size

include inputs parameters extension faithful observations functionTypes wellFormed in
theorem native_at_parameters (size : Nat) :
    NativeBodyAtWithPost (ReachedNamedLexicalBodyFaultPaths.model_bodyPost compiled.compatible.checked functions registry)
      (faults := faults) parameters.body parameters.reached size :=
  native_body_with_post functions allocation annotation validity inputs extension faithful observations
    functionTypes wellFormed parameters.body parameters.reached
    (parameters.source wellFormed) parameters.rows parameters.stable_owner size
end Parameters

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAbsentAllocationNamedBodyFaultBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLexicalNamedBodyPostProviders
/-! Supported static lexical bodies supply concrete causal posts at the real
successful argument and parameter state. The existing outer named/direct
producer consumes the same receipt once and retains its full call route. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLexicalNamedBodyPostProviders
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

/-- The actual Header-indexed compiler and child certificates select the
supported lexical grammar. These constructors contain no completed semantics. -/
inductive SupportedInputs (header : CallableIndexedOwnedFunctionValues.Header compiled program) : Prop where
  | discardReturn {expressionSyntax : ExpressionId → Prop}
      {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
      {flow : Expr} {validity : SourceSemantics.Context → Prop}
      (inputs : CallableIndexedOwnedLexicalNamedBodyFaultBounds.BodyInputs
        (functions := functions) (header := header) (registry := registry) (faults := faults)
        (certificates := certificates) (expressionSyntax := expressionSyntax) (flow := flow) validity) :
      SupportedInputs header
  | absent {expressionSyntax : ExpressionId → Prop}
      {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
      {validity : SourceSemantics.Context → Prop}
      {id : StatementId} {node : StatementNode} {binder : TypedBinder}
      {nextContext : SourceSemantics.Context} {rest : List StatementId} {payload : Ty} {suffixFlow : Expr}
      (allocation : SourceCoreAllocationLayouts.Allocation compiled.indexed.layouts header.owner header.active
        (GenericLexicalStatements.absentRequest header.function.source
          (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) binder payload))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated compiled.indexed.ancestry.layout.frame
        header.globals (compiled.indexed.layouts.allocatorAt header.owner header.active header.onError)
        (GenericLexicalStatements.absentRequest header.function.source
          (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) binder payload))
      (inputs : CallableIndexedOwnedAbsentAllocationNamedBodyFaultBounds.AbsentInputs
        (functions := functions) (header := header) (registry := registry) (faults := faults)
        (certificates := certificates) (expressionSyntax := expressionSyntax) (id := id) (node := node)
        (nextContext := nextContext) (rest := rest) (suffixFlow := suffixFlow) allocation annotation validity) :
      SupportedInputs header

/-- Finite static projections preserve the SAME actual lowering and allocator
receipt. They execute no compiler, expression or flow producer. -/
private theorem SupportedInputs.static_receipt
    {header : CallableIndexedOwnedFunctionValues.Header compiled program}
    (inputs : SupportedInputs (registry := registry) (faults := faults) functions header) :
    ∃ (expressionSyntax : ExpressionId → Prop)
      (certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate)
      (flow : Expr) (validity : SourceSemantics.Context → Prop),
      CallableIndexedOwnedLexicalNamedBodyFaultBounds.StaticBodyInputs
        (functions := functions) (header := header) (registry := registry) (faults := faults)
        (certificates := certificates) (expressionSyntax := expressionSyntax) (flow := flow) validity := by
  cases inputs with
  | @discardReturn expressionSyntax certificates flow validity inputs =>
    exact ⟨expressionSyntax, certificates, flow, validity,
      CallableIndexedOwnedLexicalNamedBodyFaultBounds.BodyInputs.static_inputs functions validity inputs⟩
  | @absent expressionSyntax certificates validity id node binder nextContext rest payload suffixFlow allocation annotation inputs =>
    exact ⟨expressionSyntax, certificates, .letE annotation.expression suffixFlow, validity,
      CallableIndexedOwnedAbsentAllocationNamedBodyFaultBounds.static_inputs
        functions allocation annotation validity inputs⟩

/-- Every supported lexical body retains the same original causal fault post. -/
abbrev FaultPost : BodyFaultPost :=
  ReachedNamedLexicalBodyFaultPaths.model_bodyPost compiled.compatible.checked functions registry

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
  (stable : CallableIndexedOwnedAllocationProducer.StableOwner keys frameLocation current)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (wellFormed : ProgramWellFormed program)

include source rows stable extension faithful observations functionTypes wellFormed in
/-- The shared lexical Tree/finish producer runs once for each genuine strict
body member at this literal parameter state and returned bodyStore. -/
theorem SupportedInputs.source_below
    (inputs : SupportedInputs (registry := registry) (faults := faults) functions header)
    (budget : Nat) : RecursiveNamedBoundedContracts.Below budget
      (SourceBodyAtWithPost (FaultPost functions (registry := registry)) (faults := faults) entry reached) := by
  obtain ⟨expressionSyntax, certificates, flow, validity, static⟩ :=
    SupportedInputs.static_receipt functions inputs
  intro child _strict
  exact CallableIndexedOwnedLexicalNamedBodyFaultBounds.source_body_with_post.with_static
    functions validity entry reached extension faithful observations functionTypes wellFormed source rows stable static child

include source rows stable extension faithful observations functionTypes wellFormed in
/-- The shared lexical Tree/finish producer runs once for each genuine strict
body member at this literal parameter state and returned bodyStore. -/
theorem SupportedInputs.native_below
    (inputs : SupportedInputs (registry := registry) (faults := faults) functions header)
    (budget : Nat) : RecursiveNamedBoundedContracts.Below budget
      (NativeBodyAtWithPost (FaultPost functions (registry := registry)) (faults := faults) entry reached) := by
  obtain ⟨expressionSyntax, certificates, flow, validity, static⟩ :=
    SupportedInputs.static_receipt functions inputs
  intro child _strict
  exact CallableIndexedOwnedLexicalNamedBodyFaultBounds.native_body_with_post.with_static
    functions validity entry reached extension faithful observations functionTypes wellFormed source rows stable static child

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
  (inputs : SupportedInputs (program := program) (registry := registry) (faults := faults) functions header)
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
  exact inputs.source_below receipt.body receipt.reached (receipt.source wellFormed) receipt.rows receipt.stable_owner
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
  exact inputs.native_below receipt.body receipt.reached (receipt.source wellFormed) receipt.rows receipt.stable_owner
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
      SupportedInputs (program := program) (registry := registry) (faults := faults) functions header) :
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
      SupportedInputs (program := program) (registry := registry) (faults := faults) functions header) :
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

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLexicalNamedBodyPostProviders
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMixedLexicalFlowFaultBounds
/-! The original lexical Tree consumes genuine strict expression members at
its actual current context. Callable children keep their causal fault post,
while allocations retain the same ordered pool and stable frame receipt. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMixedLexicalFlowFaultBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open NamedLexicalFlowFaultPostContracts
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {source : TypedSource} (evidence : Dynamic.EvidenceEnvironment)
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  (post : ExpressionFailurePostContracts.ExpressionFaultPost)
  (unique : NodeOccurrencesUnique source) (wellFormed : ProgramWellFormed program)

section Flows
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {expressionSyntax : ExpressionId → Prop}
  (definitions : layouts.definitions = (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (registered : frame.Registered (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (condition : Location → NativeFrame → Prop)
  (producer : ProtectedStateTransition.OrdinaryAllocation.Producer callerProtocol layouts frame
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
  (bindings : ProtectedStateTransition.Bindings callerProtocol)
  (acquire : ∀ location native, condition location native → ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer location native)
  (validity : SourceSemantics.Context → Prop)
  (extend : ∀ {context nextContext binder}, validity context → BinderExtends source.owner context binder nextContext → validity nextContext)

include definitions registered producer bindings acquire unique extend in
theorem flow_preserves (outer budget size : Nat) (within : budget < outer) (bounded : size ≤ budget)
    (children : ∀ child, child < outer → ∀ context, validity context →
      NamedLexicalFlowFaultPostContracts.ExpressionPreservesAt (post := post) callerProtocol (readiness bridge)
        program evidence (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        (ProtectedStateLexicalSourceSites.ExpressionFacts source) (certificates context)
        (context := context) (source := source) (faults := faults) child)
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericLexicalStatements.Tree layouts owner active frame globals onError (.initial compiled.compatible.checked)
      source certificates context scope mode statements expected type code) :
    NamedLexicalFlowFaultPostContracts.PreservesAtFor
      (post := FlowPost (post))
      callerProtocol (readiness bridge) condition (GenericLexicalStatements.Syntax source expressionSyntax)
      (values := .initial compiled.compatible.checked) (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frame) (globals := globals) size (scope := scope) mode statements expected type code := by
  intro valid sourceFacts mapping world administrative actualContext environment canonical actual before after store ξ
    contextLocation native outcome finalContext environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
  exact RecursiveNamedLexicalTreeBounds.Stateful.WithReady.preserves_at_for_with_post
    (expressionPost := post)
    (headPost := HeadPost (post))
    (flowPost := FlowPost (post))
    (joins := origin_joins _ program evidence source)
    (protocol := callerProtocol) (condition := condition) (producer := producer) (stateBindings := bindings) (acquire := acquire)
    (readiness := readiness bridge) (facts := GenericLexicalStatements.Syntax source expressionSyntax)
    (headFacts := ProtectedStateLexicalSourceSites.HeadFacts source expressionSyntax)
    (exprFacts := ProtectedStateLexicalSourceSites.ExpressionFacts source)
    (sites := ProtectedStateLexicalSourceSites.sites program evidence unique)
    (transfers := CallableIndexedOwnedAdmittedLexicalReadiness.allocation_transfers bridge bindings source)
    functions definitions registered program evidence validity extend budget size bounded
    (fun child bounded context valid => children child (Nat.lt_of_le_of_lt bounded within) context valid)
    tree valid sourceFacts unique environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace

include definitions registered producer bindings acquire unique extend in
theorem flow_reflects (outer budget size : Nat) (within : budget < outer) (bounded : size ≤ budget)
    (children : ∀ child, child < outer → ∀ context, validity context →
      NamedLexicalFlowFaultPostContracts.ExpressionReflectsAt (post := post) callerProtocol (readiness bridge)
        program evidence (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        (ProtectedStateLexicalSourceSites.ExpressionFacts source) (certificates context)
        (context := context) (source := source) (faults := faults) child)
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericLexicalStatements.Tree layouts owner active frame globals onError (.initial compiled.compatible.checked)
      source certificates context scope mode statements expected type code) :
    NamedLexicalFlowFaultPostContracts.ReflectsAtFor
      (post := FlowPost (post))
      callerProtocol (readiness bridge) condition (GenericLexicalStatements.Syntax source expressionSyntax)
      (values := .initial compiled.compatible.checked) (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frame) (globals := globals) size (scope := scope) mode statements expected type code := by
  intro valid sourceFacts mapping world administrative actualContext environment canonical actual before store finalStore ξ
    contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted evaluated
  exact RecursiveNamedLexicalTreeBounds.Stateful.WithReady.reflects_at_for_with_post
    (expressionPost := post)
    (headPost := HeadPost (post))
    (flowPost := FlowPost (post))
    (joins := origin_joins _ program evidence source)
    (protocol := callerProtocol) (condition := condition) (producer := producer) (stateBindings := bindings) (acquire := acquire)
    (readiness := readiness bridge) (facts := GenericLexicalStatements.Syntax source expressionSyntax)
    (headFacts := ProtectedStateLexicalSourceSites.HeadFacts source expressionSyntax)
    (exprFacts := ProtectedStateLexicalSourceSites.ExpressionFacts source)
    (sites := ProtectedStateLexicalSourceSites.sites program evidence unique)
    (transfers := CallableIndexedOwnedAdmittedLexicalReadiness.allocation_transfers bridge bindings source)
    functions definitions registered program evidence validity extend budget size bounded
    (fun child bounded context valid => children child (Nat.lt_of_le_of_lt bounded within) context valid)
    tree valid sourceFacts environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted evaluated

end Flows

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMixedLexicalFlowFaultBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMixedLexicalNamedBodyFaultBounds
/-! A genuine accepted lexical body consumes strict expression members from
one mixed family. The original Tree and finish retain their causal post and
actual body store, including declaration allocation and early faults. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMixedLexicalNamedBodyFaultBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open NamedLexicalFlowFaultPostContracts RecursiveNamedCatalogInvocationBounds
open CallableIndexedOwnedInvocationBounds CallableIndexedOwnedIndirectExpressionHeads
open CallableIndexedOwnedAdmittedBodyEntries (SourceReceipt)
open CallableIndexedOwnedMixedLexicalFlowFaultBounds
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {header : CallableIndexedOwnedFunctionValues.Header compiled program}
  {expressionSyntax : ExpressionId → Prop} {flow : Expr}
  (validity : SourceSemantics.Context → Prop)

/-- The exact ordered-pool bridge used by the strict child contracts. -/
def bodyBridge :
    CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) (protocol headers keys) :=
  CallableIndexedOwnedIndirectCallerProtocol.of_legacy CallableIndexedOwnedCallerProtocol.base

/-- The same literal static inputs without restricting the grammar profile. -/
structure BodyInputs : Prop where
  syntaxTree : GenericLexicalStatements.Syntax header.function.source expressionSyntax header.context true
    header.function.body header.function.resultType
  tree : GenericLexicalStatements.Tree compiled.indexed.layouts header.owner header.active
    compiled.indexed.ancestry.layout.frame header.globals header.onError (.initial compiled.compatible.checked)
    header.function.source certificates header.context
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) true
    header.function.body header.function.resultType header.output flow
  accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
    header.output header.reasonAt header.fellThrough header.escaped = .ok header.body
  generated : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
    header.output header.reasonAt true header.escaped = .ok flow
  projection : compiled.compatible.checked.catalog.project header.function.resultType = .ok header.output
  valid : validity header.context
  extend : ∀ {context nextContext binder}, validity context →
    BinderExtends header.function.source.owner context binder nextContext → validity nextContext


variable (inputs : BodyInputs (header := header) (certificates := certificates)
  (expressionSyntax := expressionSyntax) (flow := flow) validity)

include inputs in
private theorem BodyInputs.emitted :
    header.body = CompatibleStatements.finish header.output flow header.fellThrough header.escaped := by
  have accepted := inputs.accepted
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  rw [inputs.generated] at accepted
  exact Except.ok.inj accepted.symm

include inputs in
private theorem BodyInputs.transfers {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {sourceSize : Nat} {finalContext : SourceSemantics.Context} {control : Dynamic.ControlOutcome}
    (trace : RecursiveNamedLoopContracts.ExecutesAt sourceSize true program header.context header.function.evidence
      header.function.source environment before header.function.body finalContext control after) :
    ImperativeFunctionFinish.TransferFaults faults header.escaped control := by
  cases trace with
  | fault failed => constructor <;> intro next same <;> cases same
  | control executed =>
    cases GenericLexicalStatements.syntax_control_shape inputs.syntaxTree header.unique executed.sound <;>
      constructor <;> intro next same <;> cases same

variable (post : ExpressionFailurePostContracts.ExpressionFaultPost)
variable {locations : CallableIndexedOwnedFunctionValues.Header compiled program → Location} {capturePrefix : Nat}
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
  (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
    administrative actualContext actual ξ frameLocation current ghost)
  (reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
    entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
  (sourceReceipt : SourceReceipt program header.function header.context entry.environment entry.heap)
  (rows : StableRows reached)
  (stable : CallableIndexedOwnedAllocationProducer.StableOwner keys frameLocation current)

private theorem body_reference : entry.canonical[
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))).length + 1 + header.globals]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type frameLocation) := by
  simpa only [List.length_map, List.length_reverse] using entry.reference

private theorem body_unmapped : frameLocation ∉ entry.mapping := by
  have unmapped := entry.catalog.authority.unmapped
  simpa only [entry.catalog_frame] using unmapped


include inputs sourceReceipt rows stable in
/-- The Source child is strictly smaller than the enclosing mixed member;
its real parameter state supplies admission and the stable allocation hook. -/
theorem source_body_with_post (outer size : Nat) (within : size < outer)
    (children : ∀ child, child < outer → ∀ context, validity context →
      NamedLexicalFlowFaultPostContracts.ExpressionPreservesAt (post := post) (protocol headers keys)
        (readiness (bodyBridge (headers := headers) (keys := keys))) program header.function.evidence
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        (ProtectedStateLexicalSourceSites.ExpressionFacts header.function.source) (certificates context)
        (context := context) (source := header.function.source) (faults := faults) child)
    : SourceBodyAtWithPost (ReachedNamedLexicalBodyFaultPaths.bodyPost post)
      (faults := faults) entry reached size := by
    intro outcome after trace
    let bridge := bodyBridge (headers := headers) (keys := keys)
    let model := CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
    let producer := CallableIndexedOwnedAllocationProducer.producer headers keys model
    let condition := CallableIndexedOwnedAllocationProducer.StableOwner keys
    have meaning := flow_preserves bridge functions header.function.evidence
      post header.unique
      (layouts := compiled.indexed.layouts) (owner := header.owner) (active := header.active)
      (frame := compiled.indexed.ancestry.layout.frame) (globals := header.globals) (onError := header.onError)
      (expressionSyntax := expressionSyntax) rfl header.registered condition producer
      (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
      (fun _ _ seed => CallableIndexedOwnedAllocationProducer.readyAt_of_stableOwner model seed)
      validity inputs.extend outer size size within (Nat.le_refl size) children inputs.tree
    have lifted := NamedLexicalFunctionFaultPostContracts.PreservesAtWith.of_lexical
      (protocol := protocol headers keys) (readiness := readiness bridge) (condition := condition)
      (facts := GenericLexicalStatements.Syntax header.function.source expressionSyntax)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (functions := functions) (program := program) (evidence := header.function.evidence)
      (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
      (meaning := meaning)
    have matchTree := GenericImperativeMatch.Tree.body
      (definitions := (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
      (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
      inputs.syntaxTree inputs.tree
    obtain ⟨value, bodyStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame,
      metadata, _exit, finalTransition, retained⟩ :=
      RecursiveNamedFunctionFinishBounds.WithReady.preserves_at_emitted_with_state_when_with_transfers_with_post
        (functions := functions) (program := program) (tree := matchTree) (projection := inputs.projection) (unique := header.unique)
        (FlowPost (post))
        (protocol headers keys) (readiness bridge) condition
        (GenericLexicalStatements.Syntax header.function.source expressionSyntax) (BodyInputs.emitted validity inputs)
        validity size lifted inputs.valid inputs.syntaxTree
        entry.environments entry.heaps sourceReceipt.locals entry.lookups entry.actualTyped
        (body_reference functions entry) entry.state.read (body_unmapped functions entry) reached stable
        (show Admission bridge header.context reached from ⟨sourceReceipt.heapTyped, rows⟩)
        (BodyInputs.transfers validity inputs) trace
    exact ⟨value, bodyStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame,
      metadata, ProtectedStateTransition.FunctionFinish.Reached.forget finalTransition,
      ReachedNamedLexicalBodyFaultPaths.outcome_post_of_finished_for inputs.syntaxTree header.unique retained evaluated⟩


include inputs sourceReceipt rows stable in
/-- Native finish chooses its actual strict flow child. Reflection constructs
an independent Source grade at the same returned body store. -/
theorem native_body_with_post (outer size : Nat) (within : size < outer)
    (children : ∀ child, child < outer → ∀ context, validity context →
      NamedLexicalFlowFaultPostContracts.ExpressionReflectsAt (post := post) (protocol headers keys)
        (readiness (bodyBridge (headers := headers) (keys := keys))) program header.function.evidence
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        (ProtectedStateLexicalSourceSites.ExpressionFacts header.function.source) (certificates context)
        (context := context) (source := header.function.source) (faults := faults) child)
    : NativeBodyAtWithPost (ReachedNamedLexicalBodyFaultPaths.bodyPost post)
      (faults := faults) entry reached size := by
    intro value bodyStore evaluated
    let bridge := bodyBridge (headers := headers) (keys := keys)
    let model := CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
    let producer := CallableIndexedOwnedAllocationProducer.producer headers keys model
    let condition := CallableIndexedOwnedAllocationProducer.StableOwner keys
    have meaning : RecursiveNamedBoundedContracts.Below size (fun child =>
        NamedLexicalFunctionFaultPostContracts.ReflectsAtWith
          (post := FlowPost (post))
          (protocol headers keys) (readiness bridge) condition
          (GenericLexicalStatements.Syntax header.function.source expressionSyntax)
          (values := .initial compiled.compatible.checked) functions program header.function.evidence validity
          (source := header.function.source) (context := header.context) (registry := registry) (faults := faults)
          (frameLayout := compiled.indexed.ancestry.layout.frame) (globals := header.globals)
          (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
          child (scope := header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) true
          header.function.body header.function.resultType header.output flow) := by
      intro child smaller
      exact NamedLexicalFunctionFaultPostContracts.ReflectsAtWith.of_lexical
        (protocol := protocol headers keys) (readiness := readiness bridge) (condition := condition)
        (facts := GenericLexicalStatements.Syntax header.function.source expressionSyntax)
        (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (functions := functions) (program := program) (evidence := header.function.evidence)
        (meaning := flow_reflects bridge functions header.function.evidence
          post header.unique
          (layouts := compiled.indexed.layouts) (owner := header.owner) (active := header.active)
          (frame := compiled.indexed.ancestry.layout.frame) (globals := header.globals) (onError := header.onError)
          (expressionSyntax := expressionSyntax) rfl header.registered condition producer
          (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
          (fun _ _ seed => CallableIndexedOwnedAllocationProducer.readyAt_of_stableOwner model seed)
          validity inputs.extend outer child child (Nat.lt_trans smaller within) (Nat.le_refl child) children inputs.tree)
    have matchTree := GenericImperativeMatch.Tree.body
      (definitions := (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
      (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
      inputs.syntaxTree inputs.tree
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame,
      metadata, _exit, finalTransition, retained⟩ :=
      RecursiveNamedFunctionFinishBounds.WithReady.reflects_at_emitted_with_state_when_with_transfers_with_post
        (functions := functions) (program := program) (tree := matchTree) (projection := inputs.projection) (unique := header.unique)
        (FlowPost (post))
        (protocol headers keys) (readiness bridge) condition
        (GenericLexicalStatements.Syntax header.function.source expressionSyntax) (BodyInputs.emitted validity inputs)
        validity size size (Nat.le_refl size) meaning inputs.valid inputs.syntaxTree
        entry.environments entry.heaps sourceReceipt.locals entry.lookups entry.actualTyped
        (body_reference functions entry) entry.state.read (body_unmapped functions entry) reached stable
        (show Admission bridge header.context reached from ⟨sourceReceipt.heapTyped, rows⟩)
        (BodyInputs.transfers validity inputs) evaluated
    exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame,
      metadata, ProtectedStateTransition.FunctionFinish.Reached.forget finalTransition,
      ReachedNamedLexicalBodyFaultPaths.outcome_post_of_finished_for inputs.syntaxTree header.unique retained evaluated.sound⟩


include inputs sourceReceipt rows stable in
/-- Each genuine smaller body member uses the same accepted Tree and finish
at its actual parameter state. -/
theorem source_below (outer budget : Nat) (within : budget ≤ outer)
    (children : ∀ child, child < outer → ∀ context, validity context →
      NamedLexicalFlowFaultPostContracts.ExpressionPreservesAt (post := post) (protocol headers keys)
        (readiness (bodyBridge (headers := headers) (keys := keys))) program header.function.evidence
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        (ProtectedStateLexicalSourceSites.ExpressionFacts header.function.source) (certificates context)
        (context := context) (source := header.function.source) (faults := faults) child)
    : RecursiveNamedBoundedContracts.Below budget
      (SourceBodyAtWithPost (ReachedNamedLexicalBodyFaultPaths.bodyPost post)
        (faults := faults) entry reached) := by
  intro child strict
  exact source_body_with_post functions validity inputs post entry reached sourceReceipt rows stable
    outer child (Nat.lt_of_lt_of_le strict within) children

include inputs sourceReceipt rows stable in
/-- Each genuine smaller body member uses the same accepted Tree and finish
at its actual parameter state. -/
theorem native_below (outer budget : Nat) (within : budget ≤ outer)
    (children : ∀ child, child < outer → ∀ context, validity context →
      NamedLexicalFlowFaultPostContracts.ExpressionReflectsAt (post := post) (protocol headers keys)
        (readiness (bodyBridge (headers := headers) (keys := keys))) program header.function.evidence
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        (ProtectedStateLexicalSourceSites.ExpressionFacts header.function.source) (certificates context)
        (context := context) (source := header.function.source) (faults := faults) child)
    : RecursiveNamedBoundedContracts.Below budget
      (NativeBodyAtWithPost (ReachedNamedLexicalBodyFaultPaths.bodyPost post)
        (faults := faults) entry reached) := by
  intro child strict
  exact native_body_with_post functions validity inputs post entry reached sourceReceipt rows stable
    outer child (Nat.lt_of_lt_of_le strict within) children

section Parameters
variable (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {initial : ProtectedStateTransition.Index} {argumentsPool : State headers keys initial}
  {parameterArguments : List Dynamic.Value}
  (parameters : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt (registry := registry)
    functions owner argumentsPool header parameterArguments)

include inputs parameters in
/-- The authentic successful-argument receipt supplies body admission,
all ordered rows and the stable allocation hook internally. -/
theorem source_at_parameters (wellFormed : ProgramWellFormed program)
    (outer size : Nat) (within : size < outer)
    (children : ∀ child, child < outer → ∀ context, validity context →
      NamedLexicalFlowFaultPostContracts.ExpressionPreservesAt (post := post) (protocol headers keys)
        (readiness (bodyBridge (headers := headers) (keys := keys))) program header.function.evidence
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        (ProtectedStateLexicalSourceSites.ExpressionFacts header.function.source) (certificates context)
        (context := context) (source := header.function.source) (faults := faults) child)
    : SourceBodyAtWithPost (ReachedNamedLexicalBodyFaultPaths.bodyPost post)
      (faults := faults) parameters.body parameters.reached size :=
  source_body_with_post functions validity inputs post parameters.body parameters.reached
    (parameters.source wellFormed) parameters.rows parameters.stable_owner outer size within children

include inputs parameters in
/-- The authentic successful-argument receipt supplies body admission,
all ordered rows and the stable allocation hook internally. -/
theorem native_at_parameters (wellFormed : ProgramWellFormed program)
    (outer size : Nat) (within : size < outer)
    (children : ∀ child, child < outer → ∀ context, validity context →
      NamedLexicalFlowFaultPostContracts.ExpressionReflectsAt (post := post) (protocol headers keys)
        (readiness (bodyBridge (headers := headers) (keys := keys))) program header.function.evidence
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        (ProtectedStateLexicalSourceSites.ExpressionFacts header.function.source) (certificates context)
        (context := context) (source := header.function.source) (faults := faults) child)
    : NativeBodyAtWithPost (ReachedNamedLexicalBodyFaultPaths.bodyPost post)
      (faults := faults) parameters.body parameters.reached size :=
  native_body_with_post functions validity inputs post parameters.body parameters.reached
    (parameters.source wellFormed) parameters.rows parameters.stable_owner outer size within children

end Parameters

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMixedLexicalNamedBodyFaultBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMixedLexicalNamedBodyPostProviders
/-! Successful arguments construct the original typed parameter receipt.
The strict mixed expression family supplies lexical body children at that
same reached input, retaining their causal post and native prefix route. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMixedLexicalNamedBodyPostProviders
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission CallableIndexedOwnedIndirectExpressionHeads
open CallableIndexedOwnedAdmittedBodyEntries (SourceReceipt)
open CallableIndexedOwnedInvocationBounds NamedInvocationFaultPostContracts
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate} {flow : Expr}

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
  (validity : SourceSemantics.Context → Prop)
  (inputs : CallableIndexedOwnedMixedLexicalNamedBodyFaultBounds.BodyInputs
    (header := header) (certificates := certificates) (expressionSyntax := expressionSyntax) (flow := flow) validity)
  (post : ExpressionFailurePostContracts.ExpressionFaultPost)

include admitted wellFormed sourceRuntime covers locals argumentTypes application inputs in
/-- The original successful arguments supply the exact parameter receipt;
only the concrete strict body producer is invoked. -/
theorem source_invocations (outer budget : Nat) (within : budget ≤ outer)
    (children : ∀ child, child < outer → ∀ bodyContext, validity bodyContext →
      NamedLexicalFlowFaultPostContracts.ExpressionPreservesAt (post := post) (protocol headers keys)
        (CallableIndexedOwnedAdmittedLexicalReadiness.readiness
          (CallableIndexedOwnedMixedLexicalNamedBodyFaultBounds.bodyBridge (headers := headers) (keys := keys)))
        program header.function.evidence (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        (ProtectedStateLexicalSourceSites.ExpressionFacts header.function.source) (certificates bodyContext)
        (context := bodyContext) (source := header.function.source) (faults := faults) child)
    :
    CallableIndexedOwnedExpressionHeads.SourceInvocationsForWithPost (post := ReachedNamedLexicalBodyFaultPaths.bodyPost post) (source := source) (context := context)
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
  exact CallableIndexedOwnedMixedLexicalNamedBodyFaultBounds.source_below functions validity inputs post
    receipt.body receipt.reached (receipt.source wellFormed) receipt.rows receipt.stable_owner
    outer budget within children child strict trace


include admitted wellFormed sourceRuntime covers locals argumentTypes application inputs in
/-- The original successful arguments supply the exact parameter receipt;
only the concrete strict body producer is invoked. -/
theorem native_invocations (outer budget : Nat) (within : budget ≤ outer)
    (children : ∀ child, child < outer → ∀ bodyContext, validity bodyContext →
      NamedLexicalFlowFaultPostContracts.ExpressionReflectsAt (post := post) (protocol headers keys)
        (CallableIndexedOwnedAdmittedLexicalReadiness.readiness
          (CallableIndexedOwnedMixedLexicalNamedBodyFaultBounds.bodyBridge (headers := headers) (keys := keys)))
        program header.function.evidence (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        (ProtectedStateLexicalSourceSites.ExpressionFacts header.function.source) (certificates bodyContext)
        (context := bodyContext) (source := header.function.source) (faults := faults) child)
    :
    CallableIndexedOwnedExpressionHeads.NativeInvocationsForWithPost (post := ReachedNamedLexicalBodyFaultPaths.bodyPost post) (source := source) (context := context)
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
  exact CallableIndexedOwnedMixedLexicalNamedBodyFaultBounds.native_below functions validity inputs post
    receipt.body receipt.reached (receipt.source wellFormed) receipt.rows receipt.stable_owner
    outer budget within children child strict completed


end Providers

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMixedLexicalNamedBodyPostProviders
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMixedLexicalNamedExpressionHeads
/-! Strict expression children supply the actual argument sequence and lexical
body posts internally. The original outer named-head consumers preserve the
same selected call, restored pool and independent Source/native grades. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMixedLexicalNamedExpressionHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedExpressionHeads (Globals)
open RecursiveNamedBoundedContracts
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (post : ExpressionFailurePostContracts.ExpressionFaultPost)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {compilation : SourceCoreFunctions.Context}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (caller : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => Globals (headers := headers) owner compilation.administrativePrefix index.scope index.canonical) callerProtocol)
  {source : TypedSource} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
  {certificate : GenericExpressionMeaning.Certificate}
  (wellFormed : ProgramWellFormed program) (sourceRuntime : Dynamic.SourceRuntimeValid program context source)
  (covers : evidence.Covers context) (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (idsUnique : RequirementIdsUnique context)
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)

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
          (ReachedNamedLexicalBodyFaultPaths.bodyPost post) owner caller initial
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
          (ReachedNamedLexicalBodyFaultPaths.bodyPost post) owner caller initial
          compilation.administrativePrefix compilation.internalReason sourceSize (some size)
          id node lowered outcome after value finalMap finalWorld finalStore

section Heads
variable
  (bodyCertificates : CallableIndexedOwnedFunctionValues.Header compiled program →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate)
  (bodySyntax : CallableIndexedOwnedFunctionValues.Header compiled program → ExpressionId → Prop)
  (bodyFlow : CallableIndexedOwnedFunctionValues.Header compiled program → Expr)
  (bodyValidity : CallableIndexedOwnedFunctionValues.Header compiled program → SourceSemantics.Context → Prop)
  (inputs : ∀ {id node}, source.lookupExpression? id = some node → ExpressionHasType source context id node.type →
    ∀ header, header ∈ headers → ∀ {callee ids}, node.form = .call callee ids (.declaration header.instantiation) →
    CallableIndexedOwnedMixedLexicalNamedBodyFaultBounds.BodyInputs (header := header)
      (certificates := bodyCertificates header) (expressionSyntax := bodySyntax header)
      (flow := bodyFlow header) (bodyValidity header))

include wellFormed sourceRuntime covers unique sameLayouts owners idsUnique inputs in
/-- Same-family strict argument and body children supply both actual providers;
no completed argument, body or invocation law is an input. -/
theorem preserves_head_with_body_post (outer size : Nat) (within : size ≤ outer)
    (children : Below outer
      (CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
        (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        context evidence source certificate faults))
    (bodyChildren : ∀ header, header ∈ headers → ∀ child, child < outer → ∀ bodyContext,
      bodyValidity header bodyContext →
      NamedLexicalFlowFaultPostContracts.ExpressionPreservesAt (post := post) (protocol headers keys)
        (CallableIndexedOwnedAdmittedLexicalReadiness.readiness
          (CallableIndexedOwnedMixedLexicalNamedBodyFaultBounds.bodyBridge (headers := headers) (keys := keys)))
        program header.function.evidence (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        (ProtectedStateLexicalSourceSites.ExpressionFacts header.function.source) (bodyCertificates header bodyContext)
        (context := bodyContext) (source := header.function.source) (faults := faults) child) :
    PreservesHeadAtWithPost (functions := functions) (registry := registry) (faults := faults)
      (source := source) (context := context) (certificate := certificate) post owner caller evidence size := by
  intro scope id lowered head root found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial admitted trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, ⟨reached, related⟩, route⟩ :=
    CallableIndexedOwnedExpressionHeads.preserves_at_with_sequence_with_body_post functions owner sameLayouts
      (fun header => CallableIndexedOwnedInvocationBounds.stableOwnerCondition (keys := keys) functions registry header)
      (fun header _ => CallableIndexedOwnedInvocationBounds.stable_owner_authorized functions registry header owner)
      caller outer size within idsUnique unique owners head found initial environments heaps locals agrees typed
      (fun header _member callee ids codes form sequence _nativeTypes _packedType => by
        obtain ⟨originalTypes, rawResult, predicates, argumentTypes, _application⟩ :=
          CallableIndexedOwnedNamedArgumentAdmission.direct_arguments unique found form sourceTyped
        exact CallableIndexedOwnedAdmittedSequenceProducer.preserves
          (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller) initial admitted sequence unique argumentTypes
          environments heaps locals agrees typed outer children)
      (ReachedNamedLexicalBodyFaultPaths.bodyPost post)
      (fun header member callee ids form => by
        obtain ⟨originalTypes, rawResult, predicates, argumentTypes, application⟩ :=
          CallableIndexedOwnedNamedArgumentAdmission.direct_arguments unique found form sourceTyped
        exact CallableIndexedOwnedMixedLexicalNamedBodyPostProviders.source_invocations
          (owner := owner) (functions := functions) caller initial admitted wellFormed sourceRuntime covers locals
          argumentTypes application (bodyValidity header) (inputs found sourceTyped header member form) post
          outer outer (Nat.le_refl outer) (bodyChildren header member)) trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    after_expression_sized initial reached admitted wellFormed sourceRuntime covers locals sourceTyped trace frame, route⟩

include wellFormed sourceRuntime covers unique sameLayouts inputs in
/-- Native arguments and the actual strict body continuation recover their
independent Source trace before the same original caller restoration. -/
theorem reflects_head_with_body_post (outer size : Nat) (within : size ≤ outer)
    (children : Below outer
      (CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
        (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        context evidence source certificate faults))
    (bodyChildren : ∀ header, header ∈ headers → ∀ child, child < outer → ∀ bodyContext,
      bodyValidity header bodyContext →
      NamedLexicalFlowFaultPostContracts.ExpressionReflectsAt (post := post) (protocol headers keys)
        (CallableIndexedOwnedAdmittedLexicalReadiness.readiness
          (CallableIndexedOwnedMixedLexicalNamedBodyFaultBounds.bodyBridge (headers := headers) (keys := keys)))
        program header.function.evidence (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        (ProtectedStateLexicalSourceSites.ExpressionFacts header.function.source) (bodyCertificates header bodyContext)
        (context := bodyContext) (source := header.function.source) (faults := faults) child) :
    ReflectsHeadAtWithPost (functions := functions) (registry := registry) (faults := faults)
      (source := source) (context := context) (certificate := certificate) post owner caller evidence size := by
  intro scope id lowered head root found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed initial admitted completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, ⟨reached, related⟩, route⟩ :=
    CallableIndexedOwnedExpressionHeads.reflects_at_with_sequence_with_body_post functions owner sameLayouts
      (fun header => CallableIndexedOwnedInvocationBounds.stableOwnerCondition (keys := keys) functions registry header)
      (fun header _ => CallableIndexedOwnedInvocationBounds.stable_owner_authorized functions registry header owner)
      caller outer size within head found initial environments heaps locals agrees typed
      (fun header _member callee ids codes form sequence _nativeTypes _packedType => by
        obtain ⟨originalTypes, rawResult, predicates, argumentTypes, _application⟩ :=
          CallableIndexedOwnedNamedArgumentAdmission.direct_arguments unique found form sourceTyped
        exact CallableIndexedOwnedAdmittedSequenceProducer.reflects
          (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller) initial admitted sequence unique argumentTypes
          environments heaps locals agrees typed outer children)
      (ReachedNamedLexicalBodyFaultPaths.bodyPost post)
      (fun header member callee ids form => by
        obtain ⟨originalTypes, rawResult, predicates, argumentTypes, application⟩ :=
          CallableIndexedOwnedNamedArgumentAdmission.direct_arguments unique found form sourceTyped
        exact CallableIndexedOwnedMixedLexicalNamedBodyPostProviders.native_invocations
          (owner := owner) (functions := functions) caller initial admitted wellFormed sourceRuntime covers locals
          argumentTypes application (bodyValidity header) (inputs found sourceTyped header member form) post
          outer outer (Nat.le_refl outer) (bodyChildren header member)) completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    after_expression_sized initial reached admitted wellFormed sourceRuntime covers locals sourceTyped trace frame, route⟩

end Heads
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMixedLexicalNamedExpressionHeads
end
