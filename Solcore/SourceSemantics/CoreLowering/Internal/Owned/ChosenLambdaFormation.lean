import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.MixedBodyCompiler
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.OrdinaryMembers
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.OrdinaryLambdas

/-!
# Owned callables: chosen lambda formation

Formed and stored members of chosen ordinary rows, formation heads, values and expression heads.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryFormedMembers
/-! One real formation retains the selected certificate factory beside its
actual ordinary index. This positive receipt is not recovered from an opaque
value relation or from an arbitrary stored closure. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryFormedMembers
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport
open CallableIndexedOwnedPreparedMixedBodyCompilerFactory
open CallableIndexedOwnedPreparedMixedBodySiteInputs
open CallableIndexedOwnedPreparedRuntimeFamilyMembers (OrdinaryIndex)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)

section Index
variable {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.Receipt caller diagnostics namedCode compilation
    sourceContext evidence scope id lowered)
  (environment : Dynamic.Environment) {mapping : LocationMap} {world : StoreTyping} {actual : Environment}
  (captured : Captures compiled.indexed mapping world scope (receipt.formation.function environment).captured actual)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) caller)

/-- The genuine prefix equality transports two typing proofs while all
runtime capture fields remain the original literal data. -/
def capture_at : Captures compiled.indexed mapping world scope
    (receipt.formation.function environment).captured actual where
  administrative := RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) caller
  canonical := captured.canonical
  actualContext := captured.actualContext
  embedding := captured.embedding
  represented := by rw [← prefixContext]; exact captured.represented
  agrees := captured.agrees
  respects := by rw [← prefixContext]; exact captured.respects
  typed := captured.typed

/-- Code, Support and prepared body are the literal chosen Formation fields. -/
def index : OrdinaryIndex compiled :=
  ⟨receipt.formation.function environment, mapping, world, scope, actual,
    capture_at receipt environment captured prefixContext,
    receipt.formation.code environment, receipt.formation.support environment, receipt.formation.prepared environment⟩
end Index

/-- A positive constructor records the literal chosen receipt and recapture.
It supplies no inverse on FormedAt, Represents, Code, or HeapRepresents. -/
inductive FactoryMember : OrdinaryIndex compiled → Prop where
  | formed {sourceContext evidence scope id lowered mapping world actual}
      (receipt : CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.Receipt caller diagnostics namedCode compilation
        sourceContext evidence scope id lowered)
      (chosen : ChosenFactory root expressionSyntax receipt) (environment : Dynamic.Environment)
      (captured : Captures compiled.indexed mapping world scope (receipt.formation.function environment).captured actual)
      (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
        (values := .initial compiled.compatible.checked) caller) :
      FactoryMember (index receipt environment captured prefixContext)

/-- The retained certificate family belongs to that exact selected Support. -/
theorem FactoryMember.factories {i : OrdinaryIndex compiled} (member : FactoryMember root expressionSyntax i) :
    i.support.expressionSyntax = expressionSyntax ∧
    i.support.certificates = certificates root expressionSyntax := by
  cases member with
  | formed receipt chosen environment captured prefixContext =>
    exact ⟨(recaptured_factory root expressionSyntax receipt chosen environment).1,
      (recaptured_factory root expressionSyntax receipt chosen environment).2.1⟩

/-- Actual map/world growth keeps the same chosen factory and captured Source
spine. It does not assert that any mutated heap still stores this value. -/
theorem FactoryMember.extend {i : OrdinaryIndex compiled} (member : FactoryMember root expressionSyntax i)
    {futureMap : LocationMap} {futureWorld : StoreTyping}
    (maps : LocationMap.Extends i.mapping futureMap) (worlds : WorldExtends i.world futureWorld) :
    FactoryMember root expressionSyntax {
      function := i.function, mapping := futureMap, world := futureWorld, scope := i.scope
      capturedActual := i.capturedActual, captured := i.captured.extend maps worlds
      code := i.code, support := i.support, prepared := i.prepared } := by
  cases member with
  | formed receipt chosen environment captured prefixContext =>
    exact .formed receipt chosen environment (captured.extend maps worlds) prefixContext

section Formation
variable {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.Receipt caller diagnostics namedCode compilation
    sourceContext evidence scope id lowered)
  (chosen : ChosenFactory root expressionSyntax receipt) (environment : Dynamic.Environment)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {actual canonical : Environment} {heap : Dynamic.Heap} {store : Store}
  (captured : Captures compiled.indexed mapping world scope (receipt.formation.function environment).captured actual)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) caller)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner caller _ initial)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)

include chosen observed in
/-- The original formation producer runs once over the copies. The same
complete tuple and known formed member retain the positive chosen-factory
companion at the formed closure's literal index. -/
theorem formation_member_with_factory
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
      mapping world heap store) :
    let i := index receipt environment captured prefixContext
    let history := CallableIndexedOwnedPreparedOrdinaryLambdaFormation.history_at
      i.captured i.code i.support owner initial packet
    ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
        i.captured i.code history heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) i.function.context i.function.evidence
        i.function.source i.function.captured heap i.code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (i.code.lowered.expression.rename i.captured.embedding)
        (.inRight .word (value i.code formed.embedding history.native formed.closureActual)) formed.finalStore ∧
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile).Represents
        registry formed.finalMap formed.finalWorld (FunctionValues.sourceType i.function) (.closure formed.closure)
        (value i.code formed.embedding history.native formed.closureActual)
        (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore) ∧
      (∀ result finalStore, Evaluates actual store (i.code.lowered.expression.rename i.captured.embedding) result finalStore →
        result = .inRight .word (value i.code formed.embedding history.native formed.closureActual) ∧
          finalStore = formed.finalStore) ∧
      CallableIndexedOwnedPreparedOrdinaryFormedMembers.FormedAt headers keys registry faults
        formed.finalMap formed.finalWorld (FunctionValues.sourceType i.function) (.closure formed.closure)
        (value i.code formed.embedding history.native formed.closureActual)
        (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore) ∧
      FactoryMember root expressionSyntax (index receipt formed.captured formed.captures rfl) := by
  obtain ⟨formed, sourceTrace, evaluated, related, determined, member⟩ :=
    CallableIndexedOwnedPreparedOrdinaryFormedMembers.formation_member
      (capture_at receipt environment captured prefixContext) (receipt.formation.code environment)
      (receipt.formation.support environment) (receipt.formation.prepared environment) owner initial packet profile rfl
      observed heaps receipt.formation.ordinary receipt.formation.coercions
  exact ⟨formed, sourceTrace, evaluated, related, determined, member,
    .formed receipt chosen formed.captured formed.captures rfl⟩

include chosen in
/-- A real certificate of this same recaptured Support is interpreted by the
original accepted-child compiler producer; no Tree is supplied by the caller. -/
theorem coverage_at_formed
    {currentContext : SourceSemantics.Context} {childScope : SourceCoreLocalCell.Scope}
    (headers : RecursiveNamedCatalog.Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions (Program.ofChecked compiled.sourceProgram))
    (domain : DomainAt root expressionSyntax receipt.formation.body.readFuel currentContext evidence childScope headers)
    (valid : CompatibleRuntimeContextValidity.Valid (context compiled.indexed caller.named).solvedRequirements currentContext evidence)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) currentContext (source caller.named))
    {child : ExpressionId} {output : SourceCoreBasic.LoweredExpr}
    (actual : (receipt.formation.support environment).certificates
      (receipt.formation.support environment).body.readFuel (receipt.formation.function environment).source
      currentContext childScope child output) :
    RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsFor
      (BodyCalls root expressionSyntax (indirect_factory root expressionSyntax headers domain valid) headers)
      receipt.formation.body.readFuel (.initial compiled.compatible.checked) (source caller.named) currentContext
      (context compiled.indexed caller.named).solvedRequirements rootReasonAt childScope child output :=
  coverage_at_support root expressionSyntax receipt chosen environment headers domain valid runtime actual
end Formation
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryFormedMembers
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryStoredMembers
/-! Positive chosen-factory qualification stays at its literal ordinary index
through one actual formation and initialized allocation/write. Future mutation
transport uses the actual reads of the same optional payload. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryStoredMembers
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport
open CallableIndexedOwnedPreparedRuntimeFamilyMembers (OrdinaryIndex)
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open CallableIndexedOwnedPreparedMixedBodySiteInputs (ChosenFactory)
open CallableIndexedOwnedChosenOrdinaryFormedMembers (FactoryMember)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)


/-- These are the actual constructor fields at a known index and history.
No opaque value, stored relation or prior selection supplies the factory. -/
inductive ChosenAt (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (i : OrdinaryIndex compiled) (history : History i.code) : Prop where
  | ordinary (owner : OwnedKey keys) (factory : FactoryMember root expressionSyntax i)
      (origin : SourceOrigin i.support history)
      (prefixContext : i.captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
        (values := .initial compiled.compatible.checked) i.support.caller)
      (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 i.scope i.captured.canonical owner.key.frameLocation)
      (referenceIndex : i.code.referenceIndex = i.scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType i.world (value i.code i.captured.embedding history.native i.capturedActual)
        (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore)
        compiled.indexed.layouts.definitions) : ChosenAt headers keys registry faults i history

variable {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {i : OrdinaryIndex compiled} {history : History i.code}

theorem ChosenAt.formed (member : ChosenAt root expressionSyntax headers keys registry faults i history) :
    CallableIndexedOwnedPreparedOrdinaryFormedMembers.FormedAt headers keys registry faults
      i.mapping i.world (FunctionValues.sourceType i.function) (.closure i.function)
      (value i.code i.captured.embedding history.native i.capturedActual)
      (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore) := by
  cases member with
  | ordinary owner factory origin prefixContext globals referenceIndex typed =>
    exact .ordinary i owner history origin prefixContext globals referenceIndex typed

theorem ChosenAt.selection (member : ChosenAt root expressionSyntax headers keys registry faults i history) :
    CallableIndexedOwnedPreparedOrdinaryLambdaValues.Selection headers keys registry faults
      i.mapping i.world (FunctionValues.sourceType i.function) (.closure i.function)
      (value i.code i.captured.embedding history.native i.capturedActual)
      (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore) := by
  cases member with
  | ordinary owner factory origin prefixContext globals referenceIndex typed =>
    exact .prepared_ordinary owner i.captured i.code history i.support origin prefixContext globals referenceIndex typed i.prepared

theorem ChosenAt.factory (member : ChosenAt root expressionSyntax headers keys registry faults i history) :
    FactoryMember root expressionSyntax i := by
  cases member with
  | ordinary owner factory origin prefixContext globals referenceIndex typed => exact factory

/-- The future index keeps the literal function, Code, Support and prepared body. -/
def extendIndex (i : OrdinaryIndex compiled) {futureMap : LocationMap} {futureWorld : StoreTyping}
    (maps : LocationMap.Extends i.mapping futureMap) (worlds : WorldExtends i.world futureWorld) : OrdinaryIndex compiled := {
  function := i.function, mapping := futureMap, world := futureWorld, scope := i.scope
  capturedActual := i.capturedActual, captured := i.captured.extend maps worlds
  code := i.code, support := i.support, prepared := i.prepared }

theorem ChosenAt.extend (member : ChosenAt root expressionSyntax headers keys registry faults i history)
    {futureMap : LocationMap} {futureWorld : StoreTyping}
    (maps : LocationMap.Extends i.mapping futureMap) (worlds : WorldExtends i.world futureWorld) :
    ChosenAt root expressionSyntax headers keys registry faults (extendIndex i maps worlds) history := by
  cases member with
  | ordinary owner factory origin prefixContext globals referenceIndex typed =>
    exact .ordinary owner (FactoryMember.extend root expressionSyntax factory maps worlds) origin prefixContext globals referenceIndex (typed.weaken worlds)

theorem ChosenAt.map_keys (member : ChosenAt root expressionSyntax headers keys registry faults i history)
    {futureKeys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
    (embedding : CallableIndexedOwnedFunctionValues.KeyEmbedding keys futureKeys) :
    ChosenAt root expressionSyntax headers futureKeys registry faults i history := by
  cases member with
  | ordinary owner factory origin prefixContext globals referenceIndex typed =>
    have actualGlobals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers (embedding.map owner).key.locations 1 i.scope i.captured.canonical (embedding.map owner).key.frameLocation := by
      rw [embedding.same owner]
      exact globals
    exact .ordinary (embedding.map owner) factory origin prefixContext actualGlobals referenceIndex typed

/-- The real initialized cell and optional native read retain the known index. -/
def ChosenStoredAt (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (i : OrdinaryIndex compiled) (history : History i.code) (heap : Dynamic.Heap)
    (store : Store) (location : Dynamic.Location) : Prop :=
  ChosenAt root expressionSyntax headers keys registry faults i history ∧
  ∃ target, ReferenceRepresents i.mapping i.world location target
      (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore) ∧
    Dynamic.Heap.Reads heap location ⟨FunctionValues.sourceType i.function, some (.closure i.function), none⟩ ∧
    store.read? target = some (.inRight .unit (value i.code i.captured.embedding history.native i.capturedActual))

theorem ChosenStoredAt.stored {heap : Dynamic.Heap} {store : Store} {location : Dynamic.Location}
    (stored : ChosenStoredAt root expressionSyntax headers keys registry faults i history heap store location) :
    CallableIndexedOwnedPreparedOrdinaryStoredMembers.StoredAt headers keys registry faults i.mapping i.world
      heap store location (FunctionValues.sourceType i.function) (.closure i.function)
      (value i.code i.captured.embedding history.native i.capturedActual)
      (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore) :=
  ⟨stored.1.formed, stored.2⟩

theorem ChosenStoredAt.extend_with_reads {heap futureHeap : Dynamic.Heap} {store futureStore : Store}
    {location : Dynamic.Location} {futureMap : LocationMap} {futureWorld : StoreTyping}
    (stored : ChosenStoredAt root expressionSyntax headers keys registry faults i history heap store location)
    (maps : LocationMap.Extends i.mapping futureMap) (worlds : WorldExtends i.world futureWorld)
    (reads : Dynamic.Heap.Reads futureHeap location ⟨FunctionValues.sourceType i.function, some (.closure i.function), none⟩)
    (nativeReads : ∀ target, ReferenceRepresents i.mapping i.world location target
      (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore) →
      futureStore.read? target = some (.inRight .unit (value i.code i.captured.embedding history.native i.capturedActual))) :
    ChosenStoredAt root expressionSyntax headers keys registry faults (extendIndex i maps worlds) history futureHeap futureStore location := by
  obtain ⟨member, target, reference, _, _⟩ := stored
  exact ⟨ChosenAt.extend root expressionSyntax member maps worlds, target, reference.extend maps worlds, reads, nativeReads target reference⟩

theorem ChosenStoredAt.map_keys {heap : Dynamic.Heap} {store : Store} {location : Dynamic.Location}
    {futureKeys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
    (embedding : CallableIndexedOwnedFunctionValues.KeyEmbedding keys futureKeys)
    (stored : ChosenStoredAt root expressionSyntax headers keys registry faults i history heap store location) :
    ChosenStoredAt root expressionSyntax headers futureKeys registry faults i history heap store location :=
  ⟨ChosenAt.map_keys root expressionSyntax stored.1 embedding, stored.2⟩
section Formation
variable {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.Receipt caller diagnostics namedCode compilation
    sourceContext evidence scope id lowered)
  (chosen : ChosenFactory root expressionSyntax receipt) (environment : Dynamic.Environment)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {actual canonical : Environment} {heap : Dynamic.Heap} {store : Store}
  (captured : Captures compiled.indexed mapping world scope (receipt.formation.function environment).captured actual)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) caller)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner caller _ initial)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)

include chosen observed in
/-- The original formation producer runs once over the copies. The same
complete tuple and known formed member retain the positive chosen-factory
companion at the formed closure's literal index. -/
theorem formation_chosen_member
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
      mapping world heap store) :
    let i := CallableIndexedOwnedChosenOrdinaryFormedMembers.index receipt environment captured prefixContext
    let history := CallableIndexedOwnedPreparedOrdinaryLambdaFormation.history_at
      i.captured i.code i.support owner initial packet
    ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
        i.captured i.code history heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) i.function.context i.function.evidence
        i.function.source i.function.captured heap i.code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (i.code.lowered.expression.rename i.captured.embedding)
        (.inRight .word (value i.code formed.embedding history.native formed.closureActual)) formed.finalStore ∧
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile).Represents
        registry formed.finalMap formed.finalWorld (FunctionValues.sourceType i.function) (.closure formed.closure)
        (value i.code formed.embedding history.native formed.closureActual)
        (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore) ∧
      (∀ result finalStore, Evaluates actual store (i.code.lowered.expression.rename i.captured.embedding) result finalStore →
        result = .inRight .word (value i.code formed.embedding history.native formed.closureActual) ∧
          finalStore = formed.finalStore) ∧
      CallableIndexedOwnedPreparedOrdinaryFormedMembers.FormedAt headers keys registry faults
        formed.finalMap formed.finalWorld (FunctionValues.sourceType i.function) (.closure formed.closure)
        (value i.code formed.embedding history.native formed.closureActual)
        (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore) ∧
      ChosenAt root expressionSyntax headers keys registry faults
        (CallableIndexedOwnedChosenOrdinaryFormedMembers.index receipt formed.captured formed.captures rfl)
        formed.closureHistory := by
  obtain ⟨formed, sourceTrace, evaluated, related, determined, formedAt, factory⟩ :=
    CallableIndexedOwnedChosenOrdinaryFormedMembers.formation_member_with_factory root expressionSyntax
      receipt chosen environment captured prefixContext owner initial packet profile observed heaps
  let i := CallableIndexedOwnedChosenOrdinaryFormedMembers.index receipt environment captured prefixContext
  have member : ChosenAt root expressionSyntax headers keys registry faults
      (CallableIndexedOwnedChosenOrdinaryFormedMembers.index receipt formed.captured formed.captures rfl)
      formed.closureHistory :=
    .ordinary owner factory
      ⟨(CallableIndexedOwnedPreparedOrdinaryLambdaFormation.source_origin i.captured i.code i.support owner initial packet).metadata⟩
      rfl (observed.of_slots formed.slots)
      (CallableIndexedOwnedPreparedOrdinaryLambdaFormation.reference_index i.captured i.code i.support)
      ((CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile).runtime_hasType
        (registry := registry) related)
  exact ⟨formed, sourceTrace, evaluated, related, determined, formedAt, member⟩
end Formation

theorem written_chosen_member
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {heap after : Dynamic.Heap} {store : Store} {location : Dynamic.Location}
    {target : Location} {cell : Dynamic.Cell}
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
      i.mapping i.world heap store)
    (reference : ReferenceRepresents i.mapping i.world location target (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore))
    (read : Dynamic.Heap.Reads heap location cell) (cellType : cell.type = (FunctionValues.sourceType i.function))
    (member : ChosenAt root expressionSyntax headers keys registry faults i history)
    (written : Dynamic.Heap.Writes heap location (some (.closure i.function)) after) :
    ∃ updated, store.write? target (.inRight .unit (value i.code i.captured.embedding history.native i.capturedActual)) = some updated ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
        i.mapping i.world after updated ∧
      AdministrativePreserved i.mapping store i.mapping updated ∧
      Dynamic.HeapMetadataExtend heap after ∧
      ChosenStoredAt root expressionSyntax headers keys registry faults i history after updated location := by
  obtain ⟨updated, writtenCore, finalHeaps, administrative, metadata, actualStored⟩ :=
    CallableIndexedOwnedPreparedOrdinaryStoredMembers.written_member profile heaps reference read cellType member.formed written
  exact ⟨updated, writtenCore, finalHeaps, administrative, metadata, member, actualStored.2⟩

open CallableIndexedHistory CallableIndexedAllocationCompletion

theorem allocated_chosen_member
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {request : SourceCoreSourceCells.Request} {layout : SourceCoreCallableIndexedFrames.Layout}
    {globals : Nat} {allocate : SourceCoreSourceCells.Allocator}
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active request)
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated layout globals allocate request)
    (same : annotation.original = allocation.expression)
    (definitions : layouts.definitions = compiled.indexed.layouts.definitions)
    (frameRegistered : layout.Registered compiled.indexed.layouts.definitions)
    {administrative : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {contextLocation : Location}
    {frame : NativeFrame} {sourceLocation : Dynamic.Location}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      i.mapping i.world administrative request.scope environment canonical compiled.indexed.layouts.definitions)
    (agrees : EnvironmentsAgree request.references canonical actual)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
      i.mapping i.world before store)
    (reference : actual[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals request]? =
      some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout frame))
    (payloadAt : PayloadAt request actual (some (value i.code i.captured.embedding history.native i.capturedActual)))
    (payloadType : request.payloadType = (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore))
    (member : ChosenAt root expressionSyntax headers keys registry faults i history)
    (allocated : Dynamic.Heap.Allocates before (FunctionValues.sourceType i.function) (some (.closure i.function)) sourceLocation after) :
    ∃ captured,
      Captures actual request.references request.scope captured ∧
      RuntimeValueHasType i.world captured (SourceCoreSourceCells.captureType request.scope) compiled.indexed.layouts.definitions ∧
      Evaluates actual store annotation.expression
        (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2))
        (store ++ [SourceCoreCallableIndexedFrames.encode layout frame,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit (value i.code i.captured.embedding history.native i.capturedActual)]) ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
        (i.mapping ++ [store.length + 2])
        (i.world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType])
        after (store ++ [SourceCoreCallableIndexedFrames.encode layout frame,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit (value i.code i.captured.embedding history.native i.capturedActual)]) ∧
      ReferenceRepresents (i.mapping ++ [store.length + 2])
        (i.world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType])
        sourceLocation (store.length + 2) request.payloadType ∧
      AdministrativePreserved i.mapping store (i.mapping ++ [store.length + 2])
        (store ++ [SourceCoreCallableIndexedFrames.encode layout frame,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit (value i.code i.captured.embedding history.native i.capturedActual)]) ∧
      ChosenStoredAt root expressionSyntax headers keys registry faults
        (extendIndex i (futureMap := i.mapping ++ [store.length + 2])
          (futureWorld := i.world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType])
          ⟨_, rfl⟩ ⟨_, rfl⟩) history after
        (store ++ [SourceCoreCallableIndexedFrames.encode layout frame,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
          .inRight .unit (value i.code i.captured.embedding history.native i.capturedActual)]) sourceLocation := by
  obtain ⟨captured, selected, typed, evaluated, finalHeaps, finalReference, administrative, actualStored⟩ :=
    CallableIndexedOwnedPreparedOrdinaryStoredMembers.allocated_member profile allocation annotation same definitions
      frameRegistered environments agrees heaps reference read payloadAt payloadType member.formed allocated
  exact ⟨captured, selected, typed, evaluated, finalHeaps, finalReference, administrative,
    ChosenAt.extend root expressionSyntax member ⟨_, rfl⟩ ⟨_, rfl⟩, actualStored.2⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryStoredMembers
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryLambdaFormationHeads
/-! Actual formation heads preserve the positive compiler factory in the
receiving model. Original capture and formation producers construct the same
complete tuple once; no inverse on a stored value or finished body law is used. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryLambdaFormationHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedOrdinaryLambdaFormation (Formation)
open RecursiveNamedLambdaFormationHeads

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)

  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : CallableIndexedNamedGeneration.Compilation compiled.indexed caller.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt (compiled := compiled)
    caller.named diagnostics namedCode compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)

/-- A certificate keeps the actual selected compiler receipt and its factory. -/
inductive Certificate : SourceCoreLocalCell.Scope → ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | formed {scope id lowered}
      (receipt : CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.Receipt caller diagnostics namedCode compilation
        context evidence scope id lowered)
      (chosen : CallableIndexedOwnedPreparedMixedBodySiteInputs.ChosenFactory root expressionSyntax receipt) :
      Certificate scope id lowered

/-- This constructor registers only a positively qualified literal closure.
It asks for no classifier of an arbitrary function value or heap cell. -/
def Members (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) : Prop :=
  ∀ (i : CallableIndexedOwnedPreparedRuntimeFamilyMembers.OrdinaryIndex compiled) (history : History i.code),
    CallableIndexedOwnedChosenOrdinaryStoredMembers.ChosenAt root expressionSyntax headers keys registry faults i history →
    functions.Represents registry i.mapping i.world (FunctionValues.sourceType i.function) (.closure i.function)
      (value i.code i.captured.embedding history.native i.capturedActual)
      (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore)

def bridge (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) :=
  CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller

def model (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) :=
  CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

variable
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (members : Members (headers := headers) (keys := keys) (registry := registry) (faults := faults) caller root expressionSyntax functions)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (globals : caller.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (prefixZero : owner.key.capturePrefix = 0)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {source : TypedSource}
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  (sameSource : source = CallableIndexedNamedGeneration.source caller.named)

include profile members complete globals slots prefixZero wellFormed runtime covers sameSource in
/-- Actual catalog/capture receipts construct the whole finite formation leaf.
The actual factory is retained by the local model constructor. -/
theorem preserves_head_at (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt (bridge (headers := headers) caller owner)
      (model (registry := registry) functions) context evidence source
      (Certificate caller context evidence root expressionSyntax) faults size := by
  intro scope id lowered certified node found typed mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees nativeTyped initial admitted trace
  cases certified with
  | formed receipt chosen =>
    let head := receipt.formation
    let entry := CallableIndexedOwnedLambdaViewHeads.nested_entry initial.val owner prefixZero
      initial.property.observed initial.property.carried initial.property.bundle globals
    let originalCapture := captures_for complete globals entry environments agrees nativeTyped
    let i := CallableIndexedOwnedChosenOrdinaryFormedMembers.index receipt environment originalCapture rfl
    let captured := i.captured
    have observed := capture_globals_for complete globals slots entry environments agrees nativeTyped
    have observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation := by
      change CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope
        captured.canonical (initial.val.rows owner.position).authority.frameLocation at observed
      rw [(initial.val.rows owner.position).frame_eq] at observed
      exact observed
    let code := i.code
    let support := i.support
    have sourceFound : source.lookupExpression? id = some code.sourceNode := by
      simpa only [head, receipt.formation.produced.identifier, receipt.formation.produced.emitted, sameSource, code, i, CallableIndexedOwnedChosenOrdinaryFormedMembers.index, Formation.code, recaptureCode,
        CallableIndexedLambdaGeneration.closure, head.produced.identifier] using head.produced.site.code.sourceFound
    have same := Option.some.inj (found.symm.trans sourceFound)
    subst node
    have original : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
        (head.function environment).context (head.function environment).evidence (head.function environment).source
        (head.function environment).captured before code.id outcome after := by
      simpa only [head, receipt.formation.produced.identifier, receipt.formation.produced.emitted, sameSource, code, i, CallableIndexedOwnedChosenOrdinaryFormedMembers.index, Formation.code, Formation.function,
        CallableIndexedLambdaGeneration.closure, recaptureCode, head.produced.identifier] using trace
    have actualTyped : ExpressionHasType (head.function environment).source (head.function environment).context
        code.id code.sourceNode.type := by
      simpa only [head, receipt.formation.produced.identifier, receipt.formation.produced.emitted, sameSource, code, i, CallableIndexedOwnedChosenOrdinaryFormedMembers.index, Formation.code, Formation.function,
        CallableIndexedLambdaGeneration.closure, recaptureCode, head.produced.identifier] using typed
    obtain ⟨result, finalStore, native, finalMap, finalWorld, represented, finalHeaps, maps, worlds, frame, metadata,
        reached, related, post⟩ :=
      CallableIndexedOwnedPreparedOrdinaryLambdaFormation.preserves_at_with_member
        (function := head.function environment) (actual := actual)
        captured code support owner initial.val initial.property profile observed functions
        wellFormed (by simpa only [head, receipt.formation.produced.identifier, receipt.formation.produced.emitted, sameSource, Formation.function, CallableIndexedLambdaGeneration.closure] using runtime) covers locals actualTyped head.sourceType
        (head.snapshots environment) head.ordinary head.coercions heaps admitted
        (fun formed nativeTyped =>
          let formedIndex := CallableIndexedOwnedChosenOrdinaryFormedMembers.index receipt formed.captured formed.captures rfl
          have positive : CallableIndexedOwnedChosenOrdinaryStoredMembers.ChosenAt
              root expressionSyntax headers keys registry faults formedIndex formed.closureHistory :=
            .ordinary owner (.formed receipt chosen formed.captured formed.captures rfl)
              ⟨(CallableIndexedOwnedPreparedOrdinaryLambdaFormation.source_origin
                captured code support owner initial.val initial.property).metadata⟩ rfl (observed.of_slots formed.slots)
              (CallableIndexedOwnedPreparedOrdinaryLambdaFormation.reference_index captured code support) nativeTyped
          members formedIndex formed.closureHistory positive) original
    have native : Evaluates actual store (lowered.expression.rename ξ) result finalStore := by
      simpa only [head, receipt.formation.produced.identifier, receipt.formation.produced.emitted, code, i, CallableIndexedOwnedChosenOrdinaryFormedMembers.index, Formation.code, recaptureCode, head.produced.emitted, captured, i, CallableIndexedOwnedChosenOrdinaryFormedMembers.index,
        CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at, originalCapture, captures_for] using native
    have represented : GenericExpressionMeaning.ResultRepresents (model (registry := registry) functions)
        finalMap finalWorld code.sourceNode.type lowered.type faults outcome result := by
      simpa only [head, receipt.formation.produced.emitted, model, code, i, CallableIndexedOwnedChosenOrdinaryFormedMembers.index, Formation.code, recaptureCode, head.produced.emitted] using represented
    exact ⟨result, finalStore, finalMap, finalWorld, native, represented, finalHeaps, maps, worlds, frame, metadata,
      reached, related, post⟩

include profile members complete globals slots prefixZero wellFormed runtime covers sameSource in
/-- Actual native formation reflects the original Source leaf with its own
independent grade, preserving the same caller packet and generic heap model. -/
theorem reflects_head_at (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt (bridge (headers := headers) caller owner)
      (model (registry := registry) functions) context evidence source
      (Certificate caller context evidence root expressionSyntax) faults size := by
  intro scope id lowered certified node found typed mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees nativeTyped initial admitted completed
  cases certified with
  | formed receipt chosen =>
    let head := receipt.formation
    let entry := CallableIndexedOwnedLambdaViewHeads.nested_entry initial.val owner prefixZero
      initial.property.observed initial.property.carried initial.property.bundle globals
    let originalCapture := captures_for complete globals entry environments agrees nativeTyped
    let i := CallableIndexedOwnedChosenOrdinaryFormedMembers.index receipt environment originalCapture rfl
    let captured := i.captured
    have observed := capture_globals_for complete globals slots entry environments agrees nativeTyped
    have observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation := by
      change CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope
        captured.canonical (initial.val.rows owner.position).authority.frameLocation at observed
      rw [(initial.val.rows owner.position).frame_eq] at observed
      exact observed
    let code := i.code
    let support := i.support
    have sourceFound : source.lookupExpression? id = some code.sourceNode := by
      simpa only [head, receipt.formation.produced.identifier, receipt.formation.produced.emitted, sameSource, code, i, CallableIndexedOwnedChosenOrdinaryFormedMembers.index, Formation.code, recaptureCode,
        CallableIndexedLambdaGeneration.closure, head.produced.identifier] using head.produced.site.code.sourceFound
    have same := Option.some.inj (found.symm.trans sourceFound)
    subst node
    have actualTyped : ExpressionHasType (head.function environment).source (head.function environment).context
        code.id code.sourceNode.type := by
      simpa only [head, receipt.formation.produced.identifier, receipt.formation.produced.emitted, sameSource, code, i, CallableIndexedOwnedChosenOrdinaryFormedMembers.index, Formation.code, Formation.function,
        CallableIndexedLambdaGeneration.closure, recaptureCode, head.produced.identifier] using typed
    have actualCompleted : EvaluationSize size actual store (code.lowered.expression.rename captured.embedding) value finalStore := by
      simpa only [head, receipt.formation.produced.identifier, receipt.formation.produced.emitted, code, i, CallableIndexedOwnedChosenOrdinaryFormedMembers.index, Formation.code, recaptureCode, head.produced.emitted, captured, i, CallableIndexedOwnedChosenOrdinaryFormedMembers.index,
        CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at, originalCapture, captures_for] using completed
    obtain ⟨sourceSize, outcome, after, trace, native, finalMap, finalWorld, represented, finalHeaps, maps, worlds, frame, metadata,
        reached, related, post⟩ :=
      CallableIndexedOwnedPreparedOrdinaryLambdaFormation.reflects_at_with_member
        (function := head.function environment) (actual := actual)
        captured code support owner initial.val initial.property profile observed functions
        wellFormed (by simpa only [head, receipt.formation.produced.identifier, receipt.formation.produced.emitted, sameSource, Formation.function, CallableIndexedLambdaGeneration.closure] using runtime) covers locals actualTyped head.sourceType
        (head.snapshots environment) head.ordinary head.coercions heaps admitted
        (fun formed nativeTyped =>
          let formedIndex := CallableIndexedOwnedChosenOrdinaryFormedMembers.index receipt formed.captured formed.captures rfl
          have positive : CallableIndexedOwnedChosenOrdinaryStoredMembers.ChosenAt
              root expressionSyntax headers keys registry faults formedIndex formed.closureHistory :=
            .ordinary owner (.formed receipt chosen formed.captured formed.captures rfl)
              ⟨(CallableIndexedOwnedPreparedOrdinaryLambdaFormation.source_origin
                captured code support owner initial.val initial.property).metadata⟩ rfl (observed.of_slots formed.slots)
              (CallableIndexedOwnedPreparedOrdinaryLambdaFormation.reference_index captured code support) nativeTyped
          members formedIndex formed.closureHistory positive) actualCompleted
    have sourceTrace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        context evidence source environment before id outcome after := by
      simpa only [head, receipt.formation.produced.identifier, receipt.formation.produced.emitted, sameSource, code, i, CallableIndexedOwnedChosenOrdinaryFormedMembers.index, Formation.code, Formation.function,
        CallableIndexedLambdaGeneration.closure, recaptureCode, head.produced.identifier] using trace
    have represented : GenericExpressionMeaning.ResultRepresents (model (registry := registry) functions)
        finalMap finalWorld code.sourceNode.type lowered.type faults outcome value := by
      simpa only [head, receipt.formation.produced.emitted, model, code, i, CallableIndexedOwnedChosenOrdinaryFormedMembers.index, Formation.code, recaptureCode, head.produced.emitted] using represented
    exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata,
      reached, related, post⟩


end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryLambdaFormationHeads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryLambdaValues
/-! A positive chosen branch retains the literal compiler factory in the
function relation. Every General prior alternative remains explicit. The
unchanged public Prepared relation is reached only by forward forgetting. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryLambdaValues
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleEquality
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedRuntimeFamilyMembers (OrdinaryIndex)
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open CallableIndexedOwnedChosenOrdinaryStoredMembers (ChosenAt extendIndex)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)


/-- The actual constructor keeps its known index, history and chosen factory. -/
inductive Represents
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) :
    LocationMap → StoreTyping → TypeSystem.Ty → Dynamic.Value → Value → Ty → Prop where
  | prior {mapping world raw source native type}
      (related : CallableIndexedOwnedGeneralLambdaValues.Represents headers keys registry faults mapping world raw source native type) :
      Represents headers keys registry faults mapping world raw source native type
  | chosen_ordinary (i : OrdinaryIndex compiled) (history : History i.code)
      (member : ChosenAt root expressionSyntax headers keys registry faults i history) :
      Represents headers keys registry faults i.mapping i.world (FunctionValues.sourceType i.function) (.closure i.function)
        (value i.code i.captured.embedding history.native i.capturedActual)
        (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore)

variable {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {raw : TypeSystem.Ty}
  {source : Dynamic.Value} {native : Value} {type : Ty}

/-- Forward erasure retains the actual payload; it recovers no qualifier. -/
theorem Represents.forget
    (related : Represents root expressionSyntax headers keys registry faults mapping world raw source native type) :
    CallableIndexedOwnedPreparedOrdinaryLambdaValues.Represents headers keys registry faults mapping world raw source native type := by
  cases related with
  | prior original => exact .prior original
  | chosen_ordinary i history member => exact (member.formed root expressionSyntax).represents

def model
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed) where
  Represents := fun _ => Represents root expressionSyntax headers keys bodyRegistry faults
  projection := fun related => (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys bodyRegistry faults profile).projection
    (registry := bodyRegistry) (related.forget root expressionSyntax)
  runtime_hasType := fun related => (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys bodyRegistry faults profile).runtime_hasType
    (registry := bodyRegistry) (related.forget root expressionSyntax)
  source_function := fun related => (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys bodyRegistry faults profile).source_function
    (registry := bodyRegistry) (related.forget root expressionSyntax)
  extend := by
    intro registry futureRegistry mapping futureMap world futureWorld raw source native type related registries maps worlds
    cases related with
    | prior original => exact .prior ((CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).extend
        original registries maps worlds)
    | chosen_ordinary i history member =>
      exact .chosen_ordinary (extendIndex i maps worlds) history (member.extend root expressionSyntax maps worlds)

/-- All old General alternatives remain available as the explicit prior branch. -/
theorem includes_general
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).Includes
      (model root expressionSyntax headers keys bodyRegistry faults profile) := fun related => .prior related

/-- Only forward forgetting is provided to the unchanged public Prepared model. -/
theorem forget_inclusion
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    (model root expressionSyntax headers keys bodyRegistry faults profile).Includes
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys bodyRegistry faults profile) :=
  fun related => related.forget root expressionSyntax

theorem observations
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    FunctionObservations compiled.compatible.checked.catalog (model root expressionSyntax headers keys bodyRegistry faults profile)
      (CallableIndexedLambdaValues.Identity compiled.indexed) := by
  intro registry mapping world raw source native type related
  exact CallableIndexedOwnedPreparedOrdinaryLambdaValues.observations headers keys bodyRegistry faults profile
    (registry := registry) (related.forget root expressionSyntax)

theorem runtime_views
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    FunctionRuntimeViews (model root expressionSyntax headers keys bodyRegistry faults profile) := by
  intro registry mapping world parameter result source native type related
  exact CallableIndexedOwnedPreparedOrdinaryLambdaValues.runtime_views headers keys bodyRegistry faults profile
    (registry := registry) (related.forget root expressionSyntax)

/-- Genuine owner embedding transports only the key fields of the same member. -/
theorem Represents.map_keys {futureKeys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
    (embedding : CallableIndexedOwnedFunctionValues.KeyEmbedding keys futureKeys)
    (related : Represents root expressionSyntax headers keys registry faults mapping world raw source native type) :
    Represents root expressionSyntax headers futureKeys registry faults mapping world raw source native type := by
  cases related with
  | prior original => exact .prior (original.map_keys embedding)
  | chosen_ordinary i history member => exact .chosen_ordinary i history (member.map_keys root expressionSyntax embedding)

/-- Exact selection preserves either the old alternative or the positive constructor. -/
inductive Selection
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) :
    LocationMap → StoreTyping → TypeSystem.Ty → Dynamic.Value → Value → Ty → Prop where
  | prior {priorMap : LocationMap} {priorWorld : StoreTyping} {priorRaw : TypeSystem.Ty}
      {priorSource : Dynamic.Value} {priorNative : Value} {priorType : Ty}
      (selected : CallableIndexedOwnedGeneralFunctionSelection.Selection headers keys registry faults priorMap priorWorld priorRaw priorSource priorNative priorType) :
      Selection headers keys registry faults priorMap priorWorld priorRaw priorSource priorNative priorType
  | chosen_ordinary (i : OrdinaryIndex compiled) (history : History i.code)
      (member : ChosenAt root expressionSyntax headers keys registry faults i history) :
      Selection headers keys registry faults i.mapping i.world (FunctionValues.sourceType i.function) (.closure i.function)
        (value i.code i.captured.embedding history.native i.capturedActual)
        (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore)

theorem Selection.of_represents
    (related : Represents root expressionSyntax headers keys registry faults mapping world raw source native type) :
    Selection root expressionSyntax headers keys registry faults mapping world raw source native type := by
  cases related with
  | prior original => exact .prior (CallableIndexedOwnedGeneralFunctionSelection.of_represents original)
  | chosen_ordinary i history member => exact .chosen_ordinary i history member

theorem Selection.represents
    (selected : Selection root expressionSyntax headers keys registry faults mapping world raw source native type) :
    Represents root expressionSyntax headers keys registry faults mapping world raw source native type := by
  cases selected with
  | prior original => exact .prior (CallableIndexedOwnedGeneralFunctionSelection.represents original)
  | chosen_ordinary i history member => exact .chosen_ordinary i history member

section Observed
variable (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {raw : TypeSystem.Ty} {function : Dynamic.Closure}

def Selected : Prop := ∃ parameter result,
  SourceCoreRawMetadata.runtimeType raw = SourceCoreRawMetadata.runtimeType (.function parameter result) ∧
  Selection root expressionSyntax headers keys registry faults mapping world (.function parameter result) (.closure function) native type

private theorem selected_of_representation {sourceValue : Dynamic.Value}
    (related : ValueRep compiled.compatible.checked registry (model root expressionSyntax headers keys registry faults profile)
      mapping world raw sourceValue native type) (closure : sourceValue = .closure function) :
    Selected (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (mapping := mapping) (world := world) (raw := raw) (function := function) (native := native) (type := type) root expressionSyntax := by
  induction related using ValueRep.rec (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ => True) with
  | unit | bool | word | integer | product | proxy | constructed | mappingValue => cases closure
  | function value =>
    cases closure
    exact ⟨_, _, rfl, Selection.of_represents root expressionSyntax value⟩
  | compatible same inner ih =>
    obtain ⟨parameter, result, view, selected⟩ := ih closure
    exact ⟨parameter, result, same.trans view, selected⟩
  | nil | cons | empty | entry | absent | present => trivial

/-- Function-leaf selection eliminates only this actual model representation. -/
theorem selected_of_value
    (related : ValueRep compiled.compatible.checked registry (model root expressionSyntax headers keys registry faults profile)
      mapping world raw (.closure function) native type) :
    Selected (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (mapping := mapping) (world := world) (raw := raw) (function := function) (native := native) (type := type) root expressionSyntax :=
  selected_of_representation root expressionSyntax profile related rfl

universe u
variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (CallableIndexedOwnedFunctionState.Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (context : SourceSemantics.Context) {index : ProtectedStateTransition.Index} (reached : callerProtocol.State index)

/-- Current admission is taken from this exact successful tuple. -/
theorem selected_at_success
    (post : CallableIndexedOwnedSourceAdmission.PostAdmission bridge context raw (.value (.closure function)) reached)
    (related : ValueRep compiled.compatible.checked registry (model root expressionSyntax headers keys registry faults profile)
      index.mapping index.world raw (.closure function) native type) :
    Selected (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (mapping := index.mapping) (world := index.world) (raw := raw) (function := function) (native := native) (type := type) root expressionSyntax ∧
    Dynamic.ValueHasType context index.heap (.closure function) raw ∧
    CallableIndexedOwnedSourceAdmission.Admission bridge context reached := by
  exact ⟨selected_of_value root expressionSyntax profile related, post.at_value⟩
end Observed
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryLambdaValues
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryLambdaExpressionHeads
/-! Actual chosen formation certificates register their literal closure in the
full chosen model. The shared formation heads retain every returned receipt. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryLambdaExpressionHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : CallableIndexedNamedGeneration.Compilation compiled.indexed caller.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt (compiled := compiled)
    caller.named diagnostics namedCode compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)

local notation "functions" => CallableIndexedOwnedChosenOrdinaryLambdaValues.model
  root expressionSyntax headers keys registry faults profile

/-- Only the actual positive constructor supplies local formation membership. -/
theorem members : CallableIndexedOwnedChosenOrdinaryLambdaFormationHeads.Members
    (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    caller root expressionSyntax functions := by
  intro i history member
  exact .chosen_ordinary i history member

variable
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (globals : caller.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (prefixZero : owner.key.capturePrefix = 0)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {source : TypedSource}
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  (sameSource : source = CallableIndexedNamedGeneration.source caller.named)

include profile complete globals slots prefixZero wellFormed runtime covers sameSource in
/-- The actual formation head preserves its complete tuple in the chosen model. -/
theorem preserves_head_at (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedChosenOrdinaryLambdaFormationHeads.bridge (headers := headers) caller owner)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source
      (CallableIndexedOwnedChosenOrdinaryLambdaFormationHeads.Certificate caller context evidence root expressionSyntax)
      faults size :=
  CallableIndexedOwnedChosenOrdinaryLambdaFormationHeads.preserves_head_at
    caller context evidence root expressionSyntax owner profile functions (members caller root expressionSyntax profile)
    complete globals slots prefixZero wellFormed runtime covers sameSource size

include profile complete globals slots prefixZero wellFormed runtime covers sameSource in
/-- Native formation reflects the same Source leaf with its independent grade. -/
theorem reflects_head_at (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedChosenOrdinaryLambdaFormationHeads.bridge (headers := headers) caller owner)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source
      (CallableIndexedOwnedChosenOrdinaryLambdaFormationHeads.Certificate caller context evidence root expressionSyntax)
      faults size :=
  CallableIndexedOwnedChosenOrdinaryLambdaFormationHeads.reflects_head_at
    caller context evidence root expressionSyntax owner profile functions (members caller root expressionSyntax profile)
    complete globals slots prefixZero wellFormed runtime covers sameSource size

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryLambdaExpressionHeads
end
