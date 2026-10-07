import Solcore.Test.SourceCoreClosedOwnedExpressionHead
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedNamedFamilyClosure

/-! A real named Unit body discards an actual compiler lambda formation site.
Its empty literal body retains honest rank-zero static support. The original
Tree/profile factories and closed nested family prove every execution callback
internally, preserving the actual returned pool and its ordered snapshots. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
namespace Tests.SourceCoreClosedOwnedNestedNamedFamily
open Solcore Core Frontend SourceInference
open SourceSemantics SourceSemantics.CoreLowering GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds RecursiveNamedLambdaFormationHeads
open Tests.SourceCoreClosedOwnedExpressionHead (PreparedReceipts layouts PoolObservations)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (profileFlag : compiled.compatible.checked.catalog.callableContracts = true)

/-- Every parent uses rank one; its actual empty lambda body has rank zero.
This order is static and independent of Source/native execution grades. -/
def ranks (_header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)) : Nat := 1

abbrev expressions (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (context : SourceSemantics.Context) :=
  CallableIndexedOwnedNestedNamedFamilyClosure.certificates (headers := headers) (registry := registry) (faults := faults)
    ranks header context

/-- This packet contains only actual Source/compiler/static body receipts.
Site has a private constructor: its full original Code comes from real
ordinary contextual lambda compilation. BodyAt stores no execution law. -/
structure FormationBody (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)) where
  statement : StatementId
  statementNode : StatementNode
  body : header.function.body = [statement]
  found : header.function.source.lookupStatement? statement = some statementNode
  site : CallableIndexedLambdaGeneration.Site compiled.indexed header.named [] .unit []
    header.context header.function.evidence []
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    (nativePrefix (indexed := compiled.indexed) (values := .initial compiled.compatible.checked)
      (program := Program.ofChecked compiled.sourceProgram) header)
  literalBody : CallableIndexedLambdaNestedRuntimeCertificates.BodyAt
    (indexed := compiled.indexed) (values := .initial compiled.compatible.checked)
    headers header registry faults 0 site.code
  expressionFound : header.function.source.lookupExpression? site.code.id = some site.code.sourceNode
  sourceType : site.code.sourceNode.type = FunctionValues.sourceType
    (CallableIndexedLambdaGeneration.closure header.named [] .unit [] header.context header.function.evidence [])
  requirements : site.code.sourceNode.requirements = []
  coercions : site.code.sourceNode.coercions = []
  form : statementNode.form = .expression site.code.id true
  statementType : statementNode.type = .unit
  typed : ExpressionHasType header.function.source header.context site.code.id site.code.sourceNode.type
  unitResult : header.function.resultType = .unit
  generated : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
    header.output header.reasonAt true header.escaped =
      .ok (LocalSequence.discard (LocalLoop.controlType header.output) site.code.lowered.expression
        (LocalLoop.fallthrough header.output))

/-- Lambda.of_site builds the original ranked leaf and empty ordered-child
Tree from the same genuine site and honest smaller static body. -/
theorem formation_tree
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (receipt : FormationBody (headers := headers) (registry := registry) (faults := faults) header) :
    expressions (headers := headers) (registry := registry) (faults := faults) header header.context
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) receipt.site.code.id receipt.site.code.lowered := by
  have smaller : 0 < ranks header := by change 0 < 1; decide
  have support : CallableIndexedLambdaNestedRuntimeBodyMeaning.LowerSupport
      (indexed := compiled.indexed) (values := .initial compiled.compatible.checked)
      headers header registry faults (ranks header) 0 receipt.site.code := by
    simpa only [CallableIndexedLambdaNestedRuntimeBodyMeaning.LowerSupport, dif_pos smaller] using receipt.literalBody
  obtain ⟨head⟩ := CallableIndexedLambdaNestedRuntimeCertificates.Lambda.of_site
    (support := CallableIndexedLambdaNestedRuntimeBodyMeaning.LowerSupport
      (indexed := compiled.indexed) (values := .initial compiled.compatible.checked) headers header registry faults (ranks header))
    receipt.site smaller support receipt.expressionFound receipt.sourceType receipt.requirements receipt.coercions
  refine ⟨.node (entries := []) (.call (.lambda head)) (by intro _ _ member; cases member), ?_⟩
  exact .node (entries := []) (.call (.lambda head)) (by intro _ _ member; cases member) (by intro _ _ member; cases member)

/-- All family members use these concrete static body shapes. -/
inductive BodyReceipt (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)) where
  | nil (valid : CompatibleRuntimeContextValidity.Valid header.solved header.context header.function.evidence)
      (body : header.function.body = []) (unitResult : header.function.resultType = .unit)
  | formation (valid : CompatibleRuntimeContextValidity.Valid header.solved header.context header.function.evidence)
      (receipt : FormationBody (headers := headers) (registry := registry) (faults := faults) header)

variable (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (captureZero : owner.key.capturePrefix = 0)
  (receipts : PreparedReceipts (headers := headers))
  (bodies : ∀ header, header ∈ headers → BodyReceipt (headers := headers) (registry := registry) (faults := faults) header)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (globals : ∀ header, header ∈ headers → header.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) identities)
  (functionTypes : FunctionRuntimeViews (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag))
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)

include receipts in
private theorem accepted {header} (member : header ∈ headers) :
    SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
      header.output header.reasonAt header.fellThrough header.escaped = .ok header.body := by
  obtain ⟨row, prepared, instantiation, aligned⟩ := receipts header member
  exact aligned.accepted

include receipts in
private theorem projection {header} (member : header ∈ headers) :
    compiled.compatible.checked.catalog.project header.function.resultType = .ok header.output := by
  obtain ⟨row, prepared, instantiation, aligned⟩ := receipts header member
  exact aligned.projection

private def body_profile {header} (member : header ∈ headers) (administrative : Core.Context) :
    MatchProfileWith (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (fun context => RecursiveNamedCatalogMutualMeaning.ContextFor true header.solved context header.function.evidence)
      (expressions (headers := headers) (registry := registry) (faults := faults) header)
      .reachable header (fun _ => True)
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults := by
  cases bodies header member with
  | nil valid body unitResult =>
    let admission : GenericLexicalStatements.Syntax header.function.source (fun _ => True) header.context true
        header.function.body header.function.resultType := body ▸ .nil (Or.inr unitResult)
    let lexical : GenericLexicalStatements.Tree header.layouts header.owner header.active compiled.indexed.ancestry.layout.frame
        header.globals header.onError (.initial compiled.compatible.checked) header.function.source
        (expressions (headers := headers) (registry := registry) (faults := faults) header) header.context
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) true header.function.body
        header.function.resultType header.output (LocalLoop.fallthrough header.output) := body ▸ .nil (Or.inr unitResult)
    have generated : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
        header.output header.reasonAt true header.escaped = .ok (LocalLoop.fallthrough header.output) := by
      rw [body]
      cases header.fuel <;> rfl
    exact MatchProfileWith.of_extracted valid (accepted receipts member) (projection receipts member) generated
      (.body admission lexical) (.body (syntaxTree := admission) (body := lexical))
  | formation valid receipt =>
    let admission : GenericLexicalStatements.Syntax header.function.source (fun _ => True) header.context true
        header.function.body header.function.resultType := by
      rw [receipt.body]
      exact .discard receipt.found receipt.form (by decide) receipt.statementType receipt.expressionFound
        receipt.typed trivial (.nil (Or.inr receipt.unitResult))
    let lexical : GenericLexicalStatements.Tree header.layouts header.owner header.active compiled.indexed.ancestry.layout.frame
        header.globals header.onError (.initial compiled.compatible.checked) header.function.source
        (expressions (headers := headers) (registry := registry) (faults := faults) header) header.context
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) true header.function.body
        header.function.resultType header.output
        (LocalSequence.discard (LocalLoop.controlType header.output) receipt.site.code.lowered.expression
          (LocalLoop.fallthrough header.output)) := by
      rw [receipt.body]
      exact .discard receipt.found receipt.form (by decide) receipt.expressionFound
        (formation_tree receipt) (.nil (Or.inr receipt.unitResult))
    exact MatchProfileWith.of_extracted valid (accepted receipts member) (projection receipts member) receipt.generated
      (.body admission lexical) (.body (syntaxTree := admission) (body := lexical))

include captureZero profileFlag receipts bodies complete globals slots extension faithful observations functionTypes owners
  uninitialized missing escaped in
/-- The original per-header mutual family closes actual lambda formation from
these static profiles; no expression/body meaning family is a premise. -/
theorem family_preserves (size : Nat) : ∀ header, header ∈ headers →
    RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) registry header faults
      (protocol headers keys)
      (CallableIndexedOwnedNamedCanonicalEntries.condition
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) owner header) size := by
  exact CallableIndexedOwnedNestedNamedFamilyClosure.preserves_at owner captureZero profileFlag complete globals slots
    (fun _ member => layouts receipts member) extension faithful observations functionTypes owners uninitialized missing escaped ranks
    (by
      intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry allowed
      exact body_profile (registry := registry) (faults := faults) receipts bodies member administrative) size

include captureZero profileFlag receipts bodies complete globals slots extension faithful observations functionTypes
  uninitialized missing escaped in
/-- Native reflection returns an independently graded Source body and the same
actual reached pool from the closed nested family. -/
theorem family_reflects (size : Nat) : ∀ header, header ∈ headers →
    RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) registry header faults
      (protocol headers keys)
      (CallableIndexedOwnedNamedCanonicalEntries.condition
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) owner header) size := by
  exact CallableIndexedOwnedNestedNamedFamilyClosure.reflects_at owner captureZero profileFlag complete globals slots
    (fun _ member => layouts receipts member) extension faithful observations functionTypes uninitialized missing escaped ranks
    (by
      intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry allowed
      exact body_profile (registry := registry) (faults := faults) receipts bodies member administrative) size

section Parent
variable {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (member : header ∈ headers)
  (parent : FormationBody (headers := headers) (registry := registry) (faults := faults) header)
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
  (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers owner.key.locations owner.key.capturePrefix
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) registry header arguments before initialStore
    initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost)
  (initial : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
    entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
  (allowed : CallableIndexedOwnedNamedCanonicalEntries.condition
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) owner header entry)

include captureZero profileFlag receipts bodies complete globals slots extension faithful observations functionTypes owners
  uninitialized missing escaped member parent entry initial allowed in
/-- Original Source execution of the named formation body runs the genuine
compiled lambda leaf and observes every ordered record in the actual post. -/
theorem parent_source_post (size : Nat) {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyTrace (Program.ofChecked compiled.sourceProgram) size header.function header.context
      entry.environment entry.heap outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates entry.actualBody entry.store (header.body.rename entry.embedding) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag))
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      header.function.body = [parent.statement] ∧
      ∃ reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
          finalMap, finalWorld, after, finalStore, entry.canonical⟩,
        Relates initial reached ∧ PoolObservations initial reached := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, preserved, metadata, reached, related⟩ :=
    family_preserves profileFlag owner captureZero receipts bodies complete globals slots extension faithful observations functionTypes
      owners uninitialized missing escaped size header member entry initial allowed trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, preserved, metadata,
    parent.body, reached, related, Tests.SourceCoreClosedOwnedLexicalBody.reached_pool_observations related⟩

include captureZero profileFlag receipts bodies complete globals slots extension faithful observations functionTypes
  uninitialized missing escaped member parent entry initial allowed in
/-- Original native completion reflects the real formation-containing Source
body at its independent grade and retains the same actual reached pool. -/
theorem parent_native_post (size : Nat) {value : Value} {finalStore : Store}
    (completed : EvaluationSize size entry.actualBody entry.store (header.body.rename entry.embedding) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace (Program.ofChecked compiled.sourceProgram) sourceSize header.function header.context
        entry.environment entry.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag))
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      header.function.body = [parent.statement] ∧
      ∃ reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
          finalMap, finalWorld, after, finalStore, entry.canonical⟩,
        Relates initial reached ∧ PoolObservations initial reached := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, preserved, metadata, reached, related⟩ :=
    family_reflects profileFlag owner captureZero receipts bodies complete globals slots extension faithful observations functionTypes
      uninitialized missing escaped size header member entry initial allowed completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, preserved, metadata,
    parent.body, reached, related, Tests.SourceCoreClosedOwnedLexicalBody.reached_pool_observations related⟩
end Parent

end Tests.SourceCoreClosedOwnedNestedNamedFamily
