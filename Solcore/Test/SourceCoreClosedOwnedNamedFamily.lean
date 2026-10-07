import Solcore.Test.SourceCoreClosedOwnedExpressionTree
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedFamilyClosure

/-! Static nil and named-call body receipts close a complete owned body
family. A real Boolean argument enters the marked parameter prefix, and the
parent statement retains the exact returned pool. No expression or body
execution law is a premise. -/
set_option autoImplicit false
namespace Tests.SourceCoreClosedOwnedNamedFamily
open Solcore Core Frontend SourceInference
open SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds ProtectedStateTransition
open Tests.SourceCoreClosedOwnedExpressionTree (BooleanCall booleanCode)
open Tests.SourceCoreClosedOwnedExpressionHead (PreparedReceipts layouts)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions) {faults : FunctionCalls.FaultRep}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {compilation : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → SourceCoreFunctions.Context}

abbrev expressions (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (context : SourceSemantics.Context) :=
  RecursiveNamedCatalog.Expressions (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers (compilation header)
    header.readFuel header.function.source context header.solved header.reasonAt

/-- The original ordinary Head and Tree factories retain the same real
Boolean argument, emitted call code and selected header slot. -/
theorem ordinary_boolean_call_tree
    {parent callee : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    {scope : SourceCoreLocalCell.Scope} {id target argument : ExpressionId} {boolean : Bool} {code : Expr}
    (receipt : BooleanCall (headers := headers) (source := parent.function.source) (context := parent.context)
      (compilation := compilation parent) callee scope id target argument boolean code) :
    expressions (headers := headers) (compilation := compilation) parent parent.context scope id ⟨callee.output, code⟩ := by
  have literal : CompatibleExpressionLiterals.Certificate parent.solved parent.function.source argument (booleanCode boolean) :=
    ⟨receipt.argumentNode, receipt.argumentFound, .bool boolean receipt.argumentForm receipt.argumentType
      receipt.argumentRequirements receipt.argumentCoercions⟩
  have child : expressions (headers := headers) (compilation := compilation) parent parent.context scope argument (booleanCode boolean) :=
    .fragment (.fragment (.fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal literal))))))))
  have arity : callee.function.parameters.length = [argument].length := by
    rw [callee.parameters, List.length_map]
    have count := congrArg List.length receipt.parameterTypes
    simpa only [List.length_map, List.length_singleton] using count
  refine .node (entries := [(argument, booleanCode boolean)]) (.call (.named receipt.member receipt.metadata receipt.sourceType receipt.form
    receipt.calleeFound receipt.calleeForm receipt.calleeRequirements receipt.calleeCoercions receipt.valid
    receipt.predicates receipt.calleeEvidence arity receipt.emission receipt.selectedSlot ?_ ?_)) ?_
  · rw [receipt.parameterTypes]
    have sequence : DataExpressionSequence.Tree parent.function.source
        (CompatibleExpressionCalls.Entries scope [(argument, booleanCode boolean)]) scope [argument]
        [receipt.argumentNode.type] [booleanCode boolean] := .single receipt.argumentFound ⟨rfl, by simp⟩
    simpa only [receipt.argumentType] using sequence
  · simpa only [List.map_cons, List.map_nil, booleanCode] using receipt.nativeTypes.symm
  · intro selected lowered member
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp member)
    exact child

/-- The source parent contains an actual callee expression. Every field is a
source, typing or compiler receipt, with no execution callback. -/
structure CallBody (parent : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)) where
  statement : StatementId
  statementNode : StatementNode
  expression : ExpressionId
  target : ExpressionId
  argument : ExpressionId
  boolean : Bool
  code : Expr
  callee : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)
  body : parent.function.body = [statement]
  found : parent.function.source.lookupStatement? statement = some statementNode
  form : statementNode.form = .expression expression true
  statementType : statementNode.type = .unit
  call : BooleanCall (headers := headers) (source := parent.function.source) (context := parent.context)
    (compilation := compilation parent) callee
    (parent.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression target argument boolean code
  typed : ExpressionHasType parent.function.source parent.context expression call.node.type
  unitResult : parent.function.resultType = .unit
  generated : SourceCoreLoops.lowerFlowStatementsWithPolicy parent.policy parent.fuel parent.function.source
    (parent.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) parent.function.body
    parent.output parent.reasonAt true parent.escaped =
      .ok (LocalSequence.discard (LocalLoop.controlType parent.output) code (LocalLoop.fallthrough parent.output))

/-- The selected source and native parameter vectors genuinely contain one
Boolean, so this call reaches the marked allocation path. -/
theorem call_body_parameter_count
    {parent : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (receipt : CallBody (headers := headers) (compilation := compilation) parent) :
    receipt.callee.function.parameters.length = 1 ∧ receipt.callee.bindings.length = 1 := by
  have sourceCount := congrArg List.length receipt.call.parameterTypes
  have nativeCount := congrArg List.length receipt.call.nativeTypes
  constructor
  · rw [receipt.callee.parameters, List.length_map]
    simpa only [List.length_map, List.length_singleton] using sourceCount
  · simpa only [List.length_map, List.length_singleton] using nativeCount

/-- Only these static body shapes are admitted by this regression family. -/
inductive BodyReceipt (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)) where
  | nil (valid : CompatibleExpressionLiterals.ContextValid header.solved header.context header.function.evidence)
      (body : header.function.body = []) (unitResult : header.function.resultType = .unit)
  | call (valid : CompatibleExpressionLiterals.ContextValid header.solved header.context header.function.evidence)
      (receipt : CallBody (headers := headers) (compilation := compilation) header)

variable (receipts : PreparedReceipts (headers := headers))
  (bodies : ∀ header, header ∈ headers → BodyReceipt (headers := headers) (compilation := compilation) header)
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = owner.key.capturePrefix + 1)

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

private def profile {header} (member : header ∈ headers) (administrative : Core.Context) :
    RecursiveNamedCatalogMutualMeaning.MatchProfileForModeWith (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      true false .reachable headers header (compilation header) header.readFuel (fun _ => True)
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults := by
  cases bodies header member with
  | nil valid body unitResult =>
    let admission : GenericLexicalStatements.Syntax header.function.source (fun _ => True) header.context true
        header.function.body header.function.resultType := body ▸ .nil (Or.inr unitResult)
    let lexical : GenericLexicalStatements.Tree header.layouts header.owner header.active compiled.indexed.ancestry.layout.frame
        header.globals header.onError (.initial compiled.compatible.checked) header.function.source
        (expressions (headers := headers) (compilation := compilation) header) header.context
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) true header.function.body
        header.function.resultType header.output (LocalLoop.fallthrough header.output) := body ▸ .nil (Or.inr unitResult)
    have generated : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
        header.output header.reasonAt true header.escaped = .ok (LocalLoop.fallthrough header.output) := by
      rw [body]
      cases header.fuel <;> rfl
    exact MatchProfileWith.of_extracted valid (accepted receipts member) (projection receipts member) generated
      (.body admission lexical) (.body (syntaxTree := admission) (body := lexical))
  | call valid receipt =>
    let admission : GenericLexicalStatements.Syntax header.function.source (fun _ => True) header.context true
        header.function.body header.function.resultType := by
      rw [receipt.body]
      exact .discard receipt.found receipt.form (by decide) receipt.statementType receipt.call.metadata.found
        receipt.typed trivial (.nil (Or.inr receipt.unitResult))
    let lexical : GenericLexicalStatements.Tree header.layouts header.owner header.active compiled.indexed.ancestry.layout.frame
        header.globals header.onError (.initial compiled.compatible.checked) header.function.source
        (expressions (headers := headers) (compilation := compilation) header) header.context
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) true header.function.body
        header.function.resultType header.output
        (LocalSequence.discard (LocalLoop.controlType header.output) receipt.code (LocalLoop.fallthrough header.output)) := by
      rw [receipt.body]
      exact .discard receipt.found receipt.form (by decide) receipt.call.metadata.found
        (ordinary_boolean_call_tree receipt.call) (.nil (Or.inr receipt.unitResult))
    exact MatchProfileWith.of_extracted valid (accepted receipts member) (projection receipts member) receipt.generated
      (.body admission lexical) (.body (syntaxTree := admission) (body := lexical))

include extension faithful observations functionTypes receipts bodies owners uninitialized missing escaped prefixMatches in
/-- The closed named family proves every body callback from the static shapes
above, including the parent call and its real nonempty parameter prefix. -/
theorem family_preserves (size : Nat) : ∀ header, header ∈ headers →
    RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      functions registry header faults (protocol headers keys)
      (CallableIndexedOwnedNamedBodyBounds.stableCondition functions owner header) size := by
  exact CallableIndexedOwnedNamedFamilyClosure.preserves_at functions extension faithful observations functionTypes owner
    (fun _ member => layouts receipts member) false owners uninitialized missing escaped prefixMatches
    (by
      intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry
      exact profile (registry := registry) (faults := faults) receipts bodies member administrative) size

include extension faithful observations functionTypes receipts bodies uninitialized missing escaped prefixMatches in
/-- Native completion selects the strict callees independently and returns its
own source grade together with the actual final pool. -/
theorem family_reflects (size : Nat) : ∀ header, header ∈ headers →
    RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      functions registry header faults (protocol headers keys)
      (CallableIndexedOwnedNamedBodyBounds.stableCondition functions owner header) size := by
  exact CallableIndexedOwnedNamedFamilyClosure.reflects_at functions extension faithful observations functionTypes owner
    (fun _ member => layouts receipts member) false uninitialized missing escaped prefixMatches
    (by
      intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry
      exact profile (registry := registry) (faults := faults) receipts bodies member administrative) size

section Parent
variable {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (member : header ∈ headers)
  (parent : CallBody (headers := headers) (compilation := compilation) header)
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
  (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers owner.key.locations owner.key.capturePrefix
    functions registry header arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost)
  (initial : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
    entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
  (seed : CallableIndexedOwnedAllocationProducer.StableOwner keys frameLocation current)

include extension faithful observations functionTypes receipts bodies owners uninitialized missing escaped prefixMatches member parent entry initial seed in
/-- A source parent-call execution yields genuine native completion and the
live snapshots of the returned pool, with all earlier row records retained. -/
theorem parent_source_post (size : Nat) {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyTrace (Program.ofChecked compiled.sourceProgram) size header.function header.context
      entry.environment entry.heap outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates entry.actualBody entry.store (header.body.rename entry.embedding) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      header.function.body = [parent.statement] ∧ parent.callee ∈ headers ∧
      ∃ reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
          finalMap, finalWorld, after, finalStore, entry.canonical⟩,
        Relates initial reached ∧ Tests.SourceCoreClosedOwnedExpressionHead.PoolObservations initial reached := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, preserved, metadata, reached, related⟩ :=
    family_preserves functions extension faithful observations functionTypes owner receipts bodies owners uninitialized missing escaped prefixMatches
      size header member entry initial seed trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, preserved, metadata,
    parent.body, parent.call.member, reached, related, Tests.SourceCoreClosedOwnedLexicalBody.reached_pool_observations related⟩

include extension faithful observations functionTypes receipts bodies uninitialized missing escaped prefixMatches member parent entry initial seed in
/-- Original native completion reflects the actual parent call at an
independent source grade and observes the same authentic reached pool. -/
theorem parent_native_post (size : Nat) {value : Value} {finalStore : Store}
    (completed : EvaluationSize size entry.actualBody entry.store (header.body.rename entry.embedding) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace (Program.ofChecked compiled.sourceProgram) sourceSize header.function header.context
        entry.environment entry.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      header.function.body = [parent.statement] ∧ parent.callee ∈ headers ∧
      ∃ reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
          finalMap, finalWorld, after, finalStore, entry.canonical⟩,
        Relates initial reached ∧ Tests.SourceCoreClosedOwnedExpressionHead.PoolObservations initial reached := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, preserved, metadata, reached, related⟩ :=
    family_reflects functions extension faithful observations functionTypes owner receipts bodies uninitialized missing escaped prefixMatches
      size header member entry initial seed completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, preserved, metadata,
    parent.body, parent.call.member, reached, related, Tests.SourceCoreClosedOwnedLexicalBody.reached_pool_observations related⟩
end Parent
end Tests.SourceCoreClosedOwnedNamedFamily
