import Solcore.Test.SourceCoreClosedOwnedExpressionHead
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExpressionTreeBounds

/-! A complete owned expression Tree uses literal receipts and the proved nil
Unit named body family. Real Boolean arguments drive marked parameter cells,
and surrounding tuple children retain the exact returned pools. -/
set_option autoImplicit false
namespace Tests.SourceCoreClosedOwnedExpressionTree
open Solcore Core Frontend SourceInference
open SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState ProtectedStateTransition
open CallableIndexedOwnedExpressionHeads
open Tests.SourceCoreClosedOwnedExpressionHead

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
  (receipts : PreparedReceipts (headers := headers))
  (body_nil : ∀ header, header ∈ headers → header.function.body = [])
  (unit_result : ∀ header, header ∈ headers → header.function.resultType = .unit)
  (escaped : ∀ header, header ∈ headers → faults .controlEscapedFunction header.escaped)
  {source : TypedSource} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
  {compilation : SourceCoreFunctions.Context} {solved : List SolvedRequirement} {fuel : Nat}
  {reasonAt : ExpressionId → Word}
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (unique : NodeOccurrencesUnique source)
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

abbrev Calls := RecursiveNamedCallEvidenceHeads.Calls (prepared := compiled.indexed.ancestry)
  (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
  (some evidence) headers compilation source context

abbrev Expressions := CompatibleExpressionCalls.Tree (Calls (headers := headers) (source := source) (context := context) (compilation := compilation) evidence)
  fuel (.initial compiled.compatible.checked) source context solved reasonAt

include extension faithful observations functionTypes receipts body_nil unit_result escaped valid unique owners uninitialized missing in
/-- All literal and callee callbacks are proved from static receipts. The
original Tree fold closes every expression child at its actual post-state. -/
theorem closed_tree_preserves (size : Nat) (idsUnique : RequirementIdsUnique context) :
    ProtectedStateTransition.PreservesAt (argumentProtocol (headers := headers) owner compilation.administrativePrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      (Program.ofChecked compiled.sourceProgram) context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals (calls := Calls (headers := headers) (source := source) (context := context) (compilation := compilation) evidence)
        (fuel := fuel) (values := .initial compiled.compatible.checked) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt)
        (fun _ id code => CompatibleExpressionLiterals.Certificate solved source id code)) faults size := by
  exact CallableIndexedOwnedExpressionTreeBounds.preserves_at_with_literals
    (solved := solved) (fuel := fuel) (compilation := compilation) functions extension faithful observations functionTypes
    evidence unique owners uninitialized missing owner (fun header member => layouts receipts member)
    (conditions functions owner)
    (fun header member => CallableIndexedOwnedInvocationBounds.stable_owner_authorized functions registry header owner)
    idsUnique (CompatibleExpressionLiterals.preserves functions (Program.ofChecked compiled.sourceProgram) context evidence valid unique faults)
    size size (Nat.le_refl _) (by
      intro header member child smaller
      exact bodies_preserve functions extension faithful observations owner receipts body_nil unit_result escaped child header member)

include extension faithful observations functionTypes receipts body_nil unit_result escaped valid uninitialized missing in
/-- Native children select their own grades; the reconstructed source grade
and actual reached pool come from the same closed Tree. -/
theorem closed_tree_reflects (size : Nat) :
    ProtectedStateTransition.ReflectsAt (argumentProtocol (headers := headers) owner compilation.administrativePrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      (Program.ofChecked compiled.sourceProgram) context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals (calls := Calls (headers := headers) (source := source) (context := context) (compilation := compilation) evidence)
        (fuel := fuel) (values := .initial compiled.compatible.checked) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt)
        (fun _ id code => CompatibleExpressionLiterals.Certificate solved source id code)) faults size := by
  exact CallableIndexedOwnedExpressionTreeBounds.reflects_at_with_literals
    (solved := solved) (fuel := fuel) (compilation := compilation) functions extension faithful observations functionTypes
    evidence uninitialized missing owner (fun header member => layouts receipts member)
    (conditions functions owner)
    (fun header member => CallableIndexedOwnedInvocationBounds.stable_owner_authorized functions registry header owner)
    (CompatibleExpressionLiterals.reflects functions (Program.ofChecked compiled.sourceProgram) context evidence valid source faults)
    size size (Nat.le_refl _) (by
      intro header member child smaller
      exact bodies_reflect functions extension faithful observations functionTypes owner receipts body_nil unit_result escaped child header member)


/-- The exact code emitted for the ordinary Boolean literal receipt. -/
def booleanCode (boolean : Bool) : SourceCoreBasic.LoweredExpr :=
  ⟨.bool, LanguageResult.success (.bool boolean)⟩

/-- The original fragment constructors embed a real literal certificate into
the whole static Tree without a semantic callback. -/
theorem literal_tree {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {code : SourceCoreBasic.LoweredExpr}
    (literal : CompatibleExpressionLiterals.Certificate solved source id code) :
    Expressions (headers := headers) (source := source) (context := context) (compilation := compilation)
      (solved := solved) (fuel := fuel) (reasonAt := reasonAt) evidence scope id code := by
  exact .fragment (.fragment (.fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal literal))))))))

/-- This receipt chooses one genuine named header and one Boolean parameter.
The source nodes, retained metadata and complete compiler emission are inputs. -/
structure BooleanCall
    (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (scope : SourceCoreLocalCell.Scope) (id callee argument : ExpressionId) (boolean : Bool) (expression : Expr) where
  member : header ∈ headers
  node : ExpressionNode
  calleeNode : ExpressionNode
  argumentNode : ExpressionNode
  name : String
  booleanName : String
  metadata : CompatibleExpressionPrimitives.Metadata compiled.compatible.checked source id node header.output
  sourceType : node.type = header.function.resultType
  form : node.form = .call callee [argument] (.declaration header.instantiation)
  calleeFound : source.lookupExpression? callee = some calleeNode
  calleeForm : calleeNode.form = .reference name (.declaration header.instantiation)
  calleeRequirements : calleeNode.requirements = []
  calleeCoercions : calleeNode.coercions = []
  argumentFound : source.lookupExpression? argument = some argumentNode
  argumentForm : argumentNode.form = .reference booleanName (.builtinBoolean boolean)
  argumentType : argumentNode.type = .bool
  argumentRequirements : argumentNode.requirements = []
  argumentCoercions : argumentNode.coercions = []
  valid : SourceSemantics.DeclarationInstantiation.Valid context header.instantiation
  predicates : header.instantiation.predicates = []
  calleeEvidence : header.function.evidence = []
  parameterTypes : header.bindings.map (fun binding => binding.1.scheme.body) = [.bool]
  nativeTypes : header.bindings.map Prod.snd = [.bool]
  emission : NamedCalls.Arguments.Emission compilation source scope id callee [argument]
    header.instantiation header.named.signature [booleanCode boolean] ⟨header.output, expression⟩
  selectedSlot : emission.index = header.slot

/-- The actual source parameter vector is nonempty, so the real named prefix
runs its marked allocation before reaching the closed nil Unit body. -/
theorem boolean_call_tree
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    {scope : SourceCoreLocalCell.Scope} {id callee argument : ExpressionId} {boolean : Bool} {expression : Expr}
    (receipt : BooleanCall (headers := headers) (source := source) (context := context) (compilation := compilation)
      header scope id callee argument boolean expression) :
    Expressions (headers := headers) (source := source) (context := context) (compilation := compilation)
      (solved := solved) (fuel := fuel) (reasonAt := reasonAt) evidence scope id ⟨header.output, expression⟩ := by
  have literal : CompatibleExpressionLiterals.Certificate solved source argument (booleanCode boolean) :=
    ⟨receipt.argumentNode, receipt.argumentFound, .bool boolean receipt.argumentForm receipt.argumentType
      receipt.argumentRequirements receipt.argumentCoercions⟩
  have child := literal_tree (scope := scope) (headers := headers) (context := context) (compilation := compilation)
    (fuel := fuel) (reasonAt := reasonAt) evidence literal
  have arity : header.function.parameters.length = [argument].length := by
    rw [header.parameters, List.length_map]
    have count := congrArg List.length receipt.parameterTypes
    simpa only [List.length_map, List.length_singleton] using count
  refine .node (entries := [(argument, booleanCode boolean)]) (.call (.ordinary (.named receipt.member receipt.metadata receipt.sourceType receipt.form
    receipt.calleeFound receipt.calleeForm receipt.calleeRequirements receipt.calleeCoercions receipt.valid
    receipt.predicates receipt.calleeEvidence arity receipt.emission receipt.selectedSlot ?_ ?_))) ?_
  · rw [receipt.parameterTypes]
    have sequence : DataExpressionSequence.Tree source
        (CompatibleExpressionCalls.Entries scope [(argument, booleanCode boolean)]) scope
        [argument] [receipt.argumentNode.type] [booleanCode boolean] :=
      .single receipt.argumentFound ⟨rfl, by simp⟩
    simpa only [receipt.argumentType] using sequence
  · simpa only [List.map_cons, List.map_nil, booleanCode] using receipt.nativeTypes.symm
  · intro selected code member
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp member)
    exact child

/-- A real tuple head can enclose the Boolean call and another literal. Both
ordered child Trees are retained by the original factory. -/
theorem tuple_of_trees {scope : SourceCoreLocalCell.Scope} {id left right : ExpressionId}
    {node leftNode rightNode : ExpressionNode} {first second : SourceCoreBasic.LoweredExpr}
    (metadata : CompatibleExpressionPrimitives.Metadata compiled.compatible.checked source id node (.product first.type second.type))
    (form : node.form = .tuple [left, right])
    (leftFound : source.lookupExpression? left = some leftNode) (rightFound : source.lookupExpression? right = some rightNode)
    (sourceType : node.type = .product leftNode.type rightNode.type)
    (leftTree : Expressions (headers := headers) (source := source) (context := context) (compilation := compilation)
      (solved := solved) (fuel := fuel) (reasonAt := reasonAt) evidence scope left first)
    (rightTree : Expressions (headers := headers) (source := source) (context := context) (compilation := compilation)
      (solved := solved) (fuel := fuel) (reasonAt := reasonAt) evidence scope right second) :
    Expressions (headers := headers) (source := source) (context := context) (compilation := compilation)
      (solved := solved) (fuel := fuel) (reasonAt := reasonAt) evidence scope id
      ⟨.product first.type second.type, LocalSequence.pair first.type second.type first.expression second.expression⟩ := by
  refine .node (entries := [(left, first), (right, second)]) (.primitive (.pair metadata form leftFound rightFound sourceType ⟨rfl, by simp⟩ ⟨rfl, by simp⟩)) ?_
  intro child code member
  rcases List.mem_cons.mp member with equal | rest
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
    exact leftTree
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp rest)
    exact rightTree


section ComposedCall
variable {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {scope : SourceCoreLocalCell.Scope} {callId callee argument tupleId right : ExpressionId}
  {boolean rightBoolean : Bool} {expression : Expr} {tupleNode rightNode : ExpressionNode}
  (call : BooleanCall (headers := headers) (source := source) (context := context) (compilation := compilation)
    header scope callId callee argument boolean expression)
  (tupleMetadata : CompatibleExpressionPrimitives.Metadata compiled.compatible.checked source tupleId tupleNode (.product header.output .bool))
  (tupleForm : tupleNode.form = .tuple [callId, right])
  (rightFound : source.lookupExpression? right = some rightNode)
  (tupleType : tupleNode.type = .product call.node.type rightNode.type)
  (rightLiteral : CompatibleExpressionLiterals.Certificate solved source right (booleanCode rightBoolean))

include call tupleMetadata tupleForm rightFound tupleType rightLiteral in
/-- The composed expression has a real call with one Boolean parameter,
followed by a Boolean literal in the original ordered tuple Tree. -/
theorem boolean_call_tuple_tree :
    Expressions (headers := headers) (source := source) (context := context) (compilation := compilation)
      (solved := solved) (fuel := fuel) (reasonAt := reasonAt) evidence scope tupleId
      ⟨.product header.output .bool, LocalSequence.pair header.output .bool expression (booleanCode rightBoolean).expression⟩ := by
  exact tuple_of_trees evidence tupleMetadata tupleForm call.metadata.found rightFound tupleType
    (boolean_call_tree evidence call) (literal_tree evidence rightLiteral)

variable {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) mapping world
    administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (initial : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (globals : Globals (headers := headers) owner compilation.administrativePrefix scope canonical)

include fuel extension faithful observations functionTypes receipts body_nil unit_result escaped valid unique owners uninitialized missing
  call tupleMetadata tupleForm rightFound tupleType rightLiteral environments heaps locals agrees typed initial globals in
/-- A source execution of the composed Tree obtains the actual parameter,
callee and restored caller states. All semantic callbacks are closed above. -/
theorem boolean_call_tuple_source_post (size : Nat) (idsUnique : RequirementIdsUnique context)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size context evidence source
      environment before tupleId outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store
        ((LocalSequence.pair header.output .bool expression (booleanCode rightBoolean).expression).rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld tupleNode.type (.product header.output .bool) faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial reached ∧ PoolObservations initial reached := by
  have tree := boolean_call_tuple_tree (fuel := fuel) (reasonAt := reasonAt) evidence call tupleMetadata tupleForm rightFound tupleType rightLiteral
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, reached, related⟩ :=
    closed_tree_preserves functions extension faithful observations functionTypes owner receipts body_nil unit_result escaped
      evidence valid unique owners uninitialized missing size idsUnique
      ⟨tree, tree.literalSites⟩ tupleMetadata.found environments heaps locals agrees typed ⟨initial, globals⟩ trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
    reached.val, related, Tests.SourceCoreClosedOwnedLexicalBody.reached_pool_observations related⟩

include fuel extension faithful observations functionTypes receipts body_nil unit_result escaped valid uninitialized missing
  call tupleMetadata tupleForm rightFound tupleType rightLiteral environments heaps locals agrees typed initial globals in
/-- Native completion reconstructs the complete source tuple and call evidence
at an independent source grade. The observations use the actual returned pool. -/
theorem boolean_call_tuple_native_post (size : Nat) {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store
      ((LocalSequence.pair header.output .bool expression (booleanCode rightBoolean).expression).rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context evidence source
        environment before tupleId outcome after ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld tupleNode.type (.product header.output .bool) faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial reached ∧ PoolObservations initial reached := by
  have tree := boolean_call_tuple_tree (fuel := fuel) (reasonAt := reasonAt) evidence call tupleMetadata tupleForm rightFound tupleType rightLiteral
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, reached, related⟩ :=
    closed_tree_reflects functions extension faithful observations functionTypes owner receipts body_nil unit_result escaped
      evidence valid uninitialized missing size
      ⟨tree, tree.literalSites⟩ tupleMetadata.found environments heaps locals agrees typed ⟨initial, globals⟩ completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata,
    reached.val, related, Tests.SourceCoreClosedOwnedLexicalBody.reached_pool_observations related⟩
end ComposedCall

end Tests.SourceCoreClosedOwnedExpressionTree


