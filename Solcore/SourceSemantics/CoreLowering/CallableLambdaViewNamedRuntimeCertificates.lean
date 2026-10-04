import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewMatchRuntimeCertificates
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionCompilerCertificates

/-! Actual ordered child vectors and full reached nodes retain the same named
call certificates across a local lambda compiler view. Dictionary indices,
selected physical slots and every emitted Core child remain unchanged. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableLambdaViewNamedRuntimeCertificates
open Core Frontend SourceInference
open CallableLambdaViewEdits CallableLambdaBodyReachability
open CallableCoercionExpressionCertificates

/-- The actual child action retains its source and entire ordered vector.
Only the source argument passed by the enclosing receipt is adapted. -/
def vectorAdapter (child : SourceCoreEvidence.Child) (source : TypedSource) : SourceCoreEvidence.Child :=
  fun fuel _ scope id reasonAt => child fuel source scope id reasonAt

theorem direct_action_eq
    {program : CheckedProgram} {project : Projector} {caller : Specialized}
    {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child}
    {fuel : Nat} {source view : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id callee : ExpressionId} {arguments : List ExpressionId}
    {instantiation : DeclarationInstantiation} {reasonAt : ExpressionId → Word}
    {policy : SourceCoreFunctions.CallablePolicy} {node : ExpressionNode}
    (found : source.lookupExpression? id = some node)
    (same : view.lookupExpression? id = source.lookupExpression? id)
    (calleeEq : view.lookupExpression? callee = source.lookupExpression? callee)
    (form : node.form = .call callee arguments (.declaration instantiation)) :
    SourceCoreEvidence.lowerWithProjector program project caller compilation
      (vectorAdapter child source) fuel view scope id reasonAt policy =
    SourceCoreEvidence.lowerWithProjector program project caller compilation
      child fuel source scope id reasonAt policy := by
  simp only [SourceCoreEvidence.lowerWithProjector, same, found, form,
    bind, Except.bind, pure, Except.pure, vectorAdapter,
    SourceCompilationPlan.validateDirectDeclarationCallee, calleeEq]

/-- Reindex the actual direct receipt through full node lookup equality. Its
child results still come from the original accepted compiler action. -/
def direct
    {program : CheckedProgram} {project : Projector} {caller : Specialized}
    {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child}
    {fuel : Nat} {source view : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id callee : ExpressionId} {arguments : List ExpressionId}
    {instantiation : DeclarationInstantiation} {reasonAt : ExpressionId → Word}
    {policy : SourceCoreFunctions.CallablePolicy} {node : ExpressionNode} {output : Lowered}
    (same : view.lookupExpression? id = source.lookupExpression? id)
    (calleeEq : view.lookupExpression? callee = source.lookupExpression? callee)
    (receipt : Direct program project caller compilation child fuel source scope id callee arguments
      instantiation reasonAt policy node output) :
    Direct program project caller compilation (vectorAdapter child source) fuel view scope id callee arguments
      instantiation reasonAt policy node output where
  available := receipt.available
  operand := receipt.operand
  found := same.trans receipt.found
  accepted := (direct_action_eq receipt.found same calleeEq receipt.form).trans receipt.accepted
  pathValid := receipt.pathValid
  owner := receipt.owner
  resolved := receipt.resolved
  suffix := receipt.suffix
  form := receipt.form
  selection := receipt.selection
  sameAvailable := receipt.sameAvailable
  calleeAccepted := by simpa only [SourceCompilationPlan.validateDirectDeclarationCallee, calleeEq] using receipt.calleeAccepted
  arity := receipt.arity
  loweredArguments := receipt.loweredArguments
  argumentsAccepted := receipt.argumentsAccepted
  native := receipt.native


section CanonicalCalls
open CallableAncestryPairedLookup RecursiveNamedCatalog
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {headers : Inventory prepared values ambient.definitions program}
  {compilation : SourceCoreFunctions.Context} {source view : TypedSource}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {children : GenericExpressionMeaning.Certificate} {scope : SourceCoreLocalCell.Scope}

/-- The actual emission remains indexed by its real compiler view. Canonical
source fields and ordered argument certificates retain the same output code. -/
structure Ordinary (headers : Inventory prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (source : TypedSource)
    (context : SourceSemantics.Context) (children : GenericExpressionMeaning.Certificate)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (output : Lowered) where
  header : Header prepared values ambient.definitions program
  member : header ∈ headers
  node : ExpressionNode
  metadata : CompatibleExpressionPrimitives.Metadata values.checked source id node header.output
  sourceType : node.type = header.function.resultType
  callee : ExpressionId
  arguments : List ExpressionId
  form : node.form = .call callee arguments (.declaration header.instantiation)
  calleeNode : ExpressionNode
  name : String
  calleeFound : source.lookupExpression? callee = some calleeNode
  calleeForm : calleeNode.form = .reference name (.declaration header.instantiation)
  calleeRequirements : calleeNode.requirements = []
  calleeCoercions : calleeNode.coercions = []
  valid : SourceSemantics.DeclarationInstantiation.Valid context header.instantiation
  predicates : header.instantiation.predicates = []
  evidenceEmpty : header.function.evidence = []
  arity : header.function.parameters.length = arguments.length
  codes : List Lowered
  actualSource : TypedSource
  emission : NamedCalls.Arguments.Emission compilation actualSource scope id callee arguments
    header.instantiation header.named.signature codes output
  selectedSlot : emission.index = header.slot
  nativeType : output.type = header.output
  sequence : DataExpressionSequence.Tree source children scope arguments
    (header.bindings.map (fun binding => binding.1.scheme.body)) codes
  nativeTypes : codes.map (·.type) = header.bindings.map Prod.snd

inductive Head (headers : Inventory prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (source : TypedSource)
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (children : GenericExpressionMeaning.Certificate) (scope : SourceCoreLocalCell.Scope) :
    ExpressionId → Lowered → Prop where
  | ordinary {id output} (receipt : Ordinary headers compilation source context children scope id output) :
      Head headers compilation source context evidence children scope id output
  | authenticated {id output}
      (receipt : RecursiveNamedCallEvidenceHeads.Head headers compilation source context evidence children scope id output) :
      Head headers compilation source context evidence children scope id output

section Transport
variable {roots : List NodeId} {changed : List ExpressionId}
  (edited : LocalView source view changed) (avoids : Avoids source roots changed)

include edited avoids in
theorem sequence {before after : GenericExpressionMeaning.Certificate}
    {ids : List ExpressionId} {types : List TypeSystem.Ty} {codes : List Lowered}
    (expressions : ∀ child code, child ∈ ids → before scope child code → after scope child code)
    (tree : DataExpressionSequence.Tree source before scope ids types codes)
    (reached : ∀ id ∈ ids, Reaches source roots (.expression id)) :
    DataExpressionSequence.Tree view after scope ids types codes := by
  induction tree with
  | nil => exact .nil
  | single found generated =>
    exact .single ((expression_lookup edited avoids (reached _ (by simp))).symm.trans found)
      (expressions _ _ (by simp) generated)
  | cons found generated _ ih =>
    exact .cons ((expression_lookup edited avoids (reached _ (by simp))).symm.trans found)
      (expressions _ _ (by simp) generated)
      (ih (fun child code member => expressions child code (List.mem_cons_of_mem _ member)) (fun id member => reached id (List.mem_cons_of_mem _ member)))

include edited avoids in
def ordinary_transport {before after : GenericExpressionMeaning.Certificate}
    {id : ExpressionId} {output : Lowered}
    (receipt : Ordinary headers compilation source context before scope id output)
    (reached : Reaches source roots (.expression id))
    (expressions : ∀ child code, NodeId.expression child ∈ receipt.node.form.references → before scope child code → after scope child code) :
    Ordinary headers compilation view context after scope id output := by
  have argumentReached : ∀ child ∈ receipt.arguments, Reaches source roots (.expression child) := by
    intro child member
    exact .expression reached receipt.metadata.found (by simp [receipt.form, ExpressionForm.references, member])
  have calleeReached : Reaches source roots (.expression receipt.callee) :=
    .expression reached receipt.metadata.found (by simp [receipt.form, ExpressionForm.references])
  exact {receipt with
    metadata := CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt.metadata
    calleeFound := (expression_lookup edited avoids calleeReached).symm.trans receipt.calleeFound
    sequence := sequence edited avoids
      (fun child code member certified => expressions child code
        (by simp [receipt.form, ExpressionForm.references, member]) certified)
      receipt.sequence argumentReached}


include edited avoids in
theorem composition_transport {before after : GenericExpressionMeaning.Certificate}
    {id : ExpressionId} {node : ExpressionNode} {output : Lowered}
    (found : source.lookupExpression? id = some node)
    (head : CompatibleExpressionTypedCompositions.Head values.checked source before scope id output)
    (reached : Reaches source roots (.expression id))
    (expressions : ∀ child code, NodeId.expression child ∈ node.form.references → before scope child code → after scope child code) :
    CompatibleExpressionTypedCompositions.Head values.checked view after scope id output := by
  cases head with
  | group metadata form innerFound sourceType certified =>
    have same := Option.some.inj (found.symm.trans metadata.found)
    subst node
    exact .group (CallableLambdaViewExpressionLeaves.metadata edited avoids reached metadata) form
      ((expression_lookup edited avoids (.expression reached metadata.found (by simp [form, ExpressionForm.references]))).symm.trans innerFound) sourceType
      (expressions _ _ (by simp [form, ExpressionForm.references]) certified)
  | pair metadata form leftFound rightFound sourceType first second =>
    have same := Option.some.inj (found.symm.trans metadata.found)
    subst node
    exact .pair (CallableLambdaViewExpressionLeaves.metadata edited avoids reached metadata) form
      ((expression_lookup edited avoids (.expression reached metadata.found (by simp [form, ExpressionForm.references]))).symm.trans leftFound)
      ((expression_lookup edited avoids (.expression reached metadata.found (by simp [form, ExpressionForm.references]))).symm.trans rightFound)
      sourceType (expressions _ _ (by simp [form, ExpressionForm.references]) first)
      (expressions _ _ (by simp [form, ExpressionForm.references]) second)
  | unary metadata form childFound inputType outputType profile certified =>
    have same := Option.some.inj (found.symm.trans metadata.found)
    subst node
    exact .unary (CallableLambdaViewExpressionLeaves.metadata edited avoids reached metadata) form
      ((expression_lookup edited avoids (.expression reached metadata.found (by simp [form, ExpressionForm.references]))).symm.trans childFound)
      inputType outputType profile (expressions _ _ (by simp [form, ExpressionForm.references]) certified)
  | binary metadata form leftFound rightFound leftType rightType outputType profile first second =>
    have same := Option.some.inj (found.symm.trans metadata.found)
    subst node
    exact .binary (CallableLambdaViewExpressionLeaves.metadata edited avoids reached metadata) form
      ((expression_lookup edited avoids (.expression reached metadata.found (by simp [form, ExpressionForm.references]))).symm.trans leftFound)
      ((expression_lookup edited avoids (.expression reached metadata.found (by simp [form, ExpressionForm.references]))).symm.trans rightFound)
      leftType rightType outputType profile (expressions _ _ (by simp [form, ExpressionForm.references]) first)
      (expressions _ _ (by simp [form, ExpressionForm.references]) second)
  | conditional metadata form conditionFound thenFound elseFound conditionType thenType elseType first second third =>
    have same := Option.some.inj (found.symm.trans metadata.found)
    subst node
    exact .conditional (CallableLambdaViewExpressionLeaves.metadata edited avoids reached metadata) form
      ((expression_lookup edited avoids (.expression reached metadata.found (by simp [form, ExpressionForm.references]))).symm.trans conditionFound)
      ((expression_lookup edited avoids (.expression reached metadata.found (by simp [form, ExpressionForm.references]))).symm.trans thenFound)
      ((expression_lookup edited avoids (.expression reached metadata.found (by simp [form, ExpressionForm.references]))).symm.trans elseFound)
      conditionType thenType elseType (expressions _ _ (by simp [form, ExpressionForm.references]) first)
      (expressions _ _ (by simp [form, ExpressionForm.references]) second)
      (expressions _ _ (by simp [form, ExpressionForm.references]) third)

include edited avoids in
theorem call_transport {before after : GenericExpressionMeaning.Certificate}
    {id : ExpressionId} {node : ExpressionNode} {output : Lowered}
    (found : source.lookupExpression? id = some node)
    (head : RecursiveNamedCallEvidenceHeads.Head headers compilation source context evidence before scope id output)
    (reached : Reaches source roots (.expression id))
    (expressions : ∀ child code, NodeId.expression child ∈ node.form.references → before scope child code → after scope child code) :
    Head headers compilation view context evidence after scope id output := by
  cases head with
  | ordinary head =>
    cases head with
    | @named callee arguments header callNode calleeNode name codes expression member metadata sourceType form calleeFound calleeForm
        calleeRequirements calleeCoercions valid predicates evidenceEmpty arity emission selectedSlot sequence nativeTypes =>
      have same := Option.some.inj (found.symm.trans metadata.found)
      subst node
      let receipt : Ordinary headers compilation source context before scope id ⟨header.output, expression⟩ := {
        header := header, member := member, node := callNode, metadata := metadata,
        sourceType := sourceType, callee := callee, arguments := arguments, form := form,
        calleeNode := calleeNode, name := name, calleeFound := calleeFound, calleeForm := calleeForm,
        calleeRequirements := calleeRequirements, calleeCoercions := calleeCoercions, valid := valid,
        predicates := predicates, evidenceEmpty := evidenceEmpty, arity := arity, codes := codes,
        actualSource := source, emission := emission, selectedSlot := selectedSlot, nativeType := rfl,
        sequence := sequence, nativeTypes := nativeTypes }
      exact .ordinary (ordinary_transport edited avoids receipt reached expressions)
  | @direct compilerProgram project caller child fuel id callee arguments instantiation reasonAt policy callNode output header receipt certified metadata =>
    have same := Option.some.inj (found.symm.trans receipt.found)
    subst node
    have calleeReached : Reaches source roots (.expression callee) :=
      .expression reached receipt.found (by simp [receipt.form, ExpressionForm.references])
    let transported := direct (expression_lookup edited avoids reached).symm
      (expression_lookup edited avoids calleeReached).symm receipt
    have argumentReached : ∀ child ∈ arguments, Reaches source roots (.expression child) := by
      intro child member
      exact .expression reached receipt.found (by simp [receipt.form, ExpressionForm.references, member])
    have raw : RecursiveNamedCallEvidenceHeads.RawCall transported context evidence after header := {
      selected := ⟨certified.selected.member, certified.selected.plan, certified.selected.specialized,
        certified.selected.signature, certified.selected.slot, certified.selected.occurrenceOrder,
        certified.selected.headerOrder⟩, sourceType := certified.sourceType,
      calleeNode := certified.calleeNode, name := certified.name,
      calleeFound := (expression_lookup edited avoids calleeReached).symm.trans certified.calleeFound,
      calleeForm := certified.calleeForm, calleeRequirements := certified.calleeRequirements,
      calleeCoercions := certified.calleeCoercions, valid := certified.valid,
      dictionary := certified.dictionary,
      sequence := sequence edited avoids
        (fun child code member proof => expressions child code (by simp [receipt.form, ExpressionForm.references, member]) proof)
        certified.sequence argumentReached,
      nativeTypes := certified.nativeTypes }
    exact .authenticated (.direct transported raw {
      found := (expression_lookup edited avoids reached).symm.trans metadata.found,
      owner := metadata.owner.trans edited.metadata.owner,
      coercions := metadata.coercions, projected := metadata.projected })


omit edited avoids in
theorem head_found_with {calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate}
    (callFound : ∀ {children scope id output}, calls children scope id output → ∃ node, source.lookupExpression? id = some node) {id : ExpressionId} {output : Lowered}
    {reasonAt : ExpressionId → Word}
    (head : CompatibleExpressionCalls.Head
      calls
      values source context reasonAt children scope id output) :
    ∃ node, source.lookupExpression? id = some node := by
  cases head with
  | primitive head =>
    cases head with
    | group metadata _ _ _ _ => exact ⟨_, metadata.found⟩
    | pair metadata _ _ _ _ _ _ => exact ⟨_, metadata.found⟩
    | unary metadata _ _ _ _ _ _ => exact ⟨_, metadata.found⟩
    | binary metadata _ _ _ _ _ _ _ _ _ => exact ⟨_, metadata.found⟩
    | conditional metadata _ _ _ _ _ _ _ _ _ _ => exact ⟨_, metadata.found⟩
  | constructor receipt _ _ _ => exact ⟨_, receipt.metadata.found⟩
  | member metadata _ _ _ _ => exact ⟨_, metadata.found⟩
  | index header _ _ _ _ _ => exact ⟨_, header.metadata.found⟩
  | builtin head => cases head with | contracted metadata _ _ _ _ => exact ⟨_, metadata.found⟩
  | tuple receipt _ => exact ⟨_, receipt.metadata.found⟩
  | call head => exact callFound head

omit edited avoids in
theorem call_found {id : ExpressionId} {output : Lowered}
    (head : RecursiveNamedCallEvidenceHeads.Head headers compilation source context evidence children scope id output) :
    ∃ node, source.lookupExpression? id = some node := by
  cases head with
  | ordinary head => cases head with
    | named _ metadata _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact ⟨_, metadata.found⟩
  | direct receipt _ _ => exact ⟨_, receipt.found⟩

omit edited avoids in
theorem canonical_call_found {id : ExpressionId} {output : Lowered}
    (head : Head headers compilation source context evidence children scope id output) :
    ∃ node, source.lookupExpression? id = some node := by
  cases head with
  | ordinary receipt => exact ⟨_, receipt.metadata.found⟩
  | authenticated receipt => exact call_found receipt

include edited avoids in
theorem head_transport_with {calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate}
    {before after : GenericExpressionMeaning.Certificate}
    {reasonAt : ExpressionId → Word} {id : ExpressionId} {node : ExpressionNode} {output : Lowered}
    (callTransport : calls before scope id output → Reaches source roots (.expression id) →
      (∀ child code, NodeId.expression child ∈ node.form.references → before scope child code → after scope child code) →
      Head headers compilation view context evidence after scope id output)
    (found : source.lookupExpression? id = some node)
    (head : CompatibleExpressionCalls.Head
      calls
      values source context reasonAt before scope id output)
    (reached : Reaches source roots (.expression id))
    (expressions : ∀ child code, NodeId.expression child ∈ node.form.references → before scope child code → after scope child code) :
    CompatibleExpressionCalls.Head (Head headers compilation view context evidence)
      values view context reasonAt after scope id output := by
  cases head with
  | primitive head => exact .primitive (composition_transport edited avoids found head reached expressions)
  | constructor receipt form valid children =>
    have same := Option.some.inj (found.symm.trans receipt.metadata.found)
    subst node
    exact .constructor (CallableLambdaViewDataTrees.header edited avoids reached receipt) form valid
      (sequence edited avoids
        (fun child code member proof => expressions child code (by simp [form, ExpressionForm.references, member]) proof)
        children (by intro child member; exact .expression reached receipt.metadata.found (by simp [form, ExpressionForm.references, member])))
  | member metadata baseMetadata form layout certified =>
    have same := Option.some.inj (found.symm.trans metadata.found)
    subst node
    exact .member (CallableLambdaViewExpressionLeaves.metadata edited avoids reached metadata)
      (CallableLambdaViewExpressionLeaves.metadata edited avoids
        (.expression reached metadata.found (by simp [form, ExpressionForm.references])) baseMetadata)
      form layout (expressions _ _ (by simp [form, ExpressionForm.references]) certified)
  | index header keyFound form sourceType first second =>
    have same := Option.some.inj (found.symm.trans header.metadata.found)
    subst node
    exact .index (CallableLambdaViewIndexedTrees.header edited avoids reached
      (.expression reached header.metadata.found (by simp [form, ExpressionForm.references])) header)
      ((expression_lookup edited avoids (.expression reached header.metadata.found (by simp [form, ExpressionForm.references]))).symm.trans keyFound)
      form sourceType (expressions _ _ (by simp [form, ExpressionForm.references]) first)
      (expressions _ _ (by simp [form, ExpressionForm.references]) second)
  | builtin head =>
    cases head with
    | contracted metadata form sourceType children nativeTypes =>
      have same := Option.some.inj (found.symm.trans metadata.found)
      subst node
      exact .builtin (.contracted (CallableLambdaViewExpressionLeaves.metadata edited avoids reached metadata) form sourceType
        (sequence edited avoids
          (fun child code member proof => expressions child code (by simp [form, ExpressionForm.references, member]) proof)
          children (by intro child member; exact .expression reached metadata.found (by simp [form, ExpressionForm.references, member]))) nativeTypes)
  | tuple receipt children =>
    have same := Option.some.inj (found.symm.trans receipt.metadata.found)
    subst node
    exact .tuple {receipt with metadata := CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt.metadata}
      (sequence edited avoids
        (fun child code member proof => expressions child code (by simp [receipt.form, ExpressionForm.references, member]) proof)
        children (by intro child member; exact .expression reached receipt.metadata.found (by simp [receipt.form, ExpressionForm.references, member])))
  | call head => exact .call (callTransport head reached expressions)


/-- The canonical grammar retains original emission receipts and fixes the
same actual caller dictionary at every nested argument occurrence. -/
abbrev Certificates (evidence : Dynamic.EvidenceEnvironment)
    (headers : Inventory prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (fuel : Nat) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) :=
  CompatibleExpressionCalls.Tree.WithLiterals
    (calls := Head headers compilation source context evidence) (fuel := fuel) (values := values)
    (source := source) (context := context) (solved := solved) (reasonAt := reasonAt)
    (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved source id code)

include edited avoids in
theorem transport_with {calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate}
    (callFound : ∀ {children scope id output}, calls children scope id output → ∃ node, source.lookupExpression? id = some node)
    (callTransport : ∀ {before after scope id node output}, source.lookupExpression? id = some node →
      calls before scope id output → Reaches source roots (.expression id) →
      (∀ child code, NodeId.expression child ∈ node.form.references → before scope child code → after scope child code) →
      Head headers compilation view context evidence after scope id output)
    {fuel : Nat} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
    {id : ExpressionId} {output : Lowered}
    (receipt : CompatibleExpressionCalls.Tree.WithLiterals
      (calls := calls) (fuel := fuel) (values := values) (source := source) (context := context)
      (solved := solved) (reasonAt := reasonAt)
      (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved source id code) scope id output)
    (reached : Reaches source roots (.expression id)) :
    Certificates evidence headers compilation fuel view context solved reasonAt scope id output := by
  obtain ⟨tree, sites⟩ := receipt
  revert reached
  induction sites with
  | fragment child sites =>
    intro reached
    have reverse : LocalView view source changed :=
      ⟨edited.metadata.symm, fun id fresh => (edited.unchanged id fresh).symm⟩
    obtain ⟨transported, transportedSites⟩ := CallableLambdaViewMatchRuntimeCertificates.builtin_original
      reverse (avoids.view edited.metadata) ⟨child, sites⟩ (reached.metadata edited.metadata)
    exact ⟨.fragment transported, .fragment transported transportedSites⟩
  | @node id lowered entries head children sites ih =>
    intro reached
    obtain ⟨node, found⟩ := head_found_with callFound head
    -- Extra unused proof entries are excluded from the canonical proof fold;
    -- every actual ordered child vector and its emitted code stays unchanged.
    let selectedEntries := entries.filter (fun entry => decide (NodeId.expression entry.1 ∈ node.form.references))
    have transformed : CompatibleExpressionCalls.Head (Head headers compilation view context evidence)
        values view context reasonAt (CompatibleExpressionCalls.Entries scope selectedEntries) scope id lowered :=
      head_transport_with edited avoids (callTransport found) found head reached (by
        intro child code member certified
        obtain ⟨sameScope, present⟩ := certified
        exact ⟨sameScope, List.mem_filter.mpr ⟨present, by simpa using member⟩⟩)
    have transformedChildren : ∀ child code, (child, code) ∈ selectedEntries →
        Certificates evidence headers compilation fuel view context solved reasonAt scope child code := by
      intro child code member
      have selected := List.mem_filter.mp member
      have reference : NodeId.expression child ∈ node.form.references := of_decide_eq_true selected.2
      exact ih child code selected.1 (.expression reached found reference)
    let trees := fun child code (member : (child, code) ∈ selectedEntries) =>
      (transformedChildren child code member).choose
    exact ⟨.node transformed trees,
      .node transformed trees (fun child code member => (transformedChildren child code member).choose_spec)⟩

include edited avoids in
theorem transport {fuel : Nat} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
    {id : ExpressionId} {output : Lowered}
    (receipt : RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsWith
      (some evidence) headers compilation fuel source context solved reasonAt scope id output)
    (reached : Reaches source roots (.expression id)) :
    Certificates evidence headers compilation fuel view context solved reasonAt scope id output :=
  transport_with edited avoids (fun head => call_found head)
    (fun found head reached children => call_transport edited avoids found head reached children) receipt reached

include edited avoids in
theorem canonical_transport {fuel : Nat} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
    {id : ExpressionId} {output : Lowered}
    (receipt : Certificates evidence headers compilation fuel source context solved reasonAt scope id output)
    (reached : Reaches source roots (.expression id)) :
    Certificates evidence headers compilation fuel view context solved reasonAt scope id output := by
  exact transport_with edited avoids (fun head => canonical_call_found head)
    (fun found head reached children => by
      cases head with
      | ordinary receipt =>
        have same := Option.some.inj (found.symm.trans receipt.metadata.found)
        cases same
        exact .ordinary (ordinary_transport edited avoids receipt reached children)
      | authenticated receipt => exact call_transport edited avoids found receipt reached children) receipt reached

end Transport
end CanonicalCalls

end Solcore.SourceSemantics.CoreLowering.CallableLambdaViewNamedRuntimeCertificates
