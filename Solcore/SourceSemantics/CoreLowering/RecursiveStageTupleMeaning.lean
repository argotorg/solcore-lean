import Solcore.SourceSemantics.CoreLowering.RecursiveStageArguments
import Solcore.SourceSemantics.CoreLowering.RecursiveStagePrimitiveMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionTupleCertificates

/-! A finite staged tuple grammar with concrete primitive leaves. Tuple nodes
retain the actual ordered compiler vector, including repeated occurrences.
The child support is static; the unique structural proof supplies its meanings.
This does not certify the full general expression or callable grammar. -/
set_option autoImplicit false
set_option maxRecDepth 32768
namespace Solcore.SourceSemantics.CoreLowering.RecursiveStageTupleMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload

abbrev FaultRep (faults : FunctionCalls.FaultRep) : RecursiveStageMeaning.FaultRep
  | .semantic reason, token => faults reason token
  | .stage _ _ _, _ => False

def Entries (scope : SourceCoreLocalCell.Scope) (entries : List (ExpressionId × SourceCoreBasic.LoweredExpr)) :
    GenericExpressionMeaning.Certificate := fun current id code => current = scope ∧ (id, code) ∈ entries

inductive Tree (fuel : Nat) (values : SourceCoreCompatibleValues.Context) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement) (reasonAt : ExpressionId → Word)
    (scope : SourceCoreLocalCell.Scope) : ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | primitive {id code}
      (tree : CompatibleExpressionPrimitives.Tree fuel values source context solved reasonAt scope id code) :
      Tree fuel values source context solved reasonAt scope id code
  | tuple {id node ids types codes entries}
      (header : CompatibleExpressionTuples.Header values source id node ids types codes)
      (sequence : DataExpressionSequence.Tree source (Entries scope entries) scope ids types codes)
      (children : ∀ child code, (child, code) ∈ entries → Tree fuel values source context solved reasonAt scope child code) :
      Tree fuel values source context solved reasonAt scope id (SourceCoreCalls.packArguments codes)

variable {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {scope : SourceCoreLocalCell.Scope}

inductive Supported : {id : ExpressionId} → {code : SourceCoreBasic.LoweredExpr} →
    Tree fuel values source context solved reasonAt scope id code → Prop where
  | primitive {id code}
      (tree : CompatibleExpressionPrimitives.Tree fuel values source context solved reasonAt scope id code)
      (sites : RecursiveStagePrimitiveMeaning.Supported tree) : Supported (.primitive tree)
  | tuple {id node ids types codes entries}
      (header : CompatibleExpressionTuples.Header values source id node ids types codes)
      (sequence : DataExpressionSequence.Tree source (Entries scope entries) scope ids types codes)
      (children : ∀ child code, (child, code) ∈ entries → Tree fuel values source context solved reasonAt scope child code)
      (sites : ∀ child code (member : (child, code) ∈ entries), Supported (children child code member)) :
      Supported (.tuple header sequence children)

def Certificate (fuel : Nat) (values : SourceCoreCompatibleValues.Context) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement) (reasonAt : ExpressionId → Word) :
    GenericExpressionMeaning.Certificate := fun scope id code =>
  ∃ tree : Tree fuel values source context solved reasonAt scope id code, Supported tree

inductive PacksOutcome : Staging.Recursive.ValuesOutcome → Staging.Recursive.Outcome → Prop where
  | values {values value} (pack : Dynamic.ValuesPack values value) : PacksOutcome (.values values) (.value value)
  | fault (failure) : PacksOutcome (.fault failure) (.fault failure)

theorem PacksOutcome.functional {sequence : Staging.Recursive.ValuesOutcome} {left right : Staging.Recursive.Outcome}
    (first : PacksOutcome sequence left) (second : PacksOutcome sequence right) : left = right := by
  cases first with
  | values pack => cases second with | values other => exact congrArg _ (pack.functional other)
  | fault => cases second; rfl

private theorem occurrence_form {invocation : Staging.Recursive.Scope} {id : ExpressionId}
    {node : ExpressionNode} {form : ExpressionForm}
    (unique : NodeOccurrencesUnique invocation.source) (found : invocation.source.lookupExpression? id = some node)
    (owned : Staging.Recursive.Occurrence invocation id form) : node.form = form := by
  obtain ⟨other, contains, formed, _, _⟩ := owned
  have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  subst other
  exact formed

/-- Both the new arbitrary-length rules and the retained unit/pair rules expose
one ordered staged list. No source trace is recovered from a native result. -/
theorem source_inv {program : Program} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
    {checked : SourceCoreCompatibleCatalog.Checked} {id : ExpressionId} {node : ExpressionNode} {type : Ty}
    {ids : List ExpressionId} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Staging.Recursive.Outcome}
    (metadata : CompatibleExpressionPrimitives.Metadata checked invocation.source id node type)
    (form : node.form = .tuple ids) (unique : NodeOccurrencesUnique invocation.source)
    (trace : Staging.Recursive.Expression program stages invocation context environment before id outcome after) :
    ∃ sequence, Staging.Recursive.Expressions program stages invocation context environment before ids sequence after ∧
      PacksOutcome sequence outcome := by
  cases trace with
  | atomicValue contains atomic uncoerced raw =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans metadata.found)
    subst node
    rw [form] at atomic raw
    cases atomic
    cases raw with
    | tuple _ children pack =>
      cases children
      cases pack
      exact ⟨_, .nil, .values .nil⟩
  | atomicFault contains atomic uncoerced raw =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans metadata.found)
    subst node
    rw [form] at atomic raw
    cases atomic
    cases raw with | tuple _ children => cases children
  | pair owned first second =>
    have same := ExpressionForm.tuple.inj (form.symm.trans (occurrence_form unique metadata.found owned))
    subst ids
    exact ⟨_, .cons first (.cons second .nil), .values (.cons (.singleton _))⟩
  | pairLeftFault owned child =>
    have same := ExpressionForm.tuple.inj (form.symm.trans (occurrence_form unique metadata.found owned))
    subst ids
    exact ⟨_, .headFault child, .fault _⟩
  | pairRightFault owned first failed =>
    have same := ExpressionForm.tuple.inj (form.symm.trans (occurrence_form unique metadata.found owned))
    subst ids
    exact ⟨_, .tailFault first (.headFault failed), .fault _⟩
  | tupleValue owned children pack =>
    have same := ExpressionForm.tuple.inj (form.symm.trans (occurrence_form unique metadata.found owned))
    subst ids
    exact ⟨_, children, .values pack⟩
  | tupleFault owned children =>
    have same := ExpressionForm.tuple.inj (form.symm.trans (occurrence_form unique metadata.found owned))
    subst ids
    exact ⟨_, children, .fault _⟩
  | group owned child =>
    have impossible := form.symm.trans (occurrence_form unique metadata.found owned)
    cases impossible
  | unary owned child applied =>
    have impossible := form.symm.trans (occurrence_form unique metadata.found owned)
    cases impossible
  | unaryOperandFault owned child =>
    have impossible := form.symm.trans (occurrence_form unique metadata.found owned)
    cases impossible
  | unaryInvalid owned child invalid =>
    have impossible := form.symm.trans (occurrence_form unique metadata.found owned)
    cases impossible
  | binaryLeftFault owned child =>
    have impossible := form.symm.trans (occurrence_form unique metadata.found owned)
    cases impossible
  | binaryLeftInvalid owned child invalid =>
    have impossible := form.symm.trans (occurrence_form unique metadata.found owned)
    cases impossible
  | binaryShortCircuit owned child circuit =>
    have impossible := form.symm.trans (occurrence_form unique metadata.found owned)
    cases impossible
  | binaryRightFault owned first continues child =>
    have impossible := form.symm.trans (occurrence_form unique metadata.found owned)
    cases impossible
  | binary owned first continues second applies =>
    have impossible := form.symm.trans (occurrence_form unique metadata.found owned)
    cases impossible
  | binaryInvalid owned first continues second invalid =>
    have impossible := form.symm.trans (occurrence_form unique metadata.found owned)
    cases impossible
  | conditional owned test branch =>
    have impossible := form.symm.trans (occurrence_form unique metadata.found owned)
    cases impossible
  | conditionalFault owned test =>
    have impossible := form.symm.trans (occurrence_form unique metadata.found owned)
    cases impossible
  | calleeFault owned child =>
    have impossible := form.symm.trans (occurrence_form unique metadata.found owned)
    cases impossible
  | notCallable owned child invalid =>
    have impossible := form.symm.trans (occurrence_form unique metadata.found owned)
    cases impossible
  | rejected owned child rejected =>
    have impossible := form.symm.trans (occurrence_form unique metadata.found owned)
    cases impossible
  | argumentsFault owned child guard children =>
    have impossible := form.symm.trans (occurrence_form unique metadata.found owned)
    cases impossible
  | sourceArity owned child guard children mismatch =>
    have impossible := form.symm.trans (occurrence_form unique metadata.found owned)
    cases impossible
  | applied owned uncoerced child guard children arity applied =>
    have impossible := form.symm.trans (occurrence_form unique metadata.found owned)
    cases impossible

/-- The independent tuple occurrence consumes the very same staged list. -/
theorem source_intro {program : Program} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
    {id : ExpressionId} {ids : List ExpressionId} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {sequence : Staging.Recursive.ValuesOutcome} {outcome : Staging.Recursive.Outcome}
    (owned : Staging.Recursive.Occurrence invocation id (.tuple ids))
    (children : Staging.Recursive.Expressions program stages invocation context environment before ids sequence after)
    (packed : PacksOutcome sequence outcome) :
    Staging.Recursive.Expression program stages invocation context environment before id outcome after := by
  cases packed with
  | values pack => exact .tupleValue owned children pack
  | fault => exact .tupleFault owned children


theorem sequence_result {checked : SourceCoreCompatibleCatalog.Checked}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
    {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    {faults : RecursiveStageMeaning.FaultRep} {sequence : Staging.Recursive.ValuesOutcome} {value : Value}
    (represented : RecursiveStageArguments.ResultFor (CompatibleAmbientHeap.payloadModel checked registry functions)
      mapping world types codes faults sequence value) :
    ∃ outcome, PacksOutcome sequence outcome ∧
      RecursiveStageMeaning.ResultRepresentsFor (CompatibleAmbientHeap.payloadModel checked registry functions)
        mapping world (TypeSystem.Ty.productMany types) (SourceCoreCalls.packArguments codes).type faults outcome value := by
  cases represented with
  | values related =>
    obtain ⟨packed, pack, payload⟩ := CompatibleExpressionTuples.values_pack related
    exact ⟨_, .values pack, .value (by simpa only [CompatibleExpressionConstructorNativeTyping.packed_type,
      CompatibleAmbientHeap.payloadModel] using payload)⟩
  | fault matched => exact ⟨_, .fault _, .fault matched⟩

section TupleStep
variable {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (stages : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  {children : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}

private theorem tuple_reflects
    (meaning : RecursiveStageMeaning.ReflectsFor (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program stages invocation context children faults) :
    RecursiveStageMeaning.ReflectsFor (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program stages invocation context (CompatibleExpressionTuples.Certificate values invocation.source children) faults := by
  intro scope id lowered certified
  obtain ⟨node, ids, types, codes, emitted, header, sequence⟩ := certified
  subst lowered
  intro root found mapping world admin environment canonical actual before store ξ value finalStore
    environments heaps locals agrees evaluated
  have same := Option.some.inj (header.metadata.found.symm.trans found)
  subst root
  obtain ⟨sourceOutcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    RecursiveStageArguments.reflects_for sequence meaning environments heaps locals agrees evaluated
  obtain ⟨outcome, packed, payload⟩ := sequence_result represented
  have owned : Staging.Recursive.Occurrence invocation id (.tuple ids) :=
    ⟨node, lookupExpression?_sound header.metadata.found, header.form, header.metadata.requirements, header.metadata.coercions⟩
  exact ⟨outcome, after, finalMap, finalWorld, source_intro owned sourceTrace packed,
    by simpa only [header.sourceType] using payload, finalHeaps, maps, worlds, frame, metadata⟩

private theorem tuple_preserves (unique : NodeOccurrencesUnique invocation.source)
    (meaning : RecursiveStageMeaning.PreservesFor (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program stages invocation context children faults) :
    RecursiveStageMeaning.PreservesFor (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program stages invocation context (CompatibleExpressionTuples.Certificate values invocation.source children) faults := by
  intro scope id lowered certified
  obtain ⟨node, ids, types, codes, emitted, header, sequence⟩ := certified
  subst lowered
  intro root found mapping world admin environment canonical actual before store ξ outcome after
    environments heaps locals agrees trace
  have same := Option.some.inj (header.metadata.found.symm.trans found)
  subst root
  obtain ⟨sourceOutcome, sourceTrace, sourcePacked⟩ := source_inv header.metadata header.form unique trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    RecursiveStageArguments.preserves_for sequence meaning environments heaps locals agrees sourceTrace
  obtain ⟨result, packed, payload⟩ := sequence_result represented
  have same := sourcePacked.functional packed
  subst result
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated,
    by simpa only [header.sourceType] using payload, finalHeaps, maps, worlds, frame, metadata⟩
end TupleStep

section Meaning
variable {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (stages : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (sameSource : invocation.source = source) (sameLedger : context.solvedRequirements = solved)
  (runtime : RuntimeRequirementLedgerValid context) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))

include sameSource sameLedger runtime uninitialized in
/-- Each original native child is reflected by the same finite supported tree.
No preceding source trace or preservation theorem enters this direction. -/
theorem reflects :
    RecursiveStageMeaning.ReflectsFor (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program stages invocation context (Certificate fuel values source context solved reasonAt) (FaultRep faults) := by
  cases sameSource
  intro scope id code certified
  obtain ⟨tree, supported⟩ := certified
  induction supported with
  | primitive tree sites =>
    intro node found mapping world admin environment canonical actual before store ξ value finalStore
      environments heaps locals agrees evaluated
    obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
      RecursiveStagePrimitiveMeaning.reflects functions program stages invocation rfl uninitialized sameLedger runtime
        sites found environments heaps locals agrees evaluated
    refine ⟨outcome, after, finalMap, finalWorld, trace, ?_, finalHeaps, maps, worlds, frame, metadata⟩
    cases represented with
    | value payload => exact .value payload
    | fault matched => exact .fault matched
  | tuple header sequence children sites ih =>
    intro node found mapping world admin environment canonical actual before store ξ value finalStore
      environments heaps locals agrees evaluated
    refine tuple_reflects functions program stages invocation ?_ ⟨_, _, _, _, rfl, header, sequence⟩
      found environments heaps locals agrees evaluated
    intro current child childCode certified
    obtain ⟨rfl, member⟩ := certified
    exact ih child childCode member

include sameSource sameLedger runtime uninitialized in
/-- Preservation uses the sole ordered pack proof at each tuple node. The
primitive theorem discharges its own stage-fault impossibility. -/
theorem preserves (unique : NodeOccurrencesUnique source)
    (extension : SourceCoreRawMetadata.Extends values.registry registry) :
    RecursiveStageMeaning.PreservesFor (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program stages invocation context (Certificate fuel values source context solved reasonAt) (FaultRep faults) := by
  cases sameSource
  intro scope id code certified
  obtain ⟨tree, supported⟩ := certified
  induction supported with
  | primitive tree sites =>
    intro node found mapping world admin environment canonical actual before store ξ outcome after
      environments heaps locals agrees trace
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
      RecursiveStagePrimitiveMeaning.preserves functions program stages invocation rfl unique uninitialized
        extension sameLedger runtime sites found environments heaps locals agrees trace
    refine ⟨value, finalStore, finalMap, finalWorld, evaluated, ?_, finalHeaps, maps, worlds, frame, metadata⟩
    cases represented with
    | value payload => exact .value payload
    | fault matched => exact .fault matched
  | tuple header sequence children sites ih =>
    intro node found mapping world admin environment canonical actual before store ξ outcome after
      environments heaps locals agrees trace
    refine tuple_preserves functions program stages invocation unique ?_ ⟨_, _, _, _, rfl, header, sequence⟩
      found environments heaps locals agrees trace
    intro current child childCode certified
    obtain ⟨rfl, member⟩ := certified
    exact ih child childCode member
end Meaning


section Extraction
/-- A real literal receipt keeps the complete selected numeric row. -/
theorem literal {id : ExpressionId} {code : SourceCoreBasic.LoweredExpr}
    (receipt : CompatibleExpressionLiteralRuntime.Certificate solved source id code) :
    Certificate fuel values source context solved reasonAt scope id code :=
  ⟨.primitive (.product (.literal receipt.forget)), .primitive _
    (.product _ (.literal receipt.forget (RecursiveStagePrimitiveMeaning.literal_of_certificate receipt)))⟩

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- This fold transports only actual child receipts and raw source types. -/
private theorem child_certificates
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {budget : Nat}
    {compilation : SourceCoreFunctions.Context} {ids : List ExpressionId} {types : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr} {certificate : ExpressionId → SourceCoreBasic.LoweredExpr → Prop}
    (unique : NodeOccurrencesUnique source) (typed : ExpressionsHaveTypes source context ids types)
    (generated : ids.mapM (fun id => SourceCoreFunctions.lowerExpressionWithPolicy policy body budget compilation source scope id reasonAt) = .ok codes)
    (extract : ∀ id, id ∈ ids → ∀ node code, source.lookupExpression? id = some node →
      ExpressionHasType source context id node.type →
      SourceCoreFunctions.lowerExpressionWithPolicy policy body budget compilation source scope id reasonAt = .ok code →
      certificate id code) :
    ids.length = types.length ∧ CompatibleExpressionConstructors.Nodes source ids types codes ∧
      ∀ id code, (id, code) ∈ ids.zip codes → certificate id code := by
  induction ids generalizing types codes with
  | nil =>
    cases typed
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at generated
    subst codes
    exact ⟨rfl, .nil, by simp⟩
  | cons id ids ih =>
    cases typed with
    | @cons _ _ _ type types head tail =>
      rw [List.mapM_cons] at generated
      obtain ⟨code, first, generated⟩ := bind_ok generated
      obtain ⟨restCodes, rest, generated⟩ := bind_ok generated
      cases generated
      obtain ⟨node, contains, sourceType⟩ := head.stored_type
      have found := lookupExpression?_complete unique contains
      have child := extract id (by simp) node code found (sourceType ▸ head) first
      obtain ⟨count, nodes, children⟩ := ih tail rest (fun id member => extract id (by simp [member]))
      refine ⟨congrArg Nat.succ count, .cons ⟨node, found, sourceType⟩ nodes, ?_⟩
      intro other otherCode member
      rcases List.mem_cons.mp member with same | remaining
      · cases same; exact child
      · exact children other otherCode remaining

/-- The production tuple branch returns its exact mapM child vector. The caller
must discharge each reached child's static certificate from that child's actual
acceptance; this theorem does not automate the full general expression grammar. -/
theorem of_functions {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {budget : Nat} {compilation : SourceCoreFunctions.Context} {id : ExpressionId} {node : ExpressionNode}
    {ids : List ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .tuple ids) (typed : ExpressionHasType source context id node.type)
    (special : ∀ child remaining, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation child remaining source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (leaf : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (budget + 1) compilation source scope id reasonAt = .ok lowered)
    (extract : ∀ child, child ∈ ids → ∀ childNode code, source.lookupExpression? child = some childNode →
      ExpressionHasType source context child childNode.type →
      SourceCoreFunctions.lowerExpressionWithPolicy policy body budget compilation source scope child reasonAt = .ok code →
      Certificate fuel values source context compilation.solvedRequirements reasonAt scope child code) :
    Certificate fuel values source context compilation.solvedRequirements reasonAt scope id lowered := by
  classical
  obtain ⟨codes, acceptedChildren, rfl, metadata⟩ := CompatibleExpressionTuples.of_functions
    found form special readPolicy leaf accepted
  obtain ⟨types, typedChildren, sourceType⟩ := CompatibleExpressionTuples.source_types unique found form metadata.coercions typed
  obtain ⟨count, nodes, children⟩ := child_certificates unique typedChildren acceptedChildren extract
  have sequence := CompatibleExpressionConstructors.sequence_of_nodes
    (certificate := Entries scope (ids.zip codes)) count nodes (fun child code member => ⟨rfl, member⟩)
  let trees := fun child code member => (children child code member).choose
  have sites := fun child code member => (children child code member).choose_spec
  let header : CompatibleExpressionTuples.Header values source id node ids types codes :=
    ⟨metadata, form, sourceType⟩
  exact ⟨.tuple header sequence trees, .tuple header sequence trees sites⟩
end Extraction

end Solcore.SourceSemantics.CoreLowering.RecursiveStageTupleMeaning
