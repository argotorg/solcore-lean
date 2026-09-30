import Solcore.Frontend.SourceCoreControl
import Solcore.SourceSemantics.CoreLowering.BasicExpressionCertificates

/-! Conditional expressions preserve their actual evaluated read occurrence.
The provider supplies a reason word per occurrence, and fault provenance follows
left-to-right tuple evaluation and the selected conditional branch. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.ControlExpressions

open Frontend Frontend.SourceInference TypeSystem LocalCell

abbrev Metadata := BasicExpressions.Metadata

inductive Tree (source : TypedSource) (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Core.Word) :
    ExpressionId → Core.Ty → Core.Expr → Nat → Prop where
  | unit {id : ExpressionId} {node : ExpressionNode}
      (metadata : Metadata source id node .unit) (form : node.form = .tuple []) :
      Tree source scope reasonAt id .unit (Core.LanguageResult.success .unit) 1
  | bool {id : ExpressionId} {node : ExpressionNode} {name : String} (value : Bool)
      (metadata : Metadata source id node .bool)
      (form : node.form = .reference name (.builtinBoolean value)) :
      Tree source scope reasonAt id .bool (Core.LanguageResult.success (.bool value)) 1
  | word {id : ExpressionId} {node : ExpressionNode} {literal : Syntax.CoreLiteralValue}
      (value : Core.Word) (metadata : Metadata source id node .word)
      (form : node.form = .literal literal)
      (meaning : WordLiteralDenotes ⟨node.span, literal⟩ value) :
      Tree source scope reasonAt id .word (Core.LanguageResult.success (.word value)) 1
  | localRead {id : ExpressionId} {node : ExpressionNode} {type : Core.Ty}
      {binder : Resolved.LocalId} {name : String} {index : Nat}
      (metadata : Metadata source id node type)
      (form : node.form = .reference name (.local binder))
      (owned : binder.owner = source.owner)
      (slot : SourceCoreLocalCell.lookup? scope binder = some (index, type)) :
      Tree source scope reasonAt id type (Core.OptionalCell.read type (.var index) (reasonAt id)) 1
  | group {id inner : ExpressionId} {node : ExpressionNode} {type : Core.Ty}
      {expression : Core.Expr} {depth : Nat}
      (metadata : Metadata source id node type) (form : node.form = .group inner)
      (child : Tree source scope reasonAt inner type expression depth) :
      Tree source scope reasonAt id type expression (depth + 1)
  | pair {id left right : ExpressionId} {node : ExpressionNode}
      {leftType rightType : Core.Ty} {leftCode rightCode : Core.Expr} {leftDepth rightDepth : Nat}
      (metadata : Metadata source id node (.product leftType rightType))
      (form : node.form = .tuple [left, right])
      (leftTree : Tree source scope reasonAt left leftType leftCode leftDepth)
      (rightTree : Tree source scope reasonAt right rightType rightCode rightDepth) :
      Tree source scope reasonAt id (.product leftType rightType)
        (Core.LocalSequence.pair leftType rightType leftCode rightCode)
        (max leftDepth rightDepth + 1)

  | conditional {id condition thenId elseId : ExpressionId} {node : ExpressionNode}
      {type : Core.Ty} {conditionCode thenCode elseCode : Core.Expr}
      {conditionDepth thenDepth elseDepth : Nat}
      (metadata : Metadata source id node type)
      (form : node.form = .conditional condition thenId elseId)
      (conditionTree : Tree source scope reasonAt condition .bool conditionCode conditionDepth)
      (thenTree : Tree source scope reasonAt thenId type thenCode thenDepth)
      (elseTree : Tree source scope reasonAt elseId type elseCode elseDepth) :
      Tree source scope reasonAt id type (Core.LocalControl.choose type conditionCode thenCode elseCode)
        (max conditionDepth (max thenDepth elseDepth) + 1)

theorem Tree.wellFormed {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {type : Core.Ty} {expression : Core.Expr} {depth : Nat}
    (tree : Tree source scope reasonAt id type expression depth) : Core.Ty.WellFormed [] type := by
  cases tree with
  | unit metadata _ | bool _ metadata _ | word _ metadata _ _ | localRead metadata _ _ _
  | group metadata _ _ | pair metadata _ _ _ | conditional metadata _ _ _ _ => exact metadata.types.wellFormed []

theorem Tree.cellPayload {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {type : Core.Ty} {expression : Core.Expr} {depth : Nat}
    (tree : Tree source scope reasonAt id type expression depth) : Core.CellPayload type := by
  cases tree with
  | unit metadata _ | bool _ metadata _ | word _ metadata _ _ | localRead metadata _ _ _
  | group metadata _ _ | pair metadata _ _ _ | conditional metadata _ _ _ _ => exact metadata.types.cellPayload

theorem Tree.hasType {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {type : Core.Ty} {expression : Core.Expr} {depth : Nat}
    (tree : Tree source scope reasonAt id type expression depth) :
    Core.HasType (SourceCoreLocalCell.coreContext scope) expression
      (Core.LanguageResult.resultType type) := by
  induction tree with
  | unit => exact Core.LanguageResult.success_hasType .unit
  | bool => exact Core.LanguageResult.success_hasType .bool
  | word => exact Core.LanguageResult.success_hasType .word
  | localRead metadata _ _ slot =>
      exact Core.OptionalCell.read_hasType _ (metadata.types.wellFormed [])
        (.var (SourceCoreLocalCell.lookup?_context slot))
  | group _ _ _ child => exact child
  | pair _ _ leftTree rightTree left right =>
      exact Core.LocalSequence.pair_hasType leftTree.wellFormed rightTree.wellFormed left right

  | conditional metadata _ _ _ _ condition thenBranch elseBranch =>
      exact Core.LocalControl.choose_hasType (metadata.types.wellFormed []) condition thenBranch elseBranch

/-- Occurrence provenance follows the evaluated source path. In particular,
right tuple elements require a successful left prefix, and conditional branches
require the matching Boolean condition. -/
inductive UninitializedAt (program : Program) (context : Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (environment : Dynamic.Environment) (heap : Dynamic.Heap) :
    ExpressionId → ExpressionId → Dynamic.Location → Prop where
  | localRead {id : ExpressionId} {scope : SourceCoreLocalCell.Scope} {type : Core.Ty}
      {location : Dynamic.Location} {cell : Dynamic.Cell}
      (site : ReadSite source scope id type)
      (lookup : Dynamic.Environment.LooksUp environment site.binder location)
      (read : Dynamic.Heap.Reads heap location cell)
      (cellType : cell.type = site.node.type) (ordinary : cell.generalized = none)
      (empty : cell.value = none) : UninitializedAt program context evidence source environment heap id id location
  | group {id inner site : ExpressionId} {location : Dynamic.Location} {node : ExpressionNode} {type : Core.Ty}
      (metadata : Metadata source id node type) (form : node.form = .group inner)
      (child : UninitializedAt program context evidence source environment heap inner site location) :
      UninitializedAt program context evidence source environment heap id site location
  | pairLeft {id left right site : ExpressionId} {location : Dynamic.Location}
      {node : ExpressionNode} {type : Core.Ty}
      (metadata : Metadata source id node type) (form : node.form = .tuple [left, right])
      (child : UninitializedAt program context evidence source environment heap left site location) :
      UninitializedAt program context evidence source environment heap id site location
  | pairRight {id left right site : ExpressionId} {location : Dynamic.Location}
      {node : ExpressionNode} {type : Core.Ty} {leftValue : Dynamic.Value}
      (metadata : Metadata source id node type) (form : node.form = .tuple [left, right])
      (evaluatedPrefix : Dynamic.ExpressionEvaluates program context evidence source environment heap left leftValue heap)
      (child : UninitializedAt program context evidence source environment heap right site location) :
      UninitializedAt program context evidence source environment heap id site location
  | condition {id condition thenId elseId site : ExpressionId} {location : Dynamic.Location}
      {node : ExpressionNode} {type : Core.Ty}
      (metadata : Metadata source id node type) (form : node.form = .conditional condition thenId elseId)
      (child : UninitializedAt program context evidence source environment heap condition site location) :
      UninitializedAt program context evidence source environment heap id site location
  | thenBranch {id condition thenId elseId site : ExpressionId} {location : Dynamic.Location}
      {node : ExpressionNode} {type : Core.Ty}
      (metadata : Metadata source id node type) (form : node.form = .conditional condition thenId elseId)
      (evaluatedPrefix : Dynamic.ExpressionEvaluates program context evidence source environment heap condition (.bool true) heap)
      (child : UninitializedAt program context evidence source environment heap thenId site location) :
      UninitializedAt program context evidence source environment heap id site location
  | elseBranch {id condition thenId elseId site : ExpressionId} {location : Dynamic.Location}
      {node : ExpressionNode} {type : Core.Ty}
      (metadata : Metadata source id node type) (form : node.form = .conditional condition thenId elseId)
      (evaluatedPrefix : Dynamic.ExpressionEvaluates program context evidence source environment heap condition (.bool false) heap)
      (child : UninitializedAt program context evidence source environment heap elseId site location) :
      UninitializedAt program context evidence source environment heap id site location

theorem UninitializedAt.faults
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {root site : ExpressionId} {location : Dynamic.Location}
    (provenance : UninitializedAt program context evidence source environment heap root site location) :
    Dynamic.ExpressionFaults program context evidence source environment heap root
      (.uninitializedLocation location) heap := by
  induction provenance with
  | localRead site lookup read cellType ordinary empty =>
      apply Dynamic.ExpressionFaults.form site.contains
      rw [site.form, site.requirements, site.coercions]
      exact .localUninitialized (owned := []) rfl lookup read ordinary empty
        (cellType ▸ site.types.not_mapping)
  | group metadata form _ ih =>
      apply Dynamic.ExpressionFaults.form metadata.contains
      rw [form, metadata.requirements, metadata.coercions]
      exact .group rfl ih
  | pairLeft metadata form _ ih =>
      apply Dynamic.ExpressionFaults.form metadata.contains
      rw [form, metadata.requirements, metadata.coercions]
      exact .tuple rfl (.head ih)
  | pairRight metadata form evaluatedPrefix _ ih =>
      apply Dynamic.ExpressionFaults.form metadata.contains
      rw [form, metadata.requirements, metadata.coercions]
      exact .tuple rfl (.tail evaluatedPrefix (.head ih))
  | condition metadata form _ ih =>
      apply Dynamic.ExpressionFaults.form metadata.contains
      rw [form, metadata.requirements, metadata.coercions]
      exact .conditionalCondition rfl ih
  | thenBranch metadata form evaluatedPrefix _ ih =>
      apply Dynamic.ExpressionFaults.form metadata.contains
      rw [form, metadata.requirements, metadata.coercions]
      exact .conditionalTrueBranch rfl evaluatedPrefix ih
  | elseBranch metadata form evaluatedPrefix _ ih =>
      apply Dynamic.ExpressionFaults.form metadata.contains
      rw [form, metadata.requirements, metadata.coercions]
      exact .conditionalFalseBranch rfl evaluatedPrefix ih

/-- The propagated occurrence names an actual absent ordinary local cell.
No injectivity assumption is imposed on the caller's reason provider. -/
theorem UninitializedAt.read_site
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {root site : ExpressionId} {location : Dynamic.Location}
    (provenance : UninitializedAt program context evidence source environment heap root site location) :
    ∃ (scope : SourceCoreLocalCell.Scope) (type : Core.Ty)
      (readSite : ReadSite source scope site type) (cell : Dynamic.Cell),
      Dynamic.Environment.LooksUp environment readSite.binder location ∧
      Dynamic.Heap.Reads heap location cell ∧ cell.type = readSite.node.type ∧
      cell.generalized = none ∧ cell.value = none := by
  induction provenance with
  | localRead site lookup read cellType ordinary empty =>
      exact ⟨_, _, site, _, lookup, read, cellType, ordinary, empty⟩
  | group _ _ _ ih | pairLeft _ _ _ ih | pairRight _ _ _ _ ih
  | condition _ _ _ ih | thenBranch _ _ _ _ ih | elseBranch _ _ _ _ ih => exact ih

inductive OutcomeRepresents (program : Program) (context : Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (environment : Dynamic.Environment) (heap : Dynamic.Heap)
    (reasonAt : ExpressionId → Core.Word) (root : ExpressionId) (type : Core.Ty) :
    Dynamic.ExpressionOutcome → Core.Value → Prop where
  | value (value : SourceStagedValue.Value) (typed : SourceStagedValue.coreType value = type) :
      OutcomeRepresents program context evidence source environment heap reasonAt root type
        (.value (StagedValue.toSource value)) (.inRight .word (SourceStagedValue.toCore value))
  | uninitialized (site : ExpressionId) (location : Dynamic.Location)
      (provenance : UninitializedAt program context evidence source environment heap root site location) :
      OutcomeRepresents program context evidence source environment heap reasonAt root type
        (.fault (.uninitializedLocation location)) (.inLeft type (.word (reasonAt site)))


private theorem OutcomeRepresents.mapRoot
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {reasonAt : ExpressionId → Core.Word} {root parent : ExpressionId} {type : Core.Ty}
    {sourceOutcome : Dynamic.ExpressionOutcome} {coreValue : Core.Value}
    (related : OutcomeRepresents program context evidence source environment heap reasonAt root type sourceOutcome coreValue)
    (lift : ∀ site location, UninitializedAt program context evidence source environment heap root site location →
      UninitializedAt program context evidence source environment heap parent site location) :
    OutcomeRepresents program context evidence source environment heap reasonAt parent type sourceOutcome coreValue := by
  cases related with
  | value staged typed => exact .value staged typed
  | uninitialized site location provenance => exact .uninitialized site location (lift site location provenance)

private theorem word_constructs {span : Syntax.SourceSpan}
    {literal : Syntax.CoreLiteralValue} {value : Core.Word}
    (meaning : WordLiteralDenotes ⟨span, literal⟩ value) :
    Dynamic.LiteralConstructs literal (.word value) := by
  have modulo : Core.Word.ofNatModulo value.val = value := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt value.isLt
  rw [← modulo]
  exact .word meaning

/-- The certificate supplies both independent source and Core derivations.
Neither heap changes, including when a child read fails. -/
theorem Tree.preserves {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {type : Core.Ty} {expression : Core.Expr} {depth : Nat}
    (tree : Tree source scope reasonAt id type expression depth)
    (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    (environments : EnvRepresents world scope environment coreEnvironment)
    (heaps : HeapRepresents heap.cells store world) :
    ∃ sourceOutcome coreValue,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id
        sourceOutcome heap ∧
      OutcomeRepresents program context evidence source environment heap reasonAt id type sourceOutcome coreValue ∧
      Core.Evaluates coreEnvironment store expression coreValue store := by
  induction tree with
  | unit metadata form =>
      refine ⟨.value .unit, .inRight .word .unit, .value ?_, .value .unit rfl, .inRight .unit⟩
      apply Dynamic.ExpressionEvaluates.intro metadata.contains
      · rw [form, metadata.requirements, metadata.coercions]
        exact .tuple rfl .nil .nil
      · rw [metadata.coercions]; exact .nil
  | bool value metadata form =>
      refine ⟨.value (.bool value), .inRight .word (.bool value), .value ?_,
        .value (.bool value) rfl, .inRight .bool⟩
      apply Dynamic.ExpressionEvaluates.intro metadata.contains
      · rw [form, metadata.requirements, metadata.coercions]; exact .builtinBoolean rfl
      · rw [metadata.coercions]; exact .nil
  | word value metadata form meaning =>
      refine ⟨.value (.word value), .inRight .word (.word value), .value ?_,
        .value (.word value) rfl, .inRight .word⟩
      apply Dynamic.ExpressionEvaluates.intro metadata.contains
      · rw [form, metadata.requirements, metadata.coercions]
        exact .literal rfl (word_constructs meaning)
      · rw [metadata.coercions]; exact .nil
  | @localRead id node type binder name index metadata form owned slot =>
      obtain ⟨location, cell, stored, lookup, coreLookup, _, read, coreRead, related⟩ :=
        environments.lookup_heap heaps slot
      have cellType := related.types.source_unique metadata.types
      let site : ReadSite source scope id type := {
        node, binder, name, index, contains := metadata.contains, form, owner := owned
        requirements := metadata.requirements, coercions := metadata.coercions
        slot, types := metadata.types
      }
      cases related with
      | uninitialized types =>
          obtain ⟨fault, evaluated⟩ := site.uninitialized program context evidence environment heap
            coreEnvironment store location _ lookup read cellType rfl rfl coreLookup coreRead (reasonAt id)
          exact ⟨_, _, .fault fault, .uninitialized id location (.localRead site lookup read cellType rfl rfl), evaluated⟩
      | initialized value =>
          obtain ⟨evaluated, coreEvaluated⟩ := site.initialized program context evidence environment heap
            coreEnvironment store location _ value lookup read rfl rfl coreLookup coreRead (reasonAt id)
          exact ⟨_, _, .value evaluated, .value value rfl, coreEvaluated⟩
  | group metadata form child inductionHypothesis =>
      obtain ⟨outcome, coreValue, evaluated, related, coreEvaluated⟩ := inductionHypothesis
      refine ⟨outcome, coreValue, ?_, related.mapRoot (fun _ _ trace => .group metadata form trace), coreEvaluated⟩
      cases evaluated with
      | value evaluated =>
          apply Dynamic.ExpressionEvaluatesOutcome.value
          apply Dynamic.ExpressionEvaluates.intro metadata.contains
          · rw [form, metadata.requirements, metadata.coercions]; exact .group rfl evaluated
          · rw [metadata.coercions]; exact .nil
      | fault fault =>
          apply Dynamic.ExpressionEvaluatesOutcome.fault
          apply Dynamic.ExpressionFaults.form metadata.contains
          rw [form, metadata.requirements, metadata.coercions]
          exact .group rfl fault
  | @pair id left right node leftType rightType leftCode rightCode leftDepth rightDepth
      metadata form leftTree rightTree leftInduction rightInduction =>
      obtain ⟨leftOutcome, leftValue, leftSource, leftRelated, leftCore⟩ := leftInduction
      cases leftRelated with
      | uninitialized faultSite location provenance =>
          cases leftSource with
          | fault fault =>
              refine ⟨_, _, .fault ?_, .uninitialized faultSite location (.pairLeft metadata form provenance),
                Core.LocalSequence.pair_left_failure leftType rightType leftCore⟩
              apply Dynamic.ExpressionFaults.form metadata.contains
              rw [form, metadata.requirements, metadata.coercions]
              exact .tuple rfl (.head fault)
      | value leftValue leftTypeEq =>
          cases leftSource with
          | value leftSource =>
              obtain ⟨rightOutcome, rightValue, rightSource, rightRelated, rightCore⟩ := rightInduction
              have weakened := rightCore.weakenAt_zero_cellPayload rightTree.hasType
                (.sum .word rightTree.cellPayload) (environments.runtime_hasTypes [])
                (heaps.runtime_hasTypes []) heaps.firstOrder_hasTypes
                (SourceStagedValue.toCore leftValue)
              cases rightRelated with
              | uninitialized faultSite location provenance =>
                  cases rightSource with
                  | fault fault =>
                      refine ⟨_, _, .fault ?_, .uninitialized faultSite location (.pairRight metadata form leftSource provenance),
                        Core.LocalSequence.pair_right_failure leftType rightType leftCore weakened⟩
                      apply Dynamic.ExpressionFaults.form metadata.contains
                      rw [form, metadata.requirements, metadata.coercions]
                      exact .tuple rfl (.tail leftSource (.head fault))
              | value rightValue rightTypeEq =>
                  cases rightSource with
                  | value rightSource =>
                      refine ⟨.value (StagedValue.toSource (.product leftValue rightValue)),
                        .inRight .word (SourceStagedValue.toCore (.product leftValue rightValue)),
                        .value ?_, .value (.product leftValue rightValue) ?_,
                        Core.LocalSequence.pair_success leftType rightType leftCore weakened⟩
                      · apply Dynamic.ExpressionEvaluates.intro metadata.contains
                        · rw [form, metadata.requirements, metadata.coercions]
                          exact .tuple rfl (.cons leftSource (.cons rightSource .nil))
                            (.cons (.singleton _))
                        · rw [metadata.coercions]; exact .nil
                      · simp [SourceStagedValue.coreType, leftTypeEq, rightTypeEq]
  | @conditional id condition thenId elseId node type conditionCode thenCode elseCode
      conditionDepth thenDepth elseDepth metadata form conditionTree thenTree elseTree
      conditionIH thenIH elseIH =>
      obtain ⟨conditionOutcome, conditionValue, conditionSource, conditionRelated, conditionCore⟩ := conditionIH
      cases conditionRelated with
      | uninitialized site location provenance =>
          have propagated := UninitializedAt.condition metadata form provenance
          exact ⟨_, _, .fault propagated.faults, .uninitialized site location propagated,
            Core.LocalControl.choose_failure type conditionCore⟩
      | value staged typed =>
          have boolean : ∃ value, staged = .bool value := by
            cases staged <;> simp_all [SourceStagedValue.coreType]
          obtain ⟨boolean, rfl⟩ := boolean
          cases conditionSource with
          | value conditionSource =>
              cases boolean with
              | true =>
                  obtain ⟨outcome, coreValue, branchSource, branchRelated, branchCore⟩ := thenIH
                  have shifted := branchCore.weakenAt_zero_cellPayload thenTree.hasType
                    (.sum .word thenTree.cellPayload) (environments.runtime_hasTypes [])
                    (heaps.runtime_hasTypes []) heaps.firstOrder_hasTypes (.bool true)
                  refine ⟨outcome, coreValue, ?_,
                    branchRelated.mapRoot (fun _ _ trace => .thenBranch metadata form conditionSource trace),
                    Core.LocalControl.choose_true type conditionCore shifted⟩
                  cases branchSource with
                  | value evaluated =>
                      apply Dynamic.ExpressionEvaluatesOutcome.value
                      apply Dynamic.ExpressionEvaluates.intro metadata.contains
                      · rw [form, metadata.requirements, metadata.coercions]
                        exact .conditionalTrue rfl conditionSource evaluated
                      · rw [metadata.coercions]; exact .nil
                  | fault fault =>
                      apply Dynamic.ExpressionEvaluatesOutcome.fault
                      apply Dynamic.ExpressionFaults.form metadata.contains
                      rw [form, metadata.requirements, metadata.coercions]
                      exact .conditionalTrueBranch rfl conditionSource fault
              | false =>
                  obtain ⟨outcome, coreValue, branchSource, branchRelated, branchCore⟩ := elseIH
                  have shifted := branchCore.weakenAt_zero_cellPayload elseTree.hasType
                    (.sum .word elseTree.cellPayload) (environments.runtime_hasTypes [])
                    (heaps.runtime_hasTypes []) heaps.firstOrder_hasTypes (.bool false)
                  refine ⟨outcome, coreValue, ?_,
                    branchRelated.mapRoot (fun _ _ trace => .elseBranch metadata form conditionSource trace),
                    Core.LocalControl.choose_false type conditionCore shifted⟩
                  cases branchSource with
                  | value evaluated =>
                      apply Dynamic.ExpressionEvaluatesOutcome.value
                      apply Dynamic.ExpressionEvaluates.intro metadata.contains
                      · rw [form, metadata.requirements, metadata.coercions]
                        exact .conditionalFalse rfl conditionSource evaluated
                      · rw [metadata.coercions]; exact .nil
                  | fault fault =>
                      apply Dynamic.ExpressionEvaluatesOutcome.fault
                      apply Dynamic.ExpressionFaults.form metadata.contains
                      rw [form, metadata.requirements, metadata.coercions]
                      exact .conditionalFalseBranch rfl conditionSource fault


private theorem bind_ok {α β : Type} {computation : Except SourceCoreBasic.Error α}
    {next : α → Except SourceCoreBasic.Error β} {result : β}
    (accepted : computation >>= next = .ok result) :
    ∃ value, computation = .ok value ∧ next value = .ok result := by
  cases computation with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem ensureType_ok {site : SourceCoreElaboration.ErrorSite} {expected actual : Core.Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

private theorem fromBasicLeaf
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Core.Word}
    {id : ExpressionId} {node : ExpressionNode} {type : Core.Ty} {code : Core.Expr} {depth : Nat}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? id = some node)
    (notGroup : ∀ inner, node.form ≠ .group inner)
    (notPair : ∀ left right, node.form ≠ .tuple [left, right])
    (tree : BasicExpressions.Tree source scope (reasonAt id) id type code depth) :
    Tree source scope reasonAt id type code depth := by
  cases tree with
  | unit metadata form => exact .unit metadata form
  | bool value metadata form => exact .bool value metadata form
  | word value metadata form meaning => exact .word value metadata form meaning
  | localRead metadata form owned slot => exact .localRead metadata form owned slot
  | group metadata form child =>
      have same := Option.some.inj (found.symm.trans (lookupExpression?_complete unique metadata.contains))
      cases same
      exact False.elim (notGroup _ form)
  | pair metadata form left right =>
      have same := Option.some.inj (found.symm.trans (lookupExpression?_complete unique metadata.contains))
      cases same
      exact False.elim (notPair _ _ form)

private theorem tree_of_basicLeaf
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {node : ExpressionNode}
    {lowered : SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (notGroup : ∀ inner, node.form ≠ .group inner)
    (notPair : ∀ left right, node.form ≠ .tuple [left, right])
    (accepted : SourceCoreBasic.lowerExpression fuel source scope id (reasonAt id) = .ok lowered) :
    ∃ depth, depth ≤ fuel ∧ Tree source scope reasonAt id lowered.type lowered.expression depth := by
  obtain ⟨depth, bound, tree⟩ := BasicExpressions.tree_of_lowerExpression accepted
  exact ⟨depth, bound, fromBasicLeaf unique found notGroup notPair tree⟩

/-- Extraction checks the executable conditional compiler, including its
fallback leaf checks. Uniqueness identifies the same occurrence across the
control and basic metadata lookups. No semantic premise is required. -/
theorem tree_of_lowerExpression
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreControl.lowerExpressionWithReasons fuel source scope id reasonAt = .ok lowered) :
    ∃ depth, depth ≤ fuel ∧ Tree source scope reasonAt id lowered.type lowered.expression depth := by
  induction fuel generalizing id lowered with
  | zero => cases accepted
  | succ fuel ih =>
      simp only [SourceCoreControl.lowerExpressionWithReasons] at accepted
      obtain ⟨⟨node, type⟩, read, accepted⟩ := bind_ok accepted
      obtain ⟨found, metadata⟩ := BasicExpressions.readExpression_certificate read
      cases form : node.form with
      | conditional condition thenId elseId =>
          simp only [form] at accepted
          obtain ⟨condition, conditionAccepted, accepted⟩ := bind_ok accepted
          obtain ⟨checkedUnit, conditionChecked, accepted⟩ := bind_ok accepted
          cases checkedUnit
          obtain ⟨thenBranch, thenAccepted, accepted⟩ := bind_ok accepted
          obtain ⟨elseBranch, elseAccepted, accepted⟩ := bind_ok accepted
          obtain ⟨checkedUnit, thenChecked, accepted⟩ := bind_ok accepted
          cases checkedUnit
          obtain ⟨checkedUnit, elseChecked, accepted⟩ := bind_ok accepted
          cases checkedUnit
          cases accepted
          obtain ⟨conditionDepth, conditionBound, conditionTree⟩ := ih conditionAccepted
          obtain ⟨thenDepth, thenBound, thenTree⟩ := ih thenAccepted
          obtain ⟨elseDepth, elseBound, elseTree⟩ := ih elseAccepted
          rw [← ensureType_ok conditionChecked] at conditionTree
          rw [← ensureType_ok thenChecked] at thenTree
          rw [← ensureType_ok elseChecked] at elseTree
          exact ⟨max conditionDepth (max thenDepth elseDepth) + 1, by omega,
            .conditional metadata form conditionTree thenTree elseTree⟩
      | group inner =>
          simp only [form] at accepted
          obtain ⟨child, childAccepted, accepted⟩ := bind_ok accepted
          obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
          cases checkedUnit
          cases accepted
          obtain ⟨depth, bound, childTree⟩ := ih childAccepted
          exact ⟨depth + 1, by omega, .group (ensureType_ok checked ▸ metadata) form childTree⟩
      | tuple elements =>
          cases elements with
          | nil =>
              simp only [form] at accepted
              exact tree_of_basicLeaf unique found
                (by intro inner impossible; rw [form] at impossible; cases impossible)
                (by intro left right impossible; rw [form] at impossible; cases impossible) accepted
          | cons left rest =>
              cases rest with
              | nil =>
                  simp only [form] at accepted
                  exact tree_of_basicLeaf unique found
                    (by intro inner impossible; rw [form] at impossible; cases impossible)
                    (by intro left right impossible; rw [form] at impossible; cases impossible) accepted
              | cons right rest =>
                  cases rest with
                  | cons =>
                      simp only [form] at accepted
                      exact tree_of_basicLeaf unique found
                        (by intro inner impossible; rw [form] at impossible; cases impossible)
                        (by intro left right impossible; rw [form] at impossible; cases impossible) accepted
                  | nil =>
                      simp only [form] at accepted
                      obtain ⟨leftResult, leftAccepted, accepted⟩ := bind_ok accepted
                      obtain ⟨rightResult, rightAccepted, accepted⟩ := bind_ok accepted
                      obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
                      cases checkedUnit
                      cases accepted
                      obtain ⟨leftDepth, leftBound, leftTree⟩ := ih leftAccepted
                      obtain ⟨rightDepth, rightBound, rightTree⟩ := ih rightAccepted
                      have same := ensureType_ok checked
                      rw [same]
                      exact ⟨max leftDepth rightDepth + 1, by omega,
                        .pair (same ▸ metadata) form leftTree rightTree⟩
      | literal | reference | integerLiteral | unary | binary | lambda | call | constructor | member | proxy | index =>
          simp only [form] at accepted
          exact tree_of_basicLeaf unique found
            (by intro inner impossible; rw [form] at impossible; cases impossible)
            (by intro left right impossible; rw [form] at impossible; cases impossible) accepted

theorem Tree.lower
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Core.Word}
    {id : ExpressionId} {type : Core.Ty} {code : Core.Expr} {depth : Nat}
    (tree : Tree source scope reasonAt id type code depth)
    (unique : NodeOccurrencesUnique source) (fuel : Nat) (enough : depth ≤ fuel) :
    SourceCoreControl.lowerExpressionWithReasons fuel source scope id reasonAt = .ok ⟨type, code⟩ := by
  induction tree generalizing fuel with
  | unit metadata form =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [SourceCoreControl.lowerExpressionWithReasons, metadata.read unique, bind, Except.bind, form]
          exact SourceCoreBasic.lowerExpression_unit (metadata.read unique) form
  | bool value metadata form =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [SourceCoreControl.lowerExpressionWithReasons, metadata.read unique, bind, Except.bind, form]
          exact SourceCoreBasic.lowerExpression_bool (metadata.read unique) form
  | word value metadata form meaning =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [SourceCoreControl.lowerExpressionWithReasons, metadata.read unique, bind, Except.bind, form]
          exact SourceCoreBasic.lowerExpression_word (metadata.read unique) form (interpretWordLiteral?_complete meaning)
  | localRead metadata form owned slot =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [SourceCoreControl.lowerExpressionWithReasons, metadata.read unique, bind, Except.bind, form]
          apply SourceCoreBasic.lowerExpression_local (metadata.read unique) form
          exact SourceCoreLocalCell.lowerRead_eq (lookupExpression?_complete unique metadata.contains)
            form owned metadata.requirements metadata.coercions slot (metadata.types.lower _) _
  | group metadata form child ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp [SourceCoreControl.lowerExpressionWithReasons, metadata.read unique, form,
            ih fuel (by omega), SourceCoreBasic.ensureType, bind, Except.bind, pure, Pure.pure, Except.pure]
  | pair metadata form left right leftIH rightIH =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp [SourceCoreControl.lowerExpressionWithReasons, metadata.read unique, form,
            leftIH fuel (by omega), rightIH fuel (by omega), SourceCoreBasic.ensureType,
            bind, Except.bind, pure, Pure.pure, Except.pure]
  | conditional metadata form condition thenBranch elseBranch conditionIH thenIH elseIH =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          exact SourceCoreControl.lowerExpression_conditional (metadata.read unique) form
            (conditionIH fuel (by omega)) (thenIH fuel (by omega)) (elseIH fuel (by omega))

theorem lowerExpression_hasType
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreControl.lowerExpressionWithReasons fuel source scope id reasonAt = .ok lowered) :
    Core.HasType (SourceCoreLocalCell.coreContext scope) lowered.expression
      (Core.LanguageResult.resultType lowered.type) := by
  obtain ⟨_, _, tree⟩ := tree_of_lowerExpression unique accepted
  exact tree.hasType

theorem Tree.metadata
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Core.Word}
    {id : ExpressionId} {type : Core.Ty} {code : Core.Expr} {depth : Nat}
    (tree : Tree source scope reasonAt id type code depth) :
    ∃ node, Metadata source id node type := by
  cases tree with
  | unit metadata _ | bool _ metadata _ | word _ metadata _ _ | localRead metadata _ _ _
  | group metadata _ _ | pair metadata _ _ _ | conditional metadata _ _ _ _ => exact ⟨_, metadata⟩

theorem lowerExpression_metadata
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreControl.lowerExpressionWithReasons fuel source scope id reasonAt = .ok lowered) :
    ∃ node, SourceCoreBasic.readExpression source id = .ok (node, lowered.type) ∧
      Metadata source id node lowered.type := by
  obtain ⟨_, _, tree⟩ := tree_of_lowerExpression unique accepted
  obtain ⟨node, metadata⟩ := tree.metadata
  exact ⟨node, metadata.read unique, metadata⟩

/-- Actual accepted output has a finite independent source and Core evaluation.
Fault correspondence records the executed read occurrence, not just its location. -/
theorem lowerExpression_preserves
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreControl.lowerExpressionWithReasons fuel source scope id reasonAt = .ok lowered)
    (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    (environments : EnvRepresents world scope environment coreEnvironment)
    (heaps : HeapRepresents heap.cells store world) :
    ∃ sourceOutcome coreValue,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id sourceOutcome heap ∧
      OutcomeRepresents program context evidence source environment heap reasonAt id lowered.type sourceOutcome coreValue ∧
      Core.Evaluates coreEnvironment store lowered.expression coreValue store := by
  obtain ⟨_, _, tree⟩ := tree_of_lowerExpression unique accepted
  exact tree.preserves program context evidence environments heaps

/-- Every completed machine run agrees with the derived source result and
unchanged store. The finite grammar supplies sufficient runtime fuel; this is
not an unrestricted normalization or source-fault completeness statement. -/
theorem lowerExpression_run_preserves
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreControl.lowerExpressionWithReasons fuel source scope id reasonAt = .ok lowered)
    (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    (environments : EnvRepresents world scope environment coreEnvironment)
    (heaps : HeapRepresents heap.cells store world) :
    Core.infer? (SourceCoreLocalCell.coreContext scope) lowered.expression =
      some (Core.LanguageResult.resultType lowered.type) ∧
    ∃ sourceOutcome coreValue required,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id sourceOutcome heap ∧
      OutcomeRepresents program context evidence source environment heap reasonAt id lowered.type sourceOutcome coreValue ∧
      (∀ fuel, required ≤ fuel → Core.runStateful fuel (.initial lowered.expression coreEnvironment store) =
        .done coreValue store) ∧
      (∀ fuel actual actualStore, Core.runStateful fuel (.initial lowered.expression coreEnvironment store) =
        .done actual actualStore → actual = coreValue ∧ actualStore = store) := by
  obtain ⟨sourceOutcome, coreValue, sourceEvaluation, related, coreEvaluation⟩ :=
    lowerExpression_preserves unique accepted program context evidence environments heaps
  obtain ⟨required, completes⟩ := Core.evaluation_runStateful_complete_with_sufficient_fuel coreEvaluation
  refine ⟨Core.infer_complete (lowerExpression_hasType unique accepted),
    sourceOutcome, coreValue, required, sourceEvaluation, related, completes, ?_⟩
  intro fuel actual actualStore completed
  exact Core.evaluation_deterministic (Core.runStateful_evaluation_sound completed) coreEvaluation

end Solcore.SourceSemantics.CoreLowering.ControlExpressions
