import Solcore.Frontend.SourceCoreBasic
import Solcore.SourceSemantics.CoreLowering.HeapMutation

/-!
Meaning preservation for the ordinary scalar/product expression compiler.

The certificate records source occurrences and metadata, not a successful
compiler call. It includes local reads, grouping and binary tuples with
left-to-right failure propagation. Corresponding heaps contain ordinary
optional cells only. The reason word is the compiler's supplied failure token;
a complete source fault-site table is outside this fragment.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.BasicExpressions

open Frontend Frontend.SourceInference TypeSystem
open LocalCell

structure Metadata (source : TypedSource) (id : ExpressionId)
    (node : ExpressionNode) (type : Core.Ty) : Prop where
  contains : ContainsExpression source id node
  owned : id.occurrence.owner = source.owner
  types : TypeRepresents node.type type
  requirements : node.requirements = []
  coercions : node.coercions = []

theorem Metadata.read {source : TypedSource} {id : ExpressionId}
    {node : ExpressionNode} {type : Core.Ty}
    (metadata : Metadata source id node type) (unique : NodeOccurrencesUnique source) :
    SourceCoreBasic.readExpression source id = .ok (node, type) := by
  simp [SourceCoreBasic.readExpression, metadata.owned,
    lookupExpression?_complete unique metadata.contains,
    metadata.requirements, metadata.coercions, SourceCoreBasic.projectType,
    metadata.types.lower _, Except.mapError, bind, Except.bind, pure, Pure.pure, Except.pure]

inductive Tree (source : TypedSource) (scope : SourceCoreLocalCell.Scope) (reason : Core.Word) :
    ExpressionId → Core.Ty → Core.Expr → Nat → Prop where
  | unit {id : ExpressionId} {node : ExpressionNode}
      (metadata : Metadata source id node .unit) (form : node.form = .tuple []) :
      Tree source scope reason id .unit (Core.LanguageResult.success .unit) 1
  | bool {id : ExpressionId} {node : ExpressionNode} {name : String} (value : Bool)
      (metadata : Metadata source id node .bool)
      (form : node.form = .reference name (.builtinBoolean value)) :
      Tree source scope reason id .bool (Core.LanguageResult.success (.bool value)) 1
  | word {id : ExpressionId} {node : ExpressionNode} {literal : Syntax.CoreLiteralValue}
      (value : Core.Word) (metadata : Metadata source id node .word)
      (form : node.form = .literal literal)
      (meaning : WordLiteralDenotes ⟨node.span, literal⟩ value) :
      Tree source scope reason id .word (Core.LanguageResult.success (.word value)) 1
  | localRead {id : ExpressionId} {node : ExpressionNode} {type : Core.Ty}
      {binder : Resolved.LocalId} {name : String} {index : Nat}
      (metadata : Metadata source id node type)
      (form : node.form = .reference name (.local binder))
      (owned : binder.owner = source.owner)
      (slot : SourceCoreLocalCell.lookup? scope binder = some (index, type)) :
      Tree source scope reason id type (Core.OptionalCell.read type (.var index) reason) 1
  | group {id inner : ExpressionId} {node : ExpressionNode} {type : Core.Ty}
      {expression : Core.Expr} {depth : Nat}
      (metadata : Metadata source id node type) (form : node.form = .group inner)
      (child : Tree source scope reason inner type expression depth) :
      Tree source scope reason id type expression (depth + 1)
  | pair {id left right : ExpressionId} {node : ExpressionNode}
      {leftType rightType : Core.Ty} {leftCode rightCode : Core.Expr} {leftDepth rightDepth : Nat}
      (metadata : Metadata source id node (.product leftType rightType))
      (form : node.form = .tuple [left, right])
      (leftTree : Tree source scope reason left leftType leftCode leftDepth)
      (rightTree : Tree source scope reason right rightType rightCode rightDepth) :
      Tree source scope reason id (.product leftType rightType)
        (Core.LocalSequence.pair leftType rightType leftCode rightCode)
        (max leftDepth rightDepth + 1)

theorem Tree.wellFormed {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reason : Core.Word} {id : ExpressionId} {type : Core.Ty} {expression : Core.Expr} {depth : Nat}
    (tree : Tree source scope reason id type expression depth) : Core.Ty.WellFormed [] type := by
  cases tree with
  | unit metadata _ | bool _ metadata _ | word _ metadata _ _ | localRead metadata _ _ _
  | group metadata _ _ | pair metadata _ _ _ => exact metadata.types.wellFormed []

theorem Tree.cellPayload {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reason : Core.Word} {id : ExpressionId} {type : Core.Ty} {expression : Core.Expr} {depth : Nat}
    (tree : Tree source scope reason id type expression depth) : Core.CellPayload type := by
  cases tree with
  | unit metadata _ | bool _ metadata _ | word _ metadata _ _ | localRead metadata _ _ _
  | group metadata _ _ | pair metadata _ _ _ => exact metadata.types.cellPayload

theorem Tree.hasType {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reason : Core.Word} {id : ExpressionId} {type : Core.Ty} {expression : Core.Expr} {depth : Nat}
    (tree : Tree source scope reason id type expression depth) :
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

inductive OutcomeRepresents (type : Core.Ty) (reason : Core.Word) :
    Dynamic.ExpressionOutcome → Core.Value → Prop where
  | value (value : SourceStagedValue.Value)
      (typed : SourceStagedValue.coreType value = type) :
      OutcomeRepresents type reason (.value (StagedValue.toSource value))
        (.inRight .word (SourceStagedValue.toCore value))
  | uninitialized (location : Dynamic.Location) :
      OutcomeRepresents type reason (.fault (.uninitializedLocation location))
        (.inLeft type (.word reason))

/-- Every sufficient traversal budget produces the certificate's expression.
The certificate contains no compiler-success or source-evaluation premise. -/
theorem Tree.lower {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reason : Core.Word} {id : ExpressionId} {type : Core.Ty} {expression : Core.Expr} {depth : Nat}
    (tree : Tree source scope reason id type expression depth)
    (unique : NodeOccurrencesUnique source) (fuel : Nat) (enough : depth ≤ fuel) :
    SourceCoreBasic.lowerExpression fuel source scope id reason = .ok ⟨type, expression⟩ := by
  induction tree generalizing fuel with
  | unit metadata form =>
      cases fuel with
      | zero => omega
      | succ fuel => exact SourceCoreBasic.lowerExpression_unit (metadata.read unique) form
  | bool value metadata form =>
      cases fuel with
      | zero => omega
      | succ fuel => exact SourceCoreBasic.lowerExpression_bool (metadata.read unique) form
  | word value metadata form meaning =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          exact SourceCoreBasic.lowerExpression_word (metadata.read unique) form
            (interpretWordLiteral?_complete meaning)
  | localRead metadata form owned slot =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          exact SourceCoreBasic.lowerExpression_local (metadata.read unique) form
            (SourceCoreLocalCell.lowerRead_eq
              (lookupExpression?_complete unique metadata.contains) form owned
              metadata.requirements metadata.coercions slot (metadata.types.lower _) reason)
  | group metadata form child inductionHypothesis =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          exact SourceCoreBasic.lowerExpression_group (metadata.read unique) form
            (inductionHypothesis fuel (by omega))
  | pair metadata form leftTree rightTree leftInduction rightInduction =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          exact SourceCoreBasic.lowerExpression_pair (metadata.read unique) form
            (leftInduction fuel (by omega)) (rightInduction fuel (by omega))

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
    {reason : Core.Word} {id : ExpressionId} {type : Core.Ty} {expression : Core.Expr} {depth : Nat}
    (tree : Tree source scope reason id type expression depth)
    (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    (environments : EnvRepresents world scope environment coreEnvironment)
    (heaps : HeapRepresents heap.cells store world) :
    ∃ sourceOutcome coreValue,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id
        sourceOutcome heap ∧
      OutcomeRepresents type reason sourceOutcome coreValue ∧
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
            coreEnvironment store location _ lookup read cellType rfl rfl coreLookup coreRead reason
          exact ⟨_, _, .fault fault, .uninitialized location, evaluated⟩
      | initialized value =>
          obtain ⟨evaluated, coreEvaluated⟩ := site.initialized program context evidence environment heap
            coreEnvironment store location _ value lookup read rfl rfl coreLookup coreRead reason
          exact ⟨_, _, .value evaluated, .value value rfl, coreEvaluated⟩
  | group metadata form child inductionHypothesis =>
      obtain ⟨outcome, coreValue, evaluated, related, coreEvaluated⟩ := inductionHypothesis
      refine ⟨outcome, coreValue, ?_, related, coreEvaluated⟩
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
      | uninitialized location =>
          cases leftSource with
          | fault fault =>
              refine ⟨_, _, .fault ?_, .uninitialized location,
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
              | uninitialized location =>
                  cases rightSource with
                  | fault fault =>
                      refine ⟨_, _, .fault ?_, .uninitialized location,
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

/-- Actual compilation, Core checking and finite execution agree with an
independent source outcome. Completed runs reflect that same result/store;
smaller runtime fuel may retain a checkpoint. -/
theorem Tree.lower_run_preserves {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reason : Core.Word} {id : ExpressionId} {type : Core.Ty} {expression : Core.Expr} {depth : Nat}
    (tree : Tree source scope reason id type expression depth)
    (unique : NodeOccurrencesUnique source) (compilationFuel : Nat) (enough : depth ≤ compilationFuel)
    (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    (environments : EnvRepresents world scope environment coreEnvironment)
    (heaps : HeapRepresents heap.cells store world) :
    SourceCoreBasic.lowerExpression compilationFuel source scope id reason = .ok ⟨type, expression⟩ ∧
    Core.infer? (SourceCoreLocalCell.coreContext scope) expression =
      some (Core.LanguageResult.resultType type) ∧
    ∃ sourceOutcome coreValue required,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id
        sourceOutcome heap ∧
      OutcomeRepresents type reason sourceOutcome coreValue ∧
      (∀ fuel, required ≤ fuel → Core.runStateful fuel
        (.initial expression coreEnvironment store) = .done coreValue store) ∧
      (∀ fuel result finalStore, Core.runStateful fuel
        (.initial expression coreEnvironment store) = .done result finalStore →
          result = coreValue ∧ finalStore = store) := by
  obtain ⟨sourceOutcome, coreValue, sourceEvaluation, outcome, coreEvaluation⟩ :=
    tree.preserves program context evidence environments heaps
  obtain ⟨required, completes⟩ :=
    Core.evaluation_runStateful_complete_with_sufficient_fuel coreEvaluation
  refine ⟨tree.lower unique compilationFuel enough, Core.infer_complete tree.hasType,
    sourceOutcome, coreValue, required, sourceEvaluation, outcome, completes, ?_⟩
  intro fuel result finalStore completed
  exact Core.evaluation_deterministic (Core.runStateful_evaluation_sound completed) coreEvaluation

end Solcore.SourceSemantics.CoreLowering.BasicExpressions
