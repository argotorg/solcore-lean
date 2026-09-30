import Solcore.Frontend.SourceCoreElaboration
import Solcore.SourceSemantics.CoreLowering.StagedValue
import Solcore.SourceSemantics.Dynamic.Evaluation

/-!
Meaning preservation for the existing expression lowerer's literal trees.

The certificate below is a declarative finite grammar over actual source
occurrences. It requires exact type metadata, empty evidence/coercion paths,
and strict in-range Word literals. It neither assumes a compiler result nor
uses the typed-source evaluator. The internal lowering profile has no staged
cache, so these results do not establish correctness of staging or of the
whole-program compilation pipeline.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.Literals

open Frontend Frontend.SourceInference TypeSystem

/-- Closed literal trees accepted by the current ordinary-expression profile.
The index records a sufficient traversal depth, not runtime execution fuel. -/
inductive Tree (source : TypedSource) :
    ExpressionId → SourceStagedValue.Value → Nat → Prop where
  | unit {id : ExpressionId} {node : ExpressionNode}
      (contains : ContainsExpression source id node)
      (form : node.form = .tuple []) (typed : node.type = .unit)
      (requirements : node.requirements = []) (coercions : node.coercions = []) :
      Tree source id .unit 1
  | bool {id : ExpressionId} {node : ExpressionNode} {name : String} {value : Bool}
      (contains : ContainsExpression source id node)
      (form : node.form = .reference name (.builtinBoolean value))
      (typed : node.type = .bool)
      (requirements : node.requirements = []) (coercions : node.coercions = []) :
      Tree source id (.bool value) 1
  | word {id : ExpressionId} {node : ExpressionNode}
      {literal : Syntax.CoreLiteralValue} {value : Core.Word}
      (contains : ContainsExpression source id node)
      (form : node.form = .literal literal) (typed : node.type = .word)
      (requirements : node.requirements = []) (coercions : node.coercions = [])
      (meaning : WordLiteralDenotes ⟨node.span, literal⟩ value) :
      Tree source id (.word value) 1
  | pair {id leftId rightId : ExpressionId} {node : ExpressionNode}
      {left right : SourceStagedValue.Value} {leftDepth rightDepth : Nat}
      (contains : ContainsExpression source id node)
      (form : node.form = .tuple [leftId, rightId])
      (typed : node.type = .product (SourceStagedValue.sourceType left)
        (SourceStagedValue.sourceType right))
      (requirements : node.requirements = []) (coercions : node.coercions = [])
      (leftTree : Tree source leftId left leftDepth)
      (rightTree : Tree source rightId right rightDepth) :
      Tree source id (.product left right) (max leftDepth rightDepth + 1)

private theorem lowerType_sourceType (value : SourceStagedValue.Value)
    (site : SourceCoreElaboration.ErrorSite) :
    SourceCoreElaboration.lowerType site (SourceStagedValue.sourceType value) =
      .ok (SourceStagedValue.coreType value) := by
  induction value with
  | unit | bool | word => rfl
  | product left right leftInduction rightInduction =>
      exact SourceCoreElaboration.lowerType_product leftInduction rightInduction

/-- The actual recursive lowerer succeeds for every sufficient traversal
budget; no lowering-success premise appears in the certificate. -/
theorem Tree.lower {source : TypedSource} {id : ExpressionId}
    {value : SourceStagedValue.Value} {depth : Nat}
    (tree : Tree source id value depth) (unique : NodeOccurrencesUnique source)
    (scope : Resolved.Context) (fuel : Nat) (enough : depth ≤ fuel) :
    SourceCoreElaboration.Internal.lowerExpression fuel source scope id =
      .ok { resolved := SourceStagedValue.toResolved value
            consumedRequirements := [] } := by
  induction tree generalizing fuel with
  | unit contains form typed requirements coercions =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          exact SourceCoreElaboration.Internal.lowerExpression_unit
            fuel source scope _ _ (lookupExpression?_complete unique contains)
            form typed requirements coercions
  | bool contains form typed requirements coercions =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          exact SourceCoreElaboration.Internal.lowerExpression_bool
            fuel source scope _ _ _ _ (lookupExpression?_complete unique contains)
            form typed requirements coercions
  | word contains form typed requirements coercions meaning =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          exact SourceCoreElaboration.Internal.lowerExpression_word
            fuel source scope _ _ _ _ (lookupExpression?_complete unique contains)
            form typed requirements coercions meaning
  | pair contains form typed requirements coercions _ _ leftInduction rightInduction =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          exact SourceCoreElaboration.Internal.lowerExpression_pair fuel source scope
            _ _ _ _ _ _ _ _ _ _ (lookupExpression?_complete unique contains)
            form typed requirements coercions (lowerType_sourceType _ _)
            (lowerType_sourceType _ _) (leftInduction fuel (by omega))
            (rightInduction fuel (by omega))

private theorem word_constructs {span : Syntax.SourceSpan}
    {literal : Syntax.CoreLiteralValue} {value : Core.Word}
    (meaning : WordLiteralDenotes ⟨span, literal⟩ value) :
    Dynamic.LiteralConstructs literal (.word value) := by
  have modulo : Core.Word.ofNatModulo value.val = value := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt value.isLt
  rw [← modulo]
  exact .word meaning

/-- Each tree has an independent source derivation in every surrounding
runtime context, and does not change its heap. -/
theorem Tree.source_evaluates {source : TypedSource} {id : ExpressionId}
    {value : SourceStagedValue.Value} {depth : Nat}
    (tree : Tree source id value depth)
    (program : Program) (context : Context)
    (evidence : Dynamic.EvidenceEnvironment) (environment : Dynamic.Environment)
    (heap : Dynamic.Heap) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap
      id (StagedValue.toSource value) heap := by
  induction tree with
  | unit contains form typed requirements coercions =>
      apply Dynamic.ExpressionEvaluates.intro contains
      · rw [form, requirements, coercions]
        exact .tuple rfl .nil .nil
      · rw [coercions]
        exact .nil
  | bool contains form typed requirements coercions =>
      apply Dynamic.ExpressionEvaluates.intro contains
      · rw [form, requirements, coercions]
        exact .builtinBoolean rfl
      · rw [coercions]
        exact .nil
  | word contains form typed requirements coercions meaning =>
      apply Dynamic.ExpressionEvaluates.intro contains
      · rw [form, requirements, coercions]
        exact .literal rfl (word_constructs meaning)
      · rw [coercions]
        exact .nil
  | pair contains form typed requirements coercions _ _ leftInduction rightInduction =>
      apply Dynamic.ExpressionEvaluates.intro contains
      · rw [form, requirements, coercions]
        exact .tuple rfl (.cons leftInduction (.cons rightInduction .nil))
          (.cons (.singleton _))
      · rw [coercions]
        exact .nil

private theorem contains_unique {source : TypedSource} {id : ExpressionId}
    {left right : ExpressionNode} (unique : NodeOccurrencesUnique source)
    (leftContains : ContainsExpression source id left)
    (rightContains : ContainsExpression source id right) : left = right := by
  have leftLookup := lookupExpression?_complete unique leftContains
  have rightLookup := lookupExpression?_complete unique rightContains
  rw [leftLookup] at rightLookup
  exact Option.some.inj rightLookup

private theorem expression_evaluation_raw
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : ExpressionId} {node : ExpressionNode}
    {result : Dynamic.Value}
    (unique : NodeOccurrencesUnique source)
    (contains : ContainsExpression source id node)
    (ordinary : ∀ name binder, node.form ≠ .reference name (.local binder))
    (empty : node.coercions = [])
    (evaluated : Dynamic.ExpressionEvaluates program context evidence source
      environment before id result after) :
    Dynamic.ExpressionFormEvaluates program context evidence source environment
      before node.form node.requirements node.coercions result after := by
  cases evaluated with
  | intro otherContains form coercions =>
      have same := contains_unique unique otherContains contains
      rw [same] at form coercions
      rw [empty] at coercions
      cases coercions
      exact form
  | generalizedLocal otherContains form _ _ _ _ _ _ _ =>
      have same := contains_unique unique otherContains contains
      rw [same] at form
      exact False.elim (ordinary _ _ form)

/-- Every independent successful source derivation has exactly the literal
tree's value and unchanged heap. Occurrence uniqueness rules out an alternate
node at the same ID; no whole-language determinism assumption is used. -/
theorem Tree.source_sound {source : TypedSource} {id : ExpressionId}
    {value : SourceStagedValue.Value} {depth : Nat}
    (tree : Tree source id value depth) (unique : NodeOccurrencesUnique source)
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {result : Dynamic.Value}
    (evaluated : Dynamic.ExpressionEvaluates program context evidence source
      environment before id result after) :
    result = StagedValue.toSource value ∧ after = before := by
  induction tree generalizing before after result with
  | unit contains form typed requirements coercions =>
      have raw := expression_evaluation_raw unique contains
        (by simp [form]) coercions evaluated
      rw [form] at raw
      cases raw with
      | tuple _ elements pack =>
          cases elements
          cases pack
          exact ⟨rfl, rfl⟩
  | bool contains form typed requirements coercions =>
      have raw := expression_evaluation_raw unique contains
        (by simp [form]) coercions evaluated
      rw [form] at raw
      cases raw
      exact ⟨rfl, rfl⟩
  | word contains form typed requirements coercions meaning =>
      have raw := expression_evaluation_raw unique contains
        (by simp [form]) coercions evaluated
      rw [form] at raw
      cases raw with
      | literal _ construction =>
          exact ⟨Dynamic.LiteralConstructs.functional construction
            (word_constructs meaning), rfl⟩
  | pair contains form typed requirements coercions _ _ leftInduction rightInduction =>
      have raw := expression_evaluation_raw unique contains
        (by simp [form]) coercions evaluated
      rw [form] at raw
      cases raw with
      | tuple _ elements pack =>
          cases elements with
          | cons left rest =>
              cases rest with
              | cons right rest =>
                  cases rest
                  obtain ⟨rfl, rfl⟩ := leftInduction left
                  obtain ⟨rfl, rfl⟩ := rightInduction right
                  exact ⟨Dynamic.ValuesPack.functional pack
                    (.cons (.singleton _)), rfl⟩

/-- The existing ordinary expression traversal followed by the existing
resolved-to-Core traversal. This is a relation over their actual outputs. -/
def ExpressionLowers (fuel : Nat) (source : TypedSource)
    (scope : Resolved.Context) (id : ExpressionId) (expression : Core.Expr) : Prop :=
  ∃ lowered : SourceCoreElaboration.LoweredExpression,
    SourceCoreElaboration.Internal.lowerExpression fuel source scope id =
      .ok lowered ∧ lowered.resolved.lower? (scope.map Prod.fst) = some expression

section Correspondence

variable {source : TypedSource} {id : ExpressionId}
  {value : SourceStagedValue.Value} {depth traversalFuel : Nat}
  (tree : Tree source id value depth) (unique : NodeOccurrencesUnique source)
  (scope : Resolved.Context) (enough : depth ≤ traversalFuel)

include tree unique enough

/-- Construct an actual successful lowering, rather than requiring compiler
acceptance as part of the source certificate. -/
theorem Tree.lowers : ExpressionLowers traversalFuel source scope id
    (SourceStagedValue.toCoreExpr value) :=
  ⟨{ resolved := SourceStagedValue.toResolved value, consumedRequirements := [] },
    tree.lower unique scope traversalFuel enough,
    SourceStagedValue.toResolved_lower value (scope.map Prod.fst)⟩

theorem Tree.lowering_unique {expression : Core.Expr}
    (lowered : ExpressionLowers traversalFuel source scope id expression) :
    expression = SourceStagedValue.toCoreExpr value := by
  obtain ⟨intermediate, compiled, resolved⟩ := lowered
  rw [tree.lower unique scope traversalFuel enough] at compiled
  cases compiled
  rw [SourceStagedValue.toResolved_lower] at resolved
  exact (Option.some.inj resolved).symm

/-- Core checker acceptance is derived from the lowering output, rather than
added as an assumption of semantic preservation. -/
theorem Tree.lowered_infers {expression : Core.Expr}
    (lowered : ExpressionLowers traversalFuel source scope id expression)
    (context : Core.Context) (definitions : Core.DataEnvironment) :
    Core.infer? context expression definitions =
      some (SourceStagedValue.coreType value) := by
  rw [tree.lowering_unique unique scope enough lowered]
  exact StagedValue.toCoreExpr_infers value context definitions

/-- Finite successful executions agree in both directions. Both final heaps
are explicit: literal trees leave the source heap and the Core store intact.
The source side is the independent occurrence-based dynamic judgment. -/
theorem Tree.evaluates_iff {expression : Core.Expr}
    (lowered : ExpressionLowers traversalFuel source scope id expression)
    (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (sourceEnvironment : Dynamic.Environment)
    (sourceBefore sourceAfter : Dynamic.Heap)
    (coreEnvironment : Core.Environment) (coreBefore coreAfter : Core.Store)
    (result : Core.Value) :
    (Core.Evaluates coreEnvironment coreBefore expression result coreAfter ∧
        sourceAfter = sourceBefore) ↔
      ∃ sourceResult,
        Dynamic.ExpressionEvaluates program context evidence source sourceEnvironment
          sourceBefore id sourceResult sourceAfter ∧
        StagedValue.Represents sourceResult result ∧ coreAfter = coreBefore := by
  rw [tree.lowering_unique unique scope enough lowered]
  constructor
  · rintro ⟨evaluated, sameHeap⟩
    subst sourceAfter
    obtain ⟨related, sameStore⟩ := (StagedValue.toCoreExpr_evaluates_iff value
      coreEnvironment coreBefore result coreAfter).1 evaluated
    exact ⟨StagedValue.toSource value,
      tree.source_evaluates program context evidence sourceEnvironment sourceBefore,
      related, sameStore⟩
  · rintro ⟨sourceResult, evaluated, related, sameStore⟩
    obtain ⟨sameValue, sameHeap⟩ := tree.source_sound unique evaluated
    rw [sameValue] at related
    exact ⟨(StagedValue.toCoreExpr_evaluates_iff value coreEnvironment coreBefore
      result coreAfter).2 ⟨related, sameStore⟩, sameHeap⟩

/-- A finite source derivation yields a sufficiently fueled completed Core
execution. Traversal fuel and runtime fuel are separate quantities. -/
theorem Tree.run_complete {expression : Core.Expr}
    (lowered : ExpressionLowers traversalFuel source scope id expression)
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {sourceEnvironment : Dynamic.Environment}
    {sourceBefore sourceAfter : Dynamic.Heap} {sourceResult : Dynamic.Value}
    (evaluated : Dynamic.ExpressionEvaluates program context evidence source
      sourceEnvironment sourceBefore id sourceResult sourceAfter)
    (coreEnvironment : Core.Environment) (coreBefore : Core.Store) :
    ∃ required, ∀ fuel, required ≤ fuel →
      ∃ result,
        Core.runStateful fuel (Core.State.initial expression coreEnvironment coreBefore) =
          .done result coreBefore ∧
        StagedValue.Represents sourceResult result ∧ sourceAfter = sourceBefore := by
  rw [tree.lowering_unique unique scope enough lowered]
  obtain ⟨sameValue, sameHeap⟩ := tree.source_sound unique evaluated
  obtain ⟨required, completes⟩ :=
    StagedValue.toCoreExpr_run_complete value coreEnvironment coreBefore
  refine ⟨required, fun fuel enoughFuel => ⟨SourceStagedValue.toCore value,
    completes fuel enoughFuel, ?_, sameHeap⟩⟩
  rw [sameValue]
  exact StagedValue.toCore_represents value

/-- Any completed Core execution of the actual lowering output reflects a
finite source derivation and its represented value, with both stores intact. -/
theorem Tree.run_sound {expression : Core.Expr}
    (lowered : ExpressionLowers traversalFuel source scope id expression)
    (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (sourceEnvironment : Dynamic.Environment) (sourceHeap : Dynamic.Heap)
    (coreEnvironment : Core.Environment) (coreBefore : Core.Store)
    {fuel : Nat} {result : Core.Value} {coreAfter : Core.Store}
    (executed : Core.runStateful fuel
      (Core.State.initial expression coreEnvironment coreBefore) = .done result coreAfter) :
    ∃ sourceResult,
      Dynamic.ExpressionEvaluates program context evidence source sourceEnvironment
        sourceHeap id sourceResult sourceHeap ∧
      StagedValue.Represents sourceResult result ∧ coreAfter = coreBefore :=
  (tree.evaluates_iff unique scope enough lowered program context evidence
    sourceEnvironment sourceHeap sourceHeap coreEnvironment coreBefore coreAfter result).1
      ⟨Core.runStateful_evaluation_sound executed, rfl⟩

end Correspondence

end Solcore.SourceSemantics.CoreLowering.Literals
